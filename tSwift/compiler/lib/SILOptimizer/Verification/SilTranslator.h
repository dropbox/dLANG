//===--- SilTranslator.h - SIL to ConditionExpr translation -*- C++ ------===//
//
// This source file is part of the tSwift project
//
// Copyright (c) 2026 Dropbox, Inc. All rights reserved.
// Licensed under Apache License v2.0
//
//===----------------------------------------------------------------------===//
//
// This file declares the SIL to ConditionExpr translator for extracting
// function semantics for verification.
//
// For a function like:
//   func double(_ x: Int) -> Int { return x * 2 }
//
// The translator produces a ConditionExpr representing:
//   result = x * 2
//
// This allows verification to prove:
//   @requires("x > 0") && (result = x * 2) => @ensures("result > 0")
//
//===----------------------------------------------------------------------===//

#ifndef SWIFT_SILOPTIMIZER_VERIFICATION_SILTRANSLATOR_H
#define SWIFT_SILOPTIMIZER_VERIFICATION_SILTRANSLATOR_H

#include "ConditionAST.h"
#include "swift/SIL/SILFunction.h"
#include "swift/SIL/SILBasicBlock.h"
#include "swift/SIL/SILInstruction.h"
#include "swift/SIL/SILValue.h"
#include "llvm/ADT/DenseMap.h"
#include <memory>
#include <string>
#include <vector>

namespace swift {
namespace verification {

/// Represents an automatically discovered verification condition.
/// These are implicit safety conditions like overflow checks.
struct AutoVC {
  enum class Kind {
    Overflow,      // Integer overflow check
    DivByZero,     // Division by zero check
    BoundsCheck,   // Array bounds check
    NilCheck       // Optional unwrap check
  };

  /// Source of the auto-VC derivation.
  enum class Source {
    Builtin,       // Derived from SIL builtin instruction (semantic model)
    CondFail       // Derived from cond_fail instruction (runtime check)
  };

  Kind kind;
  Source source;

  /// The expression that must hold to avoid UB.
  /// For overflow: -2^63 <= expr <= 2^63-1
  std::unique_ptr<ConditionExpr> condition;

  /// Human-readable description of the check.
  std::string description;

  /// Source location info
  std::string sourceFile;
  unsigned sourceLine = 0;
  unsigned sourceColumn = 0;

  /// Unique identifier for relating VCs from the same source operation.
  /// VCs with the same checkId are semantically related (e.g., builtin + cond_fail).
  unsigned checkId = 0;

  AutoVC(Kind k, std::unique_ptr<ConditionExpr> cond, llvm::StringRef desc,
         Source src = Source::Builtin)
      : kind(k), source(src), condition(std::move(cond)), description(desc.str()) {}

  AutoVC(AutoVC &&) = default;
  AutoVC &operator=(AutoVC &&) = default;

  const char *getKindName() const {
    switch (kind) {
    case Kind::Overflow: return "overflow";
    case Kind::DivByZero: return "division_by_zero";
    case Kind::BoundsCheck: return "bounds";
    case Kind::NilCheck: return "nil";
    }
    return "unknown";
  }

  const char *getSourceName() const {
    switch (source) {
    case Source::Builtin: return "builtin";
    case Source::CondFail: return "cond_fail";
    }
    return "unknown";
  }

  /// Check if this VC is semantically equivalent to another for de-duplication.
  /// Two VCs are considered duplicates if they have the same kind, come from
  /// the same source location, and originate from related operations.
  bool isDuplicateOf(const AutoVC &other) const {
    // Different kinds are never duplicates
    if (kind != other.kind) return false;
    // Same source type means not a builtin/cond_fail pair
    if (source == other.source) return false;
    // Must be from the same source location
    if (sourceLine != other.sourceLine) return false;
    // Check IDs must match (0 = not assigned, never matches)
    if (checkId == 0 || other.checkId == 0) return false;
    return checkId == other.checkId;
  }
};

/// SMT type for parameter declarations (matches VcIrGen.h SmtType).
enum class ParamSmtType {
  Int,   // SMT-LIB2 Int (arbitrary precision integer)
  Bool   // SMT-LIB2 Bool (boolean value)
};

/// Result of translating a SIL function's semantics.
struct TranslationResult {
  /// The function semantics expression (result = <body>).
  /// Null if translation failed or function is too complex.
  std::unique_ptr<ConditionExpr> semantics;

  /// Parameter name to index mapping.
  std::vector<std::string> paramNames;

  /// Parameter types (Int or Bool). Parallel to paramNames.
  /// Bool corresponds to Builtin.Int1 / Swift Bool parameters.
  std::vector<ParamSmtType> paramTypes;

  /// Automatically discovered verification conditions (overflow, div-by-zero).
  std::vector<AutoVC> autoVCs;

  /// Whether translation succeeded.
  bool success = false;

  /// Reason for failure if !success.
  std::string error;

  /// Statistics
  unsigned instructionsProcessed = 0;
  unsigned unsupportedInstructions = 0;
  unsigned vcsDeduplicated = 0;

  static TranslationResult ok(std::unique_ptr<ConditionExpr> sem,
                              std::vector<std::string> params) {
    TranslationResult r;
    r.semantics = std::move(sem);
    r.paramNames = std::move(params);
    r.success = true;
    return r;
  }

  static TranslationResult fail(llvm::StringRef reason) {
    TranslationResult r;
    r.success = false;
    r.error = reason.str();
    return r;
  }

  /// Remove duplicate auto-VCs.
  /// When both builtin-derived and cond_fail-derived VCs exist for the same
  /// check, keep only the builtin-derived one (more semantic meaning).
  void deduplicateAutoVCs() {
    if (autoVCs.size() < 2) return;

    std::vector<AutoVC> unique;
    unique.reserve(autoVCs.size());

    for (auto &vc : autoVCs) {
      bool isDuplicate = false;
      for (const auto &existing : unique) {
        if (vc.isDuplicateOf(existing)) {
          // Prefer builtin-derived VCs (more semantic meaning)
          if (vc.source == AutoVC::Source::CondFail) {
            isDuplicate = true;
            ++vcsDeduplicated;
            break;
          }
        }
      }
      if (!isDuplicate) {
        unique.push_back(std::move(vc));
      }
    }
    autoVCs = std::move(unique);
  }
};

/// Translates SIL instructions to ConditionExpr for verification.
///
/// The translator performs symbolic execution over straight-line SIL code,
/// mapping SIL values to ConditionExpr trees. It handles:
/// - Function arguments -> ParamRef
/// - Integer literals -> IntLiteral
/// - Arithmetic builtins -> Binary operators
/// - Struct operations -> Pass-through (Int wrapper)
/// - Return -> Function semantics
class SilTranslator {
public:
  /// Translate a SIL function to its semantic ConditionExpr.
  /// Returns (result = <expr>) where <expr> is the computed return value.
  static TranslationResult translate(SILFunction &F);

  /// Collect auto-VCs from a SIL function without requiring full semantics.
  /// This method walks ALL basic blocks and collects safety conditions
  /// (overflow, div-by-zero, bounds, nil) even for multi-block functions.
  /// Unlike translate(), this never fails - it just collects what it can.
  static TranslationResult collectAutoVCs(SILFunction &F);

private:
  SilTranslator() = default;

  /// Map from SIL values to their symbolic expressions.
  llvm::DenseMap<SILValue, std::unique_ptr<ConditionExpr>> valueMap;

  /// Map from SIL values to their associated checkId (for de-duplication).
  llvm::DenseMap<SILValue, unsigned> valueCheckIdMap;

  /// Parameter names in order.
  std::vector<std::string> paramNames;

  /// Parameter types in order (parallel to paramNames).
  std::vector<ParamSmtType> paramTypes;

  /// The return expression (if found).
  std::unique_ptr<ConditionExpr> returnExpr;

  /// Automatically discovered verification conditions.
  std::vector<AutoVC> autoVCs;

  /// Statistics
  unsigned instructionsProcessed = 0;
  unsigned unsupportedInstructions = 0;

  /// Next available checkId for relating VCs.
  unsigned nextCheckId = 1;

  /// Current instruction's source location info (populated during processing).
  std::string currentSourceFile;
  unsigned currentSourceLine = 0;
  unsigned currentSourceColumn = 0;

  /// Process a single basic block.
  bool processBlock(SILBasicBlock &BB);

  /// Process individual instruction types.
  bool processInstruction(SILInstruction &I);
  bool processArgument(SILFunctionArgument *arg);
  bool processIntegerLiteral(IntegerLiteralInst *inst);
  bool processBuiltin(BuiltinInst *inst);
  bool processStructExtract(StructExtractInst *inst);
  bool processStruct(StructInst *inst);
  bool processTupleExtract(TupleExtractInst *inst);
  bool processUncheckedEnumData(UncheckedEnumDataInst *inst);
  bool processUnconditionalCheckedCast(UnconditionalCheckedCastInst *inst);
  bool processReturn(ReturnInst *inst);
  bool processDebugValue(DebugValueInst *inst);
  bool processCondFail(CondFailInst *inst);

  /// Extract source location from a SIL instruction and update current* fields.
  void extractSourceLocation(SILInstruction &I);

  /// Generate an overflow verification condition for an arithmetic operation.
  /// The condition ensures: INT64_MIN <= result <= INT64_MAX
  void addOverflowVC(const ConditionExpr *resultExpr, llvm::StringRef opName,
                     AutoVC::Source source = AutoVC::Source::Builtin,
                     unsigned checkId = 0);

  /// Generate a division-by-zero verification condition.
  /// The condition ensures: divisor != 0
  void addDivByZeroVC(const ConditionExpr *divisorExpr, llvm::StringRef opName,
                      AutoVC::Source source = AutoVC::Source::Builtin,
                      unsigned checkId = 0);

  /// Generate a bounds checking verification condition.
  /// The condition ensures: 0 <= index < length
  void addBoundsVC(const ConditionExpr *indexExpr, const ConditionExpr *lengthExpr,
                   llvm::StringRef opName,
                   AutoVC::Source source = AutoVC::Source::Builtin,
                   unsigned checkId = 0);

  /// Generate a nil check verification condition.
  /// The condition ensures: optional is not nil before force unwrap.
  void addNilCheckVC(const ConditionExpr *optionalExpr, llvm::StringRef opName,
                     AutoVC::Source source = AutoVC::Source::Builtin,
                     unsigned checkId = 0);

  /// Clone an expression (for multiple uses).
  std::unique_ptr<ConditionExpr> cloneExpr(const ConditionExpr *expr);

  /// Get or create expression for a SIL value.
  const ConditionExpr *getExpr(SILValue value);

  /// Store expression for a SIL value.
  void setExpr(SILValue value, std::unique_ptr<ConditionExpr> expr);

  /// Check if we have an expression for a value.
  bool hasExpr(SILValue value) const;

  /// Get checkId associated with a SIL value (0 if none).
  unsigned getCheckId(SILValue value) const;

  /// Associate a checkId with a SIL value.
  void setCheckId(SILValue value, unsigned checkId);
};

} // namespace verification
} // namespace swift

#endif // SWIFT_SILOPTIMIZER_VERIFICATION_SILTRANSLATOR_H
