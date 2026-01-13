//===--- VerificationSpec.h - Verification Specification Types -*- C++ -*-===//
//
// This source file is part of the tSwift project
//
// Copyright (c) 2026 Dropbox, Inc. All rights reserved.
// Licensed under Apache License v2.0
//
//===----------------------------------------------------------------------===//
//
// This file defines types for representing verification specifications
// extracted from @requires, @ensures, @invariant, and @trusted macros.
//
//===----------------------------------------------------------------------===//

#ifndef SWIFT_SILOPTIMIZER_VERIFICATION_VERIFICATIONSPEC_H
#define SWIFT_SILOPTIMIZER_VERIFICATION_VERIFICATIONSPEC_H

#include "swift/Basic/SourceLoc.h"
#include "llvm/ADT/StringRef.h"
#include <memory>
#include <string>
#include <vector>

namespace swift {

class SILFunction;

namespace verification {
class ConditionExpr;
} // namespace verification

/// Represents a single verification specification extracted from
/// a Swift verification macro (@requires, @ensures, @invariant).
struct VerificationSpec {
  /// The kind of verification specification.
  enum class Kind {
    /// @requires - precondition that must hold at function entry
    Requires,
    /// @ensures - postcondition that must hold at function exit
    Ensures,
    /// @invariant - condition that must hold throughout execution
    Invariant,
  };

  /// The kind of this specification.
  Kind kind;

  /// The condition string from the macro argument.
  /// For example, "x > 0" from @requires("x > 0").
  std::string condition;

  /// The source location of the macro attribute.
  SourceLoc location;

  /// Optional: the function this spec applies to.
  /// Useful for diagnostics and VC generation.
  SILFunction *function = nullptr;

  /// The parsed condition AST, if successfully parsed.
  /// This is populated by parseSpecifications() after extraction.
  std::shared_ptr<verification::ConditionExpr> parsedCondition;

  /// Parse error message, if parsing failed.
  std::string parseError;

  /// Whether the condition was successfully parsed.
  bool isParsed() const { return parsedCondition != nullptr; }

  /// Get a human-readable name for the spec kind.
  static llvm::StringRef kindName(Kind k) {
    switch (k) {
    case Kind::Requires: return "requires";
    case Kind::Ensures: return "ensures";
    case Kind::Invariant: return "invariant";
    }
    llvm_unreachable("Unknown VerificationSpec::Kind");
  }

  llvm::StringRef getKindName() const { return kindName(kind); }
};

/// Result of checking whether a function should be verified.
struct VerificationStatus {
  /// Whether the function is marked @trusted (skip verification).
  bool isTrusted = false;

  /// Extracted verification specifications.
  std::vector<VerificationSpec> specs;

  /// Whether there are any specs to verify.
  bool hasSpecs() const { return !specs.empty(); }

  /// Whether verification should proceed (not trusted and has specs or auto-verify).
  bool shouldVerify() const { return !isTrusted; }
};

/// Extract verification specifications from a SIL function by
/// accessing the underlying AST declaration's custom attributes.
///
/// This function:
/// 1. Gets the AbstractFunctionDecl from the SILFunction's DeclRef
/// 2. Iterates over CustomAttr attributes looking for verification macros
/// 3. Extracts the string argument from @requires/@ensures/@invariant
/// 4. Checks for @trusted to skip verification
///
/// \param F The SIL function to analyze.
/// \return A VerificationStatus containing extracted specs and trusted status.
VerificationStatus extractSpecifications(SILFunction &F);

/// Parse condition strings in verification specs into AST form.
///
/// This function takes a VerificationStatus (from extractSpecifications)
/// and parses each spec's condition string into a ConditionExpr AST.
/// The AST is stored in spec.parsedCondition; errors are stored in
/// spec.parseError.
///
/// \param status The verification status with extracted specs.
/// \param paramNames The function parameter names for reference resolution.
void parseSpecifications(VerificationStatus &status,
                         const std::vector<std::string> &paramNames);

} // end namespace swift

#endif // SWIFT_SILOPTIMIZER_VERIFICATION_VERIFICATIONSPEC_H
