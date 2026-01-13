//===--- VcIrGen.h - VC IR Generation for SMT-LIB2 output -*- C++ --------===//
//
// This source file is part of the tSwift project
//
// Copyright (c) 2026 Dropbox, Inc. All rights reserved.
// Licensed under Apache License v2.0
//
//===----------------------------------------------------------------------===//
//
// This file declares functions for generating SMT-LIB2 output from
// ConditionExpr AST nodes. The SMT-LIB2 format is used by SMT solvers
// like Z3/Z4 to prove verification conditions.
//
// Example input:
//   @requires("x > 0")
//   @ensures("result >= x")
//   func double(_ x: Int) -> Int { return x * 2 }
//
// Example SMT-LIB2 output:
//   (declare-const x Int)
//   (declare-const result Int)
//   (assert (> x 0))           ; precondition
//   (assert (= result (* x 2))) ; function semantics
//   (assert (not (>= result x))) ; negated postcondition
//   (check-sat)
//   ; Expected: unsat (postcondition is provable)
//
//===----------------------------------------------------------------------===//

#ifndef SWIFT_SILOPTIMIZER_VERIFICATION_VCIRGEN_H
#define SWIFT_SILOPTIMIZER_VERIFICATION_VCIRGEN_H

#include "ConditionAST.h"
#include <string>
#include <vector>
#include <set>
#include <map>

namespace swift {
namespace verification {

/// SMT type for variable declarations.
enum class SmtType {
  Int,   // SMT-LIB2 Int (arbitrary precision integer)
  Bool   // SMT-LIB2 Bool (boolean value)
};

/// SMT-LIB2 generation context.
/// Tracks declared variables and builds SMT-LIB2 output.
class SmtLib2Gen {
public:
  /// Create a generator with the given parameter names.
  explicit SmtLib2Gen(const std::vector<std::string> &paramNames)
      : paramNames(paramNames) {}

  /// Create a generator with parameter names and their types.
  SmtLib2Gen(const std::vector<std::string> &paramNames,
             const std::map<std::string, SmtType> &varTypes)
      : paramNames(paramNames), variableTypes(varTypes) {}

  /// Generate SMT-LIB2 expression from a ConditionExpr.
  /// Returns the s-expression string for the expression.
  std::string generateExpr(const ConditionExpr *expr);

  /// Generate a complete SMT-LIB2 script for a verification condition.
  /// @param preconditions - @requires conditions (assumed true)
  /// @param postconditions - @ensures conditions (to be proven)
  /// @param functionSemantics - Optional expression for function behavior
  /// @return Complete SMT-LIB2 script
  std::string generateVerificationScript(
      const std::vector<const ConditionExpr *> &preconditions,
      const std::vector<const ConditionExpr *> &postconditions,
      const ConditionExpr *functionSemantics = nullptr);

  /// Generate SMT-LIB2 script to verify an auto-VC (e.g., overflow check).
  /// @param preconditions - Input constraints (from @requires or implicit)
  /// @param condition - The condition that must hold to avoid UB
  /// @param description - Human-readable description for comments
  /// @return Complete SMT-LIB2 script
  std::string generateAutoVCScript(
      const std::vector<const ConditionExpr *> &preconditions,
      const ConditionExpr *condition,
      llvm::StringRef description);

  /// Generate variable declarations for all referenced variables.
  std::string generateDeclarations();

  /// Add a variable to the declaration set (defaults to Int type).
  void declareVariable(const std::string &name);

  /// Add a variable with a specific type.
  void declareVariable(const std::string &name, SmtType type);

  /// Set the type for a variable (can be called before or after declareVariable).
  void setVariableType(const std::string &name, SmtType type);

  /// Get the type for a variable (defaults to Int if not set).
  SmtType getVariableType(const std::string &name) const;

  /// Check if a variable has been declared.
  bool isVariableDeclared(const std::string &name) const;

  /// Get all declared variable names.
  const std::set<std::string> &getDeclaredVariables() const {
    return declaredVars;
  }

  /// Clear the generator state for reuse.
  void clear();

private:
  /// Parameter names from the function signature.
  std::vector<std::string> paramNames;

  /// Variables that have been referenced (need declarations).
  std::set<std::string> declaredVars;

  /// Variable type mappings (defaults to Int if not present).
  std::map<std::string, SmtType> variableTypes;

  /// Generate expression and track variable references.
  std::string generateExprImpl(const ConditionExpr *expr);

  /// Get SMT-LIB2 operator name for a binary operator.
  static const char *getBinaryOpName(ConditionExpr::Kind kind);

  /// Get SMT-LIB2 operator name for a unary operator.
  static const char *getUnaryOpName(ConditionExpr::Kind kind);
};

//===----------------------------------------------------------------------===//
// Convenience functions
//===----------------------------------------------------------------------===//

/// Generate SMT-LIB2 string for a single condition expression.
/// @param expr The parsed condition expression
/// @param paramNames Parameter names from the function
/// @return SMT-LIB2 s-expression string
std::string generateSmtLib2(const ConditionExpr *expr,
                            const std::vector<std::string> &paramNames);

/// Generate a complete verification script for @requires/@ensures.
/// @param requires Vector of precondition expressions
/// @param ensures Vector of postcondition expressions
/// @param paramNames Parameter names from the function
/// @return Complete SMT-LIB2 script with (check-sat)
std::string generateVerificationVc(
    const std::vector<const ConditionExpr *> &requires,
    const std::vector<const ConditionExpr *> &ensures,
    const std::vector<std::string> &paramNames);

} // namespace verification
} // namespace swift

#endif // SWIFT_SILOPTIMIZER_VERIFICATION_VCIRGEN_H
