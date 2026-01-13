//===--- VcIrGen.cpp - VC IR Generation for SMT-LIB2 output --------------===//
//
// This source file is part of the tSwift project
//
// Copyright (c) 2026 Dropbox, Inc. All rights reserved.
// Licensed under Apache License v2.0
//
//===----------------------------------------------------------------------===//
//
// This file implements SMT-LIB2 generation from ConditionExpr AST nodes.
//
//===----------------------------------------------------------------------===//

#include "VcIrGen.h"
#include "llvm/Support/ErrorHandling.h"
#include <sstream>
#include <limits>

namespace swift {
namespace verification {

//===----------------------------------------------------------------------===//
// SmtLib2Gen Implementation
//===----------------------------------------------------------------------===//

const char *SmtLib2Gen::getBinaryOpName(ConditionExpr::Kind kind) {
  switch (kind) {
  // Arithmetic
  case ConditionExpr::Kind::Add: return "+";
  case ConditionExpr::Kind::Sub: return "-";
  case ConditionExpr::Kind::Mul: return "*";
  case ConditionExpr::Kind::Div: return "div";  // Integer division in SMT-LIB2
  case ConditionExpr::Kind::Mod: return "mod";

  // Comparison
  case ConditionExpr::Kind::Eq:  return "=";
  case ConditionExpr::Kind::Ne:  return "distinct";  // SMT-LIB2 uses 'distinct' for !=
  case ConditionExpr::Kind::Lt:  return "<";
  case ConditionExpr::Kind::Le:  return "<=";
  case ConditionExpr::Kind::Gt:  return ">";
  case ConditionExpr::Kind::Ge:  return ">=";

  // Logical
  case ConditionExpr::Kind::And: return "and";
  case ConditionExpr::Kind::Or:  return "or";

  default:
    llvm_unreachable("Not a binary operator");
  }
}

const char *SmtLib2Gen::getUnaryOpName(ConditionExpr::Kind kind) {
  switch (kind) {
  case ConditionExpr::Kind::Neg: return "-";
  case ConditionExpr::Kind::Not: return "not";
  default:
    llvm_unreachable("Not a unary operator");
  }
}

std::string SmtLib2Gen::generateExpr(const ConditionExpr *expr) {
  return generateExprImpl(expr);
}

std::string SmtLib2Gen::generateExprImpl(const ConditionExpr *expr) {
  if (!expr) {
    return "true";  // Default for null expressions
  }

  switch (expr->getKind()) {
  // Literals
  case ConditionExpr::Kind::IntLiteral: {
    auto *lit = static_cast<const IntLiteralExpr *>(expr);
    int64_t val = lit->getValue();
    if (val < 0) {
      // SMT-LIB2 represents negative numbers as (- N)
      // Special handling for INT64_MIN to avoid overflow when negating
      if (val == std::numeric_limits<int64_t>::min()) {
        return "(- 9223372036854775808)";
      }
      std::ostringstream ss;
      ss << "(- " << (-val) << ")";
      return ss.str();
    }
    return std::to_string(val);
  }

  case ConditionExpr::Kind::BoolLiteral: {
    auto *lit = static_cast<const BoolLiteralExpr *>(expr);
    return lit->getValue() ? "true" : "false";
  }

  // References
  case ConditionExpr::Kind::ParamRef: {
    auto *ref = static_cast<const ParamRefExpr *>(expr);
    std::string name = ref->getName().str();
    declareVariable(name);
    return name;
  }

  case ConditionExpr::Kind::ResultRef: {
    declareVariable("result");
    return "result";
  }

  // Binary operators
  case ConditionExpr::Kind::Add:
  case ConditionExpr::Kind::Sub:
  case ConditionExpr::Kind::Mul:
  case ConditionExpr::Kind::Div:
  case ConditionExpr::Kind::Mod:
  case ConditionExpr::Kind::Eq:
  case ConditionExpr::Kind::Ne:
  case ConditionExpr::Kind::Lt:
  case ConditionExpr::Kind::Le:
  case ConditionExpr::Kind::Gt:
  case ConditionExpr::Kind::Ge:
  case ConditionExpr::Kind::And:
  case ConditionExpr::Kind::Or: {
    auto *binExpr = static_cast<const BinaryExpr *>(expr);
    std::ostringstream ss;
    ss << "(" << getBinaryOpName(expr->getKind()) << " "
       << generateExprImpl(binExpr->getLHS()) << " "
       << generateExprImpl(binExpr->getRHS()) << ")";
    return ss.str();
  }

  // Unary operators
  case ConditionExpr::Kind::Neg:
  case ConditionExpr::Kind::Not: {
    auto *unaryExpr = static_cast<const UnaryExpr *>(expr);
    std::ostringstream ss;
    ss << "(" << getUnaryOpName(expr->getKind()) << " "
       << generateExprImpl(unaryExpr->getOperand()) << ")";
    return ss.str();
  }
  }

  llvm_unreachable("Unhandled expression kind");
}

std::string SmtLib2Gen::generateDeclarations() {
  std::ostringstream ss;

  // Declare all referenced variables with their appropriate types
  for (const auto &var : declaredVars) {
    SmtType type = getVariableType(var);
    const char *typeName = (type == SmtType::Bool) ? "Bool" : "Int";
    ss << "(declare-const " << var << " " << typeName << ")\n";
  }

  return ss.str();
}

void SmtLib2Gen::declareVariable(const std::string &name) {
  declaredVars.insert(name);
}

void SmtLib2Gen::declareVariable(const std::string &name, SmtType type) {
  declaredVars.insert(name);
  variableTypes[name] = type;
}

void SmtLib2Gen::setVariableType(const std::string &name, SmtType type) {
  variableTypes[name] = type;
}

SmtType SmtLib2Gen::getVariableType(const std::string &name) const {
  auto it = variableTypes.find(name);
  if (it != variableTypes.end()) {
    return it->second;
  }
  return SmtType::Int;  // Default to Int
}

bool SmtLib2Gen::isVariableDeclared(const std::string &name) const {
  return declaredVars.find(name) != declaredVars.end();
}

void SmtLib2Gen::clear() {
  declaredVars.clear();
  variableTypes.clear();
}

std::string SmtLib2Gen::generateVerificationScript(
    const std::vector<const ConditionExpr *> &preconditions,
    const std::vector<const ConditionExpr *> &postconditions,
    const ConditionExpr *functionSemantics) {

  std::ostringstream ss;

  // Generate expressions first to collect variable references
  std::vector<std::string> preStrs;
  std::vector<std::string> postStrs;

  for (const auto *pre : preconditions) {
    preStrs.push_back(generateExprImpl(pre));
  }

  for (const auto *post : postconditions) {
    postStrs.push_back(generateExprImpl(post));
  }

  std::string semanticsStr;
  if (functionSemantics) {
    semanticsStr = generateExprImpl(functionSemantics);
  }

  // Header comment
  ss << "; SMT-LIB2 verification condition\n";
  ss << "; Generated by tSwift verification pass\n";
  ss << "\n";

  // Set logic (use QF_LIA for quantifier-free linear integer arithmetic)
  ss << "(set-logic QF_LIA)\n";
  ss << "\n";

  // Declare all variables
  ss << "; Variable declarations\n";
  ss << generateDeclarations();
  ss << "\n";

  // Assert preconditions (assumed true)
  if (!preStrs.empty()) {
    ss << "; Preconditions (@requires)\n";
    for (const auto &pre : preStrs) {
      ss << "(assert " << pre << ")\n";
    }
    ss << "\n";
  }

  // Assert function semantics (if provided)
  if (functionSemantics) {
    ss << "; Function semantics\n";
    ss << "(assert " << semanticsStr << ")\n";
    ss << "\n";
  }

  // Assert negated postconditions (to prove by contradiction)
  // If UNSAT, the postconditions are provable from preconditions
  if (!postStrs.empty()) {
    ss << "; Negated postconditions (@ensures) - prove by refutation\n";
    if (postStrs.size() == 1) {
      ss << "(assert (not " << postStrs[0] << "))\n";
    } else {
      // Negate the conjunction of all postconditions
      ss << "(assert (not (and";
      for (const auto &post : postStrs) {
        ss << " " << post;
      }
      ss << ")))\n";
    }
    ss << "\n";
  }

  // Check satisfiability
  ss << "; Check if negated postcondition is satisfiable\n";
  ss << "; UNSAT = postcondition is provable\n";
  ss << "; SAT = postcondition may not hold (counterexample exists)\n";
  ss << "(check-sat)\n";
  ss << "(get-model)\n";

  return ss.str();
}

std::string SmtLib2Gen::generateAutoVCScript(
    const std::vector<const ConditionExpr *> &preconditions,
    const ConditionExpr *condition,
    llvm::StringRef description) {

  std::ostringstream ss;

  // Generate expressions first to collect variable references
  std::vector<std::string> preStrs;
  for (const auto *pre : preconditions) {
    preStrs.push_back(generateExprImpl(pre));
  }

  std::string conditionStr = generateExprImpl(condition);

  // Header comment
  ss << "; SMT-LIB2 auto-verification condition\n";
  ss << "; " << description.str() << "\n";
  ss << "; Generated by tSwift verification pass\n";
  ss << "\n";

  // Use QF_NIA for nonlinear integer arithmetic (needed for multiplication bounds)
  ss << "(set-logic QF_NIA)\n";
  ss << "\n";

  // Declare all variables
  ss << "; Variable declarations\n";
  ss << generateDeclarations();
  ss << "\n";

  // Assert preconditions (assumed true)
  if (!preStrs.empty()) {
    ss << "; Preconditions (input constraints)\n";
    for (const auto &pre : preStrs) {
      ss << "(assert " << pre << ")\n";
    }
    ss << "\n";
  }

  // Assert negated condition (to prove by contradiction)
  // If UNSAT, the condition always holds (no UB possible)
  // If SAT, we found inputs that violate the condition (potential UB)
  ss << "; Negated safety condition - prove by refutation\n";
  ss << "; UNSAT = safety condition always holds\n";
  ss << "; SAT = potential UB (counterexample exists)\n";
  ss << "(assert (not " << conditionStr << "))\n";
  ss << "\n";

  ss << "(check-sat)\n";
  ss << "(get-model)\n";

  return ss.str();
}

//===----------------------------------------------------------------------===//
// Convenience Functions
//===----------------------------------------------------------------------===//

std::string generateSmtLib2(const ConditionExpr *expr,
                            const std::vector<std::string> &paramNames) {
  SmtLib2Gen gen(paramNames);
  return gen.generateExpr(expr);
}

std::string generateVerificationVc(
    const std::vector<const ConditionExpr *> &requires,
    const std::vector<const ConditionExpr *> &ensures,
    const std::vector<std::string> &paramNames) {

  SmtLib2Gen gen(paramNames);
  return gen.generateVerificationScript(requires, ensures);
}

} // namespace verification
} // namespace swift
