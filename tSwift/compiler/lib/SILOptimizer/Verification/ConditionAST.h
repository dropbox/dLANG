//===--- ConditionAST.h - AST for verification conditions -*- C++ --------===//
//
// This source file is part of the tSwift project
//
// Copyright (c) 2026 Dropbox, Inc. All rights reserved.
// Licensed under Apache License v2.0
//
//===----------------------------------------------------------------------===//
//
// This file defines a simple expression AST for representing verification
// condition expressions parsed from @requires/@ensures strings.
//
// Example: @requires("x > 0 && y >= 0")
//   -> BinaryExpr(And,
//        BinaryExpr(Gt, ParamRef("x"), IntLiteral(0)),
//        BinaryExpr(Ge, ParamRef("y"), IntLiteral(0)))
//
//===----------------------------------------------------------------------===//

#ifndef SWIFT_SILOPTIMIZER_VERIFICATION_CONDITIONAST_H
#define SWIFT_SILOPTIMIZER_VERIFICATION_CONDITIONAST_H

#include "llvm/ADT/StringRef.h"
#include "llvm/Support/raw_ostream.h"
#include <memory>
#include <string>
#include <vector>

namespace swift {
namespace verification {

/// Base class for all condition expression nodes.
class ConditionExpr {
public:
  enum class Kind {
    // Literals
    IntLiteral,      // 0, 1, -5, 42
    BoolLiteral,     // true, false

    // References
    ParamRef,        // x, y (function parameters)
    ResultRef,       // result (return value in @ensures)

    // Binary operators - Arithmetic
    Add,             // +
    Sub,             // -
    Mul,             // *
    Div,             // /
    Mod,             // %

    // Binary operators - Comparison
    Eq,              // ==
    Ne,              // !=
    Lt,              // <
    Le,              // <=
    Gt,              // >
    Ge,              // >=

    // Binary operators - Logical
    And,             // &&
    Or,              // ||

    // Unary operators
    Neg,             // - (unary minus)
    Not              // !
  };

private:
  Kind kind;

protected:
  explicit ConditionExpr(Kind k) : kind(k) {}

public:
  virtual ~ConditionExpr() = default;

  Kind getKind() const { return kind; }

  /// Check if this is a binary operator expression
  bool isBinaryOp() const {
    return kind >= Kind::Add && kind <= Kind::Or;
  }

  /// Check if this is a unary operator expression
  bool isUnaryOp() const {
    return kind == Kind::Neg || kind == Kind::Not;
  }

  /// Check if this is a literal
  bool isLiteral() const {
    return kind == Kind::IntLiteral || kind == Kind::BoolLiteral;
  }

  /// Check if this is a reference (param or result)
  bool isReference() const {
    return kind == Kind::ParamRef || kind == Kind::ResultRef;
  }

  /// Get operator precedence (higher = binds tighter)
  /// Used by the parser for correct precedence handling.
  static int getPrecedence(Kind k) {
    switch (k) {
    case Kind::Or:           return 1;
    case Kind::And:          return 2;
    case Kind::Eq:
    case Kind::Ne:           return 3;
    case Kind::Lt:
    case Kind::Le:
    case Kind::Gt:
    case Kind::Ge:           return 4;
    case Kind::Add:
    case Kind::Sub:          return 5;
    case Kind::Mul:
    case Kind::Div:
    case Kind::Mod:          return 6;
    default:                 return 0;  // Not a binary op
    }
  }

  /// Get string representation of operator kind
  static llvm::StringRef getOperatorName(Kind k);

  /// Debug print the expression tree
  virtual void dump(llvm::raw_ostream &os, int indent = 0) const = 0;
};

/// Integer literal: 0, 1, -5, 42
class IntLiteralExpr : public ConditionExpr {
  int64_t value;

public:
  explicit IntLiteralExpr(int64_t v)
      : ConditionExpr(Kind::IntLiteral), value(v) {}

  int64_t getValue() const { return value; }

  void dump(llvm::raw_ostream &os, int indent = 0) const override {
    os.indent(indent) << "IntLiteral(" << value << ")\n";
  }

  static bool classof(const ConditionExpr *e) {
    return e->getKind() == Kind::IntLiteral;
  }
};

/// Boolean literal: true, false
class BoolLiteralExpr : public ConditionExpr {
  bool value;

public:
  explicit BoolLiteralExpr(bool v)
      : ConditionExpr(Kind::BoolLiteral), value(v) {}

  bool getValue() const { return value; }

  void dump(llvm::raw_ostream &os, int indent = 0) const override {
    os.indent(indent) << "BoolLiteral(" << (value ? "true" : "false") << ")\n";
  }

  static bool classof(const ConditionExpr *e) {
    return e->getKind() == Kind::BoolLiteral;
  }
};

/// Parameter reference: x, y, count
class ParamRefExpr : public ConditionExpr {
  std::string name;
  int paramIndex;  // Index in function parameter list, -1 if unresolved

public:
  explicit ParamRefExpr(llvm::StringRef n, int idx = -1)
      : ConditionExpr(Kind::ParamRef), name(n.str()), paramIndex(idx) {}

  llvm::StringRef getName() const { return name; }
  int getParamIndex() const { return paramIndex; }
  void setParamIndex(int idx) { paramIndex = idx; }

  void dump(llvm::raw_ostream &os, int indent = 0) const override {
    os.indent(indent) << "ParamRef(" << name;
    if (paramIndex >= 0) {
      os << ", idx=" << paramIndex;
    }
    os << ")\n";
  }

  static bool classof(const ConditionExpr *e) {
    return e->getKind() == Kind::ParamRef;
  }
};

/// Result reference: result (used in @ensures)
class ResultRefExpr : public ConditionExpr {
public:
  ResultRefExpr() : ConditionExpr(Kind::ResultRef) {}

  void dump(llvm::raw_ostream &os, int indent = 0) const override {
    os.indent(indent) << "ResultRef\n";
  }

  static bool classof(const ConditionExpr *e) {
    return e->getKind() == Kind::ResultRef;
  }
};

/// Binary operator expression: lhs op rhs
class BinaryExpr : public ConditionExpr {
  std::unique_ptr<ConditionExpr> lhs;
  std::unique_ptr<ConditionExpr> rhs;

public:
  BinaryExpr(Kind op, std::unique_ptr<ConditionExpr> l,
             std::unique_ptr<ConditionExpr> r)
      : ConditionExpr(op), lhs(std::move(l)), rhs(std::move(r)) {}

  const ConditionExpr *getLHS() const { return lhs.get(); }
  const ConditionExpr *getRHS() const { return rhs.get(); }

  void dump(llvm::raw_ostream &os, int indent = 0) const override {
    os.indent(indent) << "BinaryExpr(" << getOperatorName(getKind()) << ")\n";
    lhs->dump(os, indent + 2);
    rhs->dump(os, indent + 2);
  }

  static bool classof(const ConditionExpr *e) {
    return e->isBinaryOp();
  }
};

/// Unary operator expression: op operand
class UnaryExpr : public ConditionExpr {
  std::unique_ptr<ConditionExpr> operand;

public:
  UnaryExpr(Kind op, std::unique_ptr<ConditionExpr> o)
      : ConditionExpr(op), operand(std::move(o)) {}

  const ConditionExpr *getOperand() const { return operand.get(); }

  void dump(llvm::raw_ostream &os, int indent = 0) const override {
    os.indent(indent) << "UnaryExpr(" << getOperatorName(getKind()) << ")\n";
    operand->dump(os, indent + 2);
  }

  static bool classof(const ConditionExpr *e) {
    return e->isUnaryOp();
  }
};

/// Stores the result of parsing a condition string.
struct ParseResult {
  /// The parsed expression, or nullptr on error.
  std::unique_ptr<ConditionExpr> expr;

  /// Error message if parsing failed.
  std::string error;

  /// Position in the input where error occurred.
  size_t errorPos = 0;

  bool success() const { return expr != nullptr; }
  bool failed() const { return !success(); }

  static ParseResult success(std::unique_ptr<ConditionExpr> e) {
    ParseResult r;
    r.expr = std::move(e);
    return r;
  }

  static ParseResult failure(llvm::StringRef msg, size_t pos = 0) {
    ParseResult r;
    r.error = msg.str();
    r.errorPos = pos;
    return r;
  }
};

} // namespace verification
} // namespace swift

#endif // SWIFT_SILOPTIMIZER_VERIFICATION_CONDITIONAST_H
