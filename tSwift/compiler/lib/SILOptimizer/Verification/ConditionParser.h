//===--- ConditionParser.h - Parser for verification conditions -*- C++ --===//
//
// This source file is part of the tSwift project
//
// Copyright (c) 2026 Dropbox, Inc. All rights reserved.
// Licensed under Apache License v2.0
//
//===----------------------------------------------------------------------===//
//
// This file declares the parser interface for verification condition strings.
// The parser converts strings like "x > 0 && result >= 0" into AST nodes.
//
// Grammar (simplified Swift expression subset):
//
//   condition    = or_expr
//   or_expr      = and_expr ('||' and_expr)*
//   and_expr     = compare_expr ('&&' compare_expr)*
//   compare_expr = add_expr (('==' | '!=' | '<' | '<=' | '>' | '>=') add_expr)?
//   add_expr     = mul_expr (('+' | '-') mul_expr)*
//   mul_expr     = unary_expr (('*' | '/' | '%') unary_expr)*
//   unary_expr   = ('!' | '-')? primary_expr
//   primary_expr = '(' condition ')' | identifier | int_literal | bool_literal
//   identifier   = [a-zA-Z_][a-zA-Z0-9_]*
//   int_literal  = [0-9]+
//   bool_literal = 'true' | 'false'
//
//===----------------------------------------------------------------------===//

#ifndef SWIFT_SILOPTIMIZER_VERIFICATION_CONDITIONPARSER_H
#define SWIFT_SILOPTIMIZER_VERIFICATION_CONDITIONPARSER_H

#include "ConditionAST.h"
#include "llvm/ADT/StringRef.h"
#include <vector>

namespace swift {
namespace verification {

/// Parser for verification condition strings.
///
/// This is a simple recursive-descent parser that handles a subset of
/// Swift expressions suitable for verification conditions.
///
/// Usage:
///   ConditionParser parser("x > 0 && y < 100");
///   parser.setParameterNames({"x", "y"});
///   ParseResult result = parser.parse();
///   if (result.success()) {
///     // Use result.expr
///   }
class ConditionParser {
public:
  /// Create a parser for the given condition string.
  explicit ConditionParser(llvm::StringRef input);

  /// Set the list of valid parameter names for reference resolution.
  /// Any identifier matching a parameter name becomes a ParamRefExpr.
  void setParameterNames(const std::vector<std::string> &names);

  /// Parse the condition string and return the AST.
  ParseResult parse();

  /// Static helper to parse a condition with parameter names.
  static ParseResult parse(llvm::StringRef input,
                           const std::vector<std::string> &paramNames);

private:
  // Input management
  llvm::StringRef input;
  size_t pos = 0;

  // Parameter names for resolving references
  std::vector<std::string> paramNames;

  // Lexer state
  enum class TokenKind {
    EndOfInput,
    Error,

    // Literals
    Integer,
    True,
    False,

    // Identifiers
    Identifier,

    // Operators
    Plus,        // +
    Minus,       // -
    Star,        // *
    Slash,       // /
    Percent,     // %
    EqEq,        // ==
    NotEq,       // !=
    Less,        // <
    LessEq,      // <=
    Greater,     // >
    GreaterEq,   // >=
    AmpAmp,      // &&
    PipePipe,    // ||
    Bang,        // !

    // Delimiters
    LParen,      // (
    RParen       // )
  };

  struct Token {
    TokenKind kind;
    llvm::StringRef text;
    size_t pos;
    int64_t intValue = 0;  // For Integer tokens
  };

  Token currentToken;

  // Lexer methods
  void advance();
  void skipWhitespace();
  Token lexToken();
  Token lexNumber();
  Token lexIdentifier();

  // Parser methods - recursive descent
  std::unique_ptr<ConditionExpr> parseExpression();
  std::unique_ptr<ConditionExpr> parseOrExpr();
  std::unique_ptr<ConditionExpr> parseAndExpr();
  std::unique_ptr<ConditionExpr> parseCompareExpr();
  std::unique_ptr<ConditionExpr> parseAddExpr();
  std::unique_ptr<ConditionExpr> parseMulExpr();
  std::unique_ptr<ConditionExpr> parseUnaryExpr();
  std::unique_ptr<ConditionExpr> parsePrimaryExpr();

  // Error handling
  std::string errorMessage;
  size_t errorPos = 0;

  void setError(llvm::StringRef msg);
  bool hasError() const { return !errorMessage.empty(); }

  // Helper to check if identifier is a known parameter
  int findParameterIndex(llvm::StringRef name) const;
};

} // namespace verification
} // namespace swift

#endif // SWIFT_SILOPTIMIZER_VERIFICATION_CONDITIONPARSER_H
