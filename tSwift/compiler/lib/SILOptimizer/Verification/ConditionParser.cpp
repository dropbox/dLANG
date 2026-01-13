//===--- ConditionParser.cpp - Parser for verification conditions --------===//
//
// This source file is part of the tSwift project
//
// Copyright (c) 2026 Dropbox, Inc. All rights reserved.
// Licensed under Apache License v2.0
//
//===----------------------------------------------------------------------===//

#include "ConditionParser.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/raw_ostream.h"
#include <cctype>

using namespace swift;

namespace swift {
namespace verification {

//===----------------------------------------------------------------------===//
// ConditionExpr implementations
//===----------------------------------------------------------------------===//

llvm::StringRef ConditionExpr::getOperatorName(Kind k) {
  switch (k) {
  case Kind::IntLiteral:  return "int";
  case Kind::BoolLiteral: return "bool";
  case Kind::ParamRef:    return "param";
  case Kind::ResultRef:   return "result";
  case Kind::Add:         return "+";
  case Kind::Sub:         return "-";
  case Kind::Mul:         return "*";
  case Kind::Div:         return "/";
  case Kind::Mod:         return "%";
  case Kind::Eq:          return "==";
  case Kind::Ne:          return "!=";
  case Kind::Lt:          return "<";
  case Kind::Le:          return "<=";
  case Kind::Gt:          return ">";
  case Kind::Ge:          return ">=";
  case Kind::And:         return "&&";
  case Kind::Or:          return "||";
  case Kind::Neg:         return "-";
  case Kind::Not:         return "!";
  }
  return "?";
}

//===----------------------------------------------------------------------===//
// ConditionParser implementation
//===----------------------------------------------------------------------===//

ConditionParser::ConditionParser(llvm::StringRef input)
    : input(input), pos(0) {
  advance();  // Initialize currentToken
}

void ConditionParser::setParameterNames(const std::vector<std::string> &names) {
  paramNames = names;
}

ParseResult ConditionParser::parse() {
  auto expr = parseExpression();

  if (hasError()) {
    return ParseResult::failure(errorMessage, errorPos);
  }

  if (currentToken.kind != TokenKind::EndOfInput) {
    return ParseResult::failure("unexpected token after expression",
                                currentToken.pos);
  }

  return ParseResult::success(std::move(expr));
}

ParseResult ConditionParser::parse(llvm::StringRef input,
                                   const std::vector<std::string> &paramNames) {
  ConditionParser parser(input);
  parser.setParameterNames(paramNames);
  return parser.parse();
}

//===----------------------------------------------------------------------===//
// Lexer implementation
//===----------------------------------------------------------------------===//

void ConditionParser::skipWhitespace() {
  while (pos < input.size() && std::isspace(input[pos])) {
    ++pos;
  }
}

ConditionParser::Token ConditionParser::lexNumber() {
  Token tok;
  tok.kind = TokenKind::Integer;
  tok.pos = pos;

  size_t start = pos;
  while (pos < input.size() && std::isdigit(input[pos])) {
    ++pos;
  }

  tok.text = input.slice(start, pos);
  tok.intValue = 0;

  // Parse integer value
  for (char c : tok.text) {
    tok.intValue = tok.intValue * 10 + (c - '0');
  }

  return tok;
}

ConditionParser::Token ConditionParser::lexIdentifier() {
  Token tok;
  tok.kind = TokenKind::Identifier;
  tok.pos = pos;

  size_t start = pos;
  while (pos < input.size() &&
         (std::isalnum(input[pos]) || input[pos] == '_')) {
    ++pos;
  }

  tok.text = input.slice(start, pos);

  // Check for keywords
  if (tok.text == "true") {
    tok.kind = TokenKind::True;
  } else if (tok.text == "false") {
    tok.kind = TokenKind::False;
  }

  return tok;
}

ConditionParser::Token ConditionParser::lexToken() {
  skipWhitespace();

  Token tok;
  tok.pos = pos;

  if (pos >= input.size()) {
    tok.kind = TokenKind::EndOfInput;
    tok.text = "";
    return tok;
  }

  char c = input[pos];

  // Numbers
  if (std::isdigit(c)) {
    return lexNumber();
  }

  // Identifiers and keywords
  if (std::isalpha(c) || c == '_') {
    return lexIdentifier();
  }

  // Two-character operators
  if (pos + 1 < input.size()) {
    char next = input[pos + 1];

    if (c == '=' && next == '=') {
      tok.kind = TokenKind::EqEq;
      tok.text = input.slice(pos, pos + 2);
      pos += 2;
      return tok;
    }
    if (c == '!' && next == '=') {
      tok.kind = TokenKind::NotEq;
      tok.text = input.slice(pos, pos + 2);
      pos += 2;
      return tok;
    }
    if (c == '<' && next == '=') {
      tok.kind = TokenKind::LessEq;
      tok.text = input.slice(pos, pos + 2);
      pos += 2;
      return tok;
    }
    if (c == '>' && next == '=') {
      tok.kind = TokenKind::GreaterEq;
      tok.text = input.slice(pos, pos + 2);
      pos += 2;
      return tok;
    }
    if (c == '&' && next == '&') {
      tok.kind = TokenKind::AmpAmp;
      tok.text = input.slice(pos, pos + 2);
      pos += 2;
      return tok;
    }
    if (c == '|' && next == '|') {
      tok.kind = TokenKind::PipePipe;
      tok.text = input.slice(pos, pos + 2);
      pos += 2;
      return tok;
    }
  }

  // Single-character operators
  tok.text = input.slice(pos, pos + 1);
  ++pos;

  switch (c) {
  case '+': tok.kind = TokenKind::Plus; break;
  case '-': tok.kind = TokenKind::Minus; break;
  case '*': tok.kind = TokenKind::Star; break;
  case '/': tok.kind = TokenKind::Slash; break;
  case '%': tok.kind = TokenKind::Percent; break;
  case '<': tok.kind = TokenKind::Less; break;
  case '>': tok.kind = TokenKind::Greater; break;
  case '!': tok.kind = TokenKind::Bang; break;
  case '(': tok.kind = TokenKind::LParen; break;
  case ')': tok.kind = TokenKind::RParen; break;
  default:
    tok.kind = TokenKind::Error;
    break;
  }

  return tok;
}

void ConditionParser::advance() {
  currentToken = lexToken();
}

void ConditionParser::setError(llvm::StringRef msg) {
  if (errorMessage.empty()) {  // Only keep first error
    errorMessage = msg.str();
    errorPos = currentToken.pos;
  }
}

int ConditionParser::findParameterIndex(llvm::StringRef name) const {
  for (size_t i = 0; i < paramNames.size(); ++i) {
    if (paramNames[i] == name) {
      return static_cast<int>(i);
    }
  }
  return -1;
}

//===----------------------------------------------------------------------===//
// Parser implementation - recursive descent
//===----------------------------------------------------------------------===//

std::unique_ptr<ConditionExpr> ConditionParser::parseExpression() {
  return parseOrExpr();
}

// or_expr = and_expr ('||' and_expr)*
std::unique_ptr<ConditionExpr> ConditionParser::parseOrExpr() {
  auto lhs = parseAndExpr();
  if (!lhs) return nullptr;

  while (currentToken.kind == TokenKind::PipePipe) {
    advance();
    auto rhs = parseAndExpr();
    if (!rhs) return nullptr;

    lhs = std::make_unique<BinaryExpr>(
        ConditionExpr::Kind::Or, std::move(lhs), std::move(rhs));
  }

  return lhs;
}

// and_expr = compare_expr ('&&' compare_expr)*
std::unique_ptr<ConditionExpr> ConditionParser::parseAndExpr() {
  auto lhs = parseCompareExpr();
  if (!lhs) return nullptr;

  while (currentToken.kind == TokenKind::AmpAmp) {
    advance();
    auto rhs = parseCompareExpr();
    if (!rhs) return nullptr;

    lhs = std::make_unique<BinaryExpr>(
        ConditionExpr::Kind::And, std::move(lhs), std::move(rhs));
  }

  return lhs;
}

// compare_expr = add_expr (('==' | '!=' | '<' | '<=' | '>' | '>=') add_expr)?
std::unique_ptr<ConditionExpr> ConditionParser::parseCompareExpr() {
  auto lhs = parseAddExpr();
  if (!lhs) return nullptr;

  ConditionExpr::Kind opKind;
  bool isCompare = true;

  switch (currentToken.kind) {
  case TokenKind::EqEq:      opKind = ConditionExpr::Kind::Eq; break;
  case TokenKind::NotEq:     opKind = ConditionExpr::Kind::Ne; break;
  case TokenKind::Less:      opKind = ConditionExpr::Kind::Lt; break;
  case TokenKind::LessEq:    opKind = ConditionExpr::Kind::Le; break;
  case TokenKind::Greater:   opKind = ConditionExpr::Kind::Gt; break;
  case TokenKind::GreaterEq: opKind = ConditionExpr::Kind::Ge; break;
  default:
    isCompare = false;
    break;
  }

  if (isCompare) {
    advance();
    auto rhs = parseAddExpr();
    if (!rhs) return nullptr;

    return std::make_unique<BinaryExpr>(opKind, std::move(lhs), std::move(rhs));
  }

  return lhs;
}

// add_expr = mul_expr (('+' | '-') mul_expr)*
std::unique_ptr<ConditionExpr> ConditionParser::parseAddExpr() {
  auto lhs = parseMulExpr();
  if (!lhs) return nullptr;

  while (currentToken.kind == TokenKind::Plus ||
         currentToken.kind == TokenKind::Minus) {
    ConditionExpr::Kind opKind =
        currentToken.kind == TokenKind::Plus
            ? ConditionExpr::Kind::Add
            : ConditionExpr::Kind::Sub;

    advance();
    auto rhs = parseMulExpr();
    if (!rhs) return nullptr;

    lhs = std::make_unique<BinaryExpr>(opKind, std::move(lhs), std::move(rhs));
  }

  return lhs;
}

// mul_expr = unary_expr (('*' | '/' | '%') unary_expr)*
std::unique_ptr<ConditionExpr> ConditionParser::parseMulExpr() {
  auto lhs = parseUnaryExpr();
  if (!lhs) return nullptr;

  while (currentToken.kind == TokenKind::Star ||
         currentToken.kind == TokenKind::Slash ||
         currentToken.kind == TokenKind::Percent) {
    ConditionExpr::Kind opKind;
    switch (currentToken.kind) {
    case TokenKind::Star:    opKind = ConditionExpr::Kind::Mul; break;
    case TokenKind::Slash:   opKind = ConditionExpr::Kind::Div; break;
    case TokenKind::Percent: opKind = ConditionExpr::Kind::Mod; break;
    default: llvm_unreachable("unexpected token");
    }

    advance();
    auto rhs = parseUnaryExpr();
    if (!rhs) return nullptr;

    lhs = std::make_unique<BinaryExpr>(opKind, std::move(lhs), std::move(rhs));
  }

  return lhs;
}

// unary_expr = ('!' | '-')? primary_expr
std::unique_ptr<ConditionExpr> ConditionParser::parseUnaryExpr() {
  if (currentToken.kind == TokenKind::Bang) {
    advance();
    auto operand = parseUnaryExpr();
    if (!operand) return nullptr;
    return std::make_unique<UnaryExpr>(ConditionExpr::Kind::Not,
                                       std::move(operand));
  }

  if (currentToken.kind == TokenKind::Minus) {
    advance();
    auto operand = parseUnaryExpr();
    if (!operand) return nullptr;
    return std::make_unique<UnaryExpr>(ConditionExpr::Kind::Neg,
                                       std::move(operand));
  }

  return parsePrimaryExpr();
}

// primary_expr = '(' condition ')' | identifier | int_literal | bool_literal
std::unique_ptr<ConditionExpr> ConditionParser::parsePrimaryExpr() {
  // Parenthesized expression
  if (currentToken.kind == TokenKind::LParen) {
    advance();
    auto inner = parseExpression();
    if (!inner) return nullptr;

    if (currentToken.kind != TokenKind::RParen) {
      setError("expected ')'");
      return nullptr;
    }
    advance();
    return inner;
  }

  // Integer literal
  if (currentToken.kind == TokenKind::Integer) {
    auto result = std::make_unique<IntLiteralExpr>(currentToken.intValue);
    advance();
    return result;
  }

  // Boolean literals
  if (currentToken.kind == TokenKind::True) {
    advance();
    return std::make_unique<BoolLiteralExpr>(true);
  }
  if (currentToken.kind == TokenKind::False) {
    advance();
    return std::make_unique<BoolLiteralExpr>(false);
  }

  // Identifier (parameter reference or 'result')
  if (currentToken.kind == TokenKind::Identifier) {
    llvm::StringRef name = currentToken.text;

    // Special case: 'result' keyword for @ensures
    if (name == "result") {
      advance();
      return std::make_unique<ResultRefExpr>();
    }

    // Parameter reference
    int idx = findParameterIndex(name);
    auto result = std::make_unique<ParamRefExpr>(name, idx);
    advance();
    return result;
  }

  // Error
  if (currentToken.kind == TokenKind::Error) {
    setError("unexpected character");
  } else if (currentToken.kind == TokenKind::EndOfInput) {
    setError("unexpected end of input");
  } else {
    setError("expected expression");
  }
  return nullptr;
}

} // namespace verification
} // namespace swift
