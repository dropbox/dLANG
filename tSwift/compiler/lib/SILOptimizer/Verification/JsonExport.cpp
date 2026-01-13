//===--- JsonExport.cpp - JSON export for Swift VC Bridge ----------------===//
//
// This source file is part of the tSwift project
//
// Copyright (c) 2026 Dropbox, Inc. All rights reserved.
// Licensed under Apache License v2.0
//
//===----------------------------------------------------------------------===//

#include "JsonExport.h"
#include "llvm/ADT/StringRef.h"
#include <sstream>

using namespace swift;
using namespace swift::verification;

//===----------------------------------------------------------------------===//
// JSON String Utilities
//===----------------------------------------------------------------------===//

std::string verification::escapeJson(const std::string &s) {
  std::string result;
  result.reserve(s.size() + 16);
  for (char c : s) {
    switch (c) {
    case '"':  result += "\\\""; break;
    case '\\': result += "\\\\"; break;
    case '\n': result += "\\n"; break;
    case '\r': result += "\\r"; break;
    case '\t': result += "\\t"; break;
    default:
      if (static_cast<unsigned char>(c) < 0x20) {
        char buf[8];
        snprintf(buf, sizeof(buf), "\\u%04x", static_cast<unsigned char>(c));
        result += buf;
      } else {
        result += c;
      }
    }
  }
  return result;
}

std::string verification::jsonObject(
    const std::vector<std::pair<std::string, std::string>> &fields) {
  std::ostringstream oss;
  oss << "{";
  bool first = true;
  for (const auto &field : fields) {
    if (!first) oss << ",";
    first = false;
    oss << "\"" << field.first << "\":" << field.second;
  }
  oss << "}";
  return oss.str();
}

std::string verification::jsonArray(const std::vector<std::string> &elements) {
  std::ostringstream oss;
  oss << "[";
  bool first = true;
  for (const auto &elem : elements) {
    if (!first) oss << ",";
    first = false;
    oss << elem;
  }
  oss << "]";
  return oss.str();
}

//===----------------------------------------------------------------------===//
// ConditionExpr JSON Export
//===----------------------------------------------------------------------===//

/// Get the JSON "kind" string for a ConditionExpr Kind.
static const char *getExprKindName(ConditionExpr::Kind kind) {
  switch (kind) {
  case ConditionExpr::Kind::IntLiteral:  return "IntLit";
  case ConditionExpr::Kind::BoolLiteral: return "BoolLit";
  case ConditionExpr::Kind::ParamRef:    return "ParamRef";
  case ConditionExpr::Kind::ResultRef:   return "ResultRef";
  case ConditionExpr::Kind::Add:         return "Add";
  case ConditionExpr::Kind::Sub:         return "Sub";
  case ConditionExpr::Kind::Mul:         return "Mul";
  case ConditionExpr::Kind::Div:         return "Div";
  case ConditionExpr::Kind::Mod:         return "Mod";
  case ConditionExpr::Kind::Eq:          return "Eq";
  case ConditionExpr::Kind::Ne:          return "Ne";
  case ConditionExpr::Kind::Lt:          return "Lt";
  case ConditionExpr::Kind::Le:          return "Le";
  case ConditionExpr::Kind::Gt:          return "Gt";
  case ConditionExpr::Kind::Ge:          return "Ge";
  case ConditionExpr::Kind::And:         return "And";
  case ConditionExpr::Kind::Or:          return "Or";
  case ConditionExpr::Kind::Neg:         return "Neg";
  case ConditionExpr::Kind::Not:         return "Not";
  }
  return "Unknown";
}

std::string verification::exprToJson(const ConditionExpr *expr) {
  if (!expr) {
    return "null";
  }

  std::vector<std::pair<std::string, std::string>> fields;
  fields.push_back({"kind", "\"" + std::string(getExprKindName(expr->getKind())) + "\""});

  switch (expr->getKind()) {
  case ConditionExpr::Kind::IntLiteral: {
    auto *intLit = static_cast<const IntLiteralExpr *>(expr);
    fields.push_back({"value", std::to_string(intLit->getValue())});
    break;
  }

  case ConditionExpr::Kind::BoolLiteral: {
    auto *boolLit = static_cast<const BoolLiteralExpr *>(expr);
    fields.push_back({"value", boolLit->getValue() ? "true" : "false"});
    break;
  }

  case ConditionExpr::Kind::ParamRef: {
    auto *paramRef = static_cast<const ParamRefExpr *>(expr);
    fields.push_back({"name", "\"" + escapeJson(paramRef->getName().str()) + "\""});
    fields.push_back({"index", std::to_string(paramRef->getParamIndex())});
    break;
  }

  case ConditionExpr::Kind::ResultRef:
    // ResultRef has no additional fields
    break;

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
    fields.push_back({"lhs", exprToJson(binExpr->getLHS())});
    fields.push_back({"rhs", exprToJson(binExpr->getRHS())});
    break;
  }

  // Unary operators
  case ConditionExpr::Kind::Neg:
  case ConditionExpr::Kind::Not: {
    auto *unaryExpr = static_cast<const UnaryExpr *>(expr);
    fields.push_back({"operand", exprToJson(unaryExpr->getOperand())});
    break;
  }
  }

  return jsonObject(fields);
}

//===----------------------------------------------------------------------===//
// Type JSON Export
//===----------------------------------------------------------------------===//

std::string verification::typeToJson(ParamSmtType type) {
  switch (type) {
  case ParamSmtType::Int:
    return "{\"kind\":\"Int\",\"signed\":true,\"bits\":64}";
  case ParamSmtType::Bool:
    return "{\"kind\":\"Bool\"}";
  }
  return "{\"kind\":\"Int\",\"signed\":true,\"bits\":64}";
}

//===----------------------------------------------------------------------===//
// AutoVC JSON Export
//===----------------------------------------------------------------------===//

std::string verification::autoVcToJson(const AutoVC &vc) {
  std::vector<std::pair<std::string, std::string>> fields;

  // Set the "kind" based on AutoVC::Kind
  const char *kindStr = "CondFail";
  switch (vc.kind) {
  case AutoVC::Kind::Overflow:
    kindStr = "Overflow";
    fields.push_back({"kind", "\"Overflow\""});
    fields.push_back({"operation", "\"arithmetic\""});
    // operands array - for simplicity, use condition expr
    fields.push_back({"operands", "[" + exprToJson(vc.condition.get()) + "]"});
    break;
  case AutoVC::Kind::DivByZero:
    fields.push_back({"kind", "\"DivByZero\""});
    fields.push_back({"divisor", exprToJson(vc.condition.get())});
    break;
  case AutoVC::Kind::BoundsCheck:
    fields.push_back({"kind", "\"BoundsCheck\""});
    // For bounds, condition is typically: index >= 0 && index < length
    // We store the entire condition as "index" for simplicity
    fields.push_back({"index", exprToJson(vc.condition.get())});
    fields.push_back({"length", "{\"kind\":\"IntLit\",\"value\":0}"});
    break;
  case AutoVC::Kind::NilCheck:
    fields.push_back({"kind", "\"NilCheck\""});
    fields.push_back({"value", exprToJson(vc.condition.get())});
    break;
  }

  // Common fields
  fields.push_back({"description", "\"" + escapeJson(vc.description) + "\""});

  if (vc.sourceLine > 0) {
    fields.push_back({"source_line", std::to_string(vc.sourceLine)});
  }
  if (vc.sourceColumn > 0) {
    fields.push_back({"source_column", std::to_string(vc.sourceColumn)});
  }

  return jsonObject(fields);
}

//===----------------------------------------------------------------------===//
// VcBundleExport JSON Export
//===----------------------------------------------------------------------===//

std::string VcBundleExport::toJson() const {
  std::vector<std::pair<std::string, std::string>> fields;

  // Function name
  fields.push_back({"function_name", "\"" + escapeJson(functionName) + "\""});

  // Source location
  if (!sourceFile.empty()) {
    fields.push_back({"source_file", "\"" + escapeJson(sourceFile) + "\""});
  }
  if (sourceLine > 0) {
    fields.push_back({"source_line", std::to_string(sourceLine)});
  }
  if (sourceColumn > 0) {
    fields.push_back({"source_column", std::to_string(sourceColumn)});
  }

  // Parameters
  std::vector<std::string> paramJsons;
  for (const auto &param : parameters) {
    std::vector<std::pair<std::string, std::string>> paramFields;
    paramFields.push_back({"name", "\"" + escapeJson(param.name) + "\""});
    paramFields.push_back({"type", typeToJson(param.type)});
    paramFields.push_back({"index", std::to_string(param.index)});
    paramJsons.push_back(jsonObject(paramFields));
  }
  fields.push_back({"parameters", jsonArray(paramJsons)});

  // Return type
  if (hasReturn) {
    fields.push_back({"return_type", typeToJson(returnType)});
  }

  // @requires conditions
  std::vector<std::string> requiresJsons;
  for (const auto *req : this->requires) {
    requiresJsons.push_back(exprToJson(req));
  }
  fields.push_back({"requires", jsonArray(requiresJsons)});

  // @ensures conditions
  std::vector<std::string> ensuresJsons;
  for (const auto *ens : ensures) {
    ensuresJsons.push_back(exprToJson(ens));
  }
  fields.push_back({"ensures", jsonArray(ensuresJsons)});

  // @invariant conditions
  std::vector<std::string> invariantsJsons;
  for (const auto *inv : invariants) {
    invariantsJsons.push_back(exprToJson(inv));
  }
  fields.push_back({"invariants", jsonArray(invariantsJsons)});

  // Auto VCs
  std::vector<std::string> autoVcJsons;
  for (const auto *autoVc : autoVcs) {
    if (autoVc) {
      autoVcJsons.push_back(autoVcToJson(*autoVc));
    }
  }
  fields.push_back({"auto_vcs", jsonArray(autoVcJsons)});

  // Is trusted
  fields.push_back({"is_trusted", isTrusted ? "true" : "false"});

  return jsonObject(fields);
}
