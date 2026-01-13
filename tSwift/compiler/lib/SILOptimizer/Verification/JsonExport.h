//===--- JsonExport.h - JSON export for Swift VC Bridge -*- C++ ----------===//
//
// This source file is part of the tSwift project
//
// Copyright (c) 2026 Dropbox, Inc. All rights reserved.
// Licensed under Apache License v2.0
//
//===----------------------------------------------------------------------===//
//
// This file declares JSON serialization utilities for exporting verification
// conditions to the vc-ir-swift Rust bridge library.
//
// The JSON schema matches vc-ir-swift/src/json_types.rs:
// - SwiftVcBundle: Complete function verification bundle
// - SwiftExpr: Expression AST nodes
// - SwiftAutoVc: Automatic verification conditions
// - SwiftType: Swift type representations
//
//===----------------------------------------------------------------------===//

#ifndef SWIFT_SILOPTIMIZER_VERIFICATION_JSONEXPORT_H
#define SWIFT_SILOPTIMIZER_VERIFICATION_JSONEXPORT_H

#include "ConditionAST.h"
#include "SilTranslator.h"
#include <string>
#include <vector>

namespace swift {
namespace verification {

//===----------------------------------------------------------------------===//
// ConditionExpr JSON Export
//===----------------------------------------------------------------------===//

/// Convert a ConditionExpr AST node to JSON string (SwiftExpr format).
/// The output matches the Rust SwiftExpr enum in json_types.rs.
///
/// Example output for BinaryExpr(Gt, ParamRef("x"), IntLiteral(0)):
///   {"kind":"Gt","lhs":{"kind":"ParamRef","name":"x","index":-1},
///    "rhs":{"kind":"IntLit","value":0}}
std::string exprToJson(const ConditionExpr *expr);

//===----------------------------------------------------------------------===//
// Type JSON Export
//===----------------------------------------------------------------------===//

/// Convert a ParamSmtType to JSON string (SwiftType format).
/// ParamSmtType::Int -> {"kind":"Int","signed":true,"bits":64}
/// ParamSmtType::Bool -> {"kind":"Bool"}
std::string typeToJson(ParamSmtType type);

//===----------------------------------------------------------------------===//
// AutoVC JSON Export
//===----------------------------------------------------------------------===//

/// Convert an AutoVC to JSON string (SwiftAutoVc format).
/// Matches the Rust SwiftAutoVc enum variants.
std::string autoVcToJson(const AutoVC &vc);

//===----------------------------------------------------------------------===//
// SwiftVcBundle JSON Export
//===----------------------------------------------------------------------===//

/// Information about a function parameter for JSON export.
struct ParamInfo {
  std::string name;
  ParamSmtType type;
  int index;

  ParamInfo(const std::string &n, ParamSmtType t, int i)
      : name(n), type(t), index(i) {}
};

/// Complete function verification bundle for JSON export.
/// This mirrors the Rust SwiftVcBundle struct.
struct VcBundleExport {
  /// Function name (user-facing)
  std::string functionName;

  /// Source location
  std::string sourceFile;
  unsigned sourceLine = 0;
  unsigned sourceColumn = 0;

  /// Function parameters
  std::vector<ParamInfo> parameters;

  /// Return type (optional)
  ParamSmtType returnType = ParamSmtType::Int;
  bool hasReturn = false;

  /// @requires conditions (preconditions)
  std::vector<const ConditionExpr *> requires;

  /// @ensures conditions (postconditions)
  std::vector<const ConditionExpr *> ensures;

  /// @invariant conditions (loop invariants)
  std::vector<const ConditionExpr *> invariants;

  /// Automatic verification conditions
  std::vector<const AutoVC *> autoVcs;

  /// Whether the function is @trusted
  bool isTrusted = false;

  /// Convert to JSON string (SwiftVcBundle format).
  std::string toJson() const;
};

//===----------------------------------------------------------------------===//
// JSON String Utilities
//===----------------------------------------------------------------------===//

/// Escape a string for JSON output.
/// Handles: " \ newline carriage-return tab and control characters.
std::string escapeJson(const std::string &s);

/// Build a JSON object from key-value pairs.
/// Example: jsonObject({{"name", "\"foo\""}, {"value", "42"}})
///          -> {"name":"foo","value":42}
std::string jsonObject(
    const std::vector<std::pair<std::string, std::string>> &fields);

/// Build a JSON array from elements.
/// Example: jsonArray({"1", "2", "3"}) -> [1,2,3]
std::string jsonArray(const std::vector<std::string> &elements);

} // namespace verification
} // namespace swift

#endif // SWIFT_SILOPTIMIZER_VERIFICATION_JSONEXPORT_H
