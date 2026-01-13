//===--- SolverInterface.h - SMT solver invocation interface -*- C++ ----===//
//
// This source file is part of the tSwift project
//
// Copyright (c) 2026 Dropbox, Inc. All rights reserved.
// Licensed under Apache License v2.0
//
//===----------------------------------------------------------------------===//
//
// This file declares a small interface for invoking an external SMT solver
// (Z3/Z4) on generated SMT-LIB2 scripts and interpreting the results.
//
//===----------------------------------------------------------------------===//

#ifndef SWIFT_SILOPTIMIZER_VERIFICATION_SOLVERINTERFACE_H
#define SWIFT_SILOPTIMIZER_VERIFICATION_SOLVERINTERFACE_H

#include <optional>
#include <sstream>
#include <string>

namespace swift {
namespace verification {

enum class VerificationResult {
  Verified, // UNSAT - postcondition is provable
  Failed,   // SAT - found counterexample
  Unknown,  // Solver couldn't determine
  Timeout,  // Solver timed out
  Error     // Solver error (missing solver, IO error, etc)
};

struct SolverOutput {
  VerificationResult result = VerificationResult::Error;
  std::string model;      // Counterexample/model when SAT (best-effort)
  std::string rawOutput;  // Full solver output (stdout+stderr, best-effort)
  double timeSeconds = 0.0;
  std::string error;      // Non-empty on Error/Timeout (best-effort)
};

namespace detail {

inline std::string trim(const std::string &s) {
  size_t start = 0;
  while (start < s.size() && (s[start] == ' ' || s[start] == '\t' ||
                              s[start] == '\r' || s[start] == '\n')) {
    ++start;
  }
  size_t end = s.size();
  while (end > start && (s[end - 1] == ' ' || s[end - 1] == '\t' ||
                         s[end - 1] == '\r' || s[end - 1] == '\n')) {
    --end;
  }
  return s.substr(start, end - start);
}

inline std::string firstNonEmptyLine(const std::string &output) {
  std::istringstream iss(output);
  std::string line;
  while (std::getline(iss, line)) {
    line = trim(line);
    if (!line.empty()) {
      return line;
    }
  }
  return "";
}

} // namespace detail

/// Parse solver stdout/stderr and map to a high-level verification result.
inline VerificationResult parseResult(const std::string &output) {
  std::string first = detail::firstNonEmptyLine(output);
  if (first == "unsat") return VerificationResult::Verified;
  if (first == "sat") return VerificationResult::Failed;
  if (first == "unknown") return VerificationResult::Unknown;

  // Best-effort fallback: look for tokens anywhere, taking care with "unsat".
  if (output.find("\nunsat") != std::string::npos ||
      output.rfind("unsat", 0) == 0) {
    return VerificationResult::Verified;
  }
  if (output.find("\nsat") != std::string::npos ||
      output.rfind("sat", 0) == 0) {
    return VerificationResult::Failed;
  }
  if (output.find("unknown") != std::string::npos) {
    return VerificationResult::Unknown;
  }
  if (output.find("timeout") != std::string::npos ||
      output.find("TIMEOUT") != std::string::npos) {
    return VerificationResult::Timeout;
  }
  return VerificationResult::Error;
}

/// Extract the model portion from solver output for SAT (best-effort).
inline std::string extractModel(const std::string &output) {
  // Z3 prints:
  //   sat
  //   (model ...)
  std::string marker = "\nsat\n";
  size_t pos = output.find(marker);
  if (pos == std::string::npos) {
    if (output.rfind("sat\n", 0) == 0) {
      return detail::trim(output.substr(4));
    }
    return "";
  }
  return detail::trim(output.substr(pos + marker.size()));
}

/// Find an SMT solver executable (prefers "z4" then "z3") on PATH.
std::optional<std::string> findSmtSolverProgram();

/// Invoke an SMT solver on an SMT-LIB2 script.
SolverOutput invokeSolver(const std::string &smtScript,
                          unsigned timeoutMs = 5000);

} // namespace verification
} // namespace swift

#endif // SWIFT_SILOPTIMIZER_VERIFICATION_SOLVERINTERFACE_H
