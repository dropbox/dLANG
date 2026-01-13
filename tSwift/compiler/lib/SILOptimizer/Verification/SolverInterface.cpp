//===--- SolverInterface.cpp - SMT solver invocation interface ----------===//
//
// This source file is part of the tSwift project
//
// Copyright (c) 2026 Dropbox, Inc. All rights reserved.
// Licensed under Apache License v2.0
//
//===----------------------------------------------------------------------===//
//
// Implementation of Z3/Z4 invocation using LLVM's process utilities.
//
//===----------------------------------------------------------------------===//

#include "SolverInterface.h"

#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Program.h"

#include <array>
#include <chrono>
#include <fstream>
#include <sstream>
#include <vector>

namespace swift {
namespace verification {

static std::string readFileToString(const std::string &path) {
  std::ifstream ifs(path);
  std::ostringstream ss;
  ss << ifs.rdbuf();
  return ss.str();
}

std::optional<std::string> findSmtSolverProgram() {
  if (auto z4 = llvm::sys::findProgramByName("z4")) {
    return *z4;
  }
  if (auto z3 = llvm::sys::findProgramByName("z3")) {
    return *z3;
  }
  return std::nullopt;
}

SolverOutput invokeSolver(const std::string &smtScript, unsigned timeoutMs) {
  SolverOutput output;

  auto start = std::chrono::steady_clock::now();

  llvm::SmallString<128> smtPath;
  llvm::SmallString<128> outPath;
  llvm::SmallString<128> errPath;

  if (auto ec = llvm::sys::fs::createTemporaryFile("tswift_verify", "smt2",
                                                   smtPath)) {
    output.result = VerificationResult::Error;
    output.error = "failed to create temporary SMT2 file";
    return output;
  }

  if (auto ec =
          llvm::sys::fs::createTemporaryFile("tswift_verify", "out", outPath)) {
    llvm::sys::fs::remove(smtPath);
    output.result = VerificationResult::Error;
    output.error = "failed to create temporary stdout file";
    return output;
  }

  if (auto ec =
          llvm::sys::fs::createTemporaryFile("tswift_verify", "err", errPath)) {
    llvm::sys::fs::remove(smtPath);
    llvm::sys::fs::remove(outPath);
    output.result = VerificationResult::Error;
    output.error = "failed to create temporary stderr file";
    return output;
  }

  {
    std::ofstream ofs(smtPath.c_str());
    if (!ofs) {
      llvm::sys::fs::remove(smtPath);
      llvm::sys::fs::remove(outPath);
      llvm::sys::fs::remove(errPath);
      output.result = VerificationResult::Error;
      output.error = "failed to write SMT2 script";
      return output;
    }
    ofs << smtScript;
  }

  auto solverPath = findSmtSolverProgram();
  if (!solverPath) {
    llvm::sys::fs::remove(smtPath);
    llvm::sys::fs::remove(outPath);
    llvm::sys::fs::remove(errPath);
    output.result = VerificationResult::Error;
    output.error = "no SMT solver found on PATH (tried: z4, z3)";
    return output;
  }

  std::string solverProgram = *solverPath;
  unsigned timeoutSeconds = (timeoutMs + 999) / 1000;
  std::string timeoutArg = "-T:" + std::to_string(timeoutSeconds);

  std::vector<llvm::StringRef> args;
  args.push_back(solverProgram);
  args.push_back(timeoutArg);
  args.push_back(smtPath.str());

  std::array<std::optional<llvm::StringRef>, 3> redirects = {
      llvm::StringRef("/dev/null"),
      llvm::StringRef(outPath),
      llvm::StringRef(errPath),
  };

  std::string errMsg;
  bool execFailed = false;
  int rc = llvm::sys::ExecuteAndWait(solverProgram, args,
                                     /*Env=*/std::nullopt, redirects,
                                     /*SecondsToWait=*/timeoutSeconds,
                                     /*MemoryLimit=*/0, &errMsg, &execFailed);

  output.rawOutput = readFileToString(outPath.c_str());
  std::string stderrOut = readFileToString(errPath.c_str());
  if (!stderrOut.empty()) {
    if (!output.rawOutput.empty() && output.rawOutput.back() != '\n') {
      output.rawOutput.push_back('\n');
    }
    output.rawOutput += stderrOut;
  }

  auto end = std::chrono::steady_clock::now();
  output.timeSeconds =
      std::chrono::duration_cast<std::chrono::duration<double>>(end - start)
          .count();

  // Cleanup temp files.
  llvm::sys::fs::remove(smtPath);
  llvm::sys::fs::remove(outPath);
  llvm::sys::fs::remove(errPath);

  if (rc == -1) {
    output.result = VerificationResult::Timeout;
    output.error = "solver timed out";
    return output;
  }

  if (execFailed) {
    output.result = VerificationResult::Error;
    output.error = errMsg.empty() ? "solver execution failed" : errMsg;
    return output;
  }

  // Non-zero exit codes are treated as errors, but we still try to parse output.
  output.result = parseResult(output.rawOutput);
  if (output.result == VerificationResult::Failed) {
    output.model = extractModel(output.rawOutput);
  }

  if (output.result == VerificationResult::Error && rc != 0) {
    output.error =
        errMsg.empty() ? ("solver exited with code " + std::to_string(rc))
                       : errMsg;
  }

  return output;
}

} // namespace verification
} // namespace swift
