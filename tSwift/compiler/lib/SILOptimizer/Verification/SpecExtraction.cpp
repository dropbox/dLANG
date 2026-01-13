//===--- SpecExtraction.cpp - Extract verification specs from AST --------===//
//
// This source file is part of the tSwift project
//
// Copyright (c) 2026 Dropbox, Inc. All rights reserved.
// Licensed under Apache License v2.0
//
//===----------------------------------------------------------------------===//
//
// This file implements extraction of verification specifications from
// Swift AST built-in attributes. When a function is annotated with
// @_requires("x > 0"), @_ensures("result > 0"), etc., this code extracts
// those conditions for verification condition generation.
//
//===----------------------------------------------------------------------===//

#include "swift/SILOptimizer/Verification/VerificationSpec.h"
#include "ConditionParser.h"

// Core AST includes
#include "swift/AST/Attr.h"
#include "swift/AST/Decl.h"

// SIL includes
#include "swift/SIL/SILFunction.h"
#include "swift/SIL/SILDeclRef.h"

// LLVM utilities
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"

#define DEBUG_TYPE "sil-verification-spec"

using namespace swift;

namespace swift {

VerificationStatus extractSpecifications(SILFunction &F) {
  VerificationStatus status;

  LLVM_DEBUG(llvm::dbgs() << "Extracting specs for function: "
                          << F.getName() << "\n");

  // Step 1: Get the underlying AST declaration
  SILDeclRef declRef = F.getDeclRef();
  auto *decl = declRef.getAbstractFunctionDecl();

  if (!decl) {
    // Closures, auto-generated thunks, etc. don't have AST declarations
    // with user-provided attributes. Skip them.
    LLVM_DEBUG(llvm::dbgs() << "  No AbstractFunctionDecl, skipping\n");
    return status;
  }

  // Debug: list all attributes on this decl
  LLVM_DEBUG({
    llvm::dbgs() << "  All attributes on decl:\n";
    for (auto *attr : decl->getAttrs()) {
      llvm::dbgs() << "    - Kind: " << static_cast<unsigned>(attr->getKind()) << "\n";
    }
  });

  // Step 2: Extract @_requires attributes
  for (auto *attr : decl->getAttrs().getAttributes<RequiresAttr>()) {
    VerificationSpec spec;
    spec.kind = VerificationSpec::Kind::Requires;
    spec.condition = attr->getCondition().str();
    spec.location = attr->getLocation();
    spec.function = &F;
    status.specs.push_back(std::move(spec));

    LLVM_DEBUG(llvm::dbgs() << "  Found @_requires: \""
                            << attr->getCondition() << "\"\n");
  }

  // Step 3: Extract @_ensures attributes
  for (auto *attr : decl->getAttrs().getAttributes<EnsuresAttr>()) {
    VerificationSpec spec;
    spec.kind = VerificationSpec::Kind::Ensures;
    spec.condition = attr->getCondition().str();
    spec.location = attr->getLocation();
    spec.function = &F;
    status.specs.push_back(std::move(spec));

    LLVM_DEBUG(llvm::dbgs() << "  Found @_ensures: \""
                            << attr->getCondition() << "\"\n");
  }

  // Step 4: Extract @_invariant attributes
  for (auto *attr : decl->getAttrs().getAttributes<InvariantAttr>()) {
    VerificationSpec spec;
    spec.kind = VerificationSpec::Kind::Invariant;
    spec.condition = attr->getCondition().str();
    spec.location = attr->getLocation();
    spec.function = &F;
    status.specs.push_back(std::move(spec));

    LLVM_DEBUG(llvm::dbgs() << "  Found @_invariant: \""
                            << attr->getCondition() << "\"\n");
  }

  // Step 5: Check for @_trusted attribute
  if (decl->getAttrs().hasAttribute<TrustedAttr>()) {
    status.isTrusted = true;
    LLVM_DEBUG(llvm::dbgs() << "  Found @_trusted, skipping verification\n");
  }

  LLVM_DEBUG(llvm::dbgs() << "  Total specs: " << status.specs.size()
                          << ", trusted: " << (status.isTrusted ? "yes" : "no")
                          << "\n");

  return status;
}

void parseSpecifications(VerificationStatus &status,
                         const std::vector<std::string> &paramNames) {
  LLVM_DEBUG(llvm::dbgs() << "Parsing " << status.specs.size()
                          << " specifications...\n");

  for (auto &spec : status.specs) {
    LLVM_DEBUG(llvm::dbgs() << "  Parsing @" << spec.getKindName()
                            << ": \"" << spec.condition << "\"\n");

    verification::ParseResult result =
        verification::ConditionParser::parse(spec.condition, paramNames);

    if (result.success()) {
      // Move the parsed AST into a shared_ptr for storage
      spec.parsedCondition = std::move(result.expr);

      LLVM_DEBUG({
        llvm::dbgs() << "    Parse successful:\n";
        spec.parsedCondition->dump(llvm::dbgs(), 6);
      });
    } else {
      spec.parseError = result.error;
      LLVM_DEBUG(llvm::dbgs() << "    Parse error at position "
                              << result.errorPos << ": "
                              << result.error << "\n");
    }
  }
}

} // end namespace swift
