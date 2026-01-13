//===--- SILVerificationPass.cpp - Main verification condition pass ------===//
//
// This source file is part of the tSwift project
//
// Copyright (c) 2026 Dropbox, Inc. All rights reserved.
// Licensed under Apache License v2.0
//
//===----------------------------------------------------------------------===//
//
// This file implements the main SIL verification pass that:
// 1. Extracts @requires/@ensures/@invariant specs from function attributes
// 2. Collects verification conditions from SIL instructions
// 3. Generates VC IR for proving with Z4/Kani/Lean backends
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "sil-verification"

#include "swift/SILOptimizer/Verification/VerificationSpec.h"
#include "ConditionAST.h"  // For ConditionExpr dump()
#include "VcIrGen.h"       // For SMT-LIB2 generation
#include "SolverInterface.h" // For invoking Z3/Z4
#include "SilTranslator.h"  // For SIL -> ConditionExpr translation
#include "JsonExport.h"    // For vc-ir-swift bridge JSON export

// SIL includes
#include "swift/SIL/SILFunction.h"
#include "swift/SIL/SILBasicBlock.h"
#include "swift/SIL/SILInstruction.h"
#include "swift/SIL/SILDeclRef.h"

// AST includes (for accessing parameter names)
#include "swift/AST/ASTContext.h"
#include "swift/AST/Decl.h"
#include "swift/AST/DiagnosticsCommon.h"
#include "swift/AST/ParameterList.h"

// Pass manager
#include "swift/SILOptimizer/PassManager/Transforms.h"
#include "swift/SILOptimizer/PassManager/Passes.h"

// LLVM utilities
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/Statistic.h"

// Standard library
#include <fstream>
#include <map>
#include <sstream>

using namespace swift;
using namespace swift::verification;

//===----------------------------------------------------------------------===//
// Global Verification Summary Statistics
//===----------------------------------------------------------------------===//
// These counters track verification results across all functions in a module.
// They are updated by SILVerificationPass and read by SILVerificationSummaryPass.

namespace {

/// Global statistics for verification summary output.
/// This struct accumulates results across all function passes.
struct VerificationSummaryStats {
  unsigned verified = 0;
  unsigned trusted = 0;
  unsigned failed = 0;
  unsigned unknown = 0;
  unsigned timeout = 0;
  unsigned error = 0;
  unsigned noSpecs = 0;  // Functions without specs in verify-all mode
  double totalTimeSeconds = 0.0;
  bool enabled = false;  // Only output summary when verification is enabled

  void reset() {
    verified = trusted = failed = unknown = timeout = error = noSpecs = 0;
    totalTimeSeconds = 0.0;
    enabled = false;
  }

  unsigned total() const {
    return verified + trusted + failed + unknown + timeout + error;
  }
};

/// Global instance - accumulates across all function passes in a module.
static VerificationSummaryStats GlobalVerificationStats;

} // end anonymous namespace

STATISTIC(NumFunctionsAnalyzed, "Number of functions analyzed for verification");
STATISTIC(NumSpecsExtracted, "Number of @requires/@ensures specs extracted");
STATISTIC(NumTrustedFunctions, "Number of @trusted functions skipped");
STATISTIC(NumFunctionsNoSpecs, "Number of functions without specs (in -verify-all-functions mode)");
STATISTIC(NumFunctionsVerified, "Number of functions verified (unsat)");
STATISTIC(NumFunctionsFailed, "Number of functions with failed verification (sat)");
STATISTIC(NumFunctionsUnknown, "Number of functions with unknown verification result");
STATISTIC(NumFunctionsTimeout, "Number of functions that timed out during verification");
STATISTIC(NumFunctionsError, "Number of functions with verification errors");
STATISTIC(NumOverflowVCsChecked, "Number of overflow VCs checked");
STATISTIC(NumOverflowVCsVerified, "Number of overflow VCs verified (safe)");
STATISTIC(NumOverflowVCsFailed, "Number of overflow VCs that may overflow");
STATISTIC(NumDivByZeroVCsChecked, "Number of div-by-zero VCs checked");
STATISTIC(NumDivByZeroVCsVerified, "Number of div-by-zero VCs verified (safe)");
STATISTIC(NumDivByZeroVCsFailed, "Number of div-by-zero VCs that may fail");
STATISTIC(NumBoundsVCsChecked, "Number of bounds VCs checked");
STATISTIC(NumBoundsVCsVerified, "Number of bounds VCs verified (safe)");
STATISTIC(NumBoundsVCsFailed, "Number of bounds VCs that may fail");
STATISTIC(NumNilCheckVCsChecked, "Number of nil check VCs checked");
STATISTIC(NumNilCheckVCsVerified, "Number of nil check VCs verified (safe)");
STATISTIC(NumNilCheckVCsFailed, "Number of nil check VCs that may fail");
STATISTIC(NumAutoVCsDeduplicated, "Number of auto-VCs removed by de-duplication");

namespace {

/// Escape a string for JSON output.
std::string escapeJsonString(const std::string &s) {
  std::string result;
  result.reserve(s.size() + 16);
  for (char c : s) {
    switch (c) {
    case '"': result += "\\\""; break;
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

/// Result of verifying a single auto-VC.
struct AutoVCResult {
  std::string description;
  VerificationResult result;
  double timeSeconds;
  std::string model;  // Counterexample if result == Failed
};

/// Build SMT type mapping from translation result.
/// Converts ParamSmtType (from SilTranslator) to SmtType (for SmtLib2Gen).
std::map<std::string, SmtType> buildSmtTypeMap(
    const std::vector<std::string> &paramNames,
    const std::vector<ParamSmtType> &paramTypes) {
  std::map<std::string, SmtType> typeMap;
  for (size_t i = 0; i < paramNames.size() && i < paramTypes.size(); ++i) {
    SmtType smtType = (paramTypes[i] == ParamSmtType::Bool)
                          ? SmtType::Bool
                          : SmtType::Int;
    typeMap[paramNames[i]] = smtType;
  }
  return typeMap;
}

/// Export verification conditions to JSON for vc-ir-swift bridge.
/// This exports the function's specs and auto-VCs in SwiftVcBundle format
/// which can be parsed by the Rust vc-ir-swift library.
void exportVcBundleToJson(
    const std::string &exportPath,
    const std::string &functionName,
    const std::string &sourceFile,
    unsigned sourceLine,
    unsigned sourceColumn,
    const std::vector<std::string> &paramNames,
    const std::vector<ParamSmtType> &paramTypes,
    const std::vector<const ConditionExpr *> &requires,
    const std::vector<const ConditionExpr *> &ensures,
    const std::vector<AutoVC> &autoVCs,
    bool isTrusted) {
  if (exportPath.empty()) {
    return;
  }

  // Build the VcBundleExport structure
  VcBundleExport bundle;
  bundle.functionName = functionName;
  bundle.sourceFile = sourceFile;
  bundle.sourceLine = sourceLine;
  bundle.sourceColumn = sourceColumn;
  bundle.isTrusted = isTrusted;

  // Add parameters
  for (size_t i = 0; i < paramNames.size(); ++i) {
    ParamSmtType type = (i < paramTypes.size()) ? paramTypes[i] : ParamSmtType::Int;
    bundle.parameters.push_back(ParamInfo(paramNames[i], type, static_cast<int>(i)));
  }

  // Add @requires conditions
  for (const auto *req : requires) {
    bundle.requires.push_back(req);
  }

  // Add @ensures conditions
  for (const auto *ens : ensures) {
    bundle.ensures.push_back(ens);
  }

  // Add auto-VCs
  for (const auto &autoVc : autoVCs) {
    bundle.autoVcs.push_back(&autoVc);
  }

  // Export to JSON
  std::string json = bundle.toJson();

  // Append to export file (JSON Lines format)
  std::ofstream exportFile(exportPath, std::ios::app);
  if (exportFile.is_open()) {
    exportFile << json << "\n";
    exportFile.close();
    LLVM_DEBUG(llvm::dbgs() << "  Exported VcBundle JSON for " << functionName
                            << " to " << exportPath << "\n");
  } else {
    LLVM_DEBUG(llvm::dbgs() << "  Warning: Could not open export file: "
                            << exportPath << "\n");
  }
}

/// The main SIL verification pass.
///
/// This pass runs on each SIL function and:
/// 1. Extracts user-provided specifications from AST attributes
/// 2. Collects automatic verification conditions from dangerous operations
/// 3. Outputs VC IR for backend proving
class SILVerificationPass : public SILFunctionTransform {
public:
  void run() override {
    SILFunction *F = getFunction();
    ++NumFunctionsAnalyzed;

    auto &astContext = F->getModule().getASTContext();
    auto &diags = astContext.Diags;

    LLVM_DEBUG(llvm::dbgs() << "=== SIL Verification Pass: "
                            << F->getName() << " ===\n");

    // Step 1: Extract specifications from AST attributes
    VerificationStatus status = extractSpecifications(*F);
    NumSpecsExtracted += status.specs.size();

    SILDeclRef declRef = F->getDeclRef();
    auto *funcDecl = declRef.getAbstractFunctionDecl();

    // Step 2: Check if function is @trusted
    if (status.isTrusted) {
      ++NumTrustedFunctions;
      LLVM_DEBUG(llvm::dbgs() << "  @trusted - skipping verification\n");

      // Output TRUSTED status (visible to user, distinguishes from VERIFIED)
      llvm::errs() << "[VERIFY] " << F->getName() << ": TRUSTED (assumed correct) [0.000s]\n";

      // Track in global summary stats
      GlobalVerificationStats.enabled = true;
      GlobalVerificationStats.trusted++;

      // Export @trusted function to JSON (with isTrusted=true) if path is specified
      const std::string &jsonExportPath = F->getModule().getOptions().VerifyJsonExportPath;
      if (!jsonExportPath.empty() && funcDecl) {
        std::string functionName = funcDecl->getBaseName().userFacingName().str();

        // Get source location info
        std::string sourceFile;
        unsigned sourceLine = 0;
        unsigned sourceColumn = 0;
        SourceLoc loc = funcDecl->getLoc();
        if (loc.isValid()) {
          auto &SM = astContext.SourceMgr;
          sourceFile = SM.getDisplayNameForLoc(loc).str();
          auto lineAndCol = SM.getLineAndColumnInBuffer(loc);
          sourceLine = lineAndCol.first;
          sourceColumn = lineAndCol.second;
        }

        // Get parameter info for @trusted functions
        std::vector<std::string> trustedParamNames;
        std::vector<ParamSmtType> trustedParamTypes;
        if (auto *params = funcDecl->getParameters()) {
          for (auto *param : *params) {
            trustedParamNames.push_back(param->getName().str().str());
            // For @trusted functions, assume Int type (we don't translate SIL)
            trustedParamTypes.push_back(ParamSmtType::Int);
          }
        }

        std::vector<const ConditionExpr *> emptyRequires;
        std::vector<const ConditionExpr *> emptyEnsures;
        std::vector<AutoVC> emptyAutoVCs;
        exportVcBundleToJson(
            jsonExportPath, functionName, sourceFile, sourceLine, sourceColumn,
            trustedParamNames, trustedParamTypes,
            emptyRequires, emptyEnsures, emptyAutoVCs, true /* isTrusted */);
      }

      // Write to JSON report if -verify-report path is specified
      const std::string &reportPath = F->getModule().getOptions().VerifyReportPath;
      if (!reportPath.empty() && funcDecl) {
        std::string functionName = funcDecl->getBaseName().userFacingName().str();
        std::string mangledName = F->getName().str();

        // Get source location info
        std::string sourceFile;
        unsigned sourceLine = 0;
        unsigned sourceColumn = 0;
        SourceLoc loc = funcDecl->getLoc();
        if (loc.isValid()) {
          auto &SM = astContext.SourceMgr;
          sourceFile = SM.getDisplayNameForLoc(loc).str();
          auto lineAndCol = SM.getLineAndColumnInBuffer(loc);
          sourceLine = lineAndCol.first;
          sourceColumn = lineAndCol.second;
        }

        // Write JSON line for trusted function
        std::ofstream report(reportPath, std::ios::app);
        if (report.is_open()) {
          report << "{\"function\":\"" << escapeJsonString(functionName) << "\","
                 << "\"mangled\":\"" << escapeJsonString(mangledName) << "\",";
          if (!sourceFile.empty()) {
            report << "\"file\":\"" << escapeJsonString(sourceFile) << "\","
                   << "\"line\":" << sourceLine << ","
                   << "\"column\":" << sourceColumn << ",";
          }
          report << "\"result\":\"trusted\","
                 << "\"time_seconds\":0,"
                 << "\"is_trusted\":true,"
                 << "\"specs\":[]}\n";
          report.close();
        }
      }
      return;
    }

    // Step 3: Get parameter names for condition parsing
    std::vector<std::string> paramNames;
    if (funcDecl) {
      if (auto *params = funcDecl->getParameters()) {
        for (auto *param : *params) {
          paramNames.push_back(param->getName().str().str());
        }
      }
      LLVM_DEBUG({
        llvm::dbgs() << "  Parameter names: [";
        for (size_t i = 0; i < paramNames.size(); ++i) {
          if (i > 0) llvm::dbgs() << ", ";
          llvm::dbgs() << paramNames[i];
        }
        llvm::dbgs() << "]\n";
      });
    }

    // Step 4: Parse spec condition strings into AST
    if (!status.specs.empty()) {
      parseSpecifications(status, paramNames);
    }

    bool hadSpecParseErrors = false;
    for (const auto &spec : status.specs) {
      if (!spec.isParsed() && !spec.parseError.empty()) {
        hadSpecParseErrors = true;
        std::string message = "could not parse @_" + spec.getKindName().str() +
                              "(\"" + spec.condition + "\"): " +
                              spec.parseError;
        diags.diagnose(spec.location, diag::bridged_error,
                       astContext.AllocateCopy(StringRef(message)));
      }
    }
    if (hadSpecParseErrors) {
      return;
    }

    // Step 5: Log extracted and parsed specs
    if (!status.specs.empty()) {
      LLVM_DEBUG({
        llvm::dbgs() << "  Extracted specifications:\n";
        for (const auto &spec : status.specs) {
          llvm::dbgs() << "    @" << spec.getKindName()
                       << ": \"" << spec.condition << "\"\n";
          if (spec.isParsed()) {
            llvm::dbgs() << "      Parsed AST:\n";
            spec.parsedCondition->dump(llvm::dbgs(), 8);
          } else if (!spec.parseError.empty()) {
            llvm::dbgs() << "      Parse error: " << spec.parseError << "\n";
          }
        }
      });
    }

    // Step 6: Generate SMT-LIB2 for parsed specifications
    bool verifyAllFunctions = F->getModule().getOptions().VerifyAllFunctions;
    bool hasSpecs = !status.specs.empty();

    // If no specs and not in verify-all mode, skip this function
    if (!hasSpecs && !verifyAllFunctions) {
      return;
    }

    // Handle functions without specs in verify-all mode
    if (!hasSpecs && verifyAllFunctions) {
      // Skip external/imported functions - only track user-defined functions
      if (F->isExternalDeclaration() || !funcDecl) {
        return;
      }

      // Get source location info
      std::string sourceFile;
      unsigned sourceLine = 0;
      unsigned sourceColumn = 0;
      SourceLoc loc = funcDecl->getLoc();
      if (loc.isValid()) {
        auto &SM = astContext.SourceMgr;
        sourceFile = SM.getDisplayNameForLoc(loc).str();
        auto lineAndCol = SM.getLineAndColumnInBuffer(loc);
        sourceLine = lineAndCol.first;
        sourceColumn = lineAndCol.second;
      }

      // Skip functions without source locations (stdlib functions, etc.)
      if (sourceFile.empty()) {
        return;
      }

      ++NumFunctionsNoSpecs;
      GlobalVerificationStats.enabled = true;
      GlobalVerificationStats.noSpecs++;
      LLVM_DEBUG(llvm::dbgs() << "  No specs (verify-all mode)\n");

      // Even without specs, collect and verify auto-VCs (overflow, div-by-zero, etc.)
      TranslationResult autoVCCollection = SilTranslator::collectAutoVCs(*F);
      NumAutoVCsDeduplicated += autoVCCollection.vcsDeduplicated;
      if (!autoVCCollection.autoVCs.empty()) {
        LLVM_DEBUG(llvm::dbgs() << "  Verifying auto-VCs for function without specs\n");
        // No preconditions available (no @requires specs)
        std::vector<const ConditionExpr *> emptyPreconditions;
        verifyAutoVCs(autoVCCollection, emptyPreconditions, *F, funcDecl);
      }

      // Write to JSON report if path is specified
      const std::string &reportPath = F->getModule().getOptions().VerifyReportPath;
      if (!reportPath.empty()) {
        std::string functionName = funcDecl->getBaseName().userFacingName().str();
        std::string mangledName = F->getName().str();

        // Write JSON line for function without specs
        std::ofstream report(reportPath, std::ios::app);
        if (report.is_open()) {
          report << "{\"function\":\"" << escapeJsonString(functionName) << "\","
                 << "\"mangled\":\"" << escapeJsonString(mangledName) << "\","
                 << "\"file\":\"" << escapeJsonString(sourceFile) << "\","
                 << "\"line\":" << sourceLine << ","
                 << "\"column\":" << sourceColumn << ","
                 << "\"result\":\"no_specs\","
                 << "\"time_seconds\":0,"
                 << "\"auto_vcs\":" << autoVCCollection.autoVCs.size() << ","
                 << "\"specs\":[]}\n";
          report.close();
        }
      }

      // Export VcBundle JSON for vc-ir-swift bridge if path is specified
      const std::string &jsonExportPath = F->getModule().getOptions().VerifyJsonExportPath;
      if (!jsonExportPath.empty() && !autoVCCollection.autoVCs.empty()) {
        std::string functionName = funcDecl->getBaseName().userFacingName().str();
        std::vector<const ConditionExpr *> emptyRequires;
        std::vector<const ConditionExpr *> emptyEnsures;
        exportVcBundleToJson(
            jsonExportPath, functionName, sourceFile, sourceLine, sourceColumn,
            autoVCCollection.paramNames, autoVCCollection.paramTypes,
            emptyRequires, emptyEnsures, autoVCCollection.autoVCs, false);
      }
      return;
    }

    // Function has specs - proceed with verification
    {
      std::vector<const ConditionExpr *> preconditions;
      std::vector<const ConditionExpr *> postconditions;

      for (const auto &spec : status.specs) {
        if (spec.isParsed()) {
          const ConditionExpr *expr = spec.parsedCondition.get();
          if (spec.kind == VerificationSpec::Kind::Requires) {
            preconditions.push_back(expr);
          } else if (spec.kind == VerificationSpec::Kind::Ensures) {
            postconditions.push_back(expr);
          }
        }
      }

      // Generate SMT-LIB2 script if we have any conditions
      if (!preconditions.empty() || !postconditions.empty()) {
        // Step 6a: Translate SIL to function semantics
        const ConditionExpr *functionSemantics = nullptr;
        TranslationResult translation = SilTranslator::translate(*F);
        NumAutoVCsDeduplicated += translation.vcsDeduplicated;
        bool translationSucceeded = translation.success;

        if (translationSucceeded) {
          functionSemantics = translation.semantics.get();
          LLVM_DEBUG({
            llvm::dbgs() << "  Function semantics extracted:\n";
            functionSemantics->dump(llvm::dbgs(), 4);
            llvm::dbgs() << "  Instructions processed: "
                         << translation.instructionsProcessed << "\n";
            if (translation.unsupportedInstructions > 0) {
              llvm::dbgs() << "  Unsupported instructions: "
                           << translation.unsupportedInstructions << "\n";
            }
          });
        } else {
          LLVM_DEBUG(llvm::dbgs() << "  SIL translation failed: "
                                  << translation.error << "\n");
          // Translation failed (e.g., multi-block function).
          // We still want to collect and verify auto-VCs.
          // Use collectAutoVCs to walk all blocks and gather safety conditions.
          TranslationResult autoVCCollection = SilTranslator::collectAutoVCs(*F);
          NumAutoVCsDeduplicated += autoVCCollection.vcsDeduplicated;

          // Verify auto-VCs even though we can't verify specs
          if (!autoVCCollection.autoVCs.empty()) {
            LLVM_DEBUG(llvm::dbgs() << "  Verifying auto-VCs despite translation failure\n");
            verifyAutoVCs(autoVCCollection, preconditions, *F, funcDecl);
          }

          // Warn that spec verification was skipped
          std::string functionName =
              funcDecl ? funcDecl->getBaseName().userFacingName().str()
                       : F->getName().str();
          std::string message =
              "formal verification of @ensures skipped for '" + functionName +
              "': SIL translation failed: " + translation.error +
              (autoVCCollection.autoVCs.empty() ? "" :
               " (auto-VCs still verified)");
          diags.diagnose(funcDecl ? funcDecl->getLoc() : SourceLoc(),
                         diag::bridged_warning,
                         astContext.AllocateCopy(StringRef(message)));

          // Continue to scan for auto-VCs in the logging phase
          collectAutoVerificationConditions(*F);
          return;
        }

        // Generate SMT with function semantics
        // Use type info from translation for correct Bool/Int declarations
        auto typeMap = buildSmtTypeMap(translation.paramNames, translation.paramTypes);
        SmtLib2Gen gen(paramNames, typeMap);
        std::string smtScript = gen.generateVerificationScript(
            preconditions, postconditions, functionSemantics);

        LLVM_DEBUG({
          llvm::dbgs() << "  Generated SMT-LIB2 verification script:\n";
          llvm::dbgs() << "  ----------------------------------------\n";
          // Print each line with indentation
          std::istringstream iss(smtScript);
          std::string line;
          while (std::getline(iss, line)) {
            llvm::dbgs() << "  " << line << "\n";
          }
          llvm::dbgs() << "  ----------------------------------------\n";
        });

        // Invoke SMT solver (Z4/Z3) and interpret results.
        unsigned timeoutMs = F->getModule().getOptions().VerifyTimeout;
        SolverOutput solverOut = invokeSolver(smtScript, timeoutMs);

        // Always output verification results (visible in release builds)
        llvm::errs() << "[VERIFY] " << F->getName() << ": ";
        switch (solverOut.result) {
        case VerificationResult::Verified:
          llvm::errs() << "VERIFIED (unsat)";
          break;
        case VerificationResult::Failed:
          llvm::errs() << "FAILED (sat)";
          break;
        case VerificationResult::Unknown:
          llvm::errs() << "UNKNOWN";
          break;
        case VerificationResult::Timeout:
          llvm::errs() << "TIMEOUT";
          break;
        case VerificationResult::Error:
          llvm::errs() << "ERROR";
          break;
        }
        llvm::errs() << " [" << solverOut.timeSeconds << "s]\n";
        if (!solverOut.error.empty()) {
          llvm::errs() << "  Error: " << solverOut.error << "\n";
        }
        if (solverOut.result == VerificationResult::Failed &&
            !solverOut.model.empty()) {
          llvm::errs() << "  Counterexample:\n" << solverOut.model << "\n";
        }

        // Update statistics based on result
        switch (solverOut.result) {
        case VerificationResult::Verified: ++NumFunctionsVerified; break;
        case VerificationResult::Failed: ++NumFunctionsFailed; break;
        case VerificationResult::Unknown: ++NumFunctionsUnknown; break;
        case VerificationResult::Timeout: ++NumFunctionsTimeout; break;
        case VerificationResult::Error: ++NumFunctionsError; break;
        }

        // Update global summary stats
        GlobalVerificationStats.enabled = true;
        GlobalVerificationStats.totalTimeSeconds += solverOut.timeSeconds;
        switch (solverOut.result) {
        case VerificationResult::Verified: GlobalVerificationStats.verified++; break;
        case VerificationResult::Failed: GlobalVerificationStats.failed++; break;
        case VerificationResult::Unknown: GlobalVerificationStats.unknown++; break;
        case VerificationResult::Timeout: GlobalVerificationStats.timeout++; break;
        case VerificationResult::Error: GlobalVerificationStats.error++; break;
        }

        // Write JSON report if -verify-report path is specified
        const std::string &reportPath = F->getModule().getOptions().VerifyReportPath;
        if (!reportPath.empty()) {
          std::string functionName =
              funcDecl ? funcDecl->getBaseName().userFacingName().str()
                       : F->getName().str();
          std::string mangledName = F->getName().str();

          const char *resultStr = "unknown";
          switch (solverOut.result) {
          case VerificationResult::Verified: resultStr = "verified"; break;
          case VerificationResult::Failed: resultStr = "failed"; break;
          case VerificationResult::Unknown: resultStr = "unknown"; break;
          case VerificationResult::Timeout: resultStr = "timeout"; break;
          case VerificationResult::Error: resultStr = "error"; break;
          }

          // Get source location info
          std::string sourceFile;
          unsigned sourceLine = 0;
          unsigned sourceColumn = 0;
          if (funcDecl) {
            SourceLoc loc = funcDecl->getLoc();
            if (loc.isValid()) {
              auto &SM = astContext.SourceMgr;
              sourceFile = SM.getDisplayNameForLoc(loc).str();
              auto lineAndCol = SM.getLineAndColumnInBuffer(loc);
              sourceLine = lineAndCol.first;
              sourceColumn = lineAndCol.second;
            }
          }

          // Build specs JSON array
          std::string specsJson = "[";
          bool firstSpec = true;
          for (const auto &spec : status.specs) {
            if (!firstSpec) specsJson += ",";
            firstSpec = false;
            specsJson += "{\"kind\":\"" + spec.getKindName().str() + "\",";
            specsJson += "\"condition\":\"" + escapeJsonString(spec.condition) + "\"}";
          }
          specsJson += "]";

          // Write JSON line to report file (append mode)
          std::ofstream report(reportPath, std::ios::app);
          if (report.is_open()) {
            report << "{\"function\":\"" << escapeJsonString(functionName) << "\","
                   << "\"mangled\":\"" << escapeJsonString(mangledName) << "\",";
            // Add source location if available
            if (!sourceFile.empty()) {
              report << "\"file\":\"" << escapeJsonString(sourceFile) << "\","
                     << "\"line\":" << sourceLine << ","
                     << "\"column\":" << sourceColumn << ",";
            }
            report << "\"result\":\"" << resultStr << "\","
                   << "\"time_seconds\":" << solverOut.timeSeconds << ","
                   << "\"specs\":" << specsJson;
            if (solverOut.result == VerificationResult::Failed && !solverOut.model.empty()) {
              report << ",\"counterexample\":\"" << escapeJsonString(solverOut.model) << "\"";
            }
            if (!solverOut.error.empty()) {
              report << ",\"error\":\"" << escapeJsonString(solverOut.error) << "\"";
            }
            report << "}\n";
            report.close();
          }
        }

        if (solverOut.result != VerificationResult::Verified) {
          std::string functionName =
              funcDecl ? funcDecl->getBaseName().userFacingName().str()
                       : F->getName().str();

          std::string message;
          switch (solverOut.result) {
          case VerificationResult::Failed:
            message = "formal verification failed for '" + functionName +
                      "': could not prove postconditions";
            break;
          case VerificationResult::Unknown:
            message = "formal verification inconclusive for '" + functionName +
                      "': solver returned unknown";
            break;
          case VerificationResult::Timeout:
            message = "formal verification timed out for '" + functionName + "'";
            break;
          case VerificationResult::Error:
            message = "formal verification error for '" + functionName + "'";
            if (!solverOut.error.empty()) {
              message += ": " + solverOut.error;
            }
            break;
          case VerificationResult::Verified:
            llvm_unreachable("Handled above");
          }

          // Use error in strict mode, warning otherwise
          bool strictMode = F->getModule().getOptions().VerifyStrict;
          if (strictMode) {
            diags.diagnose(funcDecl ? funcDecl->getLoc() : SourceLoc(),
                           diag::bridged_error,
                           astContext.AllocateCopy(StringRef(message)));
          } else {
            diags.diagnose(funcDecl ? funcDecl->getLoc() : SourceLoc(),
                           diag::bridged_warning,
                           astContext.AllocateCopy(StringRef(message)));
          }

          for (const auto &spec : status.specs) {
            std::string noteMsg = "@_" + spec.getKindName().str() + "(\"" +
                                  spec.condition + "\")";
            diags.diagnose(spec.location, diag::bridged_note,
                           astContext.AllocateCopy(StringRef(noteMsg)));
          }

          if (solverOut.result == VerificationResult::Failed &&
              !solverOut.model.empty()) {
            std::string modelMsg = "counterexample (model):\n";
            size_t newlineCount = 0;
            for (size_t i = 0; i < solverOut.model.size(); ++i) {
              if (newlineCount >= 25 || i >= 2000) {
                modelMsg += "\n... (truncated; full model printed to stderr)";
                break;
              }
              char c = solverOut.model[i];
              modelMsg.push_back(c);
              if (c == '\n') {
                ++newlineCount;
              }
            }
            diags.diagnose(funcDecl ? funcDecl->getLoc() : SourceLoc(),
                           diag::bridged_note,
                           astContext.AllocateCopy(StringRef(modelMsg)));
          }
        }

        LLVM_DEBUG({
          llvm::dbgs() << "  Solver result: ";
          switch (solverOut.result) {
          case VerificationResult::Verified:
            llvm::dbgs() << "VERIFIED (unsat)";
            break;
          case VerificationResult::Failed:
            llvm::dbgs() << "FAILED (sat)";
            break;
          case VerificationResult::Unknown:
            llvm::dbgs() << "UNKNOWN";
            break;
          case VerificationResult::Timeout:
            llvm::dbgs() << "TIMEOUT";
            break;
          case VerificationResult::Error:
            llvm::dbgs() << "ERROR";
            break;
          }
          llvm::dbgs() << " in " << solverOut.timeSeconds << "s\n";
        });

        // Step 6b: Verify auto-VCs (overflow checks, etc.)
        if (!translation.autoVCs.empty()) {
          verifyAutoVCs(translation, preconditions, *F, funcDecl);
        }

        // Step 6c: Export VcBundle JSON for vc-ir-swift bridge if path is specified
        const std::string &jsonExportPath = F->getModule().getOptions().VerifyJsonExportPath;
        if (!jsonExportPath.empty()) {
          std::string functionName =
              funcDecl ? funcDecl->getBaseName().userFacingName().str()
                       : F->getName().str();

          // Get source location info
          std::string sourceFile;
          unsigned sourceLine = 0;
          unsigned sourceColumn = 0;
          if (funcDecl) {
            SourceLoc loc = funcDecl->getLoc();
            if (loc.isValid()) {
              auto &SM = astContext.SourceMgr;
              sourceFile = SM.getDisplayNameForLoc(loc).str();
              auto lineAndCol = SM.getLineAndColumnInBuffer(loc);
              sourceLine = lineAndCol.first;
              sourceColumn = lineAndCol.second;
            }
          }

          exportVcBundleToJson(
              jsonExportPath, functionName, sourceFile, sourceLine, sourceColumn,
              translation.paramNames, translation.paramTypes,
              preconditions, postconditions, translation.autoVCs, false);
        }
      }
    }

    // Step 7: Collect additional auto-VCs from SIL instructions (for logging)
    collectAutoVerificationConditions(*F);
  }

private:
  /// Verify automatically discovered verification conditions (overflow, etc.).
  void verifyAutoVCs(const TranslationResult &translation,
                     const std::vector<const ConditionExpr *> &preconditions,
                     SILFunction &F,
                     AbstractFunctionDecl *funcDecl) {
    auto &astContext = F.getModule().getASTContext();
    auto &diags = astContext.Diags;
    unsigned timeoutMs = F.getModule().getOptions().VerifyTimeout;
    const std::string &reportPath = F.getModule().getOptions().VerifyReportPath;
    bool strictMode = F.getModule().getOptions().VerifyStrict;

    // Per-function counters for summary
    unsigned funcSafe = 0, funcFailed = 0, funcUnknown = 0;
    unsigned funcTimeout = 0, funcError = 0;
    double funcTotalTime = 0.0;

    for (const auto &autoVC : translation.autoVCs) {
      // Update appropriate counter based on VC kind
      bool isDivByZero = autoVC.kind == AutoVC::Kind::DivByZero;
      bool isBounds = autoVC.kind == AutoVC::Kind::BoundsCheck;
      bool isNilCheck = autoVC.kind == AutoVC::Kind::NilCheck;
      if (isDivByZero) {
        ++NumDivByZeroVCsChecked;
      } else if (isBounds) {
        ++NumBoundsVCsChecked;
      } else if (isNilCheck) {
        ++NumNilCheckVCsChecked;
      } else {
        ++NumOverflowVCsChecked;
      }

      // Generate SMT script for this auto-VC
      // Use type info from translation for correct Bool/Int declarations
      auto typeMap = buildSmtTypeMap(translation.paramNames, translation.paramTypes);
      SmtLib2Gen gen(translation.paramNames, typeMap);
      std::string smtScript = gen.generateAutoVCScript(
          preconditions, autoVC.condition.get(), autoVC.description);

      LLVM_DEBUG({
        llvm::dbgs() << "  Auto-VC: " << autoVC.description << "\n";
        llvm::dbgs() << "  Generated SMT-LIB2 script:\n";
        std::istringstream iss(smtScript);
        std::string line;
        while (std::getline(iss, line)) {
          llvm::dbgs() << "    " << line << "\n";
        }
      });

      // Invoke solver
      SolverOutput solverOut = invokeSolver(smtScript, timeoutMs);

      // Output result
      std::string functionName =
          funcDecl ? funcDecl->getBaseName().userFacingName().str()
                   : F.getName().str();

      llvm::errs() << "[AUTO-VC] " << functionName;
      // Include source location if available
      if (autoVC.sourceLine > 0) {
        if (!autoVC.sourceFile.empty()) {
          // Extract just filename from path
          std::string filename = autoVC.sourceFile;
          size_t lastSlash = filename.rfind('/');
          if (lastSlash != std::string::npos) {
            filename = filename.substr(lastSlash + 1);
          }
          llvm::errs() << " (" << filename << ":" << autoVC.sourceLine;
          if (autoVC.sourceColumn > 0) {
            llvm::errs() << ":" << autoVC.sourceColumn;
          }
          llvm::errs() << ")";
        } else {
          llvm::errs() << " (line " << autoVC.sourceLine << ")";
        }
      }
      llvm::errs() << ": " << autoVC.description;
      funcTotalTime += solverOut.timeSeconds;
      switch (solverOut.result) {
      case VerificationResult::Verified:
        ++funcSafe;
        if (isDivByZero) {
          llvm::errs() << " - SAFE (divisor always non-zero)";
          ++NumDivByZeroVCsVerified;
        } else if (isBounds) {
          llvm::errs() << " - SAFE (index always in bounds)";
          ++NumBoundsVCsVerified;
        } else if (isNilCheck) {
          llvm::errs() << " - SAFE (optional always non-nil)";
          ++NumNilCheckVCsVerified;
        } else {
          llvm::errs() << " - SAFE (no overflow possible)";
          ++NumOverflowVCsVerified;
        }
        break;
      case VerificationResult::Failed:
        ++funcFailed;
        if (isDivByZero) {
          llvm::errs() << " - POTENTIAL DIVISION BY ZERO";
          ++NumDivByZeroVCsFailed;
        } else if (isBounds) {
          llvm::errs() << " - POTENTIAL OUT OF BOUNDS ACCESS";
          ++NumBoundsVCsFailed;
        } else if (isNilCheck) {
          llvm::errs() << " - POTENTIAL NIL UNWRAP";
          ++NumNilCheckVCsFailed;
        } else {
          llvm::errs() << " - POTENTIAL OVERFLOW";
          ++NumOverflowVCsFailed;
        }
        break;
      case VerificationResult::Unknown:
        ++funcUnknown;
        llvm::errs() << " - UNKNOWN";
        break;
      case VerificationResult::Timeout:
        ++funcTimeout;
        llvm::errs() << " - TIMEOUT";
        break;
      case VerificationResult::Error:
        ++funcError;
        llvm::errs() << " - ERROR";
        break;
      }
      llvm::errs() << " [" << solverOut.timeSeconds << "s]\n";

      // Emit diagnostic for failed checks
      if (solverOut.result == VerificationResult::Failed) {
        std::string message;
        std::string notePrefix;

        // Build source location string if available
        std::string locStr;
        if (autoVC.sourceLine > 0) {
          if (!autoVC.sourceFile.empty()) {
            locStr = " at " + autoVC.sourceFile + ":" +
                     std::to_string(autoVC.sourceLine);
            if (autoVC.sourceColumn > 0) {
              locStr += ":" + std::to_string(autoVC.sourceColumn);
            }
          } else {
            locStr = " at line " + std::to_string(autoVC.sourceLine);
          }
        }

        if (isDivByZero) {
          message = "potential division by zero in '" + functionName + "'" +
                    locStr + ": " + autoVC.description;
          notePrefix = "division by zero occurs with these inputs:\n";
        } else if (isBounds) {
          message = "potential out of bounds access in '" + functionName + "'" +
                    locStr + ": " + autoVC.description;
          notePrefix = "out of bounds access occurs with these inputs:\n";
        } else if (isNilCheck) {
          message = "potential nil unwrap in '" + functionName + "'" +
                    locStr + ": " + autoVC.description;
          notePrefix = "nil unwrap occurs with these inputs:\n";
        } else {
          message = "potential integer overflow in '" + functionName + "'" +
                    locStr + ": " + autoVC.description;
          notePrefix = "overflow occurs with these inputs:\n";
        }
        if (strictMode) {
          diags.diagnose(funcDecl ? funcDecl->getLoc() : SourceLoc(),
                         diag::bridged_error,
                         astContext.AllocateCopy(StringRef(message)));
        } else {
          diags.diagnose(funcDecl ? funcDecl->getLoc() : SourceLoc(),
                         diag::bridged_warning,
                         astContext.AllocateCopy(StringRef(message)));
        }

        if (!solverOut.model.empty()) {
          std::string modelMsg = notePrefix + solverOut.model.substr(0, 500);
          diags.diagnose(funcDecl ? funcDecl->getLoc() : SourceLoc(),
                         diag::bridged_note,
                         astContext.AllocateCopy(StringRef(modelMsg)));
        }
      }

      // Write to JSON report if enabled
      if (!reportPath.empty()) {
        const char *resultStr = "unknown";
        switch (solverOut.result) {
        case VerificationResult::Verified: resultStr = "safe"; break;
        case VerificationResult::Failed:
          if (isDivByZero) {
            resultStr = "potential_div_by_zero";
          } else if (isBounds) {
            resultStr = "potential_out_of_bounds";
          } else if (isNilCheck) {
            resultStr = "potential_nil_unwrap";
          } else {
            resultStr = "potential_overflow";
          }
          break;
        case VerificationResult::Unknown: resultStr = "unknown"; break;
        case VerificationResult::Timeout: resultStr = "timeout"; break;
        case VerificationResult::Error: resultStr = "error"; break;
        }

        std::ofstream report(reportPath, std::ios::app);
        if (report.is_open()) {
          report << "{\"type\":\"auto_vc\","
                 << "\"function\":\"" << escapeJsonString(functionName) << "\","
                 << "\"kind\":\"" << autoVC.getKindName() << "\","
                 << "\"source\":\"" << autoVC.getSourceName() << "\","
                 << "\"description\":\"" << escapeJsonString(autoVC.description) << "\","
                 << "\"result\":\"" << resultStr << "\","
                 << "\"time_seconds\":" << solverOut.timeSeconds;
          // Add source location info if available
          if (!autoVC.sourceFile.empty()) {
            report << ",\"file\":\"" << escapeJsonString(autoVC.sourceFile) << "\"";
          }
          if (autoVC.sourceLine > 0) {
            report << ",\"line\":" << autoVC.sourceLine;
          }
          if (autoVC.sourceColumn > 0) {
            report << ",\"column\":" << autoVC.sourceColumn;
          }
          if (autoVC.checkId > 0) {
            report << ",\"check_id\":" << autoVC.checkId;
          }
          if (solverOut.result == VerificationResult::Failed && !solverOut.model.empty()) {
            report << ",\"counterexample\":\"" << escapeJsonString(solverOut.model) << "\"";
          }
          report << "}\n";
          report.close();
        }
      }
    }

    // Output per-function summary if there were multiple auto-VCs
    unsigned totalChecks = funcSafe + funcFailed + funcUnknown + funcTimeout + funcError;
    if (totalChecks > 1) {
      std::string functionName =
          funcDecl ? funcDecl->getBaseName().userFacingName().str()
                   : F.getName().str();
      llvm::errs() << "[AUTO-VC SUMMARY] " << functionName << ": "
                   << totalChecks << " checks - ";
      if (funcFailed == 0 && funcUnknown == 0 && funcTimeout == 0 && funcError == 0) {
        llvm::errs() << "ALL SAFE";
      } else {
        llvm::errs() << funcSafe << " safe";
        if (funcFailed > 0) llvm::errs() << ", " << funcFailed << " failed";
        if (funcUnknown > 0) llvm::errs() << ", " << funcUnknown << " unknown";
        if (funcTimeout > 0) llvm::errs() << ", " << funcTimeout << " timeout";
        if (funcError > 0) llvm::errs() << ", " << funcError << " error";
      }
      llvm::errs() << " [" << funcTotalTime << "s total]\n";
    }
  }

  /// Collect automatic verification conditions from SIL instructions.
  /// These are implicit safety conditions like bounds checks, overflow, etc.
  void collectAutoVerificationConditions(SILFunction &F) {
    LLVM_DEBUG(llvm::dbgs() << "  Scanning for auto-VCs...\n");

    for (auto &BB : F) {
      for (auto &I : BB) {
        // Check for builtin instructions (overflow, division)
        if (auto *builtin = dyn_cast<BuiltinInst>(&I)) {
          analyzeBuiltin(builtin);
        }
        // Check for index_addr (bounds)
        else if (auto *indexAddr = dyn_cast<IndexAddrInst>(&I)) {
          analyzeIndexAddr(indexAddr);
        }
        // Check for unchecked_enum_data (nil unwrap)
        else if (auto *uncheckedEnum = dyn_cast<UncheckedEnumDataInst>(&I)) {
          analyzeUncheckedEnum(uncheckedEnum);
        }
        // Check for unconditional_checked_cast (may trap; optional unwrap/cast)
        else if (auto *checkedCast = dyn_cast<UnconditionalCheckedCastInst>(&I)) {
          analyzeUnconditionalCheckedCast(checkedCast);
        }
        // Check for cond_fail (explicit failure points)
        else if (auto *condFail = dyn_cast<CondFailInst>(&I)) {
          analyzeCondFail(condFail);
        }
      }
    }
  }

  void analyzeBuiltin(BuiltinInst *builtin) {
    StringRef name = builtin->getName().str();

    // Check for overflow operations
    if (name.contains("_with_overflow")) {
      LLVM_DEBUG(llvm::dbgs() << "    Found overflow op: " << name << "\n");
      // TODO: Generate overflow VC
    }
    // Check for division
    else if (name == "sdiv" || name == "udiv" ||
             name == "srem" || name == "urem") {
      LLVM_DEBUG(llvm::dbgs() << "    Found division: " << name << "\n");
      // TODO: Generate division-by-zero VC
    }
  }

  void analyzeIndexAddr(IndexAddrInst *indexAddr) {
    LLVM_DEBUG(llvm::dbgs() << "    Found index_addr - needs bounds check\n");
    // TODO: Generate bounds check VC
    // VC: index >= 0 && index < array.count
  }

  void analyzeUncheckedEnum(UncheckedEnumDataInst *uncheckedEnum) {
    LLVM_DEBUG(llvm::dbgs() << "    Found unchecked_enum_data - needs nil check\n");
    // TODO: Generate nil check VC
    // VC: optional != nil
  }

  void analyzeUnconditionalCheckedCast(UnconditionalCheckedCastInst *checkedCast) {
    LLVM_DEBUG(llvm::dbgs() << "    Found unconditional_checked_cast - may need safety check\n");
    // TODO: Generate cast safety VC or treat Optional<T> -> T as nil check.
  }

  void analyzeCondFail(CondFailInst *condFail) {
    StringRef message = condFail->getMessage();
    LLVM_DEBUG(llvm::dbgs() << "    Found cond_fail: \"" << message << "\"\n");
    // cond_fail instructions are already verified by Swift's runtime
    // We can use them to extract implicit assumptions
  }
};

} // end anonymous namespace

//===----------------------------------------------------------------------===//
// Verification Summary Pass (Module Transform)
//===----------------------------------------------------------------------===//
//
// This pass runs after all function verification passes and outputs an
// aggregate summary of verification results.

namespace {

class SILVerificationSummaryPass : public SILModuleTransform {
public:
  void run() override {
    // Only output summary if verification was enabled
    if (!GlobalVerificationStats.enabled) {
      return;
    }

    unsigned total = GlobalVerificationStats.total();
    if (total == 0 && GlobalVerificationStats.noSpecs == 0) {
      // No functions were verified at all
      GlobalVerificationStats.reset();
      return;
    }

    // Format: [VERIFY SUMMARY] 5 verified, 2 trusted, 0 failed, 0 unknown (0.123s total)
    llvm::errs() << "[VERIFY SUMMARY] ";

    // Count functions with specs (verified/trusted/failed/unknown/timeout/error)
    bool first = true;
    if (GlobalVerificationStats.verified > 0) {
      llvm::errs() << GlobalVerificationStats.verified << " verified";
      first = false;
    }
    if (GlobalVerificationStats.trusted > 0) {
      if (!first) llvm::errs() << ", ";
      llvm::errs() << GlobalVerificationStats.trusted << " trusted";
      first = false;
    }
    if (GlobalVerificationStats.failed > 0) {
      if (!first) llvm::errs() << ", ";
      llvm::errs() << GlobalVerificationStats.failed << " failed";
      first = false;
    }
    if (GlobalVerificationStats.unknown > 0) {
      if (!first) llvm::errs() << ", ";
      llvm::errs() << GlobalVerificationStats.unknown << " unknown";
      first = false;
    }
    if (GlobalVerificationStats.timeout > 0) {
      if (!first) llvm::errs() << ", ";
      llvm::errs() << GlobalVerificationStats.timeout << " timeout";
      first = false;
    }
    if (GlobalVerificationStats.error > 0) {
      if (!first) llvm::errs() << ", ";
      llvm::errs() << GlobalVerificationStats.error << " error";
      first = false;
    }

    // If only functions without specs were analyzed (verify-all mode)
    if (first && GlobalVerificationStats.noSpecs > 0) {
      llvm::errs() << "0 verified";
    }

    // Total time
    char timeBuf[32];
    snprintf(timeBuf, sizeof(timeBuf), "%.3f", GlobalVerificationStats.totalTimeSeconds);
    llvm::errs() << " (" << timeBuf << "s total)\n";

    // Write JSON summary to report file if path is specified
    const std::string &reportPath = getModule().getOptions().VerifyReportPath;
    if (!reportPath.empty()) {
      std::ofstream report(reportPath, std::ios::app);
      if (report.is_open()) {
        report << "{\"type\":\"summary\","
               << "\"verified\":" << GlobalVerificationStats.verified << ","
               << "\"trusted\":" << GlobalVerificationStats.trusted << ","
               << "\"failed\":" << GlobalVerificationStats.failed << ","
               << "\"unknown\":" << GlobalVerificationStats.unknown << ","
               << "\"timeout\":" << GlobalVerificationStats.timeout << ","
               << "\"error\":" << GlobalVerificationStats.error << ","
               << "\"no_specs\":" << GlobalVerificationStats.noSpecs << ","
               << "\"total_time_seconds\":" << GlobalVerificationStats.totalTimeSeconds
               << "}\n";
        report.close();
      }
    }

    // Reset stats for next module (in case of multi-module compilation)
    GlobalVerificationStats.reset();
  }
};

} // end anonymous namespace

//===----------------------------------------------------------------------===//
// Pass Registration
//===----------------------------------------------------------------------===//

/// Factory function to create the verification pass.
/// This will be called by the pass manager when the pass is scheduled.
///
/// To register this pass in the Swift compiler:
/// 1. Add to Passes.def:
///    LEGACY_PASS(SILVerification, "sil-verification",
///                "Verification condition generation for formal verification")
///
/// 2. Link this file in CMakeLists.txt:
///    add_swift_host_library(swiftSILOptimizer STATIC
///      ...
///      Verification/SILVerificationPass.cpp
///      Verification/SpecExtraction.cpp
///      ...
///    )
SILTransform *swift::createSILVerification() {
  return new SILVerificationPass();
}

/// Factory function to create the verification summary pass.
/// This module pass should run after all function verification passes
/// to output an aggregate summary of verification results.
///
/// To register in Passes.def:
///    LEGACY_PASS(SILVerificationSummary, "sil-verification-summary",
///                "Output verification summary after all functions are verified")
SILTransform *swift::createSILVerificationSummary() {
  return new SILVerificationSummaryPass();
}
