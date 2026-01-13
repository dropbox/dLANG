//===--- SilTranslator.cpp - SIL to ConditionExpr translation -------------===//
//
// This source file is part of the tSwift project
//
// Copyright (c) 2026 Dropbox, Inc. All rights reserved.
// Licensed under Apache License v2.0
//
//===----------------------------------------------------------------------===//

#define DEBUG_TYPE "sil-verification-translate"

#include "SilTranslator.h"
#include "swift/SIL/SILArgument.h"
#include "swift/SIL/SILInstruction.h"
#include "swift/SIL/SILModule.h"
#include "swift/SIL/SILLocation.h"
#include "swift/SIL/InstructionUtils.h"
#include "swift/AST/Builtins.h"
#include "swift/AST/Decl.h"
#include "swift/AST/Module.h"
#include "swift/AST/ParameterList.h"
#include "swift/AST/Types.h"
#include "swift/Basic/SourceManager.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/ADT/APInt.h"

#include <limits>

using namespace swift;
using namespace swift::verification;

// INT64 bounds for overflow verification
// Note: SMT-LIB2 uses arbitrary precision integers, so we model bounds explicitly
static const int64_t INT64_MIN_VAL = std::numeric_limits<int64_t>::min();
static const int64_t INT64_MAX_VAL = std::numeric_limits<int64_t>::max();

//===----------------------------------------------------------------------===//
// Expression Cloning
//===----------------------------------------------------------------------===//

std::unique_ptr<ConditionExpr> SilTranslator::cloneExpr(const ConditionExpr *expr) {
  if (!expr) return nullptr;

  switch (expr->getKind()) {
  case ConditionExpr::Kind::IntLiteral: {
    auto *lit = static_cast<const IntLiteralExpr *>(expr);
    return std::make_unique<IntLiteralExpr>(lit->getValue());
  }
  case ConditionExpr::Kind::BoolLiteral: {
    auto *lit = static_cast<const BoolLiteralExpr *>(expr);
    return std::make_unique<BoolLiteralExpr>(lit->getValue());
  }
  case ConditionExpr::Kind::ParamRef: {
    auto *ref = static_cast<const ParamRefExpr *>(expr);
    return std::make_unique<ParamRefExpr>(ref->getName(), ref->getParamIndex());
  }
  case ConditionExpr::Kind::ResultRef: {
    return std::make_unique<ResultRefExpr>();
  }
  default:
    // For binary/unary expressions, recursively clone
    if (expr->isBinaryOp()) {
      auto *bin = static_cast<const BinaryExpr *>(expr);
      return std::make_unique<BinaryExpr>(
          expr->getKind(),
          cloneExpr(bin->getLHS()),
          cloneExpr(bin->getRHS()));
    }
    if (expr->isUnaryOp()) {
      auto *un = static_cast<const UnaryExpr *>(expr);
      return std::make_unique<UnaryExpr>(
          expr->getKind(),
          cloneExpr(un->getOperand()));
    }
    return nullptr;
  }
}

//===----------------------------------------------------------------------===//
// Value Map Operations
//===----------------------------------------------------------------------===//

const ConditionExpr *SilTranslator::getExpr(SILValue value) {
  auto it = valueMap.find(value);
  if (it != valueMap.end()) {
    return it->second.get();
  }
  return nullptr;
}

void SilTranslator::setExpr(SILValue value, std::unique_ptr<ConditionExpr> expr) {
  valueMap[value] = std::move(expr);
}

bool SilTranslator::hasExpr(SILValue value) const {
  return valueMap.count(value) > 0;
}

unsigned SilTranslator::getCheckId(SILValue value) const {
  auto it = valueCheckIdMap.find(value);
  if (it != valueCheckIdMap.end()) {
    return it->second;
  }
  return 0;
}

void SilTranslator::setCheckId(SILValue value, unsigned checkId) {
  valueCheckIdMap[value] = checkId;
}

//===----------------------------------------------------------------------===//
// Source Location Extraction
//===----------------------------------------------------------------------===//

void SilTranslator::extractSourceLocation(SILInstruction &I) {
  // Reset to defaults
  currentSourceFile.clear();
  currentSourceLine = 0;
  currentSourceColumn = 0;

  // Try to get source location from the instruction
  SILLocation loc = I.getLoc();
  if (loc.isNull()) return;

  // Try to get SourceLoc from the SIL location
  SourceLoc sourceLoc = loc.getSourceLoc();
  if (!sourceLoc.isValid()) return;

  // Get line and column from SourceManager
  if (auto *SF = I.getFunction()->getModule().getSwiftModule()) {
    auto &SM = SF->getASTContext().SourceMgr;
    auto lineAndCol = SM.getPresumedLineAndColumnForLoc(sourceLoc);
    currentSourceLine = lineAndCol.first;
    currentSourceColumn = lineAndCol.second;

    // Get filename
    unsigned bufferID = SM.findBufferContainingLoc(sourceLoc);
    currentSourceFile = SM.getIdentifierForBuffer(bufferID).str();
  }
}

//===----------------------------------------------------------------------===//
// Instruction Processing
//===----------------------------------------------------------------------===//

bool SilTranslator::processArgument(SILFunctionArgument *arg) {
  // Get parameter name from decl if available
  std::string name;
  if (auto *decl = arg->getDecl()) {
    name = decl->getBaseName().userFacingName().str();
  } else {
    // Fallback to index-based name
    name = "arg" + std::to_string(arg->getIndex());
  }

  int index = arg->getIndex();
  paramNames.push_back(name);

  // Detect if this is a Bool parameter (Builtin.Int1)
  // Swift Bool is lowered to Builtin.Int1 in SIL
  ParamSmtType smtType = ParamSmtType::Int;
  SILType silType = arg->getType();
  CanType astType = silType.getASTType();

  // Check for Builtin.Int1 (Bool's underlying type)
  if (auto builtinType = dyn_cast<BuiltinIntegerType>(astType)) {
    if (builtinType->getWidth().isFixedWidth() &&
        builtinType->getFixedWidth() == 1) {
      smtType = ParamSmtType::Bool;
      LLVM_DEBUG(llvm::dbgs() << "    Detected Bool (Int1) parameter\n");
    }
  }
  // Also check if the AST type is Swift.Bool
  else if (auto *nominalDecl = astType->getAnyNominal()) {
    if (nominalDecl->getName().str() == "Bool") {
      smtType = ParamSmtType::Bool;
      LLVM_DEBUG(llvm::dbgs() << "    Detected Swift.Bool parameter\n");
    }
  }

  paramTypes.push_back(smtType);

  auto paramRef = std::make_unique<ParamRefExpr>(name, index);
  LLVM_DEBUG(llvm::dbgs() << "    Arg " << index << " -> " << name
                          << " (type: " << (smtType == ParamSmtType::Bool ? "Bool" : "Int")
                          << ")\n");
  setExpr(arg, std::move(paramRef));
  return true;
}

bool SilTranslator::processIntegerLiteral(IntegerLiteralInst *inst) {
  APInt value = inst->getValue();
  // For now, assume the value fits in int64
  int64_t intVal = value.getSExtValue();

  auto lit = std::make_unique<IntLiteralExpr>(intVal);
  LLVM_DEBUG(llvm::dbgs() << "    IntLit: " << intVal << "\n");
  setExpr(inst, std::move(lit));
  return true;
}

bool SilTranslator::processBuiltin(BuiltinInst *inst) {
  StringRef name = inst->getName().str();
  LLVM_DEBUG(llvm::dbgs() << "    Builtin: " << name << "\n");

  // Handle common builtin "casts"/assumptions as pass-through.
  // These frequently appear in optimized SIL and are important for tracking
  // constants/parameters through cond_fail checks.
  if (name.starts_with("assumeNonNegative_") ||
      name.starts_with("int_expect_") ||
      name.starts_with("truncOrBitCast_") ||
      name.starts_with("zextOrBitCast_") ||
      name.starts_with("sextOrBitCast_")) {
    if (inst->getNumOperands() >= 1) {
      const ConditionExpr *opExpr = getExpr(inst->getOperand(0));
      if (opExpr) {
        setExpr(inst, cloneExpr(opExpr));
      }
    }
    return true;
  }

  // Handle integer comparisons (used heavily for bounds checks, etc.).
  // Examples seen in SIL:
  //   builtin "cmp_slt_Int64"(%a, %b) : $Builtin.Int1
  //   builtin "cmp_sge_Int64"(%a, %b) : $Builtin.Int1
  //   builtin "cmp_eq_Int8"(%a, %b)  : $Builtin.Int1
  if (name.starts_with("cmp_")) {
    // Parse "cmp_<op>_<type>".
    StringRef rest = name.drop_front(4);
    size_t underscorePos = rest.find('_');
    StringRef opToken = (underscorePos == StringRef::npos) ? rest : rest.take_front(underscorePos);

    ConditionExpr::Kind cmpKind;
    if (opToken == "eq") {
      cmpKind = ConditionExpr::Kind::Eq;
    } else if (opToken == "ne") {
      cmpKind = ConditionExpr::Kind::Ne;
    } else if (opToken == "slt") {
      cmpKind = ConditionExpr::Kind::Lt;
    } else if (opToken == "sle") {
      cmpKind = ConditionExpr::Kind::Le;
    } else if (opToken == "sgt") {
      cmpKind = ConditionExpr::Kind::Gt;
    } else if (opToken == "sge") {
      cmpKind = ConditionExpr::Kind::Ge;
    } else {
      LLVM_DEBUG(llvm::dbgs() << "      Unsupported cmp op: " << opToken << "\n");
      ++unsupportedInstructions;
      return true;
    }

    if (inst->getNumOperands() < 2) {
      LLVM_DEBUG(llvm::dbgs() << "      Not enough operands for cmp\n");
      return true;
    }

    const ConditionExpr *lhs = getExpr(inst->getOperand(0));
    const ConditionExpr *rhs = getExpr(inst->getOperand(1));
    if (!lhs || !rhs) {
      LLVM_DEBUG(llvm::dbgs() << "      Missing cmp operand expression\n");
      return true;
    }

    setExpr(inst, std::make_unique<BinaryExpr>(cmpKind, cloneExpr(lhs), cloneExpr(rhs)));
    return true;
  }

  // Handle boolean operations on Builtin.Int1 values.
  // Examples seen in SIL:
  //   builtin "or_Int1"(%a, %b) : $Builtin.Int1
  //   builtin "xor_Int1"(%a, %b) : $Builtin.Int1
  if (name == "and_Int1" || name == "or_Int1" || name == "xor_Int1") {
    if (inst->getNumOperands() < 2) {
      LLVM_DEBUG(llvm::dbgs() << "      Not enough operands for " << name << "\n");
      return true;
    }

    const ConditionExpr *lhs = getExpr(inst->getOperand(0));
    const ConditionExpr *rhs = getExpr(inst->getOperand(1));
    if (!lhs || !rhs) {
      LLVM_DEBUG(llvm::dbgs() << "      Missing boolean operand expression\n");
      return true;
    }

    if (name == "and_Int1") {
      setExpr(inst, std::make_unique<BinaryExpr>(ConditionExpr::Kind::And, cloneExpr(lhs), cloneExpr(rhs)));
    } else if (name == "or_Int1") {
      setExpr(inst, std::make_unique<BinaryExpr>(ConditionExpr::Kind::Or, cloneExpr(lhs), cloneExpr(rhs)));
    } else { // xor_Int1
      // XOR for Bool is inequality.
      setExpr(inst, std::make_unique<BinaryExpr>(ConditionExpr::Kind::Ne, cloneExpr(lhs), cloneExpr(rhs)));
    }
    return true;
  }

  if (name == "not_Int1") {
    if (inst->getNumOperands() < 1) {
      LLVM_DEBUG(llvm::dbgs() << "      Not enough operands for not_Int1\n");
      return true;
    }
    const ConditionExpr *op = getExpr(inst->getOperand(0));
    if (!op) {
      LLVM_DEBUG(llvm::dbgs() << "      Missing operand expression for not_Int1\n");
      return true;
    }
    setExpr(inst, std::make_unique<UnaryExpr>(ConditionExpr::Kind::Not, cloneExpr(op)));
    return true;
  }

  // Handle arithmetic builtins with overflow checking
  // Format: smul_with_overflow_Int64, sadd_with_overflow_Int64, etc.
  // These return a tuple (result, overflow_flag)

  ConditionExpr::Kind op;
  bool isOverflowOp = false;
  const char *opName = nullptr;

  if (name.contains("mul_with_overflow") || name.contains("smul") || name.contains("umul")) {
    op = ConditionExpr::Kind::Mul;
    isOverflowOp = name.contains("with_overflow");
    opName = "mul";
  } else if (name.contains("add_with_overflow") || name.contains("sadd") || name.contains("uadd")) {
    op = ConditionExpr::Kind::Add;
    isOverflowOp = name.contains("with_overflow");
    opName = "add";
  } else if (name.contains("sub_with_overflow") || name.contains("ssub") || name.contains("usub")) {
    op = ConditionExpr::Kind::Sub;
    isOverflowOp = name.contains("with_overflow");
    opName = "sub";
  } else if (name.contains("sdiv") || name.contains("udiv")) {
    op = ConditionExpr::Kind::Div;
    opName = "div";
    // Mark that we need to generate a div-by-zero check
  } else if (name.contains("srem") || name.contains("urem")) {
    op = ConditionExpr::Kind::Mod;
    opName = "mod";
    // Mark that we need to generate a div-by-zero check (mod also requires non-zero divisor)
  } else {
    // Unknown builtin - skip
    LLVM_DEBUG(llvm::dbgs() << "      Unsupported builtin\n");
    ++unsupportedInstructions;
    return true; // Continue processing, just don't track this value
  }

  // Get operands (skip the last operand for overflow ops - it's the flag)
  unsigned numOperands = inst->getNumOperands();
  if (isOverflowOp && numOperands >= 3) {
    // Operands: lhs, rhs, overflow_flag (unused)
    numOperands = 2;
  }

  if (numOperands < 2) {
    LLVM_DEBUG(llvm::dbgs() << "      Not enough operands\n");
    return true;
  }

  const ConditionExpr *lhs = getExpr(inst->getOperand(0));
  const ConditionExpr *rhs = getExpr(inst->getOperand(1));

  if (!lhs || !rhs) {
    LLVM_DEBUG(llvm::dbgs() << "      Missing operand expression\n");
    return true;
  }

  auto binExpr = std::make_unique<BinaryExpr>(
      op, cloneExpr(lhs), cloneExpr(rhs));

  // Generate overflow verification condition for signed overflow-checked ops
  if (isOverflowOp && opName) {
    // Assign a checkId for this operation to relate builtin and cond_fail VCs
    unsigned checkId = nextCheckId++;
    // The expression we want to check is the result of the operation
    addOverflowVC(binExpr.get(), opName, AutoVC::Source::Builtin, checkId);
    // Store checkId on the instruction result so cond_fail can find it
    setCheckId(inst, checkId);
  }

  // Generate division-by-zero verification condition for div/mod operations
  if ((op == ConditionExpr::Kind::Div || op == ConditionExpr::Kind::Mod) && opName) {
    // Assign a checkId for this operation
    unsigned checkId = nextCheckId++;
    // The divisor is the right-hand side operand
    addDivByZeroVC(rhs, opName, AutoVC::Source::Builtin, checkId);
    setCheckId(inst, checkId);
  }

  setExpr(inst, std::move(binExpr));
  return true;
}

bool SilTranslator::processStructExtract(StructExtractInst *inst) {
  // struct_extract is used to get the underlying value from Int wrapper
  // Pass through the expression from the operand
  SILValue operand = inst->getOperand();
  const ConditionExpr *opExpr = getExpr(operand);

  if (opExpr) {
    setExpr(inst, cloneExpr(opExpr));
    LLVM_DEBUG(llvm::dbgs() << "    StructExtract: pass-through\n");
  } else {
    LLVM_DEBUG(llvm::dbgs() << "    StructExtract: no source expr\n");
  }
  return true;
}

bool SilTranslator::processStruct(StructInst *inst) {
  // struct is used to wrap a value back into Int
  // Pass through the expression from the first operand
  if (inst->getNumOperands() >= 1) {
    const ConditionExpr *opExpr = getExpr(inst->getOperand(0));
    if (opExpr) {
      setExpr(inst, cloneExpr(opExpr));
      LLVM_DEBUG(llvm::dbgs() << "    Struct: pass-through\n");
    }
  }
  return true;
}

bool SilTranslator::processTupleExtract(TupleExtractInst *inst) {
  // tuple_extract extracts an element from a tuple
  // For overflow ops, element 0 is the result, element 1 is the overflow flag
  unsigned fieldNo = inst->getFieldIndex();

  if (fieldNo == 0) {
    // Result value - pass through from the tuple
    const ConditionExpr *tupleExpr = getExpr(inst->getOperand());
    if (tupleExpr) {
      setExpr(inst, cloneExpr(tupleExpr));
      LLVM_DEBUG(llvm::dbgs() << "    TupleExtract.0: pass-through\n");
    }
  } else {
    // Overflow flag or other field - we don't track these
    LLVM_DEBUG(llvm::dbgs() << "    TupleExtract." << fieldNo << ": ignored\n");
  }
  return true;
}

bool SilTranslator::processUncheckedEnumData(UncheckedEnumDataInst *inst) {
  // unchecked_enum_data extracts the payload from an enum case without checking.
  // For Optional<T>, this corresponds to a force unwrap of the payload.
  SILValue operand = inst->getOperand();
  const ConditionExpr *operandExpr = getExpr(operand);

  if (!operandExpr) {
    LLVM_DEBUG(llvm::dbgs() << "    UncheckedEnumData: missing operand expr\n");
    return true;
  }

  // Only treat this as a nil check if the operand is Optional<...>.
  if (operand->getType().getASTType().getOptionalObjectType()) {
    addNilCheckVC(operandExpr, "unchecked_enum_data");
  }

  // In our simplified model, treat the extracted payload as the same symbolic
  // value as the Optional itself (nil modeled as 0, non-nil as non-zero).
  setExpr(inst, cloneExpr(operandExpr));
  LLVM_DEBUG(llvm::dbgs() << "    UncheckedEnumData: payload pass-through\n");
  return true;
}

bool SilTranslator::processUnconditionalCheckedCast(UnconditionalCheckedCastInst *inst) {
  // unconditional_checked_cast traps if the cast fails.
  // If the source is Optional<...> and target is non-Optional, treat this as a
  // force unwrap requiring a nil check.
  const ConditionExpr *operandExpr = getExpr(inst->getOperand());

  if (!operandExpr) {
    LLVM_DEBUG(llvm::dbgs() << "    UnconditionalCheckedCast: missing operand expr\n");
    return true;
  }

  auto srcOpt = inst->getSourceFormalType().getOptionalObjectType();
  auto dstOpt = inst->getTargetFormalType().getOptionalObjectType();
  if (srcOpt && !dstOpt) {
    addNilCheckVC(operandExpr, "unconditional_checked_cast");
  }

  // Model casts as pass-through in the current untyped ConditionExpr world.
  setExpr(inst, cloneExpr(operandExpr));
  LLVM_DEBUG(llvm::dbgs() << "    UnconditionalCheckedCast: pass-through\n");
  return true;
}

bool SilTranslator::processReturn(ReturnInst *inst) {
  SILValue returnVal = inst->getOperand();
  const ConditionExpr *retExpr = getExpr(returnVal);

  if (retExpr) {
    returnExpr = cloneExpr(retExpr);
    LLVM_DEBUG({
      llvm::dbgs() << "    Return: ";
      returnExpr->dump(llvm::dbgs(), 0);
    });
  } else {
    LLVM_DEBUG(llvm::dbgs() << "    Return: no expression found\n");
  }
  return true;
}

bool SilTranslator::processDebugValue(DebugValueInst *inst) {
  // debug_value can give us parameter names
  // Format: debug_value %0, let, name "x", argno 1
  // Already handled in processArgument via getDecl()
  return true;
}

bool SilTranslator::processCondFail(CondFailInst *inst) {
  // cond_fail %condition : $Builtin.Int1, "message"
  // When condition is TRUE, program traps with message.
  // For verification: prove condition is ALWAYS FALSE.

  // Extract source location for this instruction
  extractSourceLocation(*inst);

  StringRef message = inst->getMessage();
  LLVM_DEBUG(llvm::dbgs() << "    CondFail: \"" << message << "\"\n");

  // Categorize the check type based on message content
  std::string lowerMsg = message.lower();
  StringRef msgLower(lowerMsg);
  AutoVC::Kind kind;
  if (msgLower.contains("overflow")) {
    kind = AutoVC::Kind::Overflow;
  } else if (msgLower.contains("bounds") || msgLower.contains("out of range")) {
    kind = AutoVC::Kind::BoundsCheck;
  } else if (msgLower.contains("nil") || msgLower.contains("unwrap")) {
    kind = AutoVC::Kind::NilCheck;
  } else if (msgLower.contains("division") || msgLower.contains("divide")) {
    kind = AutoVC::Kind::DivByZero;
  } else {
    // Unknown check type - still verify but categorize as overflow (generic safety)
    LLVM_DEBUG(llvm::dbgs() << "      Unknown cond_fail type, treating as generic check\n");
    kind = AutoVC::Kind::Overflow;
  }

  // Get the failure condition operand
  SILValue condValue = inst->getOperand();
  const ConditionExpr *condExpr = getExpr(condValue);

  // Try to find a related checkId from the operand chain
  // The cond_fail operand is usually a tuple_extract from a builtin result
  unsigned relatedCheckId = 0;

  // Walk back through the operand chain to find the source builtin
  SILValue current = condValue;
  for (int depth = 0; depth < 3 && relatedCheckId == 0; ++depth) {
    relatedCheckId = getCheckId(current);
    if (relatedCheckId != 0) break;

    // Try to walk back through tuple_extract
    if (auto *tupleExtract = dyn_cast<TupleExtractInst>(current->getDefiningInstruction())) {
      current = tupleExtract->getOperand();
    } else {
      break;
    }
  }

  if (condExpr) {
    // Create VC: NOT(failure_condition)
    // i.e., the condition that causes failure should always be FALSE.
    // For boolean-producing builtins (cmp_*, and/or/xor/not), model as (not <cond>).
    // For untyped/int-like conditions, fall back to (<cond> == 0).
    auto condCopy = cloneExpr(condExpr);
    std::unique_ptr<ConditionExpr> vcCondition;

    auto exprKind = condExpr->getKind();
    bool isBoolExpr =
        exprKind == ConditionExpr::Kind::BoolLiteral ||
        exprKind == ConditionExpr::Kind::Eq || exprKind == ConditionExpr::Kind::Ne ||
        exprKind == ConditionExpr::Kind::Lt || exprKind == ConditionExpr::Kind::Le ||
        exprKind == ConditionExpr::Kind::Gt || exprKind == ConditionExpr::Kind::Ge ||
        exprKind == ConditionExpr::Kind::And || exprKind == ConditionExpr::Kind::Or ||
        exprKind == ConditionExpr::Kind::Not;

    if (isBoolExpr) {
      vcCondition = std::make_unique<UnaryExpr>(ConditionExpr::Kind::Not, std::move(condCopy));
    } else {
      auto zeroLit = std::make_unique<IntLiteralExpr>(0);
      vcCondition = std::make_unique<BinaryExpr>(
          ConditionExpr::Kind::Eq, std::move(condCopy), std::move(zeroLit));
    }

    std::string desc = "cond_fail: " + message.str();
    LLVM_DEBUG(llvm::dbgs() << "      Added cond_fail VC: " << desc << "\n");

    AutoVC vc(kind, std::move(vcCondition), desc, AutoVC::Source::CondFail);
    vc.sourceFile = currentSourceFile;
    vc.sourceLine = currentSourceLine;
    vc.sourceColumn = currentSourceColumn;
    vc.checkId = relatedCheckId;
    autoVCs.push_back(std::move(vc));
  } else {
    // No expression for condition - try to create a symbolic one
    // This happens when the condition comes from an operation we don't track
    LLVM_DEBUG(llvm::dbgs() << "      No expression for cond_fail operand\n");

    // Create a symbolic representation using a fresh variable
    // For now, we just note this as an unconstrained check
    auto symbolicCond = std::make_unique<ParamRefExpr>("__cond_fail_" +
        std::to_string(instructionsProcessed), -1);
    auto falseLit = std::make_unique<IntLiteralExpr>(0);
    auto vcCondition = std::make_unique<BinaryExpr>(
        ConditionExpr::Kind::Eq, std::move(symbolicCond), std::move(falseLit));

    std::string desc = "cond_fail (unconstrained): " + message.str();
    AutoVC vc(kind, std::move(vcCondition), desc, AutoVC::Source::CondFail);
    vc.sourceFile = currentSourceFile;
    vc.sourceLine = currentSourceLine;
    vc.sourceColumn = currentSourceColumn;
    vc.checkId = relatedCheckId;
    autoVCs.push_back(std::move(vc));
  }

  return true;
}

//===----------------------------------------------------------------------===//
// Overflow Verification Condition Generation
//===----------------------------------------------------------------------===//

void SilTranslator::addOverflowVC(const ConditionExpr *resultExpr,
                                   llvm::StringRef opName,
                                   AutoVC::Source source,
                                   unsigned checkId) {
  if (!resultExpr) return;

  // Generate: INT64_MIN <= resultExpr && resultExpr <= INT64_MAX
  // This is the condition that must hold to avoid overflow

  // Clone the expression for use in two places
  auto exprCopy1 = cloneExpr(resultExpr);
  auto exprCopy2 = cloneExpr(resultExpr);

  // INT64_MIN <= resultExpr
  auto minLit = std::make_unique<IntLiteralExpr>(INT64_MIN_VAL);
  auto lowerBound = std::make_unique<BinaryExpr>(
      ConditionExpr::Kind::Le, std::move(minLit), std::move(exprCopy1));

  // resultExpr <= INT64_MAX
  auto maxLit = std::make_unique<IntLiteralExpr>(INT64_MAX_VAL);
  auto upperBound = std::make_unique<BinaryExpr>(
      ConditionExpr::Kind::Le, std::move(exprCopy2), std::move(maxLit));

  // Combine: lowerBound && upperBound
  auto condition = std::make_unique<BinaryExpr>(
      ConditionExpr::Kind::And, std::move(lowerBound), std::move(upperBound));

  // Create description
  std::string desc = "overflow check for " + opName.str() + " operation";

  LLVM_DEBUG(llvm::dbgs() << "    Added overflow VC: " << desc << "\n");

  AutoVC vc(AutoVC::Kind::Overflow, std::move(condition), desc, source);
  vc.sourceFile = currentSourceFile;
  vc.sourceLine = currentSourceLine;
  vc.sourceColumn = currentSourceColumn;
  vc.checkId = checkId;
  autoVCs.push_back(std::move(vc));
}

//===----------------------------------------------------------------------===//
// Division-by-Zero Verification Condition Generation
//===----------------------------------------------------------------------===//

void SilTranslator::addDivByZeroVC(const ConditionExpr *divisorExpr,
                                    llvm::StringRef opName,
                                    AutoVC::Source source,
                                    unsigned checkId) {
  if (!divisorExpr) return;

  // Generate: divisor != 0
  // This is the condition that must hold to avoid division by zero

  auto divisorCopy = cloneExpr(divisorExpr);
  auto zeroLit = std::make_unique<IntLiteralExpr>(0);

  // divisor != 0 (using Ne for "not equal")
  auto condition = std::make_unique<BinaryExpr>(
      ConditionExpr::Kind::Ne, std::move(divisorCopy), std::move(zeroLit));

  // Create description
  std::string desc = "division by zero check for " + opName.str() + " operation";

  LLVM_DEBUG(llvm::dbgs() << "    Added div-by-zero VC: " << desc << "\n");

  AutoVC vc(AutoVC::Kind::DivByZero, std::move(condition), desc, source);
  vc.sourceFile = currentSourceFile;
  vc.sourceLine = currentSourceLine;
  vc.sourceColumn = currentSourceColumn;
  vc.checkId = checkId;
  autoVCs.push_back(std::move(vc));
}

//===----------------------------------------------------------------------===//
// Bounds Checking Verification Condition Generation
//===----------------------------------------------------------------------===//

void SilTranslator::addBoundsVC(const ConditionExpr *indexExpr,
                                 const ConditionExpr *lengthExpr,
                                 llvm::StringRef opName,
                                 AutoVC::Source source,
                                 unsigned checkId) {
  if (!indexExpr || !lengthExpr) return;

  // Generate: index >= 0 && index < length
  // This is the condition that must hold to avoid out-of-bounds access

  // Clone expressions for use in two places
  auto indexCopy1 = cloneExpr(indexExpr);
  auto indexCopy2 = cloneExpr(indexExpr);
  auto lengthCopy = cloneExpr(lengthExpr);

  // index >= 0
  auto zeroLit = std::make_unique<IntLiteralExpr>(0);
  auto lowerBound = std::make_unique<BinaryExpr>(
      ConditionExpr::Kind::Ge, std::move(indexCopy1), std::move(zeroLit));

  // index < length
  auto upperBound = std::make_unique<BinaryExpr>(
      ConditionExpr::Kind::Lt, std::move(indexCopy2), std::move(lengthCopy));

  // Combine: lowerBound && upperBound
  auto condition = std::make_unique<BinaryExpr>(
      ConditionExpr::Kind::And, std::move(lowerBound), std::move(upperBound));

  // Create description
  std::string desc = "bounds check for " + opName.str() + " operation";

  LLVM_DEBUG(llvm::dbgs() << "    Added bounds VC: " << desc << "\n");

  AutoVC vc(AutoVC::Kind::BoundsCheck, std::move(condition), desc, source);
  vc.sourceFile = currentSourceFile;
  vc.sourceLine = currentSourceLine;
  vc.sourceColumn = currentSourceColumn;
  vc.checkId = checkId;
  autoVCs.push_back(std::move(vc));
}

//===----------------------------------------------------------------------===//
// Nil Check Verification Condition Generation
//===----------------------------------------------------------------------===//

void SilTranslator::addNilCheckVC(const ConditionExpr *optionalExpr,
                                   llvm::StringRef opName,
                                   AutoVC::Source source,
                                   unsigned checkId) {
  if (!optionalExpr) return;

  // Generate: optional != nil
  // In our model, we represent optionals as integers where:
  // - 0 represents nil
  // - non-zero represents a valid value (Some)
  // This is a simplification; real optionals have more complex semantics.

  auto optionalCopy = cloneExpr(optionalExpr);
  auto nilLit = std::make_unique<IntLiteralExpr>(0);

  // optional != 0 (i.e., optional is not nil)
  auto condition = std::make_unique<BinaryExpr>(
      ConditionExpr::Kind::Ne, std::move(optionalCopy), std::move(nilLit));

  // Create description
  std::string desc = "nil check for " + opName.str() + " operation";

  LLVM_DEBUG(llvm::dbgs() << "    Added nil VC: " << desc << "\n");

  AutoVC vc(AutoVC::Kind::NilCheck, std::move(condition), desc, source);
  vc.sourceFile = currentSourceFile;
  vc.sourceLine = currentSourceLine;
  vc.sourceColumn = currentSourceColumn;
  vc.checkId = checkId;
  autoVCs.push_back(std::move(vc));
}

bool SilTranslator::processInstruction(SILInstruction &I) {
  ++instructionsProcessed;

  // Extract source location for this instruction
  extractSourceLocation(I);

  // Handle each instruction type
  if (auto *intLit = dyn_cast<IntegerLiteralInst>(&I)) {
    return processIntegerLiteral(intLit);
  }
  if (auto *builtin = dyn_cast<BuiltinInst>(&I)) {
    return processBuiltin(builtin);
  }
  if (auto *structExtract = dyn_cast<StructExtractInst>(&I)) {
    return processStructExtract(structExtract);
  }
  if (auto *structInst = dyn_cast<StructInst>(&I)) {
    return processStruct(structInst);
  }
  if (auto *tupleExtract = dyn_cast<TupleExtractInst>(&I)) {
    return processTupleExtract(tupleExtract);
  }
  if (auto *uncheckedEnumData = dyn_cast<UncheckedEnumDataInst>(&I)) {
    return processUncheckedEnumData(uncheckedEnumData);
  }
  if (auto *checkedCast = dyn_cast<UnconditionalCheckedCastInst>(&I)) {
    return processUnconditionalCheckedCast(checkedCast);
  }
  if (auto *ret = dyn_cast<ReturnInst>(&I)) {
    return processReturn(ret);
  }
  if (auto *debugVal = dyn_cast<DebugValueInst>(&I)) {
    return processDebugValue(debugVal);
  }
  if (auto *condFail = dyn_cast<CondFailInst>(&I)) {
    return processCondFail(condFail);
  }

  // Unknown instruction - log but continue
  LLVM_DEBUG(llvm::dbgs() << "    Unknown: " << getSILInstructionName(I.getKind()) << "\n");
  ++unsupportedInstructions;
  return true;
}

bool SilTranslator::processBlock(SILBasicBlock &BB) {
  LLVM_DEBUG(llvm::dbgs() << "  Processing block\n");

  for (auto &I : BB) {
    if (!processInstruction(I)) {
      return false;
    }
  }
  return true;
}

//===----------------------------------------------------------------------===//
// Main Translation Entry Point
//===----------------------------------------------------------------------===//

TranslationResult SilTranslator::translate(SILFunction &F) {
  LLVM_DEBUG(llvm::dbgs() << "=== SIL Translation: " << F.getName() << " ===\n");

  // Only handle single basic block functions for now
  if (F.empty()) {
    return TranslationResult::fail("Empty function");
  }

  // For now, only handle functions with one basic block (straight-line code)
  if (std::distance(F.begin(), F.end()) > 1) {
    LLVM_DEBUG(llvm::dbgs() << "  Multiple blocks - not yet supported\n");
    return TranslationResult::fail("Multi-block functions not yet supported");
  }

  SilTranslator translator;

  // Process function arguments first
  SILBasicBlock &entryBlock = F.front();
  for (auto *arg : entryBlock.getArguments()) {
    if (auto *funcArg = dyn_cast<SILFunctionArgument>(arg)) {
      translator.processArgument(funcArg);
    }
  }

  // Process the block
  if (!translator.processBlock(entryBlock)) {
    return TranslationResult::fail("Block processing failed");
  }

  // Check if we found a return expression
  if (!translator.returnExpr) {
    LLVM_DEBUG(llvm::dbgs() << "  No return expression found\n");
    return TranslationResult::fail("No return expression");
  }

  // Build the function semantics: result = <return_expr>
  auto resultRef = std::make_unique<ResultRefExpr>();
  auto semantics = std::make_unique<BinaryExpr>(
      ConditionExpr::Kind::Eq,
      std::move(resultRef),
      std::move(translator.returnExpr));

  LLVM_DEBUG({
    llvm::dbgs() << "  Function semantics:\n";
    semantics->dump(llvm::dbgs(), 4);
  });

  auto result = TranslationResult::ok(
      std::move(semantics),
      std::move(translator.paramNames));
  result.paramTypes = std::move(translator.paramTypes);
  result.instructionsProcessed = translator.instructionsProcessed;
  result.unsupportedInstructions = translator.unsupportedInstructions;
  result.autoVCs = std::move(translator.autoVCs);

  // De-duplicate auto-VCs (prefer builtin-derived over cond_fail-derived)
  result.deduplicateAutoVCs();

  LLVM_DEBUG({
    if (!result.autoVCs.empty()) {
      llvm::dbgs() << "  Auto-VCs discovered: " << result.autoVCs.size() << "\n";
      if (result.vcsDeduplicated > 0) {
        llvm::dbgs() << "  Auto-VCs deduplicated: " << result.vcsDeduplicated << "\n";
      }
      for (const auto &vc : result.autoVCs) {
        llvm::dbgs() << "    - " << vc.description;
        if (!vc.sourceFile.empty()) {
          llvm::dbgs() << " (" << vc.sourceFile << ":" << vc.sourceLine << ")";
        }
        llvm::dbgs() << "\n";
      }
    }
  });

  return result;
}

//===----------------------------------------------------------------------===//
// Auto-VC Collection (Multi-Block Capable)
//===----------------------------------------------------------------------===//

TranslationResult SilTranslator::collectAutoVCs(SILFunction &F) {
  LLVM_DEBUG(llvm::dbgs() << "=== Auto-VC Collection: " << F.getName() << " ===\n");

  if (F.empty()) {
    return TranslationResult::fail("Empty function");
  }

  SilTranslator translator;

  // Process arguments from entry block to establish parameter mappings
  SILBasicBlock &entryBlock = F.front();
  for (auto *arg : entryBlock.getArguments()) {
    if (auto *funcArg = dyn_cast<SILFunctionArgument>(arg)) {
      translator.processArgument(funcArg);
    }
  }

  // Walk ALL basic blocks to collect auto-VCs
  // Unlike translate(), we don't fail on multi-block - we just collect what we can
  for (auto &BB : F) {
    LLVM_DEBUG(llvm::dbgs() << "  Scanning block for auto-VCs\n");
    translator.processBlock(BB);
  }

  LLVM_DEBUG({
    llvm::dbgs() << "  Auto-VC collection complete\n";
    llvm::dbgs() << "  Instructions processed: " << translator.instructionsProcessed << "\n";
    if (!translator.autoVCs.empty()) {
      llvm::dbgs() << "  Auto-VCs discovered: " << translator.autoVCs.size() << "\n";
      for (const auto &vc : translator.autoVCs) {
        llvm::dbgs() << "    - " << vc.description << "\n";
      }
    }
  });

  // Return result with auto-VCs but mark semantics translation as failed
  // (we didn't try to build full function semantics)
  auto result = TranslationResult::fail("Auto-VC collection only");
  result.paramNames = std::move(translator.paramNames);
  result.paramTypes = std::move(translator.paramTypes);
  result.autoVCs = std::move(translator.autoVCs);
  result.instructionsProcessed = translator.instructionsProcessed;
  result.unsupportedInstructions = translator.unsupportedInstructions;

  // De-duplicate auto-VCs (prefer builtin-derived over cond_fail-derived)
  result.deduplicateAutoVCs();

  LLVM_DEBUG({
    if (result.vcsDeduplicated > 0) {
      llvm::dbgs() << "  Auto-VCs deduplicated: " << result.vcsDeduplicated << "\n";
    }
  });

  return result;
}
