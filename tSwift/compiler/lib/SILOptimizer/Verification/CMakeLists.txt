# CMakeLists.txt for tSwift verification pass
#
# This builds the SIL verification pass that extracts @requires/@ensures specs
# and generates verification conditions for proving with Z4/Kani/Lean.
#
# Integration Instructions:
# ========================
# To integrate this into the Swift compiler build:
#
# 1. Copy this directory to ~/swift-project/swift/lib/SILOptimizer/Verification/
#
# 2. Add to ~/swift-project/swift/lib/SILOptimizer/CMakeLists.txt:
#    add_subdirectory(Verification)
#
# 3. Add the pass to Passes.def:
#    LEGACY_PASS(SILVerification, "sil-verification",
#                "Verification condition generation for formal verification")
#
# 4. Rebuild Swift:
#    cd ~/swift-project
#    ./utils/build-script --release-debuginfo

# The verification pass sources
set(VERIFICATION_SOURCES
  ConditionParser.cpp
  JsonExport.cpp
  SilTranslator.cpp
  SpecExtraction.cpp
  SILVerificationPass.cpp
  SolverInterface.cpp
  VcIrGen.cpp
)

# Create a static library
# In actual Swift build, this would be part of swiftSILOptimizer
# For standalone development, we create a separate library
if(BUILD_STANDALONE)
  add_library(swiftSILVerification STATIC ${VERIFICATION_SOURCES})

  target_include_directories(swiftSILVerification PUBLIC
    ${CMAKE_SOURCE_DIR}/include
    ${SWIFT_SOURCE_DIR}/include
    ${LLVM_INCLUDE_DIRS}
  )

  target_link_libraries(swiftSILVerification
    swiftSIL
    swiftAST
    swiftBasic
  )
else()
  # When integrated into Swift build, just add sources to parent
  target_sources(swiftSILOptimizer PRIVATE ${VERIFICATION_SOURCES})
endif()
