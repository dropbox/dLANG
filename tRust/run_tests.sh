#!/bin/bash
#
# tRust Integration Test Runner
#
# Test Format: examples/*_test.rs
#   Single-file tests compiled with -Zverify
#
# Cross-Crate Test Format: examples/*_crate_case/
#   Multi-file tests for cross-crate contract verification.
#   Each directory must contain:
#     - dep.rs: Dependency crate with contracts
#     - main.rs: Main crate that uses the dependency via `extern crate dep;`
#
#   Test expectations:
#     - EXPECTED_ERROR_CRATE_TESTS: main.rs should produce verification errors
#     - EXPECTED_DISPROVEN_CRATE_TESTS: dep.rs should produce DISPROVEN (verified with -Zverify)
#     - Default: Both dep.rs and main.rs should compile and verify without errors
#
#   Example cross-crate test (cross_crate_postcond_crate_case/):
#     dep.rs:
#       #[ensures("result >= 0")]
#       pub fn id_nonneg(x: i32) -> i32 { x }
#
#     main.rs:
#       extern crate dep;
#       #[ensures("result >= 0")]
#       fn call_id(x: i32) -> i32 { dep::id_nonneg(x) }
#
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
UPSTREAM_SYSROOT="$SCRIPT_DIR/upstream/rustc/build/host/stage1"
DEFAULT_SYSROOT="$SCRIPT_DIR/build/host/stage1"
if [ -d "$UPSTREAM_SYSROOT" ]; then
    DEFAULT_SYSROOT="$UPSTREAM_SYSROOT"
fi
SYSROOT="${TRUST_SYSROOT:-$DEFAULT_SYSROOT}"
RUSTC="$SYSROOT/bin/rustc"

FILTER=""
while [[ $# -gt 0 ]]; do
    case "$1" in
        -f|--filter)
            FILTER="${2:-}"
            shift 2
            ;;
        -h|--help)
            echo "Usage: $0 [--filter <pattern>]"
            echo ""
            echo "Options:"
            echo "  -f, --filter X   Only run tests whose name contains X"
            echo "  -h, --help       Show this help message"
            exit 0
            ;;
        *)
            echo "Unknown option: $1" >&2
            echo "Use --help for usage information." >&2
            exit 1
            ;;
    esac
done

if [ ! -x "$RUSTC" ]; then
    echo "Error: rustc not found at $RUSTC" >&2
    if [ -n "${TRUST_SYSROOT:-}" ]; then
        echo "TRUST_SYSROOT is set to: $TRUST_SYSROOT" >&2
    fi
    echo "Build stage1 first: cd upstream/rustc && ./x.py build --stage 1" >&2
    exit 1
fi

# Integration tests require a tRust-patched rustc with -Zverify.
rustc_supports_zverify() {
    # Avoid matching unrelated flags like verify-llvm-ir.
    "$RUSTC" -Z help 2>/dev/null | grep -Eq '^[[:space:]]*-Z[[:space:]]+verify(=|[[:space:]])'
}

if ! rustc_supports_zverify; then
    echo "Error: this rustc does not support -Zverify; integration tests require a patched tRust rustc." >&2
    echo "  rustc: $RUSTC" >&2
    echo "See: docs/GETTING_STARTED.md" >&2
    exit 1
fi

count=0
passed=0
failed=0

# Tests that are expected to have verification errors (they test that verifier catches bugs)
# These tests contain "SHOULD FAIL" functions that intentionally trigger errors
# Tests that produce errors due to verification limitations (loops, recursion, incomplete modeling)
EXPECTED_ERROR_TESTS="overflow_test bounds_test const_prop_test constant_index_test path_sensitive_test requires_test anomaly_test bitand_mask_signed_unsound_test effect_violation_test unsafe_effect_detection_test std_builtin_preconditions_test std_rounding_preconditions_test tokio_channel_preconditions_test tokio_sync_primitives_test temporal_parse_fail_test shift_overflow_test loop_soundness_test cutpoint_precond_test async_chain_test async_state_machine_test binaryheap_extended_test linkedlist_extended_test vec_sorting_test vec_extended_mutation_test decreases_test recursive_test mutual_recursion_test phase4_integration_test modular_nested_test temporal_test conditional_postcond_propagation_test tactic_test refinement_integration_test refinement_type_inference_test refinement_type_syntax_test refinement_type_vc_test trait_contract_test trait_spec_test implication_test nested_mod_test result_contracts_test combinator_methods_test constructor_tracking_test conversion_methods_test extended_option_result_test real_validation_base64_test real_validation_hex_test real_validation_subtle_test checked_shl_bounds_test checked_shr_bounds_test std_sign_contracts_test"

# Tests that are expected to DISPROVE a contract (they test that contract checking catches bugs)
EXPECTED_DISPROVEN_TESTS="ensures_test old_fail_test verify_test modular_postcond_test trait_spec_fail_test std_checked_contracts_test unwrap_or_test idx_method_test mutation_testing_test"

# Tests that are expected to produce ASSUMED (trust_level=assumed skips verification)
EXPECTED_ASSUMED_TESTS="assumed_trust_test"

# Tests to skip (empty - all tests should run)
SKIP_TESTS=""

# Cross-crate tests (directories under examples/*_crate_case)
EXPECTED_ERROR_CRATE_TESTS="cross_crate_precond_fail_crate_case cross_crate_postcond_fail_crate_case"
EXPECTED_DISPROVEN_CRATE_TESTS="cross_crate_disproven_crate_case"

for f in "$SCRIPT_DIR"/examples/*_test.rs; do
    name=$(basename "$f" .rs)

    if [ -n "$FILTER" ] && [[ "$name" != *"$FILTER"* ]]; then
        continue
    fi

    # Skip tests that need stage1 rebuild
    skip=0
    for t in $SKIP_TESTS; do
        if [ "$name" = "$t" ]; then
            skip=1
            break
        fi
    done
    if [ "$skip" -eq 1 ]; then
        echo "$name: SKIPPED (needs stage1 rebuild)"
        continue
    fi

    count=$((count+1))
    output=$($RUSTC -Zverify "$f" -o /tmp/test_out 2>&1)
    has_error=$(echo "$output" | grep -c "error:")
    has_disproven=$(echo "$output" | grep -c "DISPROVEN")
    has_assumed=$(echo "$output" | grep -c "ASSUMED")

    # Check if this test expects errors
    expects_error=0
    for t in $EXPECTED_ERROR_TESTS; do
        if [ "$name" = "$t" ]; then
            expects_error=1
            break
        fi
    done

    expects_disproven=0
    for t in $EXPECTED_DISPROVEN_TESTS; do
        if [ "$name" = "$t" ]; then
            expects_disproven=1
            break
        fi
    done

    expects_assumed=0
    for t in $EXPECTED_ASSUMED_TESTS; do
        if [ "$name" = "$t" ]; then
            expects_assumed=1
            break
        fi
    done

    # Check that errors are only verification errors (not compilation)
    compilation_error=$(echo "$output" | grep -c "cannot find\\|error\\[E")

    if [ "$compilation_error" -gt 0 ]; then
        failed=$((failed+1))
        echo "$name: FAIL (compilation error)"
        echo "$output" | grep "error" | head -3
    elif [ "$expects_assumed" -eq 1 ]; then
        if [ "$has_assumed" -gt 0 ] && [ "$has_error" -eq 0 ]; then
            passed=$((passed+1))
            echo "$name: PASS (trust_level=assumed, verification skipped)"
        else
            failed=$((failed+1))
            echo "$name: FAIL (expected ASSUMED, got error or no ASSUMED)"
            echo "$output" | head -5
        fi
    elif [ "$expects_disproven" -eq 1 ]; then
        if [ "$has_disproven" -gt 0 ]; then
            passed=$((passed+1))
            echo "$name: PASS (expected DISPROVEN)"
        else
            failed=$((failed+1))
            echo "$name: FAIL (expected DISPROVEN)"
            echo "$output" | grep "error" | head -3
        fi
    elif [ "$expects_error" -eq 1 ]; then
        if [ "$has_error" -gt 0 ]; then
            passed=$((passed+1))
            echo "$name: PASS (expected errors detected)"
        else
            failed=$((failed+1))
            echo "$name: FAIL (expected verification errors, got none)"
        fi
    else
        if [ "$has_error" -gt 0 ]; then
            failed=$((failed+1))
            echo "$name: FAIL"
            echo "$output" | grep "error" | head -3
        else
            passed=$((passed+1))
            echo "$name: PASS"
        fi
    fi
done

# Cross-crate tests
for d in "$SCRIPT_DIR"/examples/*_crate_case; do
    if [ ! -d "$d" ]; then
        continue
    fi

    name=$(basename "$d")
    if [ -n "$FILTER" ] && [[ "$name" != *"$FILTER"* ]]; then
        continue
    fi
    dep_src="$d/dep.rs"
    main_src="$d/main.rs"

    if [ ! -f "$dep_src" ] || [ ! -f "$main_src" ]; then
        echo "$name: FAIL (missing dep.rs or main.rs)"
        failed=$((failed+1))
        continue
    fi

    count=$((count+1))
    tmpdir=$(mktemp -d "/tmp/trust_${name}_XXXXXX")
    dep_rlib="$tmpdir/libdep.rlib"

    # For DISPROVEN tests, verify dep.rs with -Zverify
    expects_disproven=0
    for t in $EXPECTED_DISPROVEN_CRATE_TESTS; do
        if [ "$name" = "$t" ]; then
            expects_disproven=1
            break
        fi
    done

    if [ "$expects_disproven" -eq 1 ]; then
        dep_out=$($RUSTC --edition=2021 -Zverify --crate-type=rlib --crate-name dep "$dep_src" -o "$dep_rlib" 2>&1)
    else
        dep_out=$($RUSTC --edition=2021 --crate-type=rlib --crate-name dep "$dep_src" -o "$dep_rlib" 2>&1)
    fi
    dep_has_error=$(echo "$dep_out" | grep -c "error:")
    dep_has_disproven=$(echo "$dep_out" | grep -c "DISPROVEN")

    # For DISPROVEN tests, check if dep verification produced DISPROVEN
    if [ "$expects_disproven" -eq 1 ]; then
        if [ "$dep_has_disproven" -gt 0 ]; then
            passed=$((passed+1))
            echo "$name: PASS (expected DISPROVEN in dependency)"
            rm -rf "$tmpdir"
            continue
        else
            failed=$((failed+1))
            echo "$name: FAIL (expected DISPROVEN in dependency)"
            echo "$dep_out" | head -5
            rm -rf "$tmpdir"
            continue
        fi
    fi

    if [ "$dep_has_error" -gt 0 ]; then
        failed=$((failed+1))
        echo "$name: FAIL (dependency compile error)"
        echo "$dep_out" | grep "error" | head -3
        rm -rf "$tmpdir"
        continue
    fi

    output=$($RUSTC --edition=2021 -Zverify "$main_src" --extern dep="$dep_rlib" -o "$tmpdir/main_out" 2>&1)
    has_error=$(echo "$output" | grep -c "error:")
    has_disproven=$(echo "$output" | grep -c "DISPROVEN")

    expects_error=0
    for t in $EXPECTED_ERROR_CRATE_TESTS; do
        if [ "$name" = "$t" ]; then
            expects_error=1
            break
        fi
    done

    expects_disproven=0
    for t in $EXPECTED_DISPROVEN_CRATE_TESTS; do
        if [ "$name" = "$t" ]; then
            expects_disproven=1
            break
        fi
    done

    compilation_error=$(echo "$output" | grep -c "cannot find\\|error\\[E")

    if [ "$compilation_error" -gt 0 ]; then
        failed=$((failed+1))
        echo "$name: FAIL (compilation error)"
        echo "$output" | grep "error" | head -3
    elif [ "$expects_disproven" -eq 1 ]; then
        if [ "$has_disproven" -gt 0 ]; then
            passed=$((passed+1))
            echo "$name: PASS (expected DISPROVEN)"
        else
            failed=$((failed+1))
            echo "$name: FAIL (expected DISPROVEN)"
            echo "$output" | head -5
        fi
    elif [ "$expects_error" -eq 1 ]; then
        if [ "$has_error" -gt 0 ]; then
            passed=$((passed+1))
            echo "$name: PASS (expected errors detected)"
        else
            failed=$((failed+1))
            echo "$name: FAIL (expected verification errors, got none)"
        fi
    else
        if [ "$has_error" -gt 0 ]; then
            failed=$((failed+1))
            echo "$name: FAIL"
            echo "$output" | grep "error" | head -3
        else
            passed=$((passed+1))
            echo "$name: PASS"
        fi
    fi

    rm -rf "$tmpdir"
done

# Upstream contracts MIR regression test (ContractsVerify elision).
CONTRACTS_ELIDE_TEST_SRC="$SCRIPT_DIR/examples/upstream_contracts/elide_mir_test.rs"
if [ -f "$CONTRACTS_ELIDE_TEST_SRC" ]; then
    name="contracts_elide_mir_test"
    if [ -z "$FILTER" ] || [[ "$name" == *"$FILTER"* ]]; then
        count=$((count+1))

        tmpdir=$(mktemp -d)

        # 1) Dump after ContractsVerify: should still contain the intrinsic call.
        output_verify=$(TRUST_CONTRACTS_VERIFY=1 "$RUSTC" \
            -Zcontract-checks \
            -Zdump-mir=ContractsVerify \
            -Zdump-mir-dir="$tmpdir/mir_verify" \
            --edition=2021 \
            -o "$tmpdir/a.out" \
            "$CONTRACTS_ELIDE_TEST_SRC" 2>&1)
        status_verify=$?

        if [ $status_verify -ne 0 ] || [ ! -d "$tmpdir/mir_verify" ]; then
            failed=$((failed+1))
            echo "$name: FAIL (could not dump MIR after ContractsVerify)"
            echo "$output_verify" | head -20
            rm -rf "$tmpdir"
        else
            # 2) Dump after ContractsElide: should NOT contain the intrinsic call in *.after.mir.
            output_elide=$(TRUST_CONTRACTS_VERIFY=1 "$RUSTC" \
                -Zcontract-checks \
                -Zdump-mir=ContractsElide \
                -Zdump-mir-dir="$tmpdir/mir_elide" \
                --edition=2021 \
                -o "$tmpdir/a.out" \
                "$CONTRACTS_ELIDE_TEST_SRC" 2>&1)
            status_elide=$?

            if [ $status_elide -ne 0 ] || [ ! -d "$tmpdir/mir_elide" ]; then
                failed=$((failed+1))
                echo "$name: FAIL (could not dump MIR after ContractsElide)"
                echo "$output_elide" | head -20
                rm -rf "$tmpdir"
            else
                verify_has_call=$(grep -R "contract_check_requires" "$tmpdir/mir_verify" | grep -c ".after.mir" || true)
                elide_has_call=$(grep -R "contract_check_requires" "$tmpdir/mir_elide" | grep -c ".after.mir" || true)

                if [ "$verify_has_call" -eq 0 ]; then
                    failed=$((failed+1))
                    echo "$name: FAIL (expected contract_check_requires after ContractsVerify)"
                elif [ "$elide_has_call" -gt 0 ]; then
                    failed=$((failed+1))
                    echo "$name: FAIL (contract_check_requires still present after ContractsElide)"
                else
                    passed=$((passed+1))
                    echo "$name: PASS"
                fi

                rm -rf "$tmpdir"
            fi
        fi
    fi
fi

echo ""
echo "Results: $passed/$count passed, $failed failed"
