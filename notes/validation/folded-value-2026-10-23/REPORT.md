# Folded-value validation, 2026-10-23

Source revision: `ac6681fe013c4762158d1bc24e9ae206a19781e8`. Vyper source: `~/vyper`, clean commit `cd74ce4f57e3771aeeab8f061fa3be45bfe8a29c`.

Independent artifacts are in `lowering/defs/bytecode/folded-value-oracle/`; all 36 accepted sources have AST/layout and deploy/runtime bytes. `method_id_var` is rejected by the pinned compiler with StructureException: Value must be a literal. The corresponding synthetic HOL rejection is `check_contract_rejects_method_id_eval`.

Toolchain: uv 0.10.11, managed CPython 3.11.11, Vyper 0.5.0a4+cd74ce4f. Settings: experimental codegen, optimize NONE (the pinned O1 Venom pipeline), Prague, no metadata. Dependency versions and source/byte hashes are in the independent provenance file.

The frozen Python corpus reproduced all 101 fixtures, plus memory-store and external-call subcorpora. Four actual py-evm 0.12.1b1 PragueVM executions reverted; calldata, bytecode hashes and gas use are in `executions.json`.

Counts: {"MATCH": 30, "EXPECTED_PYTHON_REJECTION": 1, "BYTECODE_MISMATCH": 4, "COMPILE_NONE": 2}.

Full HOL corpus: {"expected_targets": 33, "attempted": 33, "passed": 28, "status": "COMPLETE"}. Seven-fixture theory exit: 0. See corpus target outcomes below for failures.

| Witness | Runtime/deploy checker | Supported | Compile | Deploy/runtime equal | Verdict | Dependency |
|---|---|---|---|---|---|---|
| pow_folded_exp | ACCEPT/ACCEPT | T | SOME | True/True | MATCH |  |
| pow_negfold_base | ACCEPT/ACCEPT | T | SOME | True/True | MATCH |  |
| fold_add | ACCEPT/ACCEPT | T | SOME | True/True | MATCH |  |
| fold_pow_lit | ACCEPT/ACCEPT | T | SOME | True/True | MATCH |  |
| fold_cmp | ACCEPT/ACCEPT | T | SOME | True/True | MATCH |  |
| fold_not | ACCEPT/ACCEPT | T | SOME | True/True | MATCH |  |
| fold_shift | ACCEPT/ACCEPT | T | SOME | True/True | MATCH |  |
| fold_minmax | ACCEPT/ACCEPT | T | SOME | True/True | MATCH |  |
| fold_powmod | ACCEPT/ACCEPT | T | SOME | True/True | MATCH |  |
| fold_addmod | ACCEPT/ACCEPT | T | SOME | True/True | MATCH |  |
| fold_abs | ACCEPT/ACCEPT | T | SOME | True/True | MATCH |  |
| keccak_literal | ACCEPT/ACCEPT | T | SOME | True/True | MATCH | #569 bytestring hashing |
| len_string_lit | ACCEPT/ACCEPT | T | SOME | True/True | MATCH | #569 bytestring hashing |
| method_id_b4 | ACCEPT/ACCEPT | T | SOME | True/True | MATCH |  |
| method_id_bytes | ACCEPT/ACCEPT | T | SOME | True/True | MATCH |  |
| method_id_const | ACCEPT/ACCEPT | F | SOME | True/True | MATCH |  |
| method_id_storage | ACCEPT/ACCEPT | F | SOME | True/True | MATCH |  |
| method_id_var | NOT_APPLICABLE_PYTHON_REJECTED/NOT_APPLICABLE_PYTHON_REJECTED | NOT_APPLICABLE_PYTHON_REJECTED | NOT_APPLICABLE_PYTHON_REJECTED | None/None | EXPECTED_PYTHON_REJECTION |  |
| enc_mid_const | ACCEPT/ACCEPT | F | SOME | True/True | MATCH |  |
| enc_mid_methodid_call | ACCEPT/ACCEPT | F | SOME | True/True | MATCH |  |
| enc_mid_bytes4lit | ACCEPT/ACCEPT | T | SOME | True/True | MATCH |  |
| enc_ensF_string_mid | ACCEPT/ACCEPT | F | SOME | True/True | MATCH |  |
| enc_ensF_uint_mid | ACCEPT/ACCEPT | F | SOME | True/True | MATCH |  |
| enc_ensure_const | ACCEPT/ACCEPT | F | SOME | True/True | MATCH |  |
| dec_unwrap_const | ACCEPT/ACCEPT | F | SOME | True/True | MATCH |  |
| ctl03_abi_method_id | ACCEPT/ACCEPT | F | SOME | False/False | BYTECODE_MISMATCH | #551 ABI encode |
| enc_ensT_uint_mid | ACCEPT/ACCEPT | F | SOME | False/False | BYTECODE_MISMATCH | #551 ABI encode |
| neg_lit | ACCEPT/ACCEPT | T | SOME | True/True | MATCH |  |
| pow_neglit_base | ACCEPT/ACCEPT | T | SOME | True/True | MATCH |  |
| lt_mixed_lit | ACCEPT/ACCEPT | T | SOME | True/True | MATCH |  |
| boolop_and3 | ACCEPT/ACCEPT | T | SOME | True/True | MATCH |  |
| i12_immut_with_storage | ACCEPT/ACCEPT | F | NONE | None/None | COMPILE_NONE | #563 immutables |
| p29_imm_multi | ACCEPT/ACCEPT | F | NONE | None/None | COMPILE_NONE | #563 immutables |
| c16_const_string_in_expr | ACCEPT/ACCEPT | F | SOME | True/True | MATCH | #565 constants |
| c27_const_binop_fold | ACCEPT/ACCEPT | F | SOME | True/True | MATCH | #565 constants |
| rc09_abi_encode_data | ACCEPT/ACCEPT | F | SOME | False/False | BYTECODE_MISMATCH | #554/#551 ABI encoding |
| rr03_abi | ACCEPT/ACCEPT | F | SOME | False/False | BYTECODE_MISMATCH | #567/#551 ABI encoding |

## Existing HOL corpus target outcomes

| Target | Outcome |
|---|---|
| evalCompilerBytecodeTheory | PASS |
| evalCompilerBytecodeControlTheory | PASS |
| evalCompilerBytecodeStateTheory | PASS |
| evalCompilerBytecodeAbiExternalStaticTheory | PASS |
| evalCompilerBytecodeAbiExternalArraysTheory | PASS |
| evalCompilerBytecodeAbiExternalDynamicTheory | PASS |
| evalCompilerBytecodeAbiEventsTheory | PASS |
| evalCompilerBytecodeAbiInternalCallsTheory | DEPENDENCY_EVALUATION_TIMEOUT |
| evalCompilerBytecodeAbiExternalCallsTheory | PASS |
| evalCompilerBytecodeAbiStaticTheory | PASS |
| evalCompilerBytecodeAbiDynamicTheory | PROCESS_KILLED |
| evalCompilerBytecodeFunctionModesTheory | PASS |
| evalCompilerBytecodeAssertRaiseTheory | PASS |
| evalCompilerBytecodeAssertReasonTheory | PASS |
| evalCompilerBytecodeRaiseBareTheory | PASS |
| evalCompilerBytecodeRaiseReasonTheory | PASS |
| evalCompilerBytecodeLoopsTheory | PASS |
| evalCompilerBytecodeScalarWidthsTheory | PASS |
| evalCompilerBytecodeScalarLiteralsTheory | PASS |
| evalCompilerBytecodeScalarLiteralsBytesTheory | PASS |
| evalCompilerBytecodeScalarArithmeticTheory | PASS |
| evalCompilerBytecodeScalarIntegerMinTheory | PASS |
| evalCompilerBytecodeScalarDecimalMinPipelineTheory | PASS |
| evalCompilerBytecodeScalarConvertDecimalTheory | BUILD_FAILURE |
| evalCompilerBytecodeScalarConvertIntToDecimalTheory | DEPENDENCY_EVALUATION_TIMEOUT |
| evalCompilerBytecodeScalarConvertBytes32ToDecimalTheory | PASS |
| evalCompilerBytecodeScalarOperatorsTheory | PASS |
| evalCompilerBytecodeScalarTypeBuiltinsTheory | PASS |
| evalCompilerBytecodeScalarWeiModularTheory | DEPENDENCY_EVALUATION_TIMEOUT |
| evalCompilerBytecodeBuiltinsEnvCoreTheory | PASS |
| evalCompilerBytecodeBuiltinsEnvBlockTheory | PASS |
| evalCompilerBytecodeBuiltinsAccountHashTheory | PASS |
| evalCompilerBytecodeBuiltinsEcTheory | PASS |

`results.json` and `results.csv` provide every source/AST/oracle identity and individual outcome. `hol/` retains translated tops, compiler EVAL results and emitted bytes. `logs/` retains each external command, exit status and stdout/stderr. `corpus/` retains each forced HOL corpus build.

MATCH means both emitted byte arrays equal the independent Python outputs. It does not imply supported_program is true: that result is recorded separately, and current restrictions remain in force.

Decoded byte arrays from checked HOL EVAL exports and independent Python oracle. Raw probe DEPLOY_EQUAL/RUNTIME_EQUAL lines compare unnormalised term syntax and are not byte equality verdicts. This report uses actual bytes.

No compiler semantics, whitelist restrictions (including Exp), frozen oracle data or existing proof statements were changed. The independent oracle is data; expected byte equalities were never installed as evaluator rewrite rules. Alan was not restarted.

The #551 dependency is still present in this revision: `lowering/defs/builtinAbiScript.sml` defines `lower_abi_encode ensure_tuple ...` but never uses `ensure_tuple` in its body. The observed selector/tuple control mismatches are recorded as failures with this dependency, not as MATCH. The two immutable NONE results belong to #563; the remaining ABI controls retain #554/#551 and #567/#551 ownership. Constants and literal hashing controls MATCH in this run.

To reproduce the permanent fixture check: `holbuild --maxheap 12000 build --tactic-timeout 600 foldedValueParityTheory`. The full corpus procedure forces targets listed by `python-o1-bytecode-fixtures`; exact progress, commands and exits are in `corpus/results.json`. Provision/export/execution/report helpers and the originally executed SML harness are retained in `runner/`. Scheduler handoff scripts record this run's process IDs and are historical records, not commands to replay. The corrected probe generator uses checked data equality for future runs.
