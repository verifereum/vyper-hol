# Differential regression fixtures

These fixtures preserve the triage of the 54 scenarios in `~/diffs_clean` against
Vyper `cd74ce4f57e3771aeeab8f061fa3be45bfe8a29c` (`0.5.0a4`, Prague, gas
optimization). Each retained directory contains the original pytest scenario,
the deployed Vyper source, capture metadata, and the compiler-reference trace.

The trace files use the existing `vyperTestLib` format and intentionally omit the
differential runner's `state_checkpoint` extension. Forty-three divergences are
observable through the standard deployment/call result runner. Findings 3 and 21
check committed log topics; findings 23, 43, and 50 check final account lifetime
through the focused helpers in `vyperRegressionStateTheory`. Broad checkpoint
support is therefore not required.

The corresponding `vyperRegression_*Script.sml` theories are discovered by the
Vyper-test CI matrix. They are expected to fail until the relevant semantics bug
is fixed; a passing theory means that regression is resolved.

## Triage

| Finding | Disposition |
|---:|---|
| 1 | Confirmed: [`finding_01_integer_to_fixed_bytes`](finding_01_integer_to_fixed_bytes/) |
| 2 | Confirmed: [`finding_02_short_bytes_to_signed`](finding_02_short_bytes_to_signed/) |
| 3 | Confirmed: [`finding_03_indexed_bytes20_topic`](finding_03_indexed_bytes20_topic/) |
| 4 | Confirmed: [`finding_04_dynamic_abi_padding`](finding_04_dynamic_abi_padding/) |
| 5 | Confirmed: [`finding_05_assignment_order`](finding_05_assignment_order/) |
| 6 | Confirmed: [`finding_06_augmented_assignment_snapshot`](finding_06_augmented_assignment_snapshot/) |
| 7 | Rejected: `skip_contract_check` scenario is the ordinary `NONE`-mode control and does not execute the reported divergent mode. |
| 8 | Rejected: default return-code-check scenario is the ordinary `NONE`-mode control and does not execute the reported divergent mode. |
| 9 | Confirmed: [`finding_09_fixed_array_default_membership`](finding_09_fixed_array_default_membership/) |
| 10 | Confirmed: [`finding_10_literal_membership_short_circuit`](finding_10_literal_membership_short_circuit/) |
| 11 | Confirmed: [`finding_11_missing_conversion_pairs`](finding_11_missing_conversion_pairs/) |
| 12 | Confirmed: [`finding_12_address_widening`](finding_12_address_widening/) |
| 13 | Confirmed: [`finding_13_dependent_tuple_targets`](finding_13_dependent_tuple_targets/) |
| 14 | Confirmed: [`finding_14_send_revert`](finding_14_send_revert/) |
| 15 | Confirmed: [`finding_15_nonreverting_raw_call`](finding_15_nonreverting_raw_call/) |
| 16 | Confirmed: [`finding_16_bytes32_binary_operators`](finding_16_bytes32_binary_operators/) |
| 17 | Confirmed: [`finding_17_blueprint_offset_wrapping`](finding_17_blueprint_offset_wrapping/) |
| 18 | Confirmed: [`finding_18_calldata_zero_extension`](finding_18_calldata_zero_extension/) |
| 19 | Confirmed: [`finding_19_extract32_full_window`](finding_19_extract32_full_window/) |
| 20 | Confirmed: [`finding_20_self_account_properties`](finding_20_self_account_properties/) |
| 21 | Confirmed: [`finding_21_event_argument_order`](finding_21_event_argument_order/) |
| 22 | Confirmed: [`finding_22_internal_selfdestruct`](finding_22_internal_selfdestruct/) |
| 23 | Confirmed: [`finding_23_created_child_lifetime`](finding_23_created_child_lifetime/) |
| 24 | Confirmed: [`finding_24_effectful_operand_order`](finding_24_effectful_operand_order/) |
| 25 | Confirmed: [`finding_25_forward_nonscalar_constants`](finding_25_forward_nonscalar_constants/) |
| 26 | Confirmed: [`finding_26_folded_builtin_keywords`](finding_26_folded_builtin_keywords/) |
| 27 | Confirmed: [`finding_27_decimal_mapping_keys`](finding_27_decimal_mapping_keys/) |
| 28 | Confirmed: [`finding_28_storage_iteration_snapshot`](finding_28_storage_iteration_snapshot/) |
| 29 | Confirmed: [`finding_29_fixed_bytes_mapping_key`](finding_29_fixed_bytes_mapping_key/) |
| 30 | Confirmed: [`finding_30_nested_builtin_module`](finding_30_nested_builtin_module/) |
| 31 | Rejected: the scenario calls an ordinary target and never establishes delegated-account state. |
| 32 | Rejected: the callback is compiled EVM code, so it does not exercise the reported source-semantics held-lock boundary. |
| 33 | Confirmed: [`finding_33_gas_expression_evaluation`](finding_33_gas_expression_evaluation/) |
| 34 | Confirmed: [`finding_34_nested_array_pop`](finding_34_nested_array_pop/) (storage-pop parameter) |
| 35 | Confirmed: [`finding_35_block_prevrandao`](finding_35_block_prevrandao/) |
| 36 | Rejected: the protocol decodes ordinary ABI returns and does not expose the reported exact-byte helper behavior. |
| 37 | Confirmed: [`finding_37_pure_function_nonreentrancy`](finding_37_pure_function_nonreentrancy/) |
| 38 | Confirmed: [`finding_38_imported_flag_complement`](finding_38_imported_flag_complement/) |
| 39 | Confirmed: [`finding_39_constructor_self_code`](finding_39_constructor_self_code/) |
| 40 | Confirmed: [`finding_40_block_gaslimit`](finding_40_block_gaslimit/) |
| 41 | Confirmed: [`finding_41_shift_builtin`](finding_41_shift_builtin/) |
| 42 | Confirmed: [`finding_42_create_argument_order`](finding_42_create_argument_order/) |
| 43 | Confirmed: [`finding_43_nested_creation_deletion`](finding_43_nested_creation_deletion/) |
| 44 | Confirmed: [`finding_44_call_argument_order`](finding_44_call_argument_order/) |
| 45 | Confirmed: [`finding_45_top_level_static_context`](finding_45_top_level_static_context/) |
| 46 | Confirmed: [`finding_46_constructor_block_gaslimit`](finding_46_constructor_block_gaslimit/) |
| 47 | Confirmed: [`finding_47_nested_create_coinbase`](finding_47_nested_create_coinbase/) |
| 48 | Confirmed: [`finding_48_nested_create_chain_id`](finding_48_nested_create_chain_id/) |
| 49 | Confirmed: [`finding_49_nested_create_randomness`](finding_49_nested_create_randomness/) |
| 50 | Confirmed: [`finding_50_constructor_selfdestruct`](finding_50_constructor_selfdestruct/) |
| 51 | Confirmed: [`finding_51_create_balance_overflow`](finding_51_create_balance_overflow/) |
| 52 | Confirmed: [`finding_52_genesis_prevhash`](finding_52_genesis_prevhash/) |
| 53 | Confirmed: [`finding_53_self_send_balance`](finding_53_self_send_balance/) |
| 54 | Rejected false positive: the deployer lacked funds for the nonzero-value deployment. Funding the deployer made the pinned compiler accept the deployment. |
