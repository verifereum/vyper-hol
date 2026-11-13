(* Discharge the conditional family interfaces here, without importing any
   recursive expression or statement correctness theorem. *)
Theory runtimeSymSrcPrimitives
Ancestors
  runtimeSymSrcGeneratorContracts runtimeSymSrcEmission
  runtimeSymSrcContextComplete runtimeSymSrcArithmetic
  runtimeSymSrcBuiltinContracts runtimeSymSrcBuiltinCalls
  runtimeSymSrcOpenValues runtimeSymSrcOpenPlaces runtimeSymSrcOpenLists
  runtimeSymSrcOpenArrays runtimeSymSrcOpenTupleStruct runtimeSymSrcOpenCalls
  runtimeSymSrcSubscriptGenerators runtimeSymSrcSubscriptPrimitives
  runtimeSymSrcContextTyped runtimeSymSrcAbiDecode stackPlanTypes

Theorem runtime_sym_closed_lower_value:
  runtime_sym_lower_value_clause tops
Proof
  irule runtime_sym_lower_value >> metis_tac[runtime_sym_unwrap_value]
QED

Theorem runtime_sym_closed_lower_value_with_loc:
  runtime_sym_lower_value_with_loc_clause tops
Proof
  irule runtime_sym_lower_value_with_loc >> metis_tac[runtime_sym_unwrap_value]
QED

Theorem runtime_sym_closed_subscript:
  runtime_sym_subscript_clause tops
Proof
  irule runtime_sym_subscript >>
  conj_tac >- MATCH_ACCEPT_TAC runtime_sym_array_subscript >>
  conj_tac >- metis_tac[runtime_sym_keccak256_key] >>
  conj_tac >- metis_tac[runtime_sym_tuple_subscript] >>
  conj_tac >- metis_tac[runtime_sym_mapping_subscript] >>
  MATCH_ACCEPT_TAC runtime_sym_closed_lower_value
QED

Theorem runtime_sym_closed_target_ptr:
  runtime_sym_target_ptr_clause tops
Proof
  irule runtime_sym_target_ptr >>
  conj_tac >- MATCH_ACCEPT_TAC runtime_sym_array_subscript >>
  conj_tac >- metis_tac[runtime_sym_keccak256_key] >>
  conj_tac >- metis_tac[runtime_sym_mapping_subscript] >>
  MATCH_ACCEPT_TAC runtime_sym_closed_lower_value
QED

Theorem runtime_sym_closed_make_tuple:
  runtime_sym_make_tuple_clause tops
Proof
  irule runtime_sym_make_tuple >> conj_tac
  >- metis_tac[runtime_sym_store_memory] >>
  metis_tac[runtime_sym_unwrap_value]
QED

Theorem runtime_sym_closed_struct_lit:
  runtime_sym_struct_lit_clause tops
Proof
  irule runtime_sym_struct_lit >> conj_tac
  >- metis_tac[runtime_sym_store_memory] >>
  metis_tac[runtime_sym_unwrap_value]
QED

Theorem runtime_sym_closed_make_array_elems:
  runtime_sym_make_array_elems_clause tops
Proof
  irule runtime_sym_make_array_elems >> conj_tac
  >- metis_tac[runtime_sym_store_memory] >>
  metis_tac[runtime_sym_unwrap_value]
QED

Theorem runtime_sym_closed_abi_encode_args:
  runtime_sym_abi_encode_args_clause tops
Proof
  irule runtime_sym_abi_encode_args >> conj_tac
  >- metis_tac[runtime_sym_materialize_vv] >>
  metis_tac[runtime_sym_unwrap_value]
QED

Theorem runtime_sym_closed_call:
  runtime_sym_call_clause tops
Proof
  irule runtime_sym_call >>
  simp[runtime_sym_multi_vvs, runtime_sym_closed_lower_value] >>
  rpt strip_tac >> irule runtime_sym_abi_decode_to_buf >>
  goal_assum (drule_at Any) >> simp[is_label_operand_def]
QED

Theorem runtime_sym_generators:
  !tops. runtime_sym_generator_contracts tops
Proof
  gen_tac >> rewrite_tac[runtime_sym_generator_contracts_def] >>
  simp[runtime_sym_closed_lower_value, runtime_sym_closed_lower_value_with_loc,
       runtime_sym_closed_subscript, runtime_sym_attribute,
       runtime_sym_closed_target_ptr, runtime_sym_multi_vvs,
       runtime_sym_closed_make_tuple, runtime_sym_closed_struct_lit,
       runtime_sym_closed_make_array_elems, runtime_sym_closed_abi_encode_args,
       runtime_sym_closed_call, runtime_sym_context_contracts,
       runtime_sym_expr_primitives, runtime_sym_math,
       runtime_sym_simple_contract, runtime_sym_misc_contract,
       runtime_sym_abi_contract] >> rpt conj_tac
  >- (irule runtime_sym_multi_exprs >> simp[runtime_sym_closed_lower_value])
  >- (irule runtime_sym_make_array >> simp[runtime_sym_closed_make_array_elems])
  >- (irule runtime_sym_concat >> simp[runtime_sym_closed_lower_value])
  >- (irule runtime_sym_acc >> simp[runtime_sym_closed_lower_value]) >>
  irule runtime_sym_arithmetic_name_fastpaths >> simp[runtime_sym_context_contracts]
QED
