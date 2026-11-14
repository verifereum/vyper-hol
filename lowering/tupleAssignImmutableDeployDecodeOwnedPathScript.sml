(* The decoder's owner is carried inside the gas bridge postcondition.
   Resource credit and gas-free code are internal caller obligations. *)
Theory tupleAssignImmutableDeployDecodeOwnedPath
Ancestors
  tupleAssignImmutableDeployDecodeOwnedRun exprSimAbiGasBridge
  exprSimAbiDecodeOblivious abiBuiltinDecodeEffect abiDecoderAllocation
  abiDecoderFrame loweringStateRelDefs venomState

Theorem tuple_immutable_decode_owned_path:
  abi_decoder_coherent ce (get_tenv cx) sf (TupleT tys) tv /\
  evaluate_type_builtin cx (AbiDecode F) (TupleT tys) arg_tys
    [vyperValue$BytesV bs] = INL v /\
  lower_abi_decode data (type_to_abi_dec_info sf ce (TupleT tys)) min_size max_size
    (type_memory_bytes ce (TupleT tys)) start = (out,final) /\
  fn_has_code start final func /\ fn_inst_ids_distinct func /\
  frag_gas_free start final /\
  (start.cs_blocks = final.cs_blocks \/ final.cs_current_insts <> [] \/
    !bb. lookup_block final.cs_current_bb func.fn_blocks = SOME bb ==>
      phi_prefix_length bb.bb_instructions = 0) /\
  val_in_memory (BaseTV (BytesT (Dynamic input_bound))) (vyperValue$BytesV bs) src_base initial.vs_memory /\
  eval_operand data initial = SOME (n2w src_base) /\ abi_decoder_operand_live start.cs_next_var data /\
  abi_builtin_decode_resources start first last min_size max_size (type_memory_bytes ce (TupleT tys))
    (LENGTH bs) src_base d b cap initial /\ final.cs_next_id <= last /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = start.cs_current_bb /\
  initial.vs_inst_idx = LENGTH start.cs_current_insts ==>
  ?actual. gas_marked_path F ctx func initial 0 (OK actual) /\
    eval_operand out actual = SOME (n2w d) /\ val_in_memory tv v d actual.vs_memory /\
    abi_builtin_decode_effect first last start final limit_st d (type_memory_bytes ce (TupleT tys))
      b cap initial actual /\
    FLOOKUP actual.vs_allocas (abi_builtin_decode_output_site start min_size max_size) =
      SOME (d,type_memory_bytes ce (TupleT tys)) /\
    start.cs_next_id <= abi_builtin_decode_output_site start min_size max_size /\
    abi_builtin_decode_output_site start min_size max_size < final.cs_next_id /\
    ~actual.vs_halted /\ actual.vs_current_bb = final.cs_current_bb /\
    actual.vs_inst_idx = LENGTH final.cs_current_insts
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule lower_abi_decode_frag_facts >> strip_tac >>
  qspec_then
    `\actual. eval_operand out actual = SOME (n2w d) /\
      val_in_memory tv v d actual.vs_memory /\
      abi_builtin_decode_effect first last start final limit_st d
        (type_memory_bytes ce (TupleT tys)) b cap initial actual /\
      FLOOKUP actual.vs_allocas (abi_builtin_decode_output_site start min_size max_size) =
        SOME (d,type_memory_bytes ce (TupleT tys)) /\
      start.cs_next_id <= abi_builtin_decode_output_site start min_size max_size /\
      abi_builtin_decode_output_site start min_size max_size < final.cs_next_id`
    mp_tac (Q.SPECL [`ctx`, `start`, `final`] abi_decode_sim_gas_path) >>
  disch_then (qspecl_then [`func`, `initial`] mp_tac) >>
  (impl_tac >-
    (asm_simp_tac bool_ss [] >> conj_tac
     >- (rpt strip_tac >>
         mp_tac (Q.INST [`func` |-> `fn'`] tuple_immutable_decode_owned_run) >>
         (impl_tac >- asm_simp_tac bool_ss []) >> strip_tac >> qexists_tac `actual` >> asm_simp_tac bool_ss []) >>
     rpt gen_tac >>
     `!op. eval_operand op (t with vs_returndata := rd) = eval_operand op t` by
       (Cases >> simp[eval_operand_def, lookup_var_def]) >>
     qpat_x_assum `!op. eval_operand op _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> disch_tac >>
     pure_rewrite_tac [abi_builtin_decode_effect_def, fresh_vars_wrt_def,
       abi_decoder_budget_def, abi_decoder_missing_def,
       abi_decode_footprint_frame_def] >>
     asm_rewrite_tac [venom_state_accfupds] >>
     disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
     asm_rewrite_tac [])) >>
  metis_tac[]
QED
