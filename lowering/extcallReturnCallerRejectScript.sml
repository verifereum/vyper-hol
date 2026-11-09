(* Caller allocation and counted rejection of malformed return data. *)
Theory extcallReturnCallerReject
Ancestors
  extcallReturnCountedReject extcallReturnCallerSuccess
  extcallReturnDecoderLabels abiReturnSize abiReturnReject
  abiMalformedRecursiveInterface exprLoweringProps exprSimWordArgs
  fragExec fragGasMode compileEnv venomState venomInst
  exprLowering loweringHalt context placeMemoryPrimitiveForward builtinSimple emitHelper emitHelperProps list rich_list arithmetic words

Theorem return_allocated_counted_reject:
  compile_alloc_buffer (type_memory_bytes ce rt) a = (buf,m) /\
  compile_return_value_decode lo cap m = (hi,st) /\
  compile_abi_decode_to_buf buf.buf_operand (Lit 0w) MLOAD base_op hi
    (type_to_abi_dec_info sf ce rt) st = ((),en) /\
  cs_extends st en /\ fn_has_code a en func /\ fn_inst_ids_distinct func /\
  (en.cs_current_insts <> [] \/
   !bb. lookup_block en.cs_current_bb func.fn_blocks = SOME bb ==>
        phi_prefix_length bb.bb_instructions = 0) /\
  stmt_state_rel ctx func ce cx ee s /\ local_ptrs_reserved ce a /\
  type_memory_bytes ce rt < dimword (:256) /\ ~s.vs_halted /\
  s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  safe_operand a base_op /\ eval_operand base_op s = SOME (n2w B) /\
  B + cap < dimword (:256) /\
  FLOOKUP s.vs_allocas live = SOME (B,bufsz) /\ cap <= bufsz /\
  live < a.cs_next_id /\
  mem_bytes_at B (LENGTH (TAKE cap bs)) s.vs_memory = TAKE cap bs /\
  lo < dimword (:256) /\ cap < dimword (:256) /\ lo <= cap /\
  s.vs_returndata = bs /\ LENGTH bs < dimword (:256) /\ lo <= LENGTH bs /\
  rt = (if needs_external_call_wrap ty then TupleT [ty] else ty) /\
  cap = vyper_abi_size_bound env rt /\
  lo = abi_static_length (vyper_to_abi_type env rt) /\
  (~is_dynamic (vyper_to_abi_type env rt) ==>
    cap = static_length (vyper_to_abi_type env rt)) /\
  evaluate_abi_decode_return env ty bs = INR err /\
  abi_decoder_coherent ce env sf rt tv /\ abi_decode_bytes_widths env rt /\
  assignable_type env rt /\ type_memory_size tv < dimword (:256) /\
  abi_size_bound sf rt < dimword (:256) /\
  (case type_to_abi_dec_info sf ce rt of DecPrimWord clamp => 32 <= lo | _ => T) ==>
  ?z. gas_marked_path F ctx func s 0 (Abort Revert_abort z)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `!aid. aid IN abi_malformed_scratch_sites st en func ==> st.cs_next_id <= aid` by
    simp[abi_malformed_scratch_sites_def] >>
  drule_all return_allocated_counted_entry >>
  disch_then (qx_choose_then `r` (qx_choose_then `u`
    (qx_choose_then `d` strip_assume_tac))) >>
  `cs_extends a m` by metis_tac[compile_alloc_buffer_extends] >>
  `cs_extends m st` by
    (drule abi_return_size_code >> simp[same_blocks_def, cs_extends_def] >>
     metis_tac[IS_PREFIX_APPEND]) >>
  `fn_has_code st en func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `!l. buf.buf_operand <> Label l` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, comp_bind_def] >>
     rpt (pairarg_tac >> simp[]) >> strip_tac >>
     drule emitted_insts_emit_op >>
     strip_tac >> gvs[comp_return_def]) >>
  `!l. buf.buf_operand <> Label l /\ base_op <> Label l /\ hi <> Label l` by
    metis_tac[return_safe_operand_not_label, return_decode_bound_not_label] >>
  `lo <= LENGTH (TAKE cap bs)` by
    (pure_rewrite_tac[LENGTH_TAKE_EQ] >> Cases_on `cap <= LENGTH bs` >> gvs[]) >>
  `?z. gas_marked_path F ctx func u 0 (Abort Revert_abort z)` by
    (irule return_capped_counted_reject >>
     first_assum (irule_at (Pat `abi_malformed_entry _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     first_assum (irule_at (Pat `abi_decoder_coherent _ _ _ _ _`)) >>
     simp[] >> qexistsl_tac [`ty`, `err`] >> simp[] >>
     qpat_x_assum `case type_to_abi_dec_info _ _ _ of _ => _ | _ => _ | _ => _ | _ => _` mp_tac >>
     Cases_on `type_to_abi_dec_info sf ce rt` >> gvs[] >> decide_tac) >>
  `gas_marked_path F ctx func r (0 + 0) (Abort Revert_abort z)` by
    (irule gas_marked_path_then >> qexists_tac `u` >> simp[]) >>
  `gas_marked_path F ctx func s (0 + 0) (Abort Revert_abort z)` by
    (irule gas_marked_path_then >> qexists_tac `r` >> gvs[]) >>
  metis_tac[ADD_0]
QED
