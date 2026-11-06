(* Source allocation/staging followed by the allocated scalar tuple encoder. *)
Theory logStoreEncodeRunPtr
Ancestors
  logSourceStoreRunPtr logTuplePathPtr logEncoderEntryPtr logGhostFramePtr
  stmtSimLogDataRun abiBuiltinAllocation emitHelperProps exprLoweringProps
  stmtFragPtr fragGasPathPtr compileEnv venomState list arithmetic words

Theorem log_source_encoder_types:
  !(xs:(operand # type) list) vs. LIST_REL (\arg v. log_arg_rel ce cx sa st es s arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\
      value_has_type tv v /\ val_wf tv v) xs vs ==>
  EVERY supported_scalar_type (MAP SND xs) /\
  LIST_REL (\ty v. ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
    value_has_type tv v) (MAP SND xs) vs
Proof
  Induct >> Cases_on `vs` >> simp[] >> rpt strip_tac >> res_tac >> simp[] >>
  metis_tac[]
QED

Theorem log_source_store_encode_path_ptr:
  compile_alloc_buffer cap st = (buf,start) /\ fn_has_code st start func /\
  compile_log_store_data ce xs buf.buf_operand 0 start = ((),mid) /\
  compile_alloc_buffer outcap mid =
    (dst,prepared) /\ fn_has_code mid prepared func /\
  compile_abi_encode_to_buf dst.buf_operand buf.buf_operand
    (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP SND xs))) prepared =
    (out,end_st) /\ fn_has_code prepared end_st func /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce st /\ cap < dimword(:256) /\
  outcap < dimword(:256) /\
  abi_size_bound ce.ce_struct_fields (TupleT (MAP SND xs)) <= outcap /\
  start.cs_next_var <= mid.cs_next_var /\
  mid.cs_next_var <= limit_st.cs_next_var /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st s /\ ~ctx_has_dalloca ctx /\ ghost_inv d ce cx es G tn s /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at st p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at st p) /\
  LIST_REL (\arg v. log_arg_rel ce cx sa st es s arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\
      value_has_type tv v /\ val_wf tv v) xs vs /\
  LIST_REL (\(op,ty) v. ptr_val_ok cx ty v op G tn s) xs vs /\
  EVERY (\arg. (!x. FST arg = Var x ==> not_fresh_at st x) /\
    (!l. FST arg <> Label l)) xs /\
  SUM (MAP (type_memory_bytes ce) (MAP SND xs)) <= cap /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st start) (DROP s.vs_inst_idx bb.bb_instructions) /\
  isPREFIX (emitted_insts start mid)
    (DROP (s.vs_inst_idx + LENGTH (emitted_insts st start)) bb.bb_instructions) /\
  isPREFIX (emitted_insts mid end_st)
    (DROP (s.vs_inst_idx + LENGTH (emitted_insts st start) +
      LENGTH (emitted_insts start mid)) bb.bb_instructions) ==>
  ?avs v db H tm.
    vyper_to_abi_list (get_tenv cx) (MAP SND xs) vs = SOME avs /\
    gas_path_ptr D 0 ctx func PG G tn s
      (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st start)) +
       LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts start mid)) +
       LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts mid end_st))) H tm (OK v) /\
    fresh_vars_wrt limit_st v /\ stmt_state_rel ctx func ce cx es v /\
    eval_operand dst.buf_operand v = SOME (n2w db) /\ db < dimword(:256) /\
    mem_bytes_at db (LENGTH (enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP SND xs)))
      (ListV avs))) v.vs_memory =
      enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP SND xs))) (ListV avs) /\
    eval_operand out v = SOME (n2w (LENGTH
      (enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP SND xs))) (ListV avs)))) /\
    op_taint tm out = {} /\ op_prov H out = NONE /\
    (!i. db <= i /\ i < db + LENGTH
      (enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP SND xs))) (ListV avs)) ==>
      i NOTIN tm.t_mem) /\
    ghost_inv d ce cx es H tm v /\ ghost_kept ce es st G tn s H tm /\
    (?dv. dst.buf_operand = Var dv /\ ptr_covers H tm dv v outcap) /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op v = SOME w) /\
    (!p. not_fresh_at st p ==> op_taint tm (Var p) = op_taint tn (Var p)) /\
    ~v.vs_halted /\ v.vs_current_bb = s.vs_current_bb /\
    v.vs_inst_idx = s.vs_inst_idx + LENGTH (emitted_insts st start) +
      LENGTH (emitted_insts start mid) + LENGTH (emitted_insts mid end_st)
Proof
  strip_tac >>
  drule_all log_source_store_run_path_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  drule log_source_encoder_types >> strip_tac >>
  `SUM (MAP (type_memory_bytes ce) (MAP SND xs)) < dimword(:256)` by decide_tac >>
  drule_all supported_log_encoder_entry_ptr >>
  disch_then (qx_choose_then `avs` (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  `st.cs_next_var <= start.cs_next_var` by
    (qpat_assum `compile_alloc_buffer cap st = _`
       (mp_then Any mp_tac abi_builtin_alloc_buffer_shape) >> strip_tac >>
     drule emitted_insts_emit_op >> simp[]) >>
  `st.cs_next_var <= mid.cs_next_var` by decide_tac >>
  `local_ptrs_reserved ce mid` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at mid p) /\
   (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at mid p)` by
    metis_tac[not_fresh_at_mono] >>
  `EVERY (supported_scalar_type o SND) xs` by
    fs[EVERY_MAP, combinTheory.o_DEF] >>
  drule_all compile_log_store_data_shape >> strip_tac >>
  `st.cs_next_id < mid.cs_next_id` by decide_tac >>
  `not_fresh_at mid src` by
    (qpat_assum `compile_alloc_buffer cap st = _`
       (mp_then Any mp_tac abi_builtin_alloc_buffer_shape) >> strip_tac >>
     drule emitted_insts_emit_op >> strip_tac >>
     qpat_assum `buf.buf_operand = Var src` mp_tac >>
     simp[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
     disch_then (SUBST1_TAC o SYM) >>
     simp[ASCIInumbersTheory.toString_inj]) >>
  `~t.vs_halted /\ lookup_block t.vs_current_bb func.fn_blocks = SOME bb` by simp[] >>
  qpat_assum `buf.buf_operand = Var src` (fn eq => RULE_ASSUM_TAC (REWRITE_RULE [eq])) >>
  `LENGTH (enc (Tuple (vyper_to_abi_types (get_tenv cx) (MAP SND xs)))
    (ListV avs)) <= outcap` by decide_tac >>
  drule_all log_allocated_tuple_path_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  suspend "post"
QED
Resume log_source_store_encode_path_ptr[post]:
  markerLib.RESUME_TAC >>
  drule_all gas_path_ptr_then >> disch_tac >>
  `ghost_kept ce es st G tn s H' tm'` by
    (irule ghost_kept_trans >>
     qexistsl_tac [`H`,`es`,`t`,`mid`,`tm`] >> asm_simp_tac bool_ss [] >> decide_tac) >>
  `!p. not_fresh_at st p ==> not_fresh_at mid p` by
    metis_tac[not_fresh_at_mono] >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    abi_decoder_operand_live mid.cs_next_var op` by
    metis_tac[abiDecoderReentryTheory.abi_decoder_operand_live_mono] >>
  qexistsl_tac [`avs`,`v`,`db`,`H'`,`tm'`] >>
  asm_simp_tac bool_ss [] >>
  qexists_tac `dv` >> asm_rewrite_tac[]
QED
Finalise log_source_store_encode_path_ptr

val _ = if null (hyp log_source_store_encode_path_ptr) then ()
  else raise Fail "log_source_store_encode_path_ptr is not closed";
