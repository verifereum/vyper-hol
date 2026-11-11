(* Successful Log suffix after topic hashing; compiler branches stay separate. *)
Theory logDataEmitSuffixPtr
Ancestors
  logStoreEncodeRunPtr logEmitPtr logGhostFramePtr stmtSimLogTrace logEventCodePtr
  stmtSimLogSuffixActual stmtSimLogArgs stmtSimLogDataRun stmtSimLogStoreFresh
  bodyPtrDefs stmtFragPtr fragGasPathPtr compileEnv loweringStateRelDefs context stmtLowering
  emitHelperProps exprLoweringProps venomState venomInst ptrDiscipline
  list arithmetic words rich_list vyperABI valueEncoding valueEncodingDefs contractABI abiDecoderReentry

Theorem eval_operands_list_rel:
  !ops ws. LIST_REL (\op w. eval_operand op s = SOME w) ops ws <=>
    eval_operands ops s = SOME ws
Proof
  Induct >> Cases_on `ws` >> simp[eval_operands_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem log_data_emit_suffix_path_ptr:
  ce.ce_event_info (nsid_to_string id) = SOME (h,tys,flags) /\
  compile_log_eval_all ce args sa = (xs,sm) /\
  compile_log_topic_ops (FST (split_log_ops xs flags)) sm = (ops,st) /\
  compile_stmt ce lctx ty (Log id args) sa = ((),sb) /\
  data_ops = SND (split_log_ops xs flags) /\
  LIST_REL (\op w. eval_operand op s = SOME w) ops topics /\
  EVERY (\op. op_taint tn op = {}) ops /\
  EVERY (\op. (!z. op = Var z ==> not_fresh_at st z) /\ (!l. op <> Label l)) ops /\
  LENGTH ops <= 3 /\
  LIST_REL (\arg v. log_arg_rel ce cx sa st es s arg v /\
    supported_scalar_type (SND arg) /\
    ?tv. evaluate_type (get_tenv cx) (SND arg) = SOME tv /\
      value_has_type tv v /\ val_wf tv v) data_ops (log_non_indexed_values flags vs) /\
  LIST_REL (\(op,ty) v. ptr_val_ok cx ty v op G tn s)
    data_ops (log_non_indexed_values flags vs) /\
  EVERY (\arg. (!z. FST arg = Var z ==> not_fresh_at st z) /\
    (!l. FST arg <> Label l)) data_ops /\
  SUM (MAP (type_memory_bytes ce) (MAP SND data_ops)) < dimword(:256) /\
  abi_size_bound ce.ce_struct_fields (TupleT (MAP SND data_ops)) < dimword(:256) /\
  vyper_to_abi_list (get_tenv cx) (MAP SND data_ops)
    (log_non_indexed_values flags vs) = SOME avs /\
  stmt_state_rel ctx func ce cx es s /\ ghost_inv d ce cx es G tn s /\
  local_ptrs_reserved ce st /\
  (!p sz. ce.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at st p) /\
  (!p sz. ce.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at st p) /\
  fn_has_code st sb func /\ fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  sb.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t H tm.
    gas_path_ptr D 0 ctx func PG G tn s
      (LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st sb))) H tm (OK t) /\
    fresh_vars_wrt limit_st t /\
    stmt_state_rel ctx func ce cx
      (es with logs := es.logs ++ [<|logger := w2w cx.txn.target;
        topics := n2w h::topics; data := enc
          (Tuple (vyper_to_abi_types (get_tenv cx) (MAP SND data_ops))) (ListV avs)|>]) t /\
    ghost_inv d ce cx
      (es with logs := es.logs ++ [<|logger := w2w cx.txn.target;
        topics := n2w h::topics; data := enc
          (Tuple (vyper_to_abi_types (get_tenv cx) (MAP SND data_ops))) (ListV avs)|>]) H tm t /\
    ghost_kept ce es st G tn s H tm /\ inst_extends st sb /\
    ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = s.vs_inst_idx + LENGTH (emitted_insts st sb) /\
    (!x w. not_fresh_at st x /\ lookup_var x s = SOME w ==> lookup_var x t = SOME w)
Proof
  strip_tac >> Cases_on `data_ops = []`
  >- suspend "empty"
  >> suspend "data"
QED
Resume log_data_emit_suffix_path_ptr[empty]:
  markerLib.RESUME_TAC >>
  `SND (split_log_ops xs flags) = []` by metis_tac[] >>
  drule_all compile_log_empty_trace >> disch_tac >>
  `emit_inst LOG (Lit (n2w (LENGTH (Lit (n2w h)::ops))) ::
    REVERSE (Lit (n2w h)::ops) ++ [Lit 0w; Lit 0w]) [] st = ((),sb)` by
    metis_tac[] >>
  `eval_operands (Lit (n2w h)::ops) s = SOME (n2w h::topics)` by
    simp[eval_operands_def, eval_operand_def, GSYM eval_operands_list_rel] >>
  `LENGTH (Lit (n2w h)::ops) < dimword(:256)` by
    (simp[dimword_def] >> decide_tac) >>
  `eval_operand (Lit 0w) s = SOME (0w:bytes32)` by simp[eval_operand_def] >>
  `EVERY (\op. op_taint tn op = {})
    (Lit 0w::Lit 0w::Lit (n2w h)::ops)` by simp[op_taint_def] >>
  `w2n (0w:bytes32) <> 0 ==> ?v. Lit 0w = Var v /\ ptr_covers G tn v s (w2n (0w:bytes32))` by simp[] >>
  `!i. w2n (0w:bytes32) <= i /\ i < w2n (0w:bytes32) + w2n (0w:bytes32) ==> i NOTIN tn.t_mem` by simp[] >>
  drule_all compile_log_emit_path_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `log_non_indexed_values flags vs = []` by
    (qpat_x_assum `LIST_REL (\arg v. log_arg_rel _ _ _ _ _ _ _ _ /\ _) _ _` mp_tac >> simp[]) >>
  `avs = []` by
    (qpat_x_assum `vyper_to_abi_list _ _ _ = _` mp_tac >>
     simp[vyper_to_abi_def]) >>
  drule emitted_insts_emit_inst >> strip_tac >>
  qexistsl_tac [`t with vs_inst_idx := SUC s.vs_inst_idx`,`G`,`tn`] >>
  fs[mem_bytes_at_def, vyper_to_abi_type_def, enc_def,
    ghost_kept_refl, mk_inst_def] >> simp[listTheory.REV_DEF] >>
  qpat_x_assum `~s.vs_halted` mp_tac >>
  qpat_x_assum `t with vs_logs := s.vs_logs = s`
    (fn th => once_rewrite_tac[GSYM th]) >> simp[lookup_var_def]
QED
Resume log_data_emit_suffix_path_ptr[data]:
  markerLib.RESUME_TAC >>
  `SND (split_log_ops xs flags) <> []` by metis_tac[] >>
  `SND (split_log_ops xs flags) = data_ops` by metis_tac[] >>
  drule_all compile_log_data_trace >> disch_tac >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  qpat_x_assum `!ty sb lctx. compile_stmt _ _ _ _ _ = _ <=> _`
    (fn th => once_rewrite_tac[th]) >> strip_tac >>
  qpat_x_assum `SND (split_log_ops xs flags) = data_ops` kall_tac >>
  drule log_source_encoder_types >> strip_tac >>
  drule_all log_data_trace_code >> strip_tac >>
  `MAX 32 (SUM (MAP (type_memory_bytes ce) (MAP SND data_ops))) < dimword(:256) /\
   MAX 32 (abi_size_bound ce.ce_struct_fields (TupleT (MAP SND data_ops))) < dimword(:256)` by
    (simp[MAX_DEF, dimword_def] >> decide_tac) >>
  `SUM (MAP (type_memory_bytes ce) (MAP SND data_ops)) <=
    MAX 32 (SUM (MAP (type_memory_bytes ce) (MAP SND data_ops))) /\
   abi_size_bound ce.ce_struct_fields (TupleT (MAP SND data_ops)) <=
    MAX 32 (abi_size_bound ce.ce_struct_fields (TupleT (MAP SND data_ops)))` by simp[] >>
  drule_all log_source_store_encode_path_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `avs' = avs` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `avs' = avs` SUBST_ALL_TAC >>
  suspend "data_emit"
QED
Resume log_data_emit_suffix_path_ptr[data_emit]:
  markerLib.RESUME_TAC >>
  `!op. MEM op ops ==> abi_decoder_operand_live st.cs_next_var op` by
    (fs[EVERY_MEM] >> rpt strip_tac >> Cases_on `op` >>
     fs[abi_decoder_operand_live_def, abi_decoder_older_vars_def, not_fresh_at_def]) >>
  `LIST_REL (\op w. eval_operand op v = SOME w) ops topics` by
    (qpat_assum `LIST_REL (\op w. eval_operand op s = SOME w) ops topics` mp_tac >>
     rewrite_tac[LIST_REL_EL_EQN] >> strip_tac >>
     asm_simp_tac bool_ss [] >> rpt strip_tac >>
     qpat_x_assum `!op w. abi_decoder_operand_live _ op /\ _ ==> _` irule >>
     metis_tac[MEM_EL]) >>
  `EVERY (\op. op_taint tm op = {}) ops` by
    (qpat_assum `EVERY (\op. op_taint tn op = {}) ops` mp_tac >>
     qpat_assum `EVERY (\op. (!z. op = Var z ==> _) /\ _) ops` mp_tac >>
     rewrite_tac[EVERY_MEM] >> ntac 2 disch_tac >>
     qx_gen_tac `op` >> strip_tac >> Cases_on `op`
     >- simp[op_taint_def]
     >- metis_tac[] >> simp[op_taint_def]) >>
  `eval_operands (Lit (n2w h)::ops) v = SOME (n2w h::topics)` by
    simp[eval_operands_def, eval_operand_def, GSYM eval_operands_list_rel] >>
  `LENGTH (Lit (n2w h)::ops) < dimword(:256)` by
    (simp[dimword_def] >> decide_tac) >>
  qmatch_asmsub_abbrev_tac `mem_bytes_at db (LENGTH bytes) v.vs_memory = bytes` >>
  `LENGTH bytes < dimword(:256)` by decide_tac >>
  `ptr_covers H tm dv v (LENGTH bytes) /\ op_taint tm dst.buf_operand = {}` by
    (fs[ptr_covers_def, MAX_DEF] >> decide_tac) >>
  `EVERY (\op. op_taint tm op = {})
    (dst.buf_operand::len::Lit (n2w h)::ops)` by simp[op_taint_def] >>
  `w2n (n2w (LENGTH bytes):bytes32) <> 0 ==>
    ?p. dst.buf_operand = Var p /\ ptr_covers H tm p v (w2n (n2w (LENGTH bytes):bytes32))` by
    (simp[] >> metis_tac[]) >>
  `!i. w2n (n2w db:bytes32) <= i /\
    i < w2n (n2w db:bytes32) + w2n (n2w (LENGTH bytes):bytes32) ==> i NOTIN tm.t_mem` by
    simp[] >>
  `lookup_block v.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts s4 sb) (DROP v.vs_inst_idx bb.bb_instructions)` by
    asm_rewrite_tac[] >>
  drule_all compile_log_emit_path_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  suspend "data_post"
QED
Resume log_data_emit_suffix_path_ptr[data_post]:
  markerLib.RESUME_TAC >>
  drule_all gas_path_ptr_then >> disch_tac >>
  `mem_bytes_at (w2n (n2w db:bytes32)) (w2n (n2w (LENGTH bytes):bytes32))
    v.vs_memory = bytes` by simp[] >>
  drule emitted_insts_emit_inst >> strip_tac >>
  `LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st sb)) =
   LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts st s1)) +
   LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts s1 s2)) +
   LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts s2 s4))` by
    (qpat_assum `emitted_insts st sb = _` (fn th => once_rewrite_tac[th]) >>
     simp[FILTER_APPEND, mk_inst_def] >> decide_tac) >>
  qexistsl_tac [`t with vs_inst_idx := SUC v.vs_inst_idx`,`H`,`tm`] >>
  qpat_x_assum `v.vs_inst_idx = _` SUBST_ALL_TAC >>
  full_simp_tac bool_ss [ADD_0] >>
  `t.vs_halted = v.vs_halted /\ t.vs_current_bb = v.vs_current_bb /\
   (!x. lookup_var x t = lookup_var x v)` by
    (qpat_x_assum `t with vs_logs := v.vs_logs = v`
       (fn th => once_rewrite_tac[GSYM th]) >> simp[lookup_var_def]) >>
  simp[LENGTH_APPEND] >> rpt strip_tac >>
  qpat_x_assum `!op w. abi_decoder_operand_live _ op /\ _ ==> _`
    (qspec_then `Var x` mp_tac) >>
  simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
       GSYM not_fresh_at_def, eval_operand_def] >>
  strip_tac >> simp[lookup_var_def] >> fs[lookup_var_def]
QED
Finalise log_data_emit_suffix_path_ptr

val _ = if null (hyp log_data_emit_suffix_path_ptr) then ()
  else raise Fail "log_data_emit_suffix_path_ptr is not closed";
