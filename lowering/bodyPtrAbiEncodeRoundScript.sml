(* Clean scalar instructions used by the bytes encoder's rounding phases. *)
Theory bodyPtrAbiEncodeRound
Ancestors
  bodyPtrAbiEncodeCursorFrame bodyPtrAbiEncodeStaticChild abiEncoderRoundExecute abiEncoderRounding abiEncoderBytesCode
  typedCopyPtr fragGasSeqPtr fragGasPathPtr emitHelperProps exprLoweringProps
  compileEnv emitHelper venomExecSemantics venomState venomInst ptrDiscipline
  finite_map words arithmetic list rich_list

Theorem abi_encode_clean_binary_sequence:
  emit_op opc [left;right] st = (out,st') /\
  (opc = ADD /\ w = a+b \/ opc = AND /\ w = word_and a b) /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  ~ctx_has_dalloca ctx /\ st'.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st s ==>
  ?p t H un. out = Var p /\
    run_inst_seq (emitted_insts st st') s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts st st') s H un /\
    abi_encode_read_frame st s G tn t H un /\
    lookup_var p t = SOME w /\ op_taint un (Var p) = {} /\
    not_fresh_at st' p /\ fresh_vars_wrt limit_st t /\
    t.vs_inst_idx = s.vs_inst_idx
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule emitted_insts_emit_op >> strip_tac >> gnvs[] >>
  qabbrev_tac `p = STRING #"%" (toString st.cs_next_var)` >>
  qabbrev_tac `t = update_var p w s` >>
  qabbrev_tac `H = step_prov PG G (mk_inst st.cs_next_id opc [left;right] [p]) t` >>
  qabbrev_tac `un = step_taint (mk_inst st.cs_next_id opc [left;right] [p]) s t tn` >>
  `opc = ADD \/ opc = AND` by metis_tac[] >>
  `ptr_inst_ok D 0 0 ctx fn G tn
    (mk_inst st.cs_next_id opc [left;right] [p]) s` by
    (irule ptr_inst_ok_copy_len_binop >> simp[]) >>
  `step_inst_base (mk_inst st.cs_next_id opc [left;right] [p]) s = OK t` by
    (gvs[] >> simp[Once step_inst_base_def, mk_inst_def, exec_pure2_def, Abbr `t`]) >>
  `fresh_vars_wrt limit_st t` by
    (simp[Abbr `t`] >> irule fresh_vars_wrt_update_var >> simp[Abbr `p`] >>
     goal_assum $ drule_at Any >> simp[]) >>
  qexistsl_tac [`t`, `H`, `un`] >>
  simp[run_inst_seq_def, inst_seq_ptr_def, abi_encode_read_frame_def,
       Abbr `H`, Abbr `un`, Abbr `t`, copy_len_binop_ghost_frame,
       update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  (conj_tac >- (rpt strip_tac >>
     `q <> p` by (gvs[not_fresh_at_def, Abbr `p`] >> metis_tac[]) >>
     simp[GSYM update_var_def, copy_len_binop_ghost_frame]) >>
   simp[not_fresh_at_def, Abbr `p`])
QED

Theorem abi_encode_clean_binary_framed_path:
  emit_op opc [left;right] st = (out,st') /\
  (opc = ADD /\ w = a+b \/ opc = AND /\ w = word_and a b) /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  ~ctx_has_dalloca ctx /\ st'.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st s /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?p t H un. out = Var p /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H un (OK t) /\
    abi_encode_read_frame st s G tn t H un /\
    lookup_var p t = SOME w /\ op_taint un (Var p) = {} /\
    not_fresh_at st' p /\ fresh_vars_wrt limit_st t /\
    t.vs_inst_idx = s.vs_inst_idx+1
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all abi_encode_clean_binary_sequence >>
  disch_then (qspecl_then [`fn`, `PG`, `G`, `D`] strip_assume_tac) >>
  drule emitted_insts_emit_op >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')` by
    (qpat_x_assum `_ /\ _ \/ _ /\ _` strip_assume_tac >>
     simp[mk_inst_def, is_terminator_def]) >>
  drule_all run_inst_seq_gas_path_ptr >> simp[mk_inst_def] >> strip_tac >>
  qexistsl_tac [`t with vs_inst_idx := s.vs_inst_idx+1`, `H`, `un`] >>
  qpat_x_assum `_ /\ _ \/ _ /\ _` strip_assume_tac >>
  gvs[abi_encode_read_frame_def, fresh_vars_wrt_def, lookup_var_def]
QED

Theorem abi_encode_round_trace:
  abi_encode_round len st = (out,en) ==>
  ?arg mid. emit_op ADD [Lit 31w;len] st = (arg,mid) /\
    emit_op AND
      [Lit 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w;arg]
      mid = (out,en) /\
    mid.cs_next_var = st.cs_next_var+1 /\ en.cs_next_var = mid.cs_next_var+1 /\
    emitted_insts st en = emitted_insts st mid ++ emitted_insts mid en /\
    LENGTH (emitted_insts st mid) = 1 /\ LENGTH (emitted_insts mid en) = 1
Proof
  simp_tac bool_ss [abi_encode_round_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `emit_op ADD _ st = (arg,mid)` >>
  imp_res_tac emitted_insts_emit_op >> simp[] >>
  simp_tac bool_ss [emitted_insts_def] >>
  asm_rewrite_tac[] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND]
QED

Theorem abi_encode_round_framed_path:
  abi_encode_round len st = (out,en) /\
  eval_operand len s = SOME (n2w cnt) /\ op_taint tn len = {} /\
  cnt+31 < dimword(:256) /\ ~ctx_has_dalloca ctx /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st en) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?p t H un. out = Var p /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H un (OK t) /\
    abi_encode_read_frame st s G tn t H un /\
    lookup_var p t = SOME (n2w (contractABI$ceil32 cnt)) /\
    op_taint un (Var p) = {} /\ not_fresh_at en p /\
    fresh_vars_wrt limit_st t /\ t.vs_inst_idx = s.vs_inst_idx+2
Proof
  strip_tac >> drule abi_encode_round_trace >> strip_tac >>
  `isPREFIX (emitted_insts st mid) (DROP s.vs_inst_idx bb.bb_instructions) /\
   isPREFIX (emitted_insts mid en) (DROP (s.vs_inst_idx+1) bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX _ _` mp_tac >> asm_rewrite_tac[] >>
     strip_tac >> drule abi_encode_static_child_sites >> simp[]) >>
  `mid.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  `eval_operand (Lit 31w) s = SOME (31w:bytes32) /\
   op_taint tn (Lit 31w) = {}` by simp[eval_operand_def, op_taint_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`, `w` |-> `a+b:bytes32`]
    (SPEC_ALL abi_encode_clean_binary_framed_path))) >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >> gvs[] >>
  drule_all abi_encode_read_frame_control >> strip_tac >>
  `eval_operand (Lit 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w) t =
     SOME (0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w:bytes32) /\
   op_taint un (Lit 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFE0w) = {} /\
   eval_operand (Var p) t = SOME (31w+n2w cnt) /\
   isPREFIX (emitted_insts mid en) (DROP t.vs_inst_idx bb.bb_instructions) /\
   en.cs_next_var <= limit_st.cs_next_var` by simp[eval_operand_def, op_taint_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `AND`, `w` |-> `word_and a b:bytes32`]
    (SPEC_ALL abi_encode_clean_binary_framed_path))) >>
  disch_then (qspecl_then [`PG`, `H`, `D`] strip_assume_tac) >> gvs[] >>
  drule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  `st.cs_next_var <= mid.cs_next_var` by decide_tac >>
  `abi_encode_read_frame st s G tn t' H' un'` by metis_tac[abi_encode_read_frame_then] >>
  qexistsl_tac [`t'`, `H'`, `un'`] >> simp[abi_encoder_round_ceil32]
QED
