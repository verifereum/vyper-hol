(* The returned bytes length is a clean scalar, not pointer provenance. *)
Theory bodyPtrAbiEncodeBytesSuffix
Ancestors
  bodyPtrAbiEncodeRound bodyPtrAbiEncodeCursorFrame bodyPtrAbiEncodeStaticChild
  abiEncoderBytesCode emitHelperProps exprLoweringProps compileEnv emitHelper
  ptrDiscipline fragGasPathPtr venomExecSemantics venomState venomInst
  words arithmetic list rich_list

Theorem abi_encode_bytes_suffix_trace:
  abi_encode_bytes_suffix len st = (out,en) ==>
  ?rounded mid. abi_encode_round len st = (rounded,mid) /\
    emit_op ADD [Lit 32w;rounded] mid = (out,en) /\
    mid.cs_next_var = st.cs_next_var+2 /\ en.cs_next_var = mid.cs_next_var+1 /\
    emitted_insts st en = emitted_insts st mid ++ emitted_insts mid en /\
    LENGTH (emitted_insts st mid) = 2
Proof
  simp_tac bool_ss [abi_encode_bytes_suffix_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  imp_res_tac abi_encode_round_trace >> imp_res_tac emitted_insts_emit_op >> simp[] >>
  simp_tac bool_ss [emitted_insts_def] >> asm_rewrite_tac[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[DROP_LENGTH_APPEND]
QED

Theorem abi_encode_bytes_suffix_framed_path:
  abi_encode_bytes_suffix len st = (out,en) /\
  eval_operand len s = SOME (n2w cnt) /\ op_taint tn len = {} /\
  cnt+31 < dimword(:256) /\ ~ctx_has_dalloca ctx /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st en) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?p t H un. out = Var p /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H un (OK t) /\
    abi_encode_read_frame st s G tn t H un /\
    lookup_var p t = SOME (n2w (32+contractABI$ceil32 cnt)) /\
    op_taint un (Var p) = {} /\ not_fresh_at en p /\
    fresh_vars_wrt limit_st t /\ t.vs_inst_idx = s.vs_inst_idx+3
Proof
  strip_tac >> drule abi_encode_bytes_suffix_trace >> strip_tac >>
  `isPREFIX (emitted_insts st mid) (DROP s.vs_inst_idx bb.bb_instructions) /\
   isPREFIX (emitted_insts mid en) (DROP (s.vs_inst_idx+2) bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX _ _` mp_tac >> asm_rewrite_tac[] >>
     strip_tac >> drule abi_encode_static_child_sites >> simp[]) >>
  `mid.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all abi_encode_round_framed_path >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >> gvs[] >>
  drule_all abi_encode_read_frame_control >> strip_tac >>
  `eval_operand (Lit 32w) t = SOME (32w:bytes32) /\ op_taint un (Lit 32w) = {} /\
   eval_operand (Var p) t = SOME (n2w (contractABI$ceil32 cnt)) /\
   isPREFIX (emitted_insts mid en) (DROP t.vs_inst_idx bb.bb_instructions) /\
   en.cs_next_var <= limit_st.cs_next_var` by simp[eval_operand_def, op_taint_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`, `w` |-> `a+b:bytes32`]
    (SPEC_ALL abi_encode_clean_binary_framed_path))) >>
  disch_then (qspecl_then [`PG`, `H`, `D`] strip_assume_tac) >> gvs[] >>
  drule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  `st.cs_next_var <= mid.cs_next_var` by decide_tac >>
  `abi_encode_read_frame st s G tn t' H' un'` by metis_tac[abi_encode_read_frame_then] >>
  qexistsl_tac [`t'`, `H'`, `un'`] >> simp[word_add_n2w]
QED
