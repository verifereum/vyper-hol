(* Counted bytes-prefix execution: source length, rounding, last-word address. *)
Theory bodyPtrAbiEncodeBytesPrefix
Ancestors
  bodyPtrAbiEncodeRound bodyPtrAbiEncodeCursorFrame bodyPtrAbiEncodeCleanStore
  bodyPtrAbiEncodeStaticChild abiEncoderBytesPrefix abiEncoderBytesCode
  emitHelperProps exprLoweringProps compileEnv emitHelper ptrDiscipline
  fragGasPathPtr venomExecSemantics venomState venomInst words arithmetic list rich_list

Theorem abi_encode_bytes_prefix_trace:
  abi_encode_bytes_prefix dst src st = (ops,en) ==>
  ?len rounded lastptr c1 c2.
    ops = (len,lastptr) /\ emit_op MLOAD [src] st = (len,c1) /\
    abi_encode_round len c1 = (rounded,c2) /\
    emit_op ADD [dst;rounded] c2 = (lastptr,en) /\
    c1.cs_next_var = st.cs_next_var+1 /\ c2.cs_next_var = c1.cs_next_var+2 /\
    en.cs_next_var = c2.cs_next_var+1 /\
    LENGTH (emitted_insts st c1) = 1 /\ LENGTH (emitted_insts c1 c2) = 2 /\
    emitted_insts st en = emitted_insts st c1 ++ emitted_insts c1 c2 ++ emitted_insts c2 en
Proof
  simp_tac bool_ss [abi_encode_bytes_prefix_def, comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac abi_encode_round_trace >>
  imp_res_tac emitted_insts_emit_op >> simp[] >>
  simp_tac bool_ss [emitted_insts_def] >> asm_rewrite_tac[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[DROP_LENGTH_APPEND]
QED

Theorem abi_encode_bytes_prefix_framed_path:
  !total.
  abi_encode_bytes_prefix (Var dst) (Var src) st = (ops,en) /\
  not_fresh_at st dst /\ lookup_var dst s = SOME a /\ lookup_var src s = SOME sa /\
  op_taint tn (Var dst) = {} /\ ptr_covers G tn dst s total /\ ptr_covers G tn src s 32 /\
  (!i. w2n sa <= i /\ i < w2n sa+32 ==> i NOTIN tn.t_mem) /\
  mload (w2n sa) s = n2w cnt /\ cnt+31 < dimword(:256) /\
  contractABI$ceil32 cnt+32 <= total /\ w2n a+contractABI$ceil32 cnt < dimword(:256) /\
  ~ctx_has_dalloca ctx /\ en.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st s /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st en) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?lp last t H un. ops = (Var lp,Var last) /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H un (OK t) /\
    abi_encode_read_frame st s G tn t H un /\
    lookup_var lp t = SOME (n2w cnt) /\ op_taint un (Var lp) = {} /\
    lookup_var last t = SOME (a+n2w (contractABI$ceil32 cnt)) /\
    ptr_covers H un last t 32 /\ op_taint un (Var last) = {} /\
    not_fresh_at en lp /\ not_fresh_at en last /\
    fresh_vars_wrt limit_st t /\ t.vs_inst_idx = s.vs_inst_idx+4
Proof
  gen_tac >> strip_tac >> drule abi_encode_bytes_prefix_trace >> strip_tac >> gvs[] >>
  `isPREFIX (emitted_insts st c1) (DROP s.vs_inst_idx bb.bb_instructions) /\
   isPREFIX (emitted_insts c1 c2) (DROP (s.vs_inst_idx+1) bb.bb_instructions) /\
   isPREFIX (emitted_insts c2 en) (DROP (s.vs_inst_idx+3) bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX _ _` mp_tac >> asm_rewrite_tac[] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC] >> strip_tac >>
     drule abi_encode_static_child_sites >> simp[] >> strip_tac >>
     drule abi_encode_static_child_sites >> simp[]) >>
  `c1.cs_next_var <= limit_st.cs_next_var /\ c2.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all abi_encode_cursor_load_framed_path >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >> gvs[] >>
  drule_all abi_encode_read_frame_control >> strip_tac >>
  `eval_operand (Var p) t = SOME (n2w cnt) /\
   isPREFIX (emitted_insts c1 c2) (DROP t.vs_inst_idx bb.bb_instructions) /\
   c2.cs_next_var <= limit_st.cs_next_var` by simp[eval_operand_def] >>
  drule_all abi_encode_round_framed_path >>
  disch_then (qspecl_then [`PG`, `H`, `D`] strip_assume_tac) >> gvs[] >>
  `st.cs_next_var <= c1.cs_next_var /\ c1.cs_next_var <= c2.cs_next_var` by decide_tac >>
  `abi_encode_read_frame st s G tn t' H' un'` by metis_tac[abi_encode_read_frame_then] >>
  `lookup_var dst t' = SOME a /\ op_taint un' (Var dst) = {} /\
   ptr_covers H' un' dst t' total'` by
    metis_tac[abi_encode_read_frame_lookup, abi_encode_read_frame_taint, abi_encode_read_frame_covers] >>
  `not_fresh_at c2 dst` by (fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
  drule_all abi_encode_read_frame_control >> strip_tac >>
  `eval_operand (Var p') t' = SOME (n2w (contractABI$ceil32 cnt)) /\
   isPREFIX (emitted_insts c2 en) (DROP t'.vs_inst_idx bb.bb_instructions) /\
   en.cs_next_var <= limit_st.cs_next_var /\
   (0<32 ==> ptr_covers H' un' dst t' total' /\ w2n a+contractABI$ceil32 cnt < dimword(:256))` by
    simp[eval_operand_def] >>
  drule_all abi_encode_scalar_add_framed_path >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >> gvs[] >>
  drule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  qpat_x_assum `gas_path_ptr _ _ _ _ _ H' un' t' _ _ _ _` kall_tac >>
  qpat_x_assum `gas_path_ptr _ _ _ _ _ H un t _ H' un' _` kall_tac >>
  drule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  `st.cs_next_var <= c2.cs_next_var /\ c1.cs_next_var <= c2.cs_next_var` by decide_tac >>
  `abi_encode_read_frame st s G tn t'' H'' un''` by metis_tac[abi_encode_read_frame_then] >>
  `not_fresh_at c2 p /\ not_fresh_at en p` by
    (fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS, LESS_EQ_ADD]) >>
  `lookup_var p t'' = SOME (n2w cnt) /\ op_taint un'' (Var p) = {}` by
    metis_tac[abi_encode_read_frame_lookup, abi_encode_read_frame_taint] >>
  qexistsl_tac [`t''`, `H''`, `un''`] >> simp[]
QED
