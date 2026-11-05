(* Exact counted write/copy phases of the bytestring encoder. *)
Theory bodyPtrAbiEncodeBytesCopy
Ancestors
  bodyPtrAbiEncodeCleanCopy bodyPtrAbiEncodeCleanStore bodyPtrAbiEncodeRound
  bodyPtrAbiEncodeCursorFrame bodyPtrAbiEncodeStaticChild bodyPtrDefs
  abiEncoderBytesCode emitHelperProps exprLoweringProps compileEnv emitHelper
  fragGasPathPtr venomExecSemantics venomState venomInst ptrDiscipline
  words arithmetic list rich_list pred_set finite_map

Theorem abi_encode_bytes_copy_trace:
  abi_encode_bytes_copy dst src len lastptr st = ((),en) ==>
  ?c1 c2 copylen.
    emit_void MSTORE [lastptr;Lit 0w] st = ((),c1) /\
    emit_op ADD [Lit 32w;len] c1 = (copylen,c2) /\
    emit_void MCOPY [dst;src;copylen] c2 = ((),en) /\
    c1.cs_next_var = st.cs_next_var /\ c2.cs_next_var = st.cs_next_var+1 /\
    en.cs_next_var = c2.cs_next_var /\
    emitted_insts st en = emitted_insts st c1 ++ emitted_insts c1 c2 ++ emitted_insts c2 en /\
    LENGTH (emitted_insts st c1) = 1 /\ LENGTH (emitted_insts c1 c2) = 1
Proof
  simp_tac bool_ss [abi_encode_bytes_copy_def, comp_bind_def, comp_ignore_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac emitted_insts_emit_void >> imp_res_tac emitted_insts_emit_op >> simp[] >>
  simp_tac bool_ss [emitted_insts_def] >> asm_rewrite_tac[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[DROP_LENGTH_APPEND]
QED

Theorem abi_encode_bytes_store_add_path:
  emit_void MSTORE [Var lastptr;Lit 0w] st = ((),mid) /\
  emit_op ADD [Lit 32w;len] mid = (out,en) /\
  lookup_var lastptr s = SOME a /\ ptr_covers G tn lastptr s 32 /\
  eval_operand len s = SOME (n2w cnt) /\ op_taint tn len = {} /\
  ~ctx_has_dalloca ctx /\ en.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st s /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st mid) (DROP s.vs_inst_idx bb.bb_instructions) /\
  isPREFIX (emitted_insts mid en) (DROP (s.vs_inst_idx+1) bb.bb_instructions) ==>
  ?p t H un. out = Var p /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H un (OK t) /\
    abi_encode_read_frame mid (mstore (w2n a) 0w s) G
      (tn with t_mem := tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a+32}) t H un /\
    lookup_var p t = SOME (n2w (32+cnt)) /\ op_taint un (Var p) = {} /\
    not_fresh_at en p /\ fresh_vars_wrt limit_st t /\ t.vs_inst_idx = s.vs_inst_idx+2
Proof
  strip_tac >>
  `eval_operand (Lit 0w) s = SOME (0w:bytes32) /\ op_taint tn (Lit 0w) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all abi_encode_clean_store_checked_path >>
  disch_then (qspecl_then [`PG`, `D`] assume_tac) >>
  qabbrev_tac `stored = (mstore (w2n a) 0w s) with vs_inst_idx := s.vs_inst_idx+1` >>
  qabbrev_tac `clean = tn with t_mem := tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a+32}` >>
  `eval_operand (Lit 32w) stored = SOME (32w:bytes32) /\
   eval_operand len stored = SOME (n2w cnt) /\
   op_taint clean (Lit 32w) = {} /\ op_taint clean len = {} /\
   fresh_vars_wrt limit_st stored /\ ~stored.vs_halted /\
   lookup_block stored.vs_current_bb fn.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts mid en) (DROP stored.vs_inst_idx bb.bb_instructions)` by
    (gvs[Abbr `stored`, Abbr `clean`, mstore_def, eval_operand_def, op_taint_def,
         fresh_vars_wrt_def, lookup_var_def]) >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`, `w` |-> `a+b:bytes32`]
    (SPEC_ALL abi_encode_clean_binary_framed_path))) >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >> gvs[] >>
  drule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  qexistsl_tac [`t`, `H`, `un`] >>
  gvs[Abbr `stored`, Abbr `clean`, word_add_n2w, abi_encode_read_frame_def, mstore_def]
QED

Theorem abi_encode_bytes_copy_framed_path:
  abi_encode_bytes_copy (Var dst) (Var src) len (Var lastptr) st = ((),en) /\
  not_fresh_at st dst /\ not_fresh_at st src /\
  lookup_var dst s = SOME b /\ lookup_var src s = SOME a /\ lookup_var lastptr s = SOME lp /\
  ptr_covers G tn lastptr s 32 /\ ptr_covers G tn dst s (32+cnt) /\
  ptr_covers G tn src s (32+cnt) /\
  eval_operand len s = SOME (n2w cnt) /\ op_taint tn len = {} /\
  (!i. w2n a <= i /\ i < w2n a+(32+cnt) ==> i NOTIN tn.t_mem) /\
  32+cnt < dimword(:256) /\ ~ctx_has_dalloca ctx /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st en) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t H un.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H un (OK t) /\
    abi_encode_read_frame st (mcopy (w2n b) (w2n a) (32+cnt) (mstore (w2n lp) 0w s)) G
      (tn with t_mem := (tn.t_mem DIFF {i | w2n lp <= i /\ i < w2n lp+32})
                           DIFF {i | w2n b <= i /\ i < w2n b+(32+cnt)}) t H un /\
    fresh_vars_wrt limit_st t /\ t.vs_inst_idx = s.vs_inst_idx+3
Proof
  strip_tac >> drule abi_encode_bytes_copy_trace >> strip_tac >>
  `isPREFIX (emitted_insts st c1) (DROP s.vs_inst_idx bb.bb_instructions) /\
   isPREFIX (emitted_insts c1 c2) (DROP (s.vs_inst_idx+1) bb.bb_instructions) /\
   isPREFIX (emitted_insts c2 en) (DROP (s.vs_inst_idx+2) bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX _ _` mp_tac >> asm_rewrite_tac[] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC] >> strip_tac >>
     drule abi_encode_static_child_sites >> simp[] >> strip_tac >>
     drule abi_encode_static_child_sites >> simp[]) >>
  `c2.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all abi_encode_bytes_store_add_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >> gvs[] >>
  `not_fresh_at c1 dst /\ not_fresh_at c1 src` by fs[not_fresh_at_def] >>
  `lookup_var dst t = SOME b /\ lookup_var src t = SOME a /\
   ptr_covers H un dst t (32+cnt) /\ ptr_covers H un src t (32+cnt)` by
    (gvs[abi_encode_read_frame_def, ptr_covers_def, mstore_def, lookup_var_def, op_taint_def] >>
     metis_tac[]) >>
  `eval_operand (Var p) t = SOME (n2w (32+cnt)) /\
   op_taint un (Var dst) = {} /\ op_taint un (Var src) = {} /\
   (!i. w2n a <= i /\ i < w2n a+(32+cnt) ==> i NOTIN un.t_mem)` by
    (gvs[abi_encode_read_frame_def, ptr_covers_def, eval_operand_def] >> metis_tac[]) >>
  `~t.vs_halted /\ lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
   isPREFIX (emitted_insts c2 en) (DROP t.vs_inst_idx bb.bb_instructions)` by
    gvs[abi_encode_read_frame_def, mstore_def] >>
  `32+cnt < dimword(:256)` by decide_tac >>
  drule_all abi_encode_clean_copy_checked_path >>
  disch_then (qspecl_then [`PG`, `D`] assume_tac) >>
  drule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  goal_assum $ drule_at Any >> simp[] >>
  conj_tac >-
    (gvs[abi_encode_read_frame_def, mcopy_def, write_memory_with_expansion_def,
         lookup_var_def, op_taint_def, not_fresh_at_def] >> metis_tac[]) >>
  metis_tac[abi_encode_clean_copy_fresh]
QED
