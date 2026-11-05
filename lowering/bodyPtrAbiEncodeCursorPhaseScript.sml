Theory bodyPtrAbiEncodeCursorPhase
Ancestors
  bodyPtrAbiEncodeCleanStore bodyPtrAbiEncodeCursorFrame bodyPtrAbiEncodeCursor bodyPtrAbiEncodeStaticChild
  abiEncoderChildCode abiEncoderChildSuffixReach emitHelper venomInst finite_map
  bodyPtrAbiEncodeWordChecks
  emitHelperProps exprLoweringProps compileEnv ptrDiscipline
  fragGasPathPtr venomExecSemantics venomState words arithmetic list rich_list

Theorem abi_encode_cursor_three_sites[local]:
  LENGTH (emitted_insts st c1) = 1 /\
  LENGTH (emitted_insts c1 c2) = 1 /\
  emitted_insts st en = emitted_insts st c1 ++ emitted_insts c1 c2 ++ emitted_insts c2 en /\
  isPREFIX (emitted_insts st en) (DROP k code) ==>
  isPREFIX (emitted_insts st c1) (DROP k code) /\
  isPREFIX (emitted_insts c1 c2) (DROP (k+1) code) /\
  isPREFIX (emitted_insts c2 en) (DROP (k+2) code)
Proof
  strip_tac >>
  qpat_x_assum `isPREFIX _ _` mp_tac >> asm_rewrite_tac[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >> strip_tac >>
  drule abi_encode_static_child_sites >> simp[] >> strip_tac >>
  drule abi_encode_static_child_sites >> simp[]
QED

(* Loading a clean scalar cursor and adding it to the covered root. *)
Theorem abi_encode_cursor_address_framed_path:
  !total.
  emit_op MLOAD [Var cursor] st = (offset,mid) /\
  emit_op ADD [Var dst;offset] mid = (out,en) /\
  mid.cs_next_var = st.cs_next_var+1 /\ en.cs_next_var = mid.cs_next_var+1 /\
  not_fresh_at st dst /\ lookup_var dst s = SOME a /\
  lookup_var cursor s = SOME ca /\ op_taint tn (Var dst) = {} /\
  ptr_covers G tn dst s total /\ ptr_covers G tn cursor s 32 /\
  (!i. w2n ca <= i /\ i < w2n ca+32 ==> i NOTIN tn.t_mem) /\
  mload (w2n ca) s = n2w off /\ off+n <= total /\
  (0<n ==> w2n a+off < dimword(:256)) /\
  ~ctx_has_dalloca ctx /\ en.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st s /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st mid) (DROP s.vs_inst_idx bb.bb_instructions) /\
  isPREFIX (emitted_insts mid en) (DROP (s.vs_inst_idx+1) bb.bb_instructions) ==>
  ?p q t H un.
    offset = Var p /\ out = Var q /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H un (OK t) /\
    abi_encode_read_frame st s G tn t H un /\
    lookup_var p t = SOME (n2w off) /\ op_taint un (Var p) = {} /\
    lookup_var q t = SOME (a+n2w off) /\ op_taint un (Var q) = {} /\
    (0<n ==> ptr_covers H un q t n) /\
    not_fresh_at en p /\ not_fresh_at en q /\
    fresh_vars_wrt limit_st t /\ t.vs_inst_idx = s.vs_inst_idx+2
Proof
  gen_tac >> strip_tac >>
  `mid.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all abi_encode_cursor_load_framed_path >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >> gvs[] >>
  `lookup_var dst t = SOME a /\ op_taint un (Var dst) = {}` by
    metis_tac[abi_encode_read_frame_lookup, abi_encode_read_frame_taint] >>
  `ptr_covers H un dst t total'` by metis_tac[abi_encode_read_frame_covers] >>
  `not_fresh_at mid dst` by
    (fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS, LESS_EQ_ADD]) >>
  `eval_operand (Var p) t = SOME (n2w off)` by simp[eval_operand_def] >>
  drule_all abi_encode_read_frame_control >> strip_tac >>
  `isPREFIX (emitted_insts mid en) (DROP t.vs_inst_idx bb.bb_instructions) /\
   en.cs_next_var <= limit_st.cs_next_var /\ off+n <= total' /\
   (0<n ==> ptr_covers H un dst t total' /\ w2n a+off < dimword(:256))` by simp[] >>
  drule_all abi_encode_scalar_add_framed_path >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >> gvs[] >>
  drule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  `st.cs_next_var <= mid.cs_next_var` by decide_tac >>
  `abi_encode_read_frame st s G tn t' H' un'` by metis_tac[abi_encode_read_frame_then] >>
  `lookup_var p t' = SOME (n2w off)` by metis_tac[abi_encode_read_frame_lookup] >>
  `op_taint un' (Var p) = {}` by metis_tac[abi_encode_read_frame_taint] >>
  `not_fresh_at en p` by
    (fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS, LESS_EQ_ADD]) >>
  qexistsl_tac [`t'`, `H'`, `un'`] >> simp[]
QED

Theorem abi_encode_cursor_prefix_framed_path:
  !total.
  abi_encode_child_prefix (Var dst) ho (Var cursor) st = (ops,en) /\
  not_fresh_at st dst /\ not_fresh_at st cursor /\
  lookup_var dst s = SOME a /\ lookup_var cursor s = SOME ca /\
  op_taint tn (Var dst) = {} /\ ptr_covers G tn dst s total /\
  ptr_covers G tn cursor s 32 /\
  (!i. w2n ca <= i /\ i < w2n ca+32 ==> i NOTIN tn.t_mem) /\
  mload (w2n ca) s = n2w off /\ ho+32 <= total /\ off+n <= total /\
  w2n a+ho < dimword(:256) /\
  (0<n ==> w2n a+off < dimword(:256)) /\
  ~ctx_has_dalloca ctx /\ en.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st s /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st en) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?head offset child t H un.
    ops = (Var head,Var offset,Var child) /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 H un (OK t) /\
    abi_encode_read_frame st s G tn t H un /\
    lookup_var head t = SOME (a+n2w ho) /\ ptr_covers H un head t 32 /\
    lookup_var offset t = SOME (n2w off) /\ op_taint un (Var offset) = {} /\
    lookup_var child t = SOME (a+n2w off) /\ op_taint un (Var child) = {} /\
    (0<n ==> ptr_covers H un child t n) /\
    not_fresh_at en head /\ not_fresh_at en offset /\ not_fresh_at en child /\
    fresh_vars_wrt limit_st t /\ t.vs_inst_idx = s.vs_inst_idx+3
Proof
  gen_tac >> strip_tac >> drule abi_encode_cursor_prefix_trace >> strip_tac >>
  `LENGTH (emitted_insts st c1) = 1` by
    (qpat_x_assum `emit_op _ _ st = _` (mp_tac o MATCH_MP emitted_insts_emit_op) >> simp[]) >>
  `LENGTH (emitted_insts c1 c2) = 1` by
    (qpat_x_assum `emit_op _ _ c1 = _` (mp_tac o MATCH_MP emitted_insts_emit_op) >> simp[]) >>
  drule_all abi_encode_cursor_three_sites >> strip_tac >>
  `c1.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  `eval_operand (Lit (n2w ho)) s = SOME (n2w ho) /\
   op_taint tn (Lit (n2w ho)) = {} /\
   (0<32 ==> ptr_covers G tn dst s total' /\ w2n a+ho < dimword(:256))` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all abi_encode_scalar_add_framed_path >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >> gvs[] >>
  `lookup_var cursor t = SOME ca /\ lookup_var dst t = SOME a` by
    metis_tac[abi_encode_read_frame_lookup] >>
  `op_taint un (Var dst) = {}` by metis_tac[abi_encode_read_frame_taint] >>
  `ptr_covers H un cursor t 32 /\ ptr_covers H un dst t total'` by
    metis_tac[abi_encode_read_frame_covers] >>
  `!i. w2n ca <= i /\ i < w2n ca+32 ==> i NOTIN un.t_mem` by
    metis_tac[abi_encode_read_frame_clean] >>
  `mload (w2n ca) t = n2w off` by metis_tac[abi_encode_read_frame_mload] >>
  drule_all abi_encode_read_frame_control >> strip_tac >>
  `isPREFIX (emitted_insts c1 c2) (DROP t.vs_inst_idx bb.bb_instructions) /\
   isPREFIX (emitted_insts c2 en) (DROP (t.vs_inst_idx+1) bb.bb_instructions) /\
   c2.cs_next_var = c1.cs_next_var+1 /\ en.cs_next_var = c2.cs_next_var+1 /\
   en.cs_next_var <= limit_st.cs_next_var /\ off+n <= total' /\
   (0<n ==> w2n a+off < dimword(:256))` by simp[] >>
  `not_fresh_at c1 dst` by
    (fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS, LESS_EQ_ADD]) >>
  drule_all abi_encode_cursor_address_framed_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >> gvs[] >>
  drule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  `st.cs_next_var <= c1.cs_next_var` by decide_tac >>
  `abi_encode_read_frame st s G tn t' H' un'` by metis_tac[abi_encode_read_frame_then] >>
  `lookup_var p t' = SOME (a+n2w ho)` by metis_tac[abi_encode_read_frame_lookup] >>
  `ptr_covers H' un' p t' 32` by metis_tac[abi_encode_read_frame_covers] >>
  `not_fresh_at en p` by
    (fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS, LESS_EQ_ADD]) >>
  qexistsl_tac [`t'`, `H'`, `un'`] >> simp[]
QED

Theorem abi_encode_cursor_suffix_trace:
  abi_encode_child_suffix head cursor offset len st = (out,en) ==>
  ?next c1 c2.
    out = len /\
    emit_void MSTORE [head;offset] st = ((),c1) /\
    emit_op ADD [offset;len] c1 = (next,c2) /\
    emit_void MSTORE [cursor;next] c2 = ((),en) /\
    c1.cs_next_var = st.cs_next_var /\
    c2.cs_next_var = c1.cs_next_var+1 /\ en.cs_next_var = c2.cs_next_var /\
    emitted_insts st en = emitted_insts st c1 ++ emitted_insts c1 c2 ++ emitted_insts c2 en
Proof
  simp_tac bool_ss [abi_encode_child_suffix_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
  simp[emitted_insts_def] >> pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND]
QED

Theorem abi_encode_cursor_advance_framed_path:
  emit_op ADD [Var offset;len_op] st = (next,mid) /\
  emit_void MSTORE [Var cursor;next] mid = ((),en) /\
  not_fresh_at st offset /\ not_fresh_at st cursor /\
  lookup_var offset s = SOME (n2w off) /\ eval_operand len_op s = SOME (n2w len) /\
  lookup_var cursor s = SOME (n2w p) /\ p < dimword(:256) /\
  op_taint tn (Var offset) = {} /\ op_taint tn len_op = {} /\
  ptr_covers G tn cursor s 32 /\
  ~ctx_has_dalloca ctx /\ en.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st s /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st mid) (DROP s.vs_inst_idx bb.bb_instructions) /\
  isPREFIX (emitted_insts mid en) (DROP (s.vs_inst_idx+1) bb.bb_instructions) ==>
  ?t H un.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H un (OK t) /\
    abi_encode_read_frame st (mstore p (n2w (off+len)) s) G
      (tn with t_mem := tn.t_mem DIFF {i | p <= i /\ i < p+32}) t H un /\
    fresh_vars_wrt limit_st t /\ t.vs_inst_idx = s.vs_inst_idx+2
Proof
  strip_tac >>
  `en.cs_next_var = mid.cs_next_var` by
    (drule emitted_insts_emit_void >> simp[]) >>
  `mid.cs_next_var <= limit_st.cs_next_var` by simp[] >>
  `len+0 <= len /\ (0<0 ==> ptr_covers G tn offset s len /\
    w2n (n2w off:bytes32)+len < dimword(:256))` by simp[] >>
  drule_all abi_encode_scalar_add_framed_path >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >> gvs[] >>
  `lookup_var cursor t = SOME (n2w p) /\ ptr_covers H un cursor t 32` by
    metis_tac[abi_encode_read_frame_lookup, abi_encode_read_frame_covers] >>
  drule_all abi_encode_read_frame_control >> strip_tac >>
  `eval_operand (Var p') t = SOME (n2w (off+len))` by
    simp[eval_operand_def, word_add_n2w] >>
  `isPREFIX (emitted_insts mid en) (DROP t.vs_inst_idx bb.bb_instructions)` by simp[] >>
  drule_all abi_encode_clean_store_checked_path >>
  disch_then (qspecl_then [`PG`, `D`] assume_tac) >>
  drule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  qexistsl_tac [`(mstore p (n2w (off+len)) t) with vs_inst_idx := t.vs_inst_idx+1`,
    `H`, `un with t_mem := un.t_mem DIFF {i | p <= i /\ i < p+32}`] >>
  simp[w2n_n2w, LESS_MOD] >> conj_tac
  >- (irule abi_encode_read_frame_store >> simp[]) >>
  irule abi_encode_clean_store_fresh >> simp[]
QED

Theorem abi_encode_cursor_suffix_framed_path:
  abi_encode_child_suffix (Var head) (Var cursor) (Var offset) len_op st = (out,en) /\
  not_fresh_at st cursor /\ not_fresh_at st offset /\
  lookup_var head s = SOME (n2w h) /\ lookup_var cursor s = SOME (n2w p) /\
  lookup_var offset s = SOME (n2w off) /\ eval_operand len_op s = SOME (n2w len) /\
  h < dimword(:256) /\ p < dimword(:256) /\
  ptr_covers G tn head s 32 /\ ptr_covers G tn cursor s 32 /\
  op_taint tn (Var offset) = {} /\ op_taint tn len_op = {} /\
  abi_decoder_operand_live st.cs_next_var len_op /\
  ~ctx_has_dalloca ctx /\ en.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st s /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st en) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t H un.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H un (OK t) /\
    eval_operand out t = SOME (n2w len) /\
    abi_encode_read_frame st (mstore p (n2w (off+len)) (mstore h (n2w off) s)) G
      (tn with t_mem := tn.t_mem DIFF
        ({i | h <= i /\ i < h+32} UNION {i | p <= i /\ i < p+32})) t H un /\
    fresh_vars_wrt limit_st t /\ t.vs_inst_idx = s.vs_inst_idx+3
Proof
  strip_tac >> drule abi_encode_cursor_suffix_trace >> strip_tac >>
  `LENGTH (emitted_insts st c1) = 1` by
    (qpat_x_assum `emit_void _ _ st = _` (mp_tac o MATCH_MP emitted_insts_emit_void) >> simp[]) >>
  `LENGTH (emitted_insts c1 c2) = 1` by
    (drule emitted_insts_emit_op >> simp[]) >>
  drule_all abi_encode_cursor_three_sites >> strip_tac >> gvs[] >>
  `eval_operand (Var offset) s = SOME (n2w off)` by simp[eval_operand_def] >>
  drule_all abi_encode_clean_store_checked_path >>
  disch_then (qspecl_then [`PG`, `D`] assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx fn PG G tn s 0 G clean (OK stored)` >>
  `lookup_var offset stored = SOME (n2w off) /\
   lookup_var cursor stored = SOME (n2w p) /\ eval_operand len_op stored = SOME (n2w len) /\
   op_taint clean (Var offset) = {} /\ op_taint clean len_op = {} /\
   ~stored.vs_halted /\ lookup_block stored.vs_current_bb fn.fn_blocks = SOME bb /\
   stored.vs_inst_idx = s.vs_inst_idx+1` by
    fs[Abbr `stored`, Abbr `clean`, mstore_def, lookup_var_def,
      eval_operand_def, op_taint_def] >>
  `ptr_covers G clean cursor stored 32` by
    (metis_tac[abi_encode_clean_store_covers]) >>
  `fresh_vars_wrt limit_st stored` by
    (simp[Abbr `stored`] >> irule abi_encode_clean_store_fresh >> simp[]) >>
  `not_fresh_at c1 offset /\ not_fresh_at c1 cursor /\
   isPREFIX (emitted_insts c1 c2) (DROP stored.vs_inst_idx bb.bb_instructions) /\
   isPREFIX (emitted_insts c2 en) (DROP (stored.vs_inst_idx+1) bb.bb_instructions)` by
    fs[not_fresh_at_def] >>
  `en.cs_next_var <= limit_st.cs_next_var` by simp[] >>
  drule_all abi_encode_cursor_advance_framed_path >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  drule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  `abi_encode_read_frame st (mstore p (n2w (off+len)) (mstore h (n2w off) s)) G
    (tn with t_mem := tn.t_mem DIFF
      ({i | h <= i /\ i < h+32} UNION {i | p <= i /\ i < p+32})) t H un` by
    (`(clean with t_mem := clean.t_mem DIFF {i | p <= i /\ i < p+32}) =
       (tn with t_mem := tn.t_mem DIFF
         ({i | h <= i /\ i < h+32} UNION {i | p <= i /\ i < p+32}))` by
       (simp[Abbr `clean`, taint_component_equality, pred_setTheory.EXTENSION] >> metis_tac[]) >>
     qpat_x_assum `abi_encode_read_frame c1 _ _ _ _ _ _` mp_tac >>
     simp[Abbr `stored`, abi_encode_mstore_inst_idx, w2n_n2w, LESS_MOD] >>
     metis_tac[abi_encode_read_frame_weaken, arithmeticTheory.LESS_EQ_REFL]) >>
  `eval_operand len_op t = SOME (n2w len)` by
    (drule_all abi_encode_read_frame_eval >>
     simp[eval_operand_mstore]) >>
  qexistsl_tac [`t`, `H`, `un`] >> simp[] >> metis_tac[ADD_COMM]
QED
