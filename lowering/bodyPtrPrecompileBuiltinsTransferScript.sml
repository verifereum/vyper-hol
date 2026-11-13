Theory bodyPtrPrecompileBuiltinsTransfer
Ancestors bodyPtrPrecompileBuiltinsStaging bodyPtrPrecompileBuiltinsSeq
          venomExecSemantics venomState venomInst ptrDiscipline bodyPtrDefs
          exprLoweringProps fragExec finite_map list emitHelper compileEnv loweringStateRelDefs
          context contextCodegenRelProps rich_list

Theorem point_word_read_trace:
  ptr_covers G tn root s capacity /\ lookup_var root s = SOME a /\
  off + 32 <= capacity /\ w2n a + off < dimword (:256) /\
  (!i. w2n (a + n2w off) <= i /\ i < w2n (a + n2w off) + 32 ==>
    i NOTIN tn.t_mem) /\ ~ctx_has_dalloca ctx ==>
  ?t G' tn'.
    run_inst_seq [mk_inst id ADD [Var root; Lit (n2w off)] [src];
      mk_inst (id+1) MLOAD [Var src] [tmp]] s = OK t /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id ADD [Var root; Lit (n2w off)] [src];
       mk_inst (id+1) MLOAD [Var src] [tmp]]
      (s with vs_inst_idx := k) G' tn') /\
    lookup_var tmp t = SOME (mload (w2n (a + n2w off)) s) /\
    op_taint tn' (Var tmp) = {} /\ t.vs_memory = s.vs_memory /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\
    (!p. p <> src /\ p <> tmp ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all point_offset_trace_cursors >>
  disch_then (qspec_then `src` mp_tac) >>
  disch_then (qspec_then `id` mp_tac) >>
  disch_then (mp_tac o SPEC_ALL) >>
  disch_then (qx_choose_then `s1` (qx_choose_then `G1`
    (qx_choose_then `tn1` strip_assume_tac))) >>
  `!i. w2n (a + n2w off) <= i /\ i < w2n (a + n2w off) + 32 ==>
      i NOTIN tn1.t_mem` by simp[] >>
  drule_all clean_word_load_trace_cursors >>
  disch_then (qspec_then `tmp` mp_tac) >>
  disch_then (qspec_then `id+1` mp_tac) >>
  disch_then (mp_tac o SPEC_ALL) >>
  disch_then (qx_choose_then `s2` (qx_choose_then `G2`
    (qx_choose_then `tn2` strip_assume_tac))) >>
  qexistsl [`s2`, `G2`, `tn2`] >>
  conj_tac
  >- (qsuff_tac `run_inst_seq
        ([mk_inst id ADD [Var root; Lit (n2w off)] [src]] ++
         [mk_inst (id+1) MLOAD [Var src] [tmp]]) s = OK s2`
      >- simp[] >>
      rev_drule run_inst_seq_append >> simp[]) >>
  conj_tac
  >- (qsuff_tac `!k. inst_seq_ptr D 0 ctx fn PG G tn
        ([mk_inst id ADD [Var root; Lit (n2w off)] [src]] ++
         [mk_inst (id+1) MLOAD [Var src] [tmp]])
        (s with vs_inst_idx := k) G2 tn2`
      >- simp[] >>
      irule inst_seq_ptr_append_cursors >>
      reverse conj_tac >- simp[mk_inst_def, is_terminator_def] >>
      qexistsl [`G1`, `s1`, `tn1`] >>
      simp[mk_inst_def, is_terminator_def]) >>
  simp[mload_def] >> metis_tac[]
QED

Theorem offset_word_store_trace:
  ptr_covers G tn bufroot s capacity /\ lookup_var bufroot s = SOME a /\
  off + 32 <= capacity /\ w2n a + off < dimword (:256) /\
  eval_operand v s = SOME w /\ op_taint tn v = {} /\
  (!p. v = Var p ==> p <> dst) /\ ~ctx_has_dalloca ctx ==>
  ?t G' tn'.
    run_inst_seq [mk_inst id ADD [Var bufroot; Lit (n2w off)] [dst];
      mk_inst (id+1) MSTORE [Var dst; v] []] s = OK t /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id ADD [Var bufroot; Lit (n2w off)] [dst];
       mk_inst (id+1) MSTORE [Var dst; v] []]
      (s with vs_inst_idx := k) G' tn') /\
    t.vs_memory = (mstore (w2n (a + n2w off)) w s).vs_memory /\
    tn'.t_mem = tn.t_mem DIFF
      {i | w2n (a + n2w off) <= i /\ i < w2n (a + n2w off) + 32} /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    (!p. p <> dst ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all point_offset_trace_cursors >>
  disch_then (qspec_then `dst` mp_tac) >>
  disch_then (qspec_then `id` mp_tac) >>
  disch_then (mp_tac o SPEC_ALL) >>
  disch_then (qx_choose_then `s1` (qx_choose_then `G1`
    (qx_choose_then `tn1` strip_assume_tac))) >>
  `s1.vs_labels = s.vs_labels` by
    (qpat_x_assum `run_inst_seq _ s = OK s1` mp_tac >>
     simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
          exec_pure2_def, eval_operand_def, update_var_def] >>
     strip_tac >> gvs[]) >>
  `eval_operand v s1 = SOME w /\ op_taint tn1 v = {}` by
    (Cases_on `v` >> gvs[eval_operand_def, op_taint_def] >> metis_tac[]) >>
  drule_all clean_word_store_trace_cursors >>
  disch_then (qspec_then `id+1` mp_tac) >>
  disch_then (mp_tac o SPEC_ALL) >>
  disch_then (qx_choose_then `s2` (qx_choose_then `tn2` strip_assume_tac)) >>
  qexistsl [`s2`, `G1`, `tn2`] >>
  conj_tac
  >- (qsuff_tac `run_inst_seq
        ([mk_inst id ADD [Var bufroot; Lit (n2w off)] [dst]] ++
         [mk_inst (id+1) MSTORE [Var dst; v] []]) s = OK s2`
      >- simp[] >> rev_drule run_inst_seq_append >> simp[]) >>
  conj_tac
  >- (qsuff_tac `!k. inst_seq_ptr D 0 ctx fn PG G tn
        ([mk_inst id ADD [Var bufroot; Lit (n2w off)] [dst]] ++
         [mk_inst (id+1) MSTORE [Var dst; v] []])
        (s with vs_inst_idx := k) G1 tn2`
      >- simp[] >> irule inst_seq_ptr_append_cursors >>
      reverse conj_tac >- simp[mk_inst_def, is_terminator_def] >>
      qexistsl [`G1`, `s1`, `tn1`] >> simp[]) >>
  simp[] >> conj_tac
  >- simp[mstore_def, write_memory_with_expansion_def] >>
  rpt strip_tac >>
  qpat_x_assum `!p. p <> dst ==> _` (qspec_then `p` mp_tac) >>
  simp[] >> strip_tac >>
  gvs[lookup_var_def, mstore_def, write_memory_with_expansion_def, op_taint_def]
QED

Theorem point_word_transfer_trace:
  !src tmp dst id.
  ptr_covers G tn root s capacity /\ lookup_var root s = SOME a /\
  ptr_covers G tn bufroot s bufsize /\ lookup_var bufroot s = SOME b /\
  off + 32 <= capacity /\ w2n a + off < dimword (:256) /\
  dstoff + 32 <= bufsize /\ w2n b + dstoff < dimword (:256) /\
  (!i. w2n (a + n2w off) <= i /\ i < w2n (a + n2w off) + 32 ==>
    i NOTIN tn.t_mem) /\
  bufroot <> src /\ bufroot <> tmp /\ tmp <> dst /\
  ~ctx_has_dalloca ctx ==>
  ?t G' tn'.
    run_inst_seq [mk_inst id ADD [Var root; Lit (n2w off)] [src];
      mk_inst (id+1) MLOAD [Var src] [tmp];
      mk_inst (id+2) ADD [Var bufroot; Lit (n2w dstoff)] [dst];
      mk_inst (id+3) MSTORE [Var dst; Var tmp] []] s = OK t /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id ADD [Var root; Lit (n2w off)] [src];
       mk_inst (id+1) MLOAD [Var src] [tmp];
       mk_inst (id+2) ADD [Var bufroot; Lit (n2w dstoff)] [dst];
       mk_inst (id+3) MSTORE [Var dst; Var tmp] []]
      (s with vs_inst_idx := k) G' tn') /\
    t.vs_memory = (mstore (w2n (b + n2w dstoff))
      (mload (w2n (a + n2w off)) s) s).vs_memory /\
    tn'.t_mem = tn.t_mem DIFF
      {i | w2n (b + n2w dstoff) <= i /\ i < w2n (b + n2w dstoff) + 32} /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    (!p. p <> src /\ p <> tmp /\ p <> dst ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> strip_tac >> drule_all point_word_read_trace >>
  disch_then (qspecl_then [`tmp`, `src`, `id`] mp_tac) >>
  disch_then (mp_tac o SPEC_ALL) >>
  disch_then (qx_choose_then `s1` (qx_choose_then `G1`
    (qx_choose_then `tn1` strip_assume_tac))) >>
  `lookup_var bufroot s1 = SOME b /\ ptr_covers G1 tn1 bufroot s1 bufsize` by
    (qpat_assum `!p. p <> src /\ p <> tmp ==> _`
       (qspec_then `bufroot` mp_tac) >> gvs[ptr_covers_def]) >>
  `eval_operand (Var tmp) s1 = SOME (mload (w2n (a + n2w off)) s)` by
    simp[eval_operand_def] >>
  `!p. Var tmp = Var p ==> p <> dst` by simp[] >>
  drule_all offset_word_store_trace >>
  disch_then (qspec_then `id+2` mp_tac) >>
  disch_then (mp_tac o SPEC_ALL) >>
  disch_then (qx_choose_then `s2` (qx_choose_then `G2`
    (qx_choose_then `tn2` strip_assume_tac))) >>
  qexistsl [`s2`, `G2`, `tn2`] >> suspend "compose"
QED

Resume point_word_transfer_trace[compose]:
  rpt (qpat_x_assum `ptr_covers _ _ _ _ _` kall_tac) >>
  qmatch_asmsub_abbrev_tac `run_inst_seq xs s = OK s1` >>
  qmatch_asmsub_abbrev_tac `run_inst_seq ys s1 = OK s2` >>
  `EVERY (\i. ~is_terminator i.inst_opcode) xs` by
    simp[Abbr `xs`, mk_inst_def, is_terminator_def] >>
  `run_inst_seq (xs ++ ys) s = OK s2` by
    (rev_drule run_inst_seq_append >> simp[]) >>
  `!k. inst_seq_ptr D 0 ctx fn PG G tn (xs ++ ys)
      (s with vs_inst_idx := k) G2 tn2` by
    (irule inst_seq_ptr_append_cursors >> reverse conj_tac >- simp[] >>
     qexistsl [`G1`, `s1`, `tn1`] >> simp[]) >>
  gvs[Abbr `xs`, Abbr `ys`] >>
  simp[mstore_def, write_memory_with_expansion_def]
QED

Finalise point_word_transfer_trace

Theorem point_word_transfer_code:
  (do src <- emit_op ADD [Var root; Lit (n2w off)];
      value <- emit_op MLOAD [src];
      dst <- emit_op ADD [Var bufroot; Lit (n2w dstoff)];
      emit_void MSTORE [dst; value] od) sa = ((),sb) ==>
  ?src tmp dst.
    emitted_insts sa sb =
      [mk_inst sa.cs_next_id ADD [Var root; Lit (n2w off)] [src];
       mk_inst (sa.cs_next_id+1) MLOAD [Var src] [tmp];
       mk_inst (sa.cs_next_id+2) ADD [Var bufroot; Lit (n2w dstoff)] [dst];
       mk_inst (sa.cs_next_id+3) MSTORE [Var dst; Var tmp] []] /\
    (!p. not_fresh_at sa p ==> p <> src /\ p <> tmp /\ p <> dst) /\
    tmp <> dst /\ sa.cs_next_var <= sb.cs_next_var
Proof
  simp[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  qexistsl [`STRING #"%" (toString sa.cs_next_var)`,
    `STRING #"%" (toString (sa.cs_next_var+1))`,
    `STRING #"%" (toString (sa.cs_next_var+2))`] >>
  simp[emitted_insts_def, DROP_APPEND1] >>
  rpt strip_tac >> gvs[not_fresh_at_def] >>
  first_x_assum irule >> decide_tac
QED

Theorem emitted_point_word_transfer_checked:
  (do src <- emit_op ADD [Var root; Lit (n2w off)];
      value <- emit_op MLOAD [src];
      dst <- emit_op ADD [Var bufroot; Lit (n2w dstoff)];
      emit_void MSTORE [dst; value] od) sa = ((),sb) /\
  ptr_covers G tn root s capacity /\ lookup_var root s = SOME a /\
  ptr_covers G tn bufroot s bufsize /\ lookup_var bufroot s = SOME b /\
  off + 32 <= capacity /\ w2n a + off < dimword (:256) /\
  dstoff + 32 <= bufsize /\ w2n b + dstoff < dimword (:256) /\
  (!i. w2n (a + n2w off) <= i /\ i < w2n (a + n2w off) + 32 ==>
    i NOTIN tn.t_mem) /\
  not_fresh_at sa root /\ not_fresh_at sa bufroot /\ ~ctx_has_dalloca ctx ==>
  ?t G' tn'.
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) G' tn') /\
    t.vs_memory = (mstore (w2n (b + n2w dstoff))
      (mload (w2n (a + n2w off)) s) s).vs_memory /\
    tn'.t_mem = tn.t_mem DIFF
      {i | w2n (b + n2w dstoff) <= i /\ i < w2n (b + n2w dstoff) + 32} /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP G' p = FLOOKUP G p /\
      op_taint tn' (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule point_word_transfer_code >>
  disch_then (qx_choose_then `src` (qx_choose_then `tmp`
    (qx_choose_then `dst` strip_assume_tac))) >>
  `bufroot <> src /\ bufroot <> tmp /\ tmp <> dst` by metis_tac[] >>
  qspecl_then [`src`, `tmp`, `dst`, `sa.cs_next_id`] mp_tac
    point_word_transfer_trace >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `t` (qx_choose_then `Gf`
    (qx_choose_then `tnf` strip_assume_tac))) >>
  qexistsl [`t`, `Gf`, `tnf`] >> simp[] >> metis_tac[]
QED

Theorem emitted_point_word_transfer_keeps_covers:
  (do src <- emit_op ADD [Var root; Lit (n2w off)];
      value <- emit_op MLOAD [src];
      dst <- emit_op ADD [Var bufroot; Lit (n2w dstoff)];
      emit_void MSTORE [dst; value] od) sa = ((),sb) /\
  ptr_covers G tn root s capacity /\ lookup_var root s = SOME a /\
  ptr_covers G tn bufroot s bufsize /\ lookup_var bufroot s = SOME b /\
  off + 32 <= capacity /\ w2n a + off < dimword (:256) /\
  dstoff + 32 <= bufsize /\ w2n b + dstoff < dimword (:256) /\
  (!i. w2n (a + n2w off) <= i /\ i < w2n (a + n2w off) + 32 ==>
    i NOTIN tn.t_mem) /\
  not_fresh_at sa root /\ not_fresh_at sa bufroot /\ ~ctx_has_dalloca ctx ==>
  ?t G' tn'.
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    (!k. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb)
      (s with vs_inst_idx := k) G' tn') /\
    ptr_covers G' tn' root t capacity /\ ptr_covers G' tn' bufroot t bufsize
Proof
  strip_tac >> drule_all emitted_point_word_transfer_checked >>
  disch_then (mp_tac o SPEC_ALL) >>
  disch_then (qx_choose_then `t` (qx_choose_then `Gf`
    (qx_choose_then `tnf` strip_assume_tac))) >>
  qexistsl [`t`, `Gf`, `tnf`] >> simp[] >>
  conj_tac >> gvs[ptr_covers_def] >> metis_tac[]
QED

Theorem point_word_transfer_progress:
  (do src <- emit_op ADD [Var root; Lit (n2w off)];
      value <- emit_op MLOAD [src];
      dst <- emit_op ADD [Var bufroot; Lit (n2w dstoff)];
      emit_void MSTORE [dst; value] od) sa = ((),sb) ==>
  sa.cs_next_var <= sb.cs_next_var /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
  EVERY (\i. i.inst_opcode = ALLOCA \/ i.inst_opcode = ADD \/
    i.inst_opcode = MLOAD \/ i.inst_opcode = MSTORE) (emitted_insts sa sb)
Proof
  strip_tac >> drule point_word_transfer_code >> strip_tac >>
  simp[mk_inst_def, is_terminator_def]
QED
