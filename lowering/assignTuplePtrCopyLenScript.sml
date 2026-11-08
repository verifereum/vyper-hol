(* Counted bytestring copy-length computation and its ghost frames. *)
Theory assignTuplePtrCopyLen
Ancestors
  assignTuplePtrLocalBytesCopy bodyPtrDefs emitHelperProps exprLoweringProps
  emitHelper compileEnv context venomState venomExecSemantics venomInst
  ptrDiscipline finite_map list arithmetic words freshWrites

Theorem ptr_covers_lookup_frame:
  ptr_covers G tn p s n /\
  lookup_var p t = lookup_var p s /\ FLOOKUP G' p = FLOOKUP G p /\
  op_taint tn' (Var p) = op_taint tn (Var p) ==>
  ptr_covers G' tn' p t n
Proof
  simp[ptr_covers_def]
QED

Theorem emitted_insts_join_normalized_ptr:
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  sc.cs_current_insts = sb.cs_current_insts ++ emitted_insts sb sc /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sb sc) /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK (t with vs_inst_idx := s.vs_inst_idx) /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G1 tn1 /\
  run_inst_seq (emitted_insts sb sc) t = OK (u with vs_inst_idx := t.vs_inst_idx) /\
  u.vs_inst_idx = LENGTH sc.cs_current_insts /\
  inst_seq_ptr D 0 ctx fn PG G1 tn1 (emitted_insts sb sc) t G2 tn2 ==>
  run_inst_seq (emitted_insts sa sc) s = OK (u with vs_inst_idx := s.vs_inst_idx) /\
  inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sc) s G2 tn2 /\
  sc.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sc /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sc)
Proof
  strip_tac >>
  `emitted_insts sa sc = emitted_insts sa sb ++ emitted_insts sb sc` by
    (irule emitted_insts_append >> simp[]) >>
  `t.vs_inst_idx = s.vs_inst_idx + LENGTH (emitted_insts sa sb) /\
   u.vs_inst_idx = t.vs_inst_idx + LENGTH (emitted_insts sb sc)` by
    simp[LENGTH_APPEND] >>
  qpat_assum `run_inst_seq (emitted_insts sa sb) s = _`
    (mp_then (Pat `run_inst_seq xs s = _`) mp_tac inst_seq_ptr_append_normalized) >>
  disch_then drule_all >> strip_tac >> simp[APPEND_ASSOC]
QED

Theorem copy_len_round_tail_ptr:
  emit_op AND [input; Lit (i2w (-32))] sa = (Var middle,sb) /\
  emit_op ADD [Var middle; Lit 32w] sb = (Var out,sc) /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~ctx_has_dalloca ctx /\
  eval_operand input s = SOME a /\ op_taint tn input = {} ==>
  ?Gf tnf t.
    run_inst_seq (emitted_insts sa sc) s =
      OK (t with vs_inst_idx := s.vs_inst_idx) /\
    t.vs_inst_idx = LENGTH sc.cs_current_insts /\
    t.vs_current_bb = s.vs_current_bb /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sc) s Gf tnf /\
    lookup_var out t = SOME ((a && i2w (-32)) + 32w) /\
    op_taint tnf (Var out) = {} /\
    t.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    sc.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sc /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sc)
Proof
  strip_tac >>
  qpat_assum `emit_op AND _ sa = _`
    (mp_then Any mp_tac emit_copy_len_binop_normalized_ptr) >>
  `!tn. op_taint tn (Lit (i2w (-32))) = {}` by simp[op_taint_def] >>
  simp[eval_operand_def] >> disch_then drule_all >>
  disch_then (qspecl_then [`fn`, `PG`, `G`, `D`] strip_assume_tac) >>
  rename1 `inst_seq_ptr D 0 ctx fn PG G tn _ s G1 tn1` >>
  rename1 `lookup_var middle t1 = SOME _` >>
  qpat_assum `emit_op ADD _ sb = _`
    (mp_then Any mp_tac emit_copy_len_binop_normalized_ptr) >>
  `!tn. op_taint tn (Lit 32w) = {}` by simp[op_taint_def] >>
  simp[eval_operand_def] >> disch_then drule_all >>
  disch_then (qspecl_then [`fn`, `PG`, `G1`, `D`] strip_assume_tac) >>
  rename1 `inst_seq_ptr D 0 ctx fn PG G1 tn1 _ t1 G2 tn2` >>
  rename1 `lookup_var out t2 = SOME _` >>
  imp_res_tac emitted_insts_emit_op >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
   EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sb sc)` by
    simp[mk_inst_def, is_terminator_def] >>
  `!p. not_fresh_at sa p ==> not_fresh_at sb p` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `run_inst_seq (emitted_insts sb sc) t1 =
    OK (t2 with vs_inst_idx := t1.vs_inst_idx)` by simp[] >>
  `run_inst_seq (emitted_insts sa sb) s =
    OK (t1 with vs_inst_idx := s.vs_inst_idx)` by simp[] >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
   sc.cs_current_insts = sb.cs_current_insts ++ emitted_insts sb sc` by simp[] >>
  qpat_assum `run_inst_seq (emitted_insts sa sb) s = OK (t1 with vs_inst_idx := s.vs_inst_idx)`
    (mp_then (Pat `run_inst_seq (emitted_insts sa sb) s = _`)
      mp_tac emitted_insts_join_normalized_ptr) >>
  disch_then drule_all >> strip_tac >>
  qexistsl_tac [`G2`, `tn2`, `t2`] >>
  gs[] >> metis_tac[]
QED

Theorem copy_len_arith_ptr:
  emit_op ADD [input; Lit 31w] sa = (Var first,sb) /\
  emit_op AND [Var first; Lit (i2w (-32))] sb = (Var middle,sc) /\
  emit_op ADD [Var middle; Lit 32w] sc = (Var out,sd) /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~ctx_has_dalloca ctx /\
  eval_operand input s = SOME a /\ op_taint tn input = {} ==>
  ?Gf tnf t.
    run_inst_seq (emitted_insts sa sd) s =
      OK (t with vs_inst_idx := s.vs_inst_idx) /\
    t.vs_inst_idx = LENGTH sd.cs_current_insts /\
    t.vs_current_bb = s.vs_current_bb /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sd) s Gf tnf /\
    lookup_var out t = SOME (((a + 31w) && i2w (-32)) + 32w) /\
    op_taint tnf (Var out) = {} /\
    t.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    sd.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sd /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sd)
Proof
  strip_tac >>
  qpat_assum `emit_op ADD _ sa = _`
    (mp_then Any mp_tac emit_copy_len_binop_normalized_ptr) >>
  `!tn. op_taint tn (Lit 31w) = {}` by simp[op_taint_def] >>
  simp[eval_operand_def] >> disch_then drule_all >>
  disch_then (qspecl_then [`fn`, `PG`, `G`, `D`] strip_assume_tac) >>
  rename1 `inst_seq_ptr D 0 ctx fn PG G tn _ s G1 tn1` >>
  rename1 `lookup_var first t1 = SOME _` >>
  `eval_operand (Var first) t1 = SOME (a + 31w)` by simp[eval_operand_def] >>
  drule_all copy_len_round_tail_ptr >>
  disch_then (qspecl_then [`fn`, `PG`, `G1`, `D`] strip_assume_tac) >>
  rename1 `inst_seq_ptr D 0 ctx fn PG G1 tn1 _ t1 G2 tn2` >>
  rename1 `lookup_var out t2 = SOME _` >>
  qpat_assum `emit_op ADD _ sa = _`
    (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    simp[mk_inst_def, is_terminator_def] >>
  `!p. not_fresh_at sa p ==> not_fresh_at sb p` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `run_inst_seq (emitted_insts sb sd) t1 =
    OK (t2 with vs_inst_idx := t1.vs_inst_idx)` by simp[] >>
  `run_inst_seq (emitted_insts sa sb) s =
    OK (t1 with vs_inst_idx := s.vs_inst_idx)` by simp[] >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by simp[] >>
  qpat_assum `run_inst_seq (emitted_insts sa sb) s = OK (t1 with vs_inst_idx := s.vs_inst_idx)`
    (mp_then (Pat `run_inst_seq (emitted_insts sa sb) s = _`)
      mp_tac emitted_insts_join_normalized_ptr) >>
  disch_then drule_all >> strip_tac >>
  qexistsl_tac [`G2`, `tn2`, `t2`] >> gs[] >> metis_tac[]
QED

Theorem copy_len_load_arith_ptr:
  emit_op MLOAD [Var src] sa = (Var first,sb) /\
  emit_op ADD [Var first; Lit 31w] sb = (Var second,sc) /\
  emit_op AND [Var second; Lit (i2w (-32))] sc = (Var middle,sd) /\
  emit_op ADD [Var middle; Lit 32w] sd = (Var out,se) /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~ctx_has_dalloca ctx /\
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
  ?Gf tnf t.
    run_inst_seq (emitted_insts sa se) s =
      OK (t with vs_inst_idx := s.vs_inst_idx) /\
    t.vs_inst_idx = LENGTH se.cs_current_insts /\
    t.vs_current_bb = s.vs_current_bb /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa se) s Gf tnf /\
    lookup_var out t = SOME (((mload (w2n a) s + 31w) && i2w (-32)) + 32w) /\
    op_taint tnf (Var out) = {} /\
    t.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    se.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa se /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa se)
Proof
  strip_tac >> drule_all emit_mload_clean_normalized_ptr >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  rename1 `inst_seq_ptr D 0 ctx fn PG G tn _ s G1 tn1` >>
  rename1 `lookup_var first t1 = SOME _` >>
  `eval_operand (Var first) t1 = SOME (mload (w2n a) s)` by simp[eval_operand_def] >>
  drule_all copy_len_arith_ptr >>
  disch_then (qspecl_then [`fn`, `PG`, `G1`, `D`] strip_assume_tac) >>
  rename1 `inst_seq_ptr D 0 ctx fn PG G1 tn1 _ t1 G2 tn2` >>
  rename1 `lookup_var out t2 = SOME _` >>
  qpat_assum `emit_op MLOAD _ sa = _`
    (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    simp[mk_inst_def, is_terminator_def] >>
  `!p. not_fresh_at sa p ==> not_fresh_at sb p` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `run_inst_seq (emitted_insts sb se) t1 =
    OK (t2 with vs_inst_idx := t1.vs_inst_idx)` by simp[] >>
  `run_inst_seq (emitted_insts sa sb) s =
    OK (t1 with vs_inst_idx := s.vs_inst_idx)` by simp[] >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by simp[] >>
  qpat_assum `run_inst_seq (emitted_insts sa sb) s = OK (t1 with vs_inst_idx := s.vs_inst_idx)`
    (mp_then (Pat `run_inst_seq (emitted_insts sa sb) s = _`)
      mp_tac emitted_insts_join_normalized_ptr) >>
  disch_then drule_all >> strip_tac >>
  qexistsl_tac [`G2`, `tn2`, `t2`] >> gs[] >> metis_tac[]
QED

Theorem compile_bytestring_copy_len_normalized_ptr:
  compile_bytestring_copy_len (Var src) sa = (count_op,sb) /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~ctx_has_dalloca ctx /\
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
  ?Gf tnf t.
    run_inst_seq (emitted_insts sa sb) s =
      OK (t with vs_inst_idx := s.vs_inst_idx) /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_current_bb = s.vs_current_bb /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf /\
    eval_operand count_op t =
      SOME (((mload (w2n a) s + 31w) && i2w (-32)) + 32w) /\
    op_taint tnf count_op = {} /\
    t.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==>
      lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p)) /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)
Proof
  strip_tac >>
  qpat_x_assum `compile_bytestring_copy_len _ _ = _` mp_tac >>
  simp[compile_bytestring_copy_len_def, comp_bind_def] >>
  ntac 3 (pairarg_tac >> simp[LET_THM, pairTheory.pair_case_def]) >>
  strip_tac >>
  imp_res_tac (cj 2 emitted_insts_emit_op) >>
  gvs[] >>
  drule_all copy_len_load_arith_ptr >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf`, `t`] >> simp[eval_operand_def]
QED
