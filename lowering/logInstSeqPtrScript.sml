(* Successful straight-line pointer sequences, with explicit cursors. *)
Theory logInstSeqPtr
Ancestors
  fragGasSeqPtr fragExec instIdxIndep ghostPcTransportPtr exprLoweringProps
  typedCopyPtr fragExecPtr emitHelperProps emitHelper compileEnv context finite_map words
  ptrSafeRun ptrDiscipline venomExecSemantics venomInst venomState list arithmetic

Theorem inst_seq_ptr_singleton:
  ptr_inst_ok D lo 0 ctx fn G tn i s /\ step_inst_base i s = OK t ==>
  inst_seq_ptr D lo ctx fn PG G tn [i] s
    (step_prov PG G i t) (step_taint i s t tn)
Proof
  simp[inst_seq_ptr_def]
QED

Theorem inst_seq_ptr_append:
  !xs s t G tn H tm ys K tk.
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) xs /\
    run_inst_seq xs s = OK t /\
    inst_seq_ptr D lo ctx fn PG G tn xs s H tm /\
    inst_seq_ptr D lo ctx fn PG H tm ys
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH xs) K tk ==>
    inst_seq_ptr D lo ctx fn PG G tn (xs ++ ys) s K tk
Proof
  Induct >> simp[run_inst_seq_def, inst_seq_ptr_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `step_inst_base h s` >>
  gvs[inst_seq_ptr_def] >>
  rename1 `step_inst_base h s = OK u` >>
  `EVERY (\i. ~is_terminator i.inst_opcode) xs` by fs[EVERY_MEM] >>
  first_x_assum irule >> simp[] >>
  qexistsl_tac [`H`, `t with vs_inst_idx := SUC s.vs_inst_idx`, `tm`] >>
  simp[run_inst_seq_inst_idx, exec_result_map_def, ADD_CLAUSES] >>
  metis_tac[ADD_CLAUSES]
QED

(* A two-step consumer keeps the caller's cursor, including nonzero cursors. *)
Theorem inst_seq_ptr_pair:
  ptr_inst_ok D lo 0 ctx fn G tn i s /\ step_inst_base i s = OK t /\
  ptr_inst_ok D lo 0 ctx fn (step_prov PG G i t) (step_taint i s t tn)
    j (t with vs_inst_idx := SUC s.vs_inst_idx) /\
  step_inst_base j (t with vs_inst_idx := SUC s.vs_inst_idx) = OK u ==>
  inst_seq_ptr D lo ctx fn PG G tn [i;j] s
    (step_prov PG (step_prov PG G i t) j u)
    (step_taint j (t with vs_inst_idx := SUC s.vs_inst_idx) u
      (step_taint i s t tn))
Proof
  simp[inst_seq_ptr_def]
QED

Theorem emit_copy_len_binop_seq_ptr:
  (opc = ADD /\ f = word_add \/ opc = AND /\ f = word_and) /\
  emit_op opc [left;right] sa = (Var out,sb) /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  ~ctx_has_dalloca ctx ==>
  ?Gf tnf sf.
    run_inst_seq (emitted_insts sa sb) s = OK sf /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf /\
    lookup_var out sf = SOME (f a b) /\ op_taint tnf (Var out) = {} /\
    op_prov Gf (Var out) =
      (if opc = ADD then first_prov G [left;right] else NONE) /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `emitted_insts sa sb = [mk_inst sa.cs_next_id opc [left;right] [out]]` by
    (drule emitted_insts_emit_op >> simp[] >> metis_tac[]) >>
  `!p. not_fresh_at sa p ==> p <> out` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     metis_tac[LESS_EQ_REFL]) >>
  qabbrev_tac `t = update_var out (f a b) s` >>
  qabbrev_tac `i = mk_inst sa.cs_next_id opc [left;right] [out]` >>
  `step_inst_base i s = OK t` by
    (gvs[Abbr `i`, Abbr `t`] >>
     simp[step_inst_base_opcode_eqs, mk_inst_def] >> simp[exec_pure2_def]) >>
  qexistsl_tac [`step_prov PG G i t`, `step_taint i s t tn`, `t`] >>
  conj_tac >- simp[run_inst_seq_def] >>
  conj_tac >-
    (simp[] >> irule inst_seq_ptr_singleton >> simp[] >>
     simp[Abbr `i`] >> irule ptr_inst_ok_copy_len_binop >> simp[] >> metis_tac[]) >>
  `opc = ADD \/ opc = AND` by metis_tac[] >>
  `op_prov (step_prov PG G i t) (Var out) =
    (if opc = ADD then first_prov G [left;right] else NONE)` by
    (Cases_on `first_prov G [left;right]` >>
     gvs[Abbr `i`, step_prov_def, set_prov_def, out_prov_def,
         op_prov_def, mk_inst_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]) >>
  simp[Abbr `i`, Abbr `t`, copy_len_binop_ghost_frame,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> `p <> out` by metis_tac[] >>
  simp[copy_len_binop_ghost_frame, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem emit_mload_clean_seq_ptr:
  emit_op MLOAD [Var src] sa = (Var out,sb) /\
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx ==>
  ?Gf tnf sf.
    run_inst_seq (emitted_insts sa sb) s = OK sf /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf /\
    lookup_var out sf = SOME (mload (w2n a) s) /\ op_taint tnf (Var out) = {} /\
    op_prov Gf (Var out) = NONE /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `emitted_insts sa sb = [mk_inst sa.cs_next_id MLOAD [Var src] [out]]` by
    (drule emitted_insts_emit_op >> simp[] >> metis_tac[]) >>
  `!p. not_fresh_at sa p ==> p <> out` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     metis_tac[LESS_EQ_REFL]) >>
  qabbrev_tac `t = update_var out (mload (w2n a) s) s` >>
  qabbrev_tac `i = mk_inst sa.cs_next_id MLOAD [Var src] [out]` >>
  `step_inst_base i s = OK t` by
    (simp[Abbr `i`, Abbr `t`, step_inst_base_opcode_eqs,
          mk_inst_def, exec_read1_def, eval_operand_def]) >>
  qexistsl_tac [`step_prov PG G i t`, `step_taint i s t tn`, `t`] >>
  conj_tac >- simp[run_inst_seq_def] >>
  conj_tac >-
    (simp[] >> irule inst_seq_ptr_singleton >> simp[Abbr `i`] >>
     irule ptr_inst_ok_mload >> simp[]) >>
  `op_taint (step_taint i s t tn) (Var out) = {} /\
   (step_taint i s t tn).t_mem = tn.t_mem /\
   (step_taint i s t tn).t_stor = tn.t_stor /\
   (step_taint i s t tn).t_trans = tn.t_trans` by
    (simp[Abbr `i`, Abbr `t`] >> irule mload_ghost_clean >>
     simp[eval_operand_def]) >>
  `op_prov (step_prov PG G i t) (Var out) = NONE` by
    simp[Abbr `i`, step_prov_def, set_prov_def, out_prov_def,
      op_prov_def, mk_inst_def, FLOOKUP_DRESTRICT] >>
  simp[Abbr `t`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> `p <> out` by metis_tac[] >>
  simp[Abbr `i`, step_prov_def, set_prov_def, out_prov_def,
       step_taint_def, set_var_taint_def, mk_inst_def, op_taint_def,
       FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED

Theorem emit_mstore_clean_seq_ptr:
  emit_void MSTORE [Var dst;value] sa = ((),sb) /\
  ptr_covers G tn dst s 32 /\ op_taint tn value = {} /\
  lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
  ~ctx_has_dalloca ctx ==>
  ?tnf sf.
    run_inst_seq (emitted_insts sa sb) s = OK sf /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G tnf /\
    sf = mstore (w2n a) w s /\
    tnf.t_var = tn.t_var /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32}
Proof
  strip_tac >>
  `emitted_insts sa sb = [mk_inst sa.cs_next_id MSTORE [Var dst;value] []]` by
    (drule emitted_insts_emit_void >> simp[]) >>
  qabbrev_tac `t = mstore (w2n a) w s` >>
  qabbrev_tac `i = mk_inst sa.cs_next_id MSTORE [Var dst;value] []` >>
  `step_inst_base i s = OK t` by
    simp[Abbr `i`, Abbr `t`, step_inst_base_opcode_eqs,
         mk_inst_def, exec_write2_def, eval_operand_def] >>
  `step_prov PG G i t = G /\
   (step_taint i s t tn).t_var = tn.t_var /\
   (step_taint i s t tn).t_stor = tn.t_stor /\
   (step_taint i s t tn).t_trans = tn.t_trans /\
   (step_taint i s t tn).t_mem =
     tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32}` by
    (simp[Abbr `i`, Abbr `t`] >> irule mstore_ghost_frame >> simp[]) >>
  qexistsl_tac [`step_taint i s t tn`, `t`] >>
  simp[run_inst_seq_def] >>
  simp[inst_seq_ptr_def] >>
  simp[Abbr `i`] >> irule ptr_inst_ok_mstore >> simp[]
QED

Theorem emit_mcopy_seq_ptr:
  emit_void MCOPY [Var dst;Var src;count_op] sa = ((),sb) /\
  eval_operand count_op s = SOME n /\ op_taint tn count_op = {} /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn dst s (w2n n) /\ ptr_covers G tn src s (w2n n) /\
  ~ctx_has_dalloca ctx ==>
  ?tnf sf.
    run_inst_seq (emitted_insts sa sb) s = OK sf /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s G tnf /\
    sf = mcopy (w2n b) (w2n a) (w2n n) s /\
    tnf.t_var = tn.t_var /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\
    tnf.t_mem = (tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + w2n n}) UNION
      {w2n b + i | i < w2n n /\ w2n a + i IN tn.t_mem}
Proof
  strip_tac >>
  `emitted_insts sa sb =
    [mk_inst sa.cs_next_id MCOPY [Var dst;Var src;count_op] []]` by
    (drule emitted_insts_emit_void >> simp[]) >>
  qabbrev_tac `t = mcopy (w2n b) (w2n a) (w2n n) s` >>
  qabbrev_tac `i = mk_inst sa.cs_next_id MCOPY [Var dst;Var src;count_op] []` >>
  `step_inst_base i s = OK t` by
    simp[Abbr `i`, Abbr `t`, step_inst_base_opcode_eqs,
         mk_inst_def, eval_operand_def] >>
  `step_prov PG G i t = G /\
   (step_taint i s t tn).t_var = tn.t_var /\
   (step_taint i s t tn).t_stor = tn.t_stor /\
   (step_taint i s t tn).t_trans = tn.t_trans /\
   (step_taint i s t tn).t_mem =
     (tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + w2n n}) UNION
       {w2n b + i | i < w2n n /\ w2n a + i IN tn.t_mem}` by
    (qunabbrev_tac `i` >> qunabbrev_tac `t` >> irule mcopy_operand_ghost_frame >>
     simp[eval_operand_def]) >>
  qexistsl_tac [`step_taint i s t tn`, `t`] >>
  simp[run_inst_seq_def, inst_seq_ptr_def] >>
  simp[Abbr `i`] >> irule ptr_inst_ok_mcopy_operand >> simp[]
QED

(* Exercise the clean arithmetic interface at the advanced instruction cursor. *)
Theorem emit_round_pair_seq_ptr:
  emit_op ADD [left;Lit 31w] sa = (Var tmp,sm) /\
  emit_op AND [Var tmp;Lit mask] sm = (Var out,sb) /\
  eval_operand left s = SOME a /\ op_taint tn left = {} /\
  ~ctx_has_dalloca ctx ==>
  ?Gf tnf t sf.
    run_inst_seq (emitted_insts sa sm) s = OK t /\
    run_inst_seq (emitted_insts sm sb)
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sm)) = OK sf /\
    inst_seq_ptr D 0 ctx fn PG G tn
      (emitted_insts sa sm ++ emitted_insts sm sb) s Gf tnf /\
    lookup_var out sf = SOME ((a + 31w) && mask) /\
    op_taint tnf (Var out) = {}
Proof
  strip_tac >>
  `eval_operand (Lit 31w) s = SOME 31w /\ op_taint tn (Lit 31w) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`, `f` |-> `word_add`]
    emit_copy_len_binop_seq_ptr)) >>
  disch_then (qspecl_then [`fn`, `PG`, `G`, `D`]
    (qx_choose_then `G1` (qx_choose_then `tn1` (qx_choose_then `t` strip_assume_tac)))) >>
  qabbrev_tac `u = t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sm)` >>
  `eval_operand (Var tmp) u = SOME (a + 31w) /\
   eval_operand (Lit mask) u = SOME mask /\ op_taint tn1 (Lit mask) = {}` by
    gvs[Abbr `u`, eval_operand_def, lookup_var_def, op_taint_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `AND`, `f` |-> `word_and`]
    emit_copy_len_binop_seq_ptr)) >>
  disch_then (qspecl_then [`fn`, `PG`, `G1`, `D`]
    (qx_choose_then `Gf` (qx_choose_then `tnf` (qx_choose_then `sf` strip_assume_tac)))) >>
  qexistsl_tac [`Gf`, `tnf`, `t`, `sf`] >>
  gvs[Abbr `u`] >> irule inst_seq_ptr_append >>
  conj_tac >-
    (qpat_assum `emit_op ADD _ _ = _` (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     simp[is_terminator_def, mk_inst_def]) >>
  qexistsl_tac [`G1`, `t`, `tn1`] >> simp[] >> metis_tac[ADD_COMM]
QED

(* Exact copy-taint formula, viewed through destination-window boundaries. *)
Theorem copied_taint_window:
  (new_t : num set) = (old_t DIFF {i | b <= i /\ i < b+n}) UNION
    {b+i | i < n /\ a+i IN old_t} ==>
  !j. j < n ==> (b+j IN new_t <=> a+j IN old_t)
Proof
  strip_tac >> simp[] >> rpt strip_tac >>
  simp[pred_setTheory.IN_UNION, pred_setTheory.IN_DIFF] >>
  eq_tac >> rpt strip_tac >> gvs[] >> decide_tac
QED

Theorem copied_taint_outside:
  (new_t : num set) = (old_t DIFF {i | b <= i /\ i < b+n}) UNION
    {b+i | i < n /\ a+i IN old_t} ==>
  !j. j < b \/ b+n <= j ==> (j IN new_t <=> j IN old_t)
Proof
  strip_tac >> simp[] >> rpt strip_tac >>
  simp[pred_setTheory.IN_UNION, pred_setTheory.IN_DIFF] >>
  eq_tac >> rpt strip_tac >> gvs[] >> decide_tac
QED

(* A successful second phase is checked at its advanced cursor. Restore only
   the raw semantic run's cursor when composing the two run_inst_seq witnesses. *)
Theorem run_inst_seq_append_advanced:
  EVERY (\i. ~is_terminator i.inst_opcode) ys /\
  run_inst_seq xs s = OK t /\
  run_inst_seq ys (t with vs_inst_idx := s.vs_inst_idx + LENGTH xs) = OK u ==>
  run_inst_seq (xs ++ ys) s = OK (u with vs_inst_idx := t.vs_inst_idx)
Proof
  strip_tac >>
  qpat_assum `run_inst_seq xs s = OK t`
    (mp_then Any (qspec_then `ys` SUBST1_TAC) run_inst_seq_append) >>
  qspec_then `t with vs_inst_idx := s.vs_inst_idx + LENGTH xs` mp_tac
    (Q.SPEC `ys` run_inst_seq_inst_idx) >> simp[] >>
  disch_then (qspec_then `t.vs_inst_idx` mp_tac) >>
  simp[exec_result_map_def]
QED

Theorem successful_seq_ptr_append:
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) xs /\
  EVERY (\i. ~is_terminator i.inst_opcode) ys /\
  run_inst_seq xs s = OK t /\ inst_seq_ptr D lo ctx fn PG G tn xs s H tm /\
  run_inst_seq ys (t with vs_inst_idx := s.vs_inst_idx + LENGTH xs) = OK u /\
  inst_seq_ptr D lo ctx fn PG H tm ys
    (t with vs_inst_idx := s.vs_inst_idx + LENGTH xs) Gf tk ==>
  run_inst_seq (xs ++ ys) s = OK (u with vs_inst_idx := t.vs_inst_idx) /\
  inst_seq_ptr D lo ctx fn PG G tn (xs ++ ys) s Gf tk
Proof
  strip_tac >> conj_tac
  >- (irule run_inst_seq_append_advanced >> simp[]) >>
  irule inst_seq_ptr_append >> simp[] >>
  qexistsl_tac [`H`, `tm`] >> metis_tac[ADD_COMM]
QED

Theorem variable_ptr_frame_trans:
  (!p. A p ==> B p) /\
  (!p. A p ==> lookup_var p t = lookup_var p s /\
    FLOOKUP H p = FLOOKUP G p /\ op_taint tm (Var p) = op_taint tn (Var p)) /\
  (!p. B p ==> lookup_var p u = lookup_var p t /\
    FLOOKUP Gf p = FLOOKUP H p /\ op_taint tk (Var p) = op_taint tm (Var p)) ==>
  !p. A p ==> lookup_var p u = lookup_var p s /\
    FLOOKUP Gf p = FLOOKUP G p /\ op_taint tk (Var p) = op_taint tn (Var p)
Proof
  metis_tac[]
QED
