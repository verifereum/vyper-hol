(* Actual fragment endpoints for normalization allocation. *)
Theory normalizationAllocExecPtr
Ancestors wordLoadStorePtr normalizationAllocPtr typedCopyPtr fragExecPtr instIdxIndep

Theorem alloca_step_old_register_frame:
  step_inst_base (mk_inst id ALLOCA [Lit n] [out]) s = OK s1 ==>
  s1.vs_current_bb = s.vs_current_bb /\ s1.vs_halted = s.vs_halted /\
  (!q. q <> out ==>
    lookup_var q s1 = lookup_var q s /\
    FLOOKUP (step_prov PG G (mk_inst id ALLOCA [Lit n] [out]) s1) q = FLOOKUP G q /\
    op_taint (step_taint (mk_inst id ALLOCA [Lit n] [out]) s s1 tn) (Var q) =
      op_taint tn (Var q))
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[Once venomExecSemanticsTheory.step_inst_base_opcode_eqs, venomInstTheory.mk_inst_def,
    venomStateTheory.eval_operand_def, venomExecSemanticsTheory.exec_alloca_def] >>
  Cases_on `FLOOKUP s.vs_allocas id` >> simp[]
  >- (strip_tac >> gvs[] >>
      simp[venomStateTheory.update_var_def, venomStateTheory.lookup_var_def,
        ptrDisciplineTheory.step_prov_def, ptrDisciplineTheory.out_prov_def,
        ptrDisciplineTheory.set_prov_def, ptrDisciplineTheory.step_taint_def,
        ptrDisciplineTheory.set_var_taint_def, ptrDisciplineTheory.out_taint_def,
        ptrDisciplineTheory.op_taint_def, venomInstTheory.mk_inst_def,
        finite_mapTheory.FLOOKUP_UPDATE, venomStateTheory.eval_operand_def]) >>
  rename1 `SOME site` >> PairCases_on `site` >> strip_tac >> gvs[] >>
  simp[venomStateTheory.update_var_def, venomStateTheory.lookup_var_def,
    ptrDisciplineTheory.step_prov_def, ptrDisciplineTheory.out_prov_def,
    ptrDisciplineTheory.set_prov_def, ptrDisciplineTheory.step_taint_def,
    ptrDisciplineTheory.set_var_taint_def, ptrDisciplineTheory.out_taint_def,
    ptrDisciplineTheory.op_taint_def, venomInstTheory.mk_inst_def,
        finite_mapTheory.FLOOKUP_UPDATE, venomStateTheory.eval_operand_def]
QED

Theorem compile_alloc_buffer_step_frag_ptr:
  compile_alloc_buffer n sb = (buf,sc) /\
  buf.buf_operand = Var out /\
  step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s = OK s1 ==>
  frag_exec_ptr cx ctx PG sb sc
    (\g t v. g = G /\ t = tn /\ v = s)
    (\g t v.
      g = step_prov PG G (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s1 /\
      t = step_taint (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out]) s s1 tn /\
      v = (s1 with vs_inst_idx := SUC s.vs_inst_idx)) R
Proof
  strip_tac >> drule loweringHaltTheory.compile_alloc_buffer_insts >> strip_tac >> gvs[] >>
  drule alloca_step_old_register_frame >> strip_tac >>
  irule ptr_fragment_step >> simp[venomInstTheory.mk_inst_def,
    venomInstTheory.is_terminator_def] >>
  rpt strip_tac >> gvs[] >> qexists_tac `s1` >>
  rewrite_tac[GSYM venomInstTheory.mk_inst_def] >>
  simp[ptr_inst_ok_alloca]
QED

Theorem compile_alloc_buffer_expr_robust_frag_ptr:
  !ctx func cenv cx e es sa sb s0 es' v op s n buf sc tv w tn PG G R.
    expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
    fresh_vars_wrt sb s /\ fn_inst_ids_distinct func /\
    compile_alloc_buffer n sb = (buf,sc) /\ fn_has_code sb sc func /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    ~is_word_type (expr_type e) /\ val_wf tv v /\ n < dimword (:256) /\
    eval_operand op s = SOME w /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv v (w2n w) m) ==>
    ?out b G1 tn1 sf.
      buf.buf_operand = Var out /\
      frag_exec_ptr cx ctx PG sb sc
        (\g t v. g = G /\ t = tn /\ v = s)
        (\g t v. g = G1 /\ t = tn1 /\ v = sf) R /\
      b+n < dimword(:256) /\
      eval_operand (Var out) sf = SOME (n2w b) /\
      eval_operand op sf = SOME w /\ ptr_covers G1 tn1 out sf n /\
      (!j. w2n w <= j /\ j < w2n w + val_footprint tv v ==>
        ~(b <= j /\ j < b+n)) /\
      (!m. mem_agree_outside tn1.t_mem sf.vs_memory m ==>
        val_in_memory tv v (w2n w) m) /\
      (!p k. ptr_covers G tn p s k ==> ptr_covers G1 tn1 p sf k) /\
      (stor_taint_ok cx tn s ==> stor_taint_ok cx tn1 sf) /\
      not_fresh_at sc out /\
      (!q. not_fresh_at sb q ==>
        lookup_var q sf = lookup_var q s /\ FLOOKUP G1 q = FLOOKUP G q /\
        op_taint tn1 (Var q) = op_taint tn (Var q))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_alloc_buffer_expr_resources >>
  disch_then (qspecl_then [`PG`, `G`] strip_assume_tac) >>
  qexistsl [`out`, `b`, `G1`, `tn1`, `s1 with vs_inst_idx := SUC s.vs_inst_idx`] >>
  simp[instIdxIndepTheory.eval_op_inst_idx] >>
  conj_tac >- (gvs[] >> irule compile_alloc_buffer_step_frag_ptr >> simp[]) >>
  `!H u p k. ptr_covers H u p (s1 with vs_inst_idx := SUC s.vs_inst_idx) k <=>
      ptr_covers H u p s1 k` by
    simp[bodyPtrDefsTheory.ptr_covers_def, venomStateTheory.eval_operand_def,
      venomStateTheory.lookup_var_def] >>
  `stor_taint_ok cx tn1 (s1 with vs_inst_idx := SUC s.vs_inst_idx) <=>
      stor_taint_ok cx tn1 s1` by simp[bodyPtrDefsTheory.stor_taint_ok_def] >>
  gvs[] >> simp[] >>
  drule loweringHaltTheory.compile_alloc_buffer_emission >> strip_tac >> gvs[] >>
  rpt strip_tac >>
  `q <> out` by metis_tac[] >>
  drule alloca_step_old_register_frame >>
  disch_then (qspecl_then [`tn`, `PG`, `G`] mp_tac) >>
  simp[venomStateTheory.lookup_var_def]
QED
