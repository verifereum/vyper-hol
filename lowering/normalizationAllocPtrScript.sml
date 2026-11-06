(* Robust source values survive actual normalization allocation steps. *)
Theory normalizationAllocPtr
Ancestors allocationPtr robustCopyTransportPtr loweringHalt bodyPtrDefs loweringPosts exprSimDefs exprSimProps
  venomState venomExecSemantics venomInst finite_map ptrDiscipline fragExec
  localPtrsProps compileEnv exprLoweringProps

Theorem alloca_step_expr_robust_preserved:
  !ctx func cenv cx es s t sa sb v op tv w id n out s1 b tn.
    stmt_state_rel ctx func cenv cx es s /\
    expr_val_at cenv cx t sa sb es v op s /\
    evaluate_type (get_tenv cx) t = SOME tv /\ ~is_word_type t /\
    val_wf tv v /\ eval_operand op s = SOME w /\ fn_inst_ids_distinct func /\
    MEM (mk_inst id ALLOCA [Lit (n2w n)] [out]) (fn_insts func) /\
    not_local_ptr cenv es.scopes out /\
    (id < sa.cs_next_id \/ sb.cs_next_id <= id) /\ n < dimword (:256) /\
    step_inst_base (mk_inst id ALLOCA [Lit (n2w n)] [out]) s = OK s1 /\
    FLOOKUP s1.vs_allocas id = SOME (b,n) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv v (w2n w) m) ==>
    !m. mem_agree_outside
      (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn).t_mem
      s1.vs_memory m ==> val_in_memory tv v (w2n w) m
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `!i. w2n w <= i /\ i < w2n w + val_footprint tv v ==>
    ~(b <= i /\ i < b+n)` by
    (rpt strip_tac >> drule_all alloca_step_expr_disjoint >> simp[]) >>
  `s1.vs_memory = s.vs_memory /\
   (!i. ~(b <= i /\ i < b+n) ==>
    (i IN (step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn).t_mem
     <=> i IN tn.t_mem))` by suspend "effects" >>
  rpt strip_tac >> irule robust_val_in_memory_exterior_frame >>
  conj_tac >- simp[] >>
  qexistsl_tac [`s.vs_memory`, `s1.vs_memory`, `tn.t_mem`,
    `(step_taint (mk_inst id ALLOCA [Lit (n2w n)] [out]) s s1 tn).t_mem`,
    `{i | b <= i /\ i < b+n}`] >> simp[]
QED

Resume alloca_step_expr_robust_preserved[effects]:
  Cases_on `FLOOKUP s.vs_allocas id`
  >- (drule_all fresh_alloca_ghost >>
      disch_then (qspecl_then [`[]`, `FEMPTY`, `tn`] strip_assume_tac) >>
      drule step_alloca_fresh >> disch_then (qspec_then `n` mp_tac) >>
      simp[] >> disch_then (qspec_then `out` assume_tac) >>
      gvs[update_var_def, FLOOKUP_UPDATE]) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >> gvs[] >>
  drule reused_alloca_step >> disch_then (qspec_then `out` assume_tac) >>
  gvs[] >> drule reused_alloca_memory_taint >>
  disch_then (qspecl_then [`out`, `tn`] mp_tac) >> simp[update_var_def]
QED

Finalise alloca_step_expr_robust_preserved

Theorem compile_alloc_buffer_expr_resources_separated:
  !ctx func cenv cx e es sa sb s0 es' v op s n buf sc tv w tn PG G.
    expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
    not_local_ptr cenv es'.scopes (STRING #"%" (toString sb.cs_next_var)) /\
    (!p. op = Var p ==> p <> STRING #"%" (toString sb.cs_next_var)) /\
    fn_inst_ids_distinct func /\
    compile_alloc_buffer n sb = (buf,sc) /\ fn_has_code sb sc func /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    ~is_word_type (expr_type e) /\ val_wf tv v /\ n < dimword (:256) /\
    eval_operand op s = SOME w /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv v (w2n w) m) ==>
    ?out i s1 b G1 tn1.
      buf.buf_operand = Var out /\
      i = mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out] /\
      step_inst_base i s = OK s1 /\
      FLOOKUP s1.vs_allocas sb.cs_next_id = SOME (b,n) /\
      b+n < dimword (:256) /\
      G1 = step_prov PG G i s1 /\ tn1 = step_taint i s s1 tn /\
      eval_operand (Var out) s1 = SOME (n2w b) /\
      eval_operand op s1 = SOME w /\ ptr_covers G1 tn1 out s1 n /\
      (!j. w2n w <= j /\ j < w2n w + val_footprint tv v ==>
        ~(b <= j /\ j < b+n)) /\
      (!m. mem_agree_outside tn1.t_mem s1.vs_memory m ==>
        val_in_memory tv v (w2n w) m) /\
      (!p k. p <> out /\ ptr_covers G tn p s k ==>
        ptr_covers G1 tn1 p s1 k) /\
      (stor_taint_ok cx tn s ==> stor_taint_ok cx tn1 s1)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule compile_alloc_buffer_emission >> strip_tac >>
  `MEM (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [p]) (fn_insts func)` by
    (drule_all fn_has_code_split >> strip_tac >>
     drule_all emit_inst_fn_member >> simp[]) >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_post_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `p = STRING #"%" (toString sb.cs_next_var)` by
    (drule compile_alloc_buffer_parts >> strip_tac >> gvs[]) >>
  `not_local_ptr cenv es'.scopes p` by gvs[] >>
  `?s1. step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [p]) s = OK s1`
    by suspend "step" >>
  drule_all alloca_step_site >> strip_tac >>
  qexistsl_tac [`p`, `mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [p]`,
    `s1`, `b`, `step_prov PG G (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [p]) s1`,
    `step_taint (mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [p]) s s1 tn`] >>
  simp[] >> suspend "resources"
QED

Resume compile_alloc_buffer_expr_resources_separated[step]:
  Cases_on `FLOOKUP s.vs_allocas sb.cs_next_id`
  >- (drule step_alloca_fresh >> disch_then (qspec_then `n` mp_tac) >>
      simp[] >> disch_then (qspec_then `STRING #"%" (toString sb.cs_next_var)` assume_tac) >> metis_tac[]) >>
  rename1 `FLOOKUP s.vs_allocas sb.cs_next_id = SOME site` >> PairCases_on `site` >>
  drule_all stmt_state_rel_alloca_site_bound >> strip_tac >> gvs[] >>
  drule reused_alloca_step >> disch_then (qspec_then `STRING #"%" (toString sb.cs_next_var)` assume_tac) >>
  metis_tac[]
QED

Resume compile_alloc_buffer_expr_resources_separated[resources]:
  qpat_x_assum `!aid off sz. _` kall_tac >>
  qpat_x_assum `!aid b. _` kall_tac >>
  qpat_x_assum `!x w. _` kall_tac >>
  qpat_x_assum `locals_kept _ _ _ _` kall_tac >>
  rpt conj_tac
  >- suspend "operand"
  >- (drule_all alloca_step_ptr_covers >> simp[])
  >- (rpt strip_tac >> rewrite_tac[GSYM DE_MORGAN_THM] >>
      irule alloca_step_expr_disjoint >>
      metis_tac[arithmeticTheory.LESS_EQ_REFL])
  >- (rpt strip_tac >> irule alloca_step_expr_robust_preserved >>
      simp[] >> metis_tac[arithmeticTheory.LESS_EQ_REFL])
  >- suspend "oldptr" >>
  strip_tac >> drule_all alloca_step_stor_taint_ok >> simp[]
QED

Resume compile_alloc_buffer_expr_resources_separated[operand]:
  drule alloca_step_operand_preserved >>
  disch_then (qspec_then `op` mp_tac) >>
  (impl_tac >- (rpt strip_tac >> gvs[eval_operand_def] >> metis_tac[])) >>
  simp[]
QED

Resume compile_alloc_buffer_expr_resources_separated[oldptr]:
  rpt strip_tac >> rename1 `ptr_covers G tn old s k` >>
  `old <> p` by metis_tac[] >>
  drule_all alloca_step_old_ptr_covers >> simp[]
QED

Finalise compile_alloc_buffer_expr_resources_separated

Theorem compile_alloc_buffer_expr_resources:
  !ctx func cenv cx e es sa sb s0 es' v op s n buf sc tv w tn PG G.
    expr_post ctx func cenv cx e es sa sb s0 es' v op s /\
    fresh_vars_wrt sb s /\ fn_inst_ids_distinct func /\
    compile_alloc_buffer n sb = (buf,sc) /\ fn_has_code sb sc func /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    ~is_word_type (expr_type e) /\ val_wf tv v /\ n < dimword (:256) /\
    eval_operand op s = SOME w /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv v (w2n w) m) ==>
    ?out i s1 b G1 tn1.
      buf.buf_operand = Var out /\
      i = mk_inst sb.cs_next_id ALLOCA [Lit (n2w n)] [out] /\
      step_inst_base i s = OK s1 /\
      FLOOKUP s1.vs_allocas sb.cs_next_id = SOME (b,n) /\
      b+n < dimword (:256) /\
      G1 = step_prov PG G i s1 /\ tn1 = step_taint i s s1 tn /\
      eval_operand (Var out) s1 = SOME (n2w b) /\
      eval_operand op s1 = SOME w /\ ptr_covers G1 tn1 out s1 n /\
      (!j. w2n w <= j /\ j < w2n w + val_footprint tv v ==>
        ~(b <= j /\ j < b+n)) /\
      (!m. mem_agree_outside tn1.t_mem s1.vs_memory m ==>
        val_in_memory tv v (w2n w) m) /\
      (!p k. ptr_covers G tn p s k ==> ptr_covers G1 tn1 p s1 k) /\
      (stor_taint_ok cx tn s ==> stor_taint_ok cx tn1 s1)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `lookup_var (STRING #"%" (toString sb.cs_next_var)) s = NONE` by
    fs[fresh_vars_wrt_def, lookup_var_def, FLOOKUP_DEF] >>
  `not_local_ptr cenv es'.scopes (STRING #"%" (toString sb.cs_next_var))` by
    (irule local_ptrs_rel_fresh_not_local_ptr >>
     qexistsl_tac [`func`, `s`, `sb`] >>
     fs[expr_post_def, stmt_state_rel_def, state_rel_def]) >>
  `!p. op = Var p ==> p <> STRING #"%" (toString sb.cs_next_var)` by
    (rpt strip_tac >> gvs[eval_operand_def] >> metis_tac[]) >>
  drule_all compile_alloc_buffer_expr_resources_separated >>
  disch_then (qspecl_then [`PG`, `G`] strip_assume_tac) >>
  qexistsl_tac [`out`, `i`, `s1`, `b`, `G1`, `tn1`] >> asm_rewrite_tac[] >>
  rpt strip_tac >>
  `out = STRING #"%" (toString sb.cs_next_var)` by
    (drule compile_alloc_buffer_parts >> strip_tac >> gvs[]) >>
  `p <> out` by (strip_tac >> gvs[ptr_covers_def]) >>
  metis_tac[]
QED
