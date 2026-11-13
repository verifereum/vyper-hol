(* Declaration layout protects the other initialized immutable slices. *)
Theory immutableAssignSeparation
Ancestors
  exprSimHypsDefs exprLoweringProps localPtrsProps bodyImmutableAssignFacts
  vyperTypeInvariants vyperState
  loweringStateRelDefs valueEncodingProps venomState finite_map arithmetic

Theorem immutable_assignment_other_regions:
  expr_sim_inv ce cx env es /\ stmt_state_rel ctx func ce cx es s /\
  ce.ce_is_ctor /\
  FLOOKUP env.bare_globals (ce.ce_module,id) = SOME ity /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off) /\
  evaluate_type (get_tenv cx) ity = SOME tv /\ n <= type_memory_size tv /\
  imms = (case ALOOKUP es.immutables cx.txn.target of NONE => [] | SOME m => m) /\
  (!q k. q+k <= s.vs_alloca_next /\ (q+k <= off \/ off+n <= q) ==>
    mem_bytes_at q k t.vs_memory = mem_bytes_at q k s.vs_memory) ==>
  !name tv0 v0 off0. name <> id /\
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off0) /\
    FLOOKUP (get_source_immutables ce.ce_module imms) name = SOME (tv0,v0) ==>
    mem_bytes_at off0 (type_memory_size tv0) t.vs_memory =
    mem_bytes_at off0 (type_memory_size tv0) s.vs_memory
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `bare_globals_layout ce.ce_is_ctor ce.ce_module_var_type ce.ce_module_vars
     cx env.bare_globals env.bare_global_assignable /\
   env_immutables_consistent env cx es` by
    fs[expr_sim_inv_def,env_consistent_def] >>
  `?ty0. FLOOKUP env.bare_globals (ce.ce_module,name) = SOME ty0` by
    metis_tac[bare_globals_layout_def] >>
  `evaluate_type (get_tenv cx) ty0 = SOME tv0` by
    (fs[env_immutables_consistent_def] >> metis_tac[]) >>
  `regions_disjoint off (type_memory_size tv) off0 (type_memory_size tv0)` by
    (qpat_x_assum `bare_globals_layout _ _ _ _ _ _`
       (mp_tac o cj 4 o REWRITE_RULE [bare_globals_layout_def]) >>
     disch_then (qspecl_then [`ce.ce_module`, `id`, `name`, `ity`, `ty0`,
       `off`, `off0`, `tv`, `tv0`] mp_tac) >> simp[]) >>
  `off0 + type_memory_size tv0 <= s.vs_alloca_next` by
    (`immutable_alloca_sep func ce cx es s` by fs[stmt_state_rel_def] >>
     qpat_x_assum `immutable_alloca_sep _ _ _ _ _`
       (mp_tac o cj 2 o REWRITE_RULE [immutable_alloca_sep_def]) >>
     simp[] >> disch_then (qspecl_then [`name`, `tv0`, `v0`, `off0`] mp_tac) >>
     Cases_on `ALOOKUP es.immutables cx.txn.target` >>
     gvs[get_source_immutables_def]) >>
  qpat_x_assum `!q k. _ ==> _` irule >>
  simp[] >> fs[regions_disjoint_def] >> decide_tac
QED

Theorem immutable_assignment_local_regions:
  stmt_state_rel ctx func ce cx es s /\ ce.ce_is_ctor /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,id) = SOME (ImmutableLoc off) /\
  ce.ce_module_var_type (ce.ce_module,id) = SOME ity /\
  evaluate_type (get_tenv cx) ity = SOME tv /\ n <= type_memory_size tv /\
  (!q k. q+k <= s.vs_alloca_next /\ (q+k <= off \/ off+n <= q) ==>
    mem_bytes_at q k t.vs_memory = mem_bytes_at q k s.vs_memory) ==>
  !name b sz. local_region ce es.scopes s name b sz ==>
    mem_bytes_at b sz s.vs_memory = mem_bytes_at b sz t.vs_memory
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `alloca_room ctx func s /\ local_ptrs_rel func ce es.scopes s` by
    fs[stmt_state_rel_def,state_rel_def] >>
  `b+sz <= s.vs_alloca_next` by
    (fs[local_ptrs_rel_def,local_region_def] >>
     first_x_assum drule_all >> strip_tac >> gvs[]) >>
  drule_all immutable_assignment_destination >> strip_tac >>
  `regions_disjoint off (type_memory_size tv) b sz` by metis_tac[] >>
  `b+sz <= off \/ off+n <= b` by
    (fs[regions_disjoint_def] >> decide_tac) >> metis_tac[]
QED
