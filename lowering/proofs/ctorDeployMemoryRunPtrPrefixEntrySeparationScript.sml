Theory ctorDeployMemoryRunPtrPrefixEntrySeparation
Ancestors
 ctorDeployMemoryRunPtrPrefixEntrySemantic
 compileEnv vyperCall vyperState finite_map list rich_list
 exprLoweringProps ptrDiscipline immutableRelation immutableSectionRel
 ctorDeployLoweringEntrySourceFrame ctorDeployMemoryRunPtrPrefixEntryImmutable
 ctorDeployDefs e2eEntry e2eDeployDefs vyperInterpreter

Theorem prefix_entry_local_region_unique:
  local_region ce scopes s name b sz /\
  local_region ce scopes s name d cap ==> b = d /\ sz = cap
Proof
  simp[local_region_def] >> rpt strip_tac >> gvs[]
QED

Theorem prefix_entry_bound_argument_regions:
  bind_arguments env fargs vals = SOME scope /\
  (!j. j < LENGTH fargs ==> ?d cap.
    local_region ce [scope] actual (FST (EL j fargs)) d cap /\ lo <= d) ==>
  !id b sz. local_region ce [scope] actual id b sz ==> lo <= b
Proof
  strip_tac >> drule bind_arguments_fdom >> disch_tac >>
  rpt gen_tac >> strip_tac >>
  `MEM id (MAP FST fargs)` by
    (qpat_x_assum `local_region _ _ _ _ _ _` mp_tac >>
     simp[local_region_def, lookup_scopes_def, FLOOKUP_DEF, AllCaseEqs()] >>
     strip_tac >> gvs[]) >>
  `?j. j < LENGTH fargs /\ id = FST (EL j fargs)` by
    (fs[MEM_EL, EL_MAP] >> metis_tac[]) >>
  first_x_assum drule >> strip_tac >>
  metis_tac[prefix_entry_local_region_unique]
QED

Theorem prefix_entry_immutable_interval:
  immutable_section_layout ce tops /\ ce.ce_module = NONE /\
  immutables_section_rel tops imms section /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
  FLOOKUP (get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
  off + type_memory_size tv <= LENGTH section
Proof
  strip_tac >> gvs[] >>
  qpat_x_assum `immutable_section_layout _ _`
    (mp_tac o REWRITE_RULE [immutable_section_layout_def]) >>
  disch_then drule >> strip_tac >>
  drule_all immutables_section_rel_lookup >> simp[]
QED

Theorem prefix_entry_immutable_separation:
  immutable_section_layout ce tops /\ ce.ce_module = NONE /\
  immutables_section_rel tops imms (REPLICATE lo 0w) /\
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  lo <= actual.vs_alloca_next /\ allocas_from lo actual /\
  (!id b sz. local_region ce es.scopes actual id b sz ==> lo <= b) ==>
  immutable_alloca_sep func ce cx es actual
Proof
  strip_tac >> simp[immutable_alloca_sep_def] >> rpt strip_tac >>
  `off + type_memory_size tv <= lo` by
    (drule prefix_entry_immutable_interval >> simp[] >>
     disch_then drule >> simp[] >> disch_then drule >> simp[]) >>
  simp[compileEnvTheory.regions_disjoint_def] >>
  fs[allocas_from_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem prefix_entry_source_immutable_separation:
  deploy_typing_ok tops am tx /\
  deploy_ctor_start tops am tx (mut,nr,stmts,am_c,es0) /\
  es0.immutables = am_c.immutables /\
  immutable_section_layout ce tops /\ ce.ce_module = NONE /\
  imm_len tops <= actual.vs_alloca_next /\ allocas_from (imm_len tops) actual /\
  (!id b sz. local_region ce es0.scopes actual id b sz ==> imm_len tops <= b) ==>
  immutable_alloca_sep func ce (deploy_evaluation_context tops am tx)
    (es0 with outcomes := SOME outcomes) actual
Proof
  strip_tac >> drule_all prefix_entry_start_zero_section >> disch_tac >>
  Cases_on `ALOOKUP am_c.immutables tx.target`
  >- simp[immutable_alloca_sep_def, deploy_evaluation_context_def,
          initial_evaluation_context_def] >>
  irule prefix_entry_immutable_separation >> simp[] >>
  goal_assum (drule_at Any) >>
  simp[deploy_evaluation_context_def, initial_evaluation_context_def] >> gvs[]
QED
