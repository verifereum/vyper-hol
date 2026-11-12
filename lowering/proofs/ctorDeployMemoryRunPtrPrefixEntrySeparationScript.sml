Theory ctorDeployMemoryRunPtrPrefixEntrySeparation
Ancestors
  compileEnv
  ctorDeployMemoryRunPtrPrefixEntrySemantic
  vyperCall vyperState finite_map list rich_list
  exprLoweringProps ptrDiscipline immutableRelation immutableSectionRel
  ctorDeployLoweringEntrySourceFrame ctorDeployLoweringEntryImmutableMemory ctorDeployLoweringNoCtor
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
