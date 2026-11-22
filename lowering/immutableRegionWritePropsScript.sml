Theory immutableRegionWriteProps
Ancestors
  bodyInvSplit bodyInvCodeProps bodyFullShadowBodyInv immutableRegionTypingProps
  immutableRegionDeadProps ctorDeployDeadSection loweringStateRelDefs
  compileEnv finite_map list

Theorem immutable_slot_span_mods:
  contract_inv mods exps ctx cenv cx /\
  expr_sim_inv_mods mods cenv cx env es /\
  cenv.ce_is_ctor /\ dead_lo_ok_mods H D lo cenv cx /\
  FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
  cenv.ce_module_var_type (src,id) = SOME ty /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  immutable_region_mods mods src id off (type_memory_size tv) /\
  off + type_memory_size tv <= lo /\ FLOOKUP env.bare_globals (src,id) = SOME ty
Proof
  strip_tac >>
  drule_then assume_tac contract_inv_cenv_modules >>
  drule_then (strip_assume_tac o REWRITE_RULE [immutable_section_layout_mods_def])
    contract_inv_immutable_section_layout >>
  `?size. immutable_region_mods mods src id off size` by metis_tac[] >>
  drule_all_then strip_assume_tac immutable_region_mods_type >>
  `lo = imm_len_mods mods` by fs[dead_lo_ok_mods_def] >>
  gvs[] >> res_tac
QED

Theorem immutable_section_replace_mods:
  contract_inv mods exps ctx cenv cx /\
  expr_sim_inv_mods mods cenv cx env es /\
  immutable_region_mods mods src id off (type_memory_size tv) /\
  FLOOKUP env.bare_globals (src,id) = SOME ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  LENGTH sec1 = lo /\ LENGTH sec2 = lo /\
  (!j. j < lo /\ ~(off <= j /\ j < off + type_memory_size tv) ==>
       EL j sec2 = EL j sec1) /\
  (!j. j < lo /\ j IN M1 ==> imm_section_dead_mods cenv sec1 j) /\
  (!j. j < lo /\ ~(off <= j /\ j < off + type_memory_size tv) /\
       j IN M2 ==> j IN M1) /\
  (!j. off <= j /\ j < off + type_memory_size tv /\ j IN M2 ==>
       mem_dead_bytes sec2 off tv j) ==>
  !j. j < lo /\ j IN M2 ==> imm_section_dead_mods cenv sec2 j
Proof
  strip_tac >>
  drule_all_then assume_tac imm_section_dead_mods_regions >>
  rpt strip_tac >>
  Cases_on `off <= j /\ j < off + type_memory_size tv`
  >- (fs[] >> qexistsl_tac [`src`, `id`, `off`, `ty`, `tv`] >> simp[]) >>
  `imm_section_dead_mods cenv sec1 j` by metis_tac[] >>
  qpat_assum `!sec q. imm_section_dead_mods _ sec q <=> _` (fn regions =>
    qpat_assum `imm_section_dead_mods cenv sec1 j`
      (strip_assume_tac o REWRITE_RULE [regions])) >>
  rename1 `immutable_region_mods mods src' id' off' (type_memory_size tv')` >>
  rename1 `FLOOKUP env.bare_globals (src',id') = SOME ty'` >>
  drule_then (strip_assume_tac o REWRITE_RULE [immutable_section_layout_mods_def])
    contract_inv_immutable_section_layout >>
  drule_then strip_assume_tac (cj 1 mem_dead_bytes_range) >>
  Cases_on `(src',id') = (src,id)`
  >- (`off' = off` by metis_tac[optionTheory.SOME_11, compileEnvTheory.var_location_11] >>
      gvs[]) >>
  `regions_disjoint off (type_memory_size tv) off' (type_memory_size tv')` by metis_tac[] >>
  `mem_dead_bytes sec2 off' tv' = mem_dead_bytes sec1 off' tv'` by
    (irule mem_dead_bytes_frame >> simp[] >> rpt strip_tac >>
     qpat_assum `!j. _ ==> EL j sec2 = EL j sec1` irule >>
     fs[regions_disjoint_def] >> decide_tac) >>
  simp[] >> qexistsl_tac [`src'`, `id'`, `off'`, `ty'`, `tv'`] >> simp[]
QED
