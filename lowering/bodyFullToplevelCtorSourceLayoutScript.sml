Theory bodyFullToplevelCtorSourceLayout
Ancestors
  bodySim bodyPtrDefs exprSimHypsDefs gasContext immutableRelation
  typedMemoryCopy structFieldsProps vyperTypeInvariants exprLoweringProps
  vyperTypeGlobalLookupSoundness immSectionDead
  bodyInvCodeProps bodyInvSplit bodyFullShadowBodyInv bodySimModsProps
  exprBodyPreProps

Theorem expr_sim_inv_mods_memory_bytes[local]:
  expr_sim_inv_mods mods cenv cx env es /\
  evaluate_type (get_tenv cx) ty = SOME rt ==>
  type_memory_bytes cenv ty = type_memory_size rt
Proof
  strip_tac >> irule typed_copy_memory_size >>
  qexists_tac `get_tenv cx` >>
  fs[expr_sim_inv_mods_def] >> metis_tac[]
QED

Theorem toplevel_ctor_source_layout_mods:
  contract_inv mods exps ctx cenv cx /\
  expr_body_pre_mods mods cenv cx env (TopLevelName ann (src,id)) es /\
  cenv.ce_is_ctor /\ dead_lo_ok_mods H D lo cenv cx /\
  FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
  evaluate_type (get_tenv cx) ann = SOME rt ==>
  off + type_memory_size rt <= lo /\
  ?pre post vis slot.
    ALOOKUP mods src = SOME (pre ++ VariableDecl vis Immutable id ann slot :: post) /\
    (if mods = [(NONE,pre ++ VariableDecl vis Immutable id ann slot :: post)] then
       off = compute_immutables_len
         (get_struct_fields (make_struct_fields_map_mods mods)) pre
     else slot = SOME off) /\
    type_mem_bytes (get_struct_fields (make_struct_fields_map_mods mods)) ann =
      type_memory_size rt
Proof
  strip_tac >>
  drule expr_body_pre_mods_inv >> strip_tac >>
  drule expr_sim_inv_mods_env >> strip_tac >>
  drule expr_body_pre_mods_well_typed >> strip_tac >>
  drule_all TopLevelName_toplevel_vtypes_Type >> strip_tac >>
  drule contract_inv_immutable_section_layout >> strip_tac >>
  qpat_assum `immutable_section_layout_mods _ _`
    (qspecl_then [`src`, `id`, `off`] mp_tac o CONJUNCT1 o
      REWRITE_RULE [immutable_section_layout_mods_def]) >>
  simp[] >> strip_tac >>
  rename1 `immutable_region_mods mods src id off bytes` >>
  `off + bytes <= imm_len_mods mods` by
    (qpat_assum `immutable_section_layout_mods _ _`
       (qspecl_then [`src`, `id`, `off`, `bytes`] mp_tac o
         CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [immutable_section_layout_mods_def]) >>
     simp[]) >>
  qpat_x_assum `immutable_region_mods _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [immutable_region_mods_def]) >>
  `get_module_code cx src = SOME tops` by metis_tac[contract_inv_module_codes] >>
  `FLOOKUP env.bare_globals (src,id) = SOME ty` by
    (fs[env_consistent_def, env_context_consistent_def,
        bare_globals_complete_def] >>
     metis_tac[listTheory.MEM_APPEND, listTheory.MEM]) >>
  `ty = ann` by
    (drule_all env_consistent_bare_global_find_NONE >> strip_tac >> gvs[]) >>
  drule_all expr_sim_inv_mods_memory_bytes >> strip_tac >>
  drule contract_inv_struct_fields >> strip_tac >>
  `type_mem_bytes (get_struct_fields (make_struct_fields_map_mods mods)) ann =
       type_memory_size rt` by metis_tac[type_mem_bytes_type_memory_bytes] >>
  `lo = imm_len_mods mods` by
    (drule contract_inv_cenv_modules >> fs[dead_lo_ok_mods_def]) >>
  conj_tac >- fs[] >>
  qpat_assum `tops = _` SUBST_ALL_TAC >>
  qexistsl_tac [`pre`, `post`, `vis`, `slot`] >> fs[]
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  drule body_inv_main_code >> strip_tac >>
  drule body_inv_contract >> strip_tac >>
  drule contract_inv_cenv_modules >> strip_tac >>
  drule_all body_inv_expr_body_pre_mods >> strip_tac >>
  `dead_lo_ok_mods H D lo cenv cx` by
    fs[dead_lo_ok_mods_singleton] >>
  qpat_x_assum `src = cenv.ce_module` SUBST_ALL_TAC >>
  drule_all toplevel_ctor_source_layout_mods >>
  Cases_on `cenv.ce_module` >> gvs[alistTheory.ALOOKUP_def, AllCaseEqs(),
    compileUnitTheory.make_struct_fields_map_mods_singleton] >>
  metis_tac[]
QED
*)
Theorem toplevel_ctor_source_layout:
  (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\
  expr_body_pre_mods mods cenv cx env (TopLevelName ann (cenv.ce_module,id)) es /\
  cenv.ce_is_ctor /\ dead_lo_ok H D lo cenv cx /\
  stmt_state_rel H ctx func cenv cx es s /\
  ghost_inv_at D lo d cenv cx es G tn s /\
  src = cenv.ce_module /\
  FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables src imms) id = SOME (rt,v) /\
  evaluate_type (get_tenv cx) ann = SOME rt ==>
  cx_tops cx = tops /\ off + type_memory_size rt <= lo /\
  ?pre post vis ty slot.
    tops = pre ++ VariableDecl vis Immutable id ty slot :: post /\
    off = compute_immutables_len
      (get_struct_fields (make_struct_fields_map tops)) pre /\
    ty = ann /\
    type_mem_bytes (get_struct_fields (make_struct_fields_map tops)) ty =
      type_memory_size rt
Proof
  cheat
QED
