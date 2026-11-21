Theory immutableRegionDeadProps
Ancestors
  bodySim exprSimHypsDefs ctorDeployDeadSectionFrame abiCallerTypeEnv
  typedMemoryCopy structFieldsProps valueEncodingProps valueEncodingProofs
  immSectionDead ctorDeployDeadSection
  abiCanonicalHeadSize vyperContext finite_map list
  bodyInvSplit bodySimModsProps bodyInvCodeProps bodyInvMetadataProps
  immutableRegionTypingProps compileUnit alist

Theorem imm_section_dead_mods_other:
  (!ts. cenv.ce_modules <> [(NONE,ts)]) ==>
  (imm_section_dead_mods cenv sec q <=>
   ?src ts vis id ty slot off tv.
     ALOOKUP cenv.ce_modules src = SOME ts /\
     MEM (VariableDecl vis Immutable id ty slot) ts /\
     FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
     evaluate_type (type_env_all_modules cenv.ce_modules) ty = SOME tv /\
     mem_dead_bytes sec off tv q)
Proof
  Cases_on `cenv.ce_modules` >>
  simp[imm_section_dead_mods_def, ALOOKUP_def] >>
  PairCases_on `h` >> Cases_on `t` >> Cases_on `h0` >>
  simp[imm_section_dead_mods_def]
QED

Theorem immutable_region_eval_size:
  contract_inv mods exps ctx cenv cx /\
  expr_sim_inv_mods mods cenv cx env es /\
  ALOOKUP mods src = SOME tops /\
  MEM (VariableDecl vis Immutable name ty slot) tops /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  immutable_region_mods mods src name off bytes ==>
  FLOOKUP env.bare_globals (src,name) = SOME ty /\ bytes = type_memory_size tv
Proof
  strip_tac >>
  drule_all_then assume_tac immutable_decl_bare_global_mods >>
  drule_all_then strip_assume_tac immutable_region_mods_type >> gvs[]
QED

Theorem imm_section_dead_mods_regions:
  contract_inv mods exps ctx cenv cx /\
  expr_sim_inv_mods mods cenv cx env es ==>
  (imm_section_dead_mods cenv sec q <=>
   ?src id off ty tv.
     immutable_region_mods mods src id off (type_memory_size tv) /\
     FLOOKUP env.bare_globals (src,id) = SOME ty /\
     evaluate_type (get_tenv cx) ty = SOME tv /\
     mem_dead_bytes sec off tv q)
Proof
  strip_tac >>
  drule_then assume_tac contract_inv_cenv_modules >>
  drule_then assume_tac contract_inv_type_env >>
  drule_then assume_tac contract_inv_struct_fields >>
  drule_then (strip_assume_tac o REWRITE_RULE [immutable_section_layout_mods_def])
    contract_inv_immutable_section_layout >>
  Cases_on `?ts. mods = [(NONE,ts)]`
  >- (gvs[] >>
      qpat_assum `cenv.ce_modules = [(NONE,ts)]`
        (fn th => REWRITE_TAC [MATCH_MP imm_section_dead_mods_singleton th,
                              imm_section_dead_def]) >>
      eq_tac
      >- (disch_then (qx_choosel_then [`pre`,`vis`,`name`,`ty`,`slot`,`post`,`tv`]
                       strip_assume_tac) >>
          `evaluate_type (get_tenv cx) ty = SOME tv` by
            (qpat_x_assum `ts = _` SUBST_ALL_TAC >>
             fs[vyperContextTheory.type_env_def, type_env_all_modules_def]) >>
          `type_memory_bytes cenv ty = type_memory_size tv` by
            (irule typed_copy_memory_size >> qexists_tac `get_tenv cx` >>
             fs[expr_sim_inv_mods_def] >> metis_tac[]) >>
          `type_mem_bytes (get_struct_fields (make_struct_fields_map ts)) ty =
             type_memory_size tv` by
            (qpat_assum `type_memory_bytes cenv ty = _`
               (assume_tac o REWRITE_RULE [GSYM type_mem_bytes_type_memory_bytes]) >>
             fs[make_struct_fields_map_mods_singleton] >> metis_tac[]) >>
          `immutable_region_mods [(NONE,ts)] NONE name
             (compute_immutables_len (get_struct_fields (make_struct_fields_map ts)) pre)
             (type_memory_size tv)` by
            (simp[singleton_immutable_region] >>
             qexistsl_tac [`pre`,`post`,`vis`,`ty`,`slot`] >>
             simp[] >> metis_tac[]) >>
          `FLOOKUP env.bare_globals (NONE,name) = SOME ty` by
            (irule immutable_decl_bare_global_mods >>
             qexistsl_tac [`cenv`,`ctx`,`cx`,`es`,`exps`,`[(NONE,ts)]`,`slot`,`ts`,`vis`] >>
             fs[ALOOKUP_def] >> simp[]) >>
          qexistsl_tac [`NONE`,`name`,
            `compute_immutables_len (get_struct_fields (make_struct_fields_map ts)) pre`,
            `ty`,`tv`] >>
          metis_tac[]) >>
      disch_then (qx_choosel_then [`src`,`name`,`off`,`ty`,`tv`] strip_assume_tac) >>
      fs[singleton_immutable_region] >>
      `FLOOKUP env.bare_globals (NONE,name) = SOME ty'` by
        (irule immutable_decl_bare_global_mods >>
         qexistsl_tac [`cenv`,`ctx`,`cx`,`es`,`exps`,`[(NONE,ts)]`,`slot`,`ts`,`vis`] >>
         fs[ALOOKUP_def] >> simp[]) >>
      qexistsl_tac [`pre`,`vis`,`name`,`ty'`,`slot`,`post`,`tv`] >>
      gvs[vyperContextTheory.type_env_def, type_env_all_modules_def]) >>
  `!ts. cenv.ce_modules <> [(NONE,ts)]` by (fs[] >> metis_tac[]) >>
  qpat_assum `!ts. cenv.ce_modules <> [(NONE,ts)]` (fn th =>
    qpat_assum `cenv.ce_modules = mods` (fn modules =>
      REWRITE_TAC [REWRITE_RULE [modules] (MATCH_MP imm_section_dead_mods_other th)])) >>
  eq_tac >> strip_tac
  >- (`?bytes. immutable_region_mods mods src id off bytes` by metis_tac[] >>
      `evaluate_type (get_tenv cx) ty = SOME tv` by
        (qpat_assum `get_tenv cx = _` (fn th => REWRITE_TAC [th]) >>
         first_assum ACCEPT_TAC) >>
      drule_all_then strip_assume_tac immutable_region_eval_size >>
      qexistsl_tac [`src`,`id`,`off`,`ty`,`tv`] >> gvs[]) >>
  qpat_assum `immutable_region_mods _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [immutable_region_mods_def]) >>
  `FLOOKUP env.bare_globals (src,id) = SOME ty'` by
    (irule immutable_decl_bare_global_mods >>
     qexistsl_tac [`cenv`,`ctx`,`cx`,`es`,`exps`,`mods`,`slot`,`tops`,`vis`] >>
     fs[] >> simp[]) >>
  qexistsl_tac [`src`,`tops`,`vis`,`id`,`ty'`,`slot`,`off`,`tv`] >>
  gvs[] >> metis_tac[]
QED
