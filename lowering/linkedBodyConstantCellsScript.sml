(* Install the checked unit's qualified constant data in the body relation. *)
Theory linkedBodyConstantCells
Ancestors
  bodyFullPredsMods constSubstCorrect constSubstMods constSubst
  linkedConstantReplacementValue linkedConstantReplacementTyping linkedConstantReplacementEval
  vyperTypeContract vyperTypeContractStaticMaps vyperTypeConstantFold vyperTypeEnv
  vyperTypeSystem vyperInterpreter vyperState vyperContext vyperSubscriptOverlap
  list alist finite_map option pair combin

Theorem checked_body_const_cells_agree_mods:
  check_contract cx.in_deploy cx.layouts cx.txn.target mods = SOME art /\
  ALOOKUP cx.sources cx.txn.target = SOME mods /\
  frame_maps env art /\ env.toplevel_vtypes = art.cta_toplevel_vtypes /\
  env.type_defs = get_tenv cx /\ state_well_typed es /\
  imms = (case ALOOKUP es.immutables cx.txn.target of
            NONE => empty_immutables | SOME cells => cells) /\
  (!src tops. MEM (src,tops) mods ==>
    ?A. constants_fold_module mods imms src tops FEMPTY = SOME A /\
        A SUBMAP get_source_immutables src imms) /\
  EVERY (no_sha256_expr o SND) (consts_env_mods mods) /\
  EVERY (no_neg_exp_expr o SND) (consts_env_mods mods) ==>
  body_const_cells_agree_mods mods cx env es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `(!e. constant_expr mods e /\ no_sha256_expr e ==>
       ~MEM RiskyAcc (accesses_expr e)) /\
    (!es. EVERY (constant_expr mods) es /\ no_sha256_exprs es ==>
       ~MEM RiskyAcc (accesses_exprs es)) /\
    (!fs. EVERY (constant_expr mods) (MAP SND fs) /\ no_sha256_fields fs ==>
       ~MEM RiskyAcc (accesses_named_exprs fs))` by
    (ho_match_mp_tac const_local_refs_ind >>
     simp[constant_expr_def, no_sha256_expr_def, accesses_expr_def,
          MEM_APPEND, SF ETA_ss] >>
     rpt strip_tac >> gvs[SF ETA_ss] >>
     Cases_on `bi` >> gvs[constant_builtin_def, risky_builtin_def]) >>
  qabbrev_tac `E = consts_env_mods mods` >>
  qabbrev_tac `roots =
    MAP (\(src,id). (cx.txn.target,src,id,
                    THE (FLOOKUP (get_source_immutables src imms) id)))
        (MAP FST E)` >>
  `contract_namespaces_ok F mods` by
    drule_then ACCEPT_TAC check_contract_runtime_namespaces >>
  `get_tenv cx = type_env_all_modules mods` by
    drule_then ACCEPT_TAC get_tenv_sources >>
  `!src id r. ALOOKUP E (src,id) = SOME r ==>
    ?ts vis init ty slot tv v.
      ALOOKUP mods src = SOME ts /\
      MEM (VariableDecl vis (Constant init) id ty slot) ts /\
      expr_type r = ty /\ declared_constant mods src id /\
      constant_expr mods r /\ accesses_expr r = [] /\
      evaluate_type (get_tenv cx) ty = SOME tv /\
      FLOOKUP (get_source_immutables src imms) id = SOME (tv,v) /\
      ALOOKUP es.immutables cx.txn.target = SOME imms /\
      value_has_type tv v /\
      MEM (cx.txn.target,src,id,tv,v) roots /\
      constant_value mods imms r = SOME v` by
    (rpt gen_tac >> strip_tac >>
     `ALOOKUP (consts_env_mods mods) (src,id) = SOME r` by fs[Abbr `E`] >>
     drule_all_then strip_assume_tac checked_linked_constant_replacement_value >>
     `no_sha256_expr r` by
       (qpat_assum `ALOOKUP E (src,id) = SOME r` (assume_tac o MATCH_MP ALOOKUP_MEM) >>
        qpat_assum `EVERY (no_sha256_expr o SND) E`
          (qspec_then `((src,id),r)` mp_tac o REWRITE_RULE [EVERY_MEM]) >> simp[]) >>
     `~MEM RiskyAcc (accesses_expr r)` by
       (qpat_assum `!e. constant_expr mods e /\ no_sha256_expr e ==> _`
          (drule_all_then ACCEPT_TAC)) >>
     `accesses_expr r = []` by
       (Cases_on `accesses_expr r` >> gvs[] >> metis_tac[]) >>
     `ALOOKUP es.immutables cx.txn.target = SOME imms` by
       (Cases_on `ALOOKUP es.immutables cx.txn.target` >> gvs[] >>
        fs[empty_immutables_def, get_source_immutables_def, FLOOKUP_EMPTY]) >>
     drule_all_then assume_tac state_well_typed_immutables_ALOOKUP >>
     drule_all_then strip_assume_tac imms_well_typed_get_source_immutables >>
     `declared_constant mods src id` by
       (simp[declared_constant_def] >>
        qexistsl_tac [`ts`,`vis`,`init`,`ty`,`slot`] >>
        simp[ALOOKUP_MEM]) >>
     `MEM (src,id) (MAP FST E)` by
       (qpat_assum `ALOOKUP E (src,id) = SOME r` (assume_tac o MATCH_MP ALOOKUP_MEM) >>
        simp[MEM_MAP] >> goal_assum (drule_at Any) >> simp[]) >>
     qexistsl_tac [`ts`,`vis`,`init`,`ty`,`slot`,`tv`,`v`] >>
     rpt conj_tac >> FIRST [FIRST_ASSUM ACCEPT_TAC,
       qpat_assum `get_tenv cx = type_env_all_modules mods`
         (fn eq => simp[NoAsms, eq] >> FIRST_ASSUM ACCEPT_TAC),
       simp[NoAsms, Abbr `roots`, MEM_MAP, EXISTS_PROD] >>
       conj_tac
       >- (qpat_assum `FLOOKUP (get_source_immutables src imms) id = SOME (tv,v)`
            (fn cell => simp[NoAsms, cell])) >>
       qexists_tac `r` >> drule_then ACCEPT_TAC ALOOKUP_MEM]) >>
  `!addr src id tv v. MEM (addr,src,id,tv,v) roots ==>
    ?r. addr = cx.txn.target /\ ALOOKUP E (src,id) = SOME r /\
        ALOOKUP es.immutables cx.txn.target = SOME imms /\
        declared_constant mods src id /\
        FLOOKUP (get_source_immutables src imms) id = SOME (tv,v)` by
    (rpt gen_tac >> simp[NoAsms, Abbr `roots`, MEM_MAP, EXISTS_PROD] >>
     rpt strip_tac >> gvs[] >>
     `ALOOKUP E (src,id) <> NONE` by
       (simp[NoAsms, ALOOKUP_NONE, MEM_MAP, EXISTS_PROD] >>
        goal_assum (drule_at Any)) >>
     Cases_on `ALOOKUP E (src,id)` >> fs[] >>
     first_x_assum drule >> strip_tac >> gvs[] >> metis_tac[]) >>
  rewrite_tac[body_const_cells_agree_mods_def] >>
  qexistsl_tac [`roots`,`art`,`imms`] >> asm_rewrite_tac[] >>
  rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >>
      simp[checked_frame_context_def] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >>
      `ALOOKUP E (src,id) = SOME r` by fs[Abbr `E`] >>
      first_x_assum drule >> strip_tac >>
      `FLOOKUP env.bare_globals (src,id) = SOME ty` by
        (qpat_assum `frame_maps env art`
           (strip_assume_tac o REWRITE_RULE [frame_maps_def]) >>
         drule check_contract_nonsig_maps >> strip_tac >> simp[] >>
         irule build_contract_type_artifact_bare_globals_complete >> metis_tac[]) >>
      `FLOOKUP art.cta_toplevel_vtypes (src,id) = SOME (Type ty)` by
        (qpat_assum `check_contract cx.in_deploy cx.layouts cx.txn.target mods = SOME art`
           (mp_then Any mp_tac vyperTypeContractStaticMapsTheory.check_contract_bare_global_toplevel_vtype) >>
         disch_then (qspecl_then [`vis`,`ty`,`ts`,`src`,`Constant init`,`slot`,`id`] mp_tac) >>
         simp[]) >>
      asm_rewrite_tac[] >>
      qexistsl_tac [`Value v`,`v`] >>
      conj_tac
      >- (simp[const_result_at_def, subscripts_type_def, evaluate_subscripts_def] >>
          metis_tac[]) >>
      conj_tac >- (simp[const_result_at_def] >> metis_tac[]) >>
      gen_tac >> strip_tac >> conj_tac
      >- (`find_var_decl_by_name id ts = NONE` by
            (irule find_var_decl_by_name_NONE_Constant >>
             conj_tac
             >- (qexists_tac `src` >>
                 irule contract_namespaces_ok_module_toplevel_vtype_keys >>
                 metis_tac[ALOOKUP_MEM]) >>
             qexistsl_tac [`init`,`slot`,`ty`,`vis`] >> FIRST_ASSUM ACCEPT_TAC) >>
          qpat_assum `const_cells_agree roots st`
            (mp_tac o REWRITE_RULE [const_cells_agree_def]) >>
          disch_then (qspecl_then [`cx.txn.target`,`src`,`id`,`tv`,`v`] mp_tac) >>
          simp[] >> strip_tac >>
          simp[lookup_global_def, get_module_code_def, get_immutables_def,
               get_address_immutables_def, bind_def, lift_option_type_def, return_def]) >>
      `well_typed_expr (artifact_env art mods NONE) r` by
        (`EVERY (no_neg_exp_expr o SND) (consts_env_mods mods)` by fs[Abbr `E`] >>
         drule_all checked_linked_constant_replacements_typed >>
         disch_then (qspec_then `NONE` ACCEPT_TAC)) >>
      irule eval_closed_constant_expr >>
      conj_tac
      >- (qpat_assum `ALOOKUP E (src,id) = SOME r` (assume_tac o MATCH_MP ALOOKUP_MEM) >>
          qpat_assum `EVERY (no_sha256_expr o SND) E`
            (qspec_then `((src,id),r)` mp_tac o REWRITE_RULE [EVERY_MEM]) >> simp[]) >>
      conj_tac >- FIRST_ASSUM ACCEPT_TAC >>
      qexistsl_tac [`artifact_env art mods NONE`,`imms`,`mods`] >>
      simp[artifact_env_def]) >>
  simp[const_cells_agree_def] >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  qpat_x_assum `addr = cx.txn.target` SUBST_ALL_TAC >>
  qexists_tac `imms` >> conj_tac >> FIRST_ASSUM ACCEPT_TAC
QED
