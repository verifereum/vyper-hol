(* Runtime selection retains one compiler interval and its packaged callee. *)
Theory bodyIntCallFamCallIntEntryRuntimeCode
Ancestors
  bodyIntCallFamCallIntEntryLookup bodySim actualDecoderPackaging compileVyper
  vyperCompiler loweringShapeProps ctorDeployLoweringCode

Theorem intcall_package_shape_certificates:
  !tops target ut key is_ctor cap.
    supported_program tops ==>
    EVERY external_fn_shape_ok
      (MAP (set_external_package_target target o package_external_fn tops ut key)
        (FST (classify_functions tops))) /\
    fallback_shape_ok (set_fallback_package_target target
      (package_fallback_fn tops ut key (FST (SND (SND (classify_functions tops)))))) /\
    EVERY internal_fn_shape_ok
      (MAP (set_internal_package_target target o package_internal_fn tops ut key is_ctor cap)
        (FST (SND (classify_functions tops)))) /\
    EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors
      (MAP (set_internal_package_target target o package_internal_fn tops ut key is_ctor cap)
        (FST (SND (classify_functions tops))))) /\
    ALL_DISTINCT (MAP FST (internal_fn_descriptors
      (MAP (set_internal_package_target target o package_internal_fn tops ut key is_ctor cap)
        (FST (SND (classify_functions tops))))))
Proof
  rpt gen_tac >> strip_tac >>
  `runtime_bodies_shape_ok tops` by
    metis_tac[supported_program_runtime_bodies_shape_ok] >>
  conj_tac >-
    (simp[listTheory.EVERY_MAP, listTheory.EVERY_MEM] >> rpt strip_tac >>
     irule package_external_fn_shape_ok >> simp[]) >>
  conj_tac >- (irule package_fallback_fn_shape_ok >> simp[]) >>
  irule deploy_internal_package_certificates >>
  qexistsl [`cap`, `is_ctor`, `key`, `target`, `tops`, `ut`] >> simp[]
QED

Theorem intcall_runtime_selected_code:
  !tops ctx caller cx mut rr name args ret ss.
    body_inv tops ctx caller cx /\ ~cx.in_deploy /\
    MEM (FunctionDecl Internal mut F rr name args [] ret ss) tops ==>
    ?ut nk im lbl ce params rb nr key tr view ctor il body rt b c callee.
      set_internal_package_target caller.ce_target
        (package_internal_fn tops ut nk caller.ce_is_ctor im
          (mut,F,rr,name,args,([]:expr list),ret,ss)) =
        (lbl,ce,params,rb,nr,key,tr,view,ctor,il,body,rt) /\
      lookup_function lbl ctx.ctx_functions = SOME callee /\
      compile_internal_function ce params rb nr key tr view ctor il body rt b =
        ((),c) /\ fn_has_code b c callee
Proof
  rpt gen_tac >> simp[body_inv_def] >> strip_tac >> gvs[] >>
  qpat_x_assum `lower_vyper_runtime_unit _ _ = _` mp_tac >>
  simp[lower_vyper_runtime_unit_def, AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  qspecl_then [`tops`, `rpolicy.rpol_target`, `F`, `assign_nkeys tops 0`, `F`, `0`]
    mp_tac intcall_package_shape_certificates >> simp[] >> strip_tac >>
  qpat_x_assum `run_lowering _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[run_lowering_def, lowering_policy_ok_def, AllCaseEqs()] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  `EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl)
    (build_selectors (type_env tops) ext_fns)` by
    simp[build_selectors_fn_labels] >>
  drule_all runtime_packaged_external_boundary >> strip_tac >>
  gvs[] >>
  drule runtime_entry_blocks_shape >> strip_tac >>
  `EVERY (\d. ~compiler_label (FST d) /\
      ~MEM (FST d) (MAP (\bb. bb.bb_label) (all_blocks entry_end)))
    (internal_fn_descriptors (MAP (set_internal_package_target rpolicy.rpol_target o
      package_internal_fn tops F (assign_nkeys tops 0) F 0) int_fns))` by
    (rewrite_tac[listTheory.EVERY_MEM] >> rpt gen_tac >> disch_tac >> BETA_TAC >>
     irule internal_name_not_entry_label >> simp[] >>
     gvs[listTheory.EVERY_MEM]) >>
  `MEM (mut,F,rr,name,args,[],ret,ss) int_fns` by
    (drule (iffRL MEM_classify_internal) >> simp[]) >>
  qpat_x_assum `MEM (_,F,_,_,_,[],_,_) int_fns`
    (mp_tac o REWRITE_RULE [listTheory.MEM_SPLIT]) >>
  strip_tac >> gvs[listTheory.MAP_APPEND] >>
  qmatch_asmsub_abbrev_tac `internal_fn_shape_ok pkg` >>
  PairCases_on `pkg` >>
  rename1 `internal_fn_shape_ok (labelx,cex,paramsx,rbx,nrx,keyx,trx,viewx,ctorx,ilx,bodyx,rtx)` >>
  rule_assum_tac (PURE_REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_at (Pat `extract_context_with_internals _ _ _ = _`)
    intcall_selected_packaged_compilation >>
  disch_then (qspecl_then [`entry_end`, `0`] mp_tac) >>
  fs[install_immutable_reservation_def, venomInstTheory.mk_venom_context_def,
    listTheory.EVERY_APPEND] >>
  strip_tac >>
  qexistsl [`F`, `assign_nkeys tops 0`, `0`, `labelx`, `cex`, `paramsx`,
    `rbx`, `nrx`, `keyx`, `trx`, `viewx`, `ctorx`, `ilx`, `bodyx`, `rtx`] >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  simp[]
QED
