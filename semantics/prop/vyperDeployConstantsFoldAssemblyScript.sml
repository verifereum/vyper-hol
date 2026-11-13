(* Conditional assembly at the deployment boundary. *)
Theory vyperDeployConstantsFoldAssembly
Ancestors
  vyperInterpreter vyperState vyperContext vyperMisc vyperValue
  vyperTypeContract vyperTypeConstantFold vyperTypeContractSoundness
  vyperTypeExternalDefaults vyperCheckedConstantWrites vyperRuntimeWriteSafety
  vyperBareGlobalName vyperStatePreservation vyperTypeConstantCells
  vyperEvalPreservesImmutablesDom
  list rich_list finite_map alist

Theorem eval_external_defaults_protected_lookup[local]:
  (!st r st'. eval_exprs cx es st = (r,st') ==>
    lookup_immutable cx st' sid nm = lookup_immutable cx st sid nm) /\
  eval_external_defaults cx es st = (r,st') ==>
  lookup_immutable cx st' sid nm = lookup_immutable cx st sid nm
Proof
  simp[eval_external_defaults_run] >>
  Cases_on `eval_exprs cx es (st with scopes := [FEMPTY])` >>
  simp[] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule >> simp[lookup_immutable_def]
QED

Theorem call_bdy_protected_lookup[local]:
  (!st r st'. eval_stmts cx bdy st = (r,st') ==>
    lookup_immutable cx st' sid nm = lookup_immutable cx st sid nm) /\
  (do
    (if nr then
       case cx.nonreentrant_slot of
         NONE => raise (Error (TypeError "nonreentrant slot missing"))
       | SOME slot => do
           acquire_nonreentrant_lock cx.txn.target slot
             ((mut = View \/ mut = Pure) \/ cx.txn.is_static);
           if (mut = View \/ mut = Pure) then return () else check_not_static cx
         od
     else return ());
    eval_stmts cx bdy
   od) st = (res,st') ==>
  lookup_immutable cx st' sid nm = lookup_immutable cx st sid nm
Proof
  rpt gen_tac >> strip_tac >>
  gvs[ignore_bind_def, bind_def, AllCaseEqs()] >>
  rename1 `(if nr then _ else _) st = (_,body_st)` >>
  `body_st.immutables = st.immutables` by
    (Cases_on `nr` >> gvs[return_def] >>
     Cases_on `cx.nonreentrant_slot` >> gvs[raise_def] >>
     gvs[bind_def, AllCaseEqs()] >>
     imp_res_tac acquire_nonreentrant_lock_immutables >>
     Cases_on `mut = View \/ mut = Pure` >>
     gvs[check_not_static_def, assert_def, check_def, return_def, raise_def,
         AllCaseEqs()]) >>
  metis_tac[lookup_immutable_def]
QED

Theorem call_external_function_protected_lookup[local]:
  cx.in_deploy /\
  (!st r st'. eval_exprs cx
    (DROP (LENGTH dflts - (LENGTH args - LENGTH vals)) dflts) st = (r,st') ==>
    lookup_immutable cx st' sid nm = lookup_immutable cx st sid nm) /\
  (!st r st'. eval_stmts cx bdy st = (r,st') ==>
    lookup_immutable cx st' sid nm = lookup_immutable cx st sid nm) /\
  call_external_function orc gobs am cx nr mut ts mods args dflts vals bdy ret =
    (INL v,am_out,rqs) /\
  evaluate_all_constants cx am cx.txn.target mods = SOME am_c ==>
  lookup_immutable cx (initial_state am_out []) sid nm =
  lookup_immutable cx (initial_state am_c []) sid nm
Proof
  rpt gen_tac >> strip_tac >>
  drule call_external_function_success_phases >> strip_tac >> gvs[] >>
  drule_all eval_external_defaults_protected_lookup >> strip_tac >>
  drule_all call_bdy_protected_lookup >> strip_tac >>
  imp_res_tac send_call_value_preserves_immutables >>
  Cases_on `nr /\ ~(mut = View \/ mut = Pure)` >>
  gvs[return_def] >>
  TRY (Cases_on `cx.nonreentrant_slot` >> gvs[return_def]) >>
  imp_res_tac release_nonreentrant_lock_immutables >>
  gvs[lookup_immutable_def, initial_state_def, abstract_machine_from_state_def]
QED

Theorem checked_singleton_installed_constants[local]:
  check_contract mode layouts (addr : 'checker_addr) [(NONE,tops)] = SOME art /\
  initial_immutables (type_env_all_modules [(NONE,tops)]) [(NONE,tops)] = SOME imms /\
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] /\
  ALOOKUP am.immutables cx.txn.target = SOME imms /\
  evaluate_all_constants cx am cx.txn.target [(NONE,tops)] = SOME am_c ==>
  ?cenv.
    constants_fold_module [(NONE,tops)] imms NONE tops FEMPTY = SOME cenv /\
    ALOOKUP am_c.immutables cx.txn.target = SOME (merge_constant_imms NONE cenv imms) /\
    constant_fmap_declared_typed (type_env_all_modules [(NONE,tops)]) tops cenv
Proof
  rpt gen_tac >> strip_tac >>
  `contract_constants_ok [(NONE,tops)]` by
    (qpat_x_assum `check_contract _ _ _ _ = _` mp_tac >>
     simp[check_contract_def] >> metis_tac[]) >>
  gvs[contract_constants_ok_def, constants_order_def, constants_fold_def] >>
  Cases_on `constants_fold_module [(NONE,tops)] imms NONE tops FEMPTY` >> gvs[] >>
  rename1 `constants_fold_module [(NONE,tops)] imms NONE tops FEMPTY = SOME env` >>
  `deployment_constant_cells_typed (type_env_all_modules [(NONE,tops)])
     cx.txn.target [(NONE,tops)] am` by
    (rw[deployment_constant_cells_typed_def] >>
     drule_at (Pat `check_contract _ _ _ _ = _`)
       checked_initial_immutables_constant_absent >>
     simp[] >> disch_then drule >>
     disch_then drule >> simp[]) >>
  `constants_env cx am cx.txn.target NONE tops FEMPTY = SOME env /\
   constant_fmap_declared_typed (type_env_all_modules [(NONE,tops)]) tops env` by
    (irule constants_fold_module_constants_env >>
     simp[EVERY_MEM] >>
     qexistsl [`addr`,`art`,`layouts`,`mode`] >> simp[]) >>
  drule_at (Pat `check_contract _ _ _ _ = _`) constants_fold_evaluate_module_constants >>
  disch_then (qspec_then `[(NONE,tops)]` mp_tac) >>
  disch_then (qspecl_then [`imms`,`am`,`merge_constant_imms NONE env imms`,`cx`] mp_tac) >>
  simp[constants_fold_def] >> strip_tac >>
  gvs[evaluate_all_constants_def, constants_order_def]
QED

Theorem call_external_function_deploy_immutables_address[local]:
  cx.in_deploy /\
  call_external_function orc gobs am cx nr mut ts mods args dflts vals bdy ret =
    (INL v,am_out,rqs) /\
  evaluate_all_constants cx am cx.txn.target mods = SOME am_c ==>
  !tgt. IS_SOME (ALOOKUP am_out.immutables tgt) = IS_SOME (ALOOKUP am_c.immutables tgt)
Proof
  rpt gen_tac >> strip_tac >>
  drule call_external_function_success_phases >> strip_tac >> gvs[] >>
  drule_all actual_entry_prefix_preserves_immutables_dom >> strip_tac >>
  Cases_on `nr /\ ~(mut = View \/ mut = Pure)` >>
  gvs[return_def] >>
  TRY (Cases_on `cx.nonreentrant_slot` >> gvs[return_def]) >>
  imp_res_tac release_nonreentrant_lock_immutables >>
  gvs[preserves_immutables_dom_def, initial_state_def, abstract_machine_from_state_def]
QED

Theorem load_contract_constants_fold_from_frames:
  (!R K cx es.
    (!sid nm. R sid nm ==> ~K sid nm) /\
    (!sid fn ts mut nr args dflts ret bdy.
      get_module_code cx sid = SOME ts /\
      lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,bdy) ==>
      EVERY (expr_writes_ok (runtime_write_root R)) dflts /\
      stmts_writes_ok (runtime_write_root R) bdy) /\
    EVERY (expr_writes_ok (runtime_write_root R)) es ==>
    !st res st'. eval_exprs cx es st = (res,st') ==>
      !sid nm. K sid nm ==>
        lookup_immutable cx st' sid nm = lookup_immutable cx st sid nm) /\
  (!R K cx ss.
    (!sid nm. R sid nm ==> ~K sid nm) /\
    (!sid fn ts mut nr args dflts ret bdy.
      get_module_code cx sid = SOME ts /\
      lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,bdy) ==>
      EVERY (expr_writes_ok (runtime_write_root R)) dflts /\
      stmts_writes_ok (runtime_write_root R) bdy) /\
    stmts_writes_ok (runtime_write_root R) ss ==>
    !st res st'. eval_stmts cx ss st = (res,st') ==>
      !sid nm. K sid nm ==>
        lookup_immutable cx st' sid nm = lookup_immutable cx st sid nm) /\
  load_contract orc gobs am deploy_tx [(NONE,tops)] exps = INL (am_deployed,rqs) /\
  am_deployed.sources <> am.sources /\
  check_contract T layouts deploy_tx.target [(NONE,tops)] = SOME art ==>
  ?imms cenv.
    ALOOKUP am_deployed.immutables deploy_tx.target = SOME imms /\
    constants_fold_module [(NONE,tops)] imms NONE tops FEMPTY = SOME cenv /\
    cenv SUBMAP get_source_immutables NONE imms
Proof
  strip_tac >>
  drule_all load_contract_success_constructor_constants_context >> strip_tac >>
  gvs[] >>
  qmatch_asmsub_abbrev_tac `call_external_function orc gobs am0 cx` >>
  `cx.in_deploy /\ cx.txn.target = deploy_tx.target /\
   ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]` by
    simp[Abbr `cx`, initial_evaluation_context_def] >>
  `ALOOKUP am0.immutables cx.txn.target = SOME imms` by
    simp[Abbr `am0`] >>
  `?cenv.
    constants_fold_module [(NONE,tops)] imms NONE tops FEMPTY = SOME cenv /\
    ALOOKUP am_c.immutables cx.txn.target = SOME (merge_constant_imms NONE cenv imms) /\
    constant_fmap_declared_typed (type_env_all_modules [(NONE,tops)]) tops cenv` by
    (irule (INST_TYPE [``:'checker_addr`` |-> ``:address``] checked_singleton_installed_constants) >>
     goal_assum (drule_at Any) >> simp[] >>
     conj_tac >- (qexistsl [`deploy_tx.target`,`art`,`layouts`,`T`] >> simp[]) >>
     qexists_tac `am0` >> simp[Abbr `am0`]) >>
  suspend "constructor_frames"
QED

Resume load_contract_constants_fold_from_frames[constructor_frames]:
  qabbrev_tac `R = \(sid:num option) id. sid = NONE ==> ~(?vis e ty slot.
    MEM (VariableDecl vis (Constant e) id ty slot) tops)` >>
  qabbrev_tac `protected = \(sid:num option) id. sid = NONE /\ (?vis e ty slot.
    MEM (VariableDecl vis (Constant e) id ty slot) tops)` >>
  `!sid nm. R sid nm ==> ~protected sid nm` by simp[Abbr `R`, Abbr `protected`] >>
  `!sid fn ts mut nr args dflts ret bdy.
     get_module_code cx sid = SOME ts /\
     lookup_callable_function cx.in_deploy fn ts = SOME (mut,nr,args,dflts,ret,bdy) ==>
     EVERY (expr_writes_ok (runtime_write_root R)) dflts /\
     stmts_writes_ok (runtime_write_root R) bdy` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `get_module_code _ _ = _` mp_tac >>
     simp[get_module_code_def] >> strip_tac >>
     drule checked_singleton_constant_callable_writes >>
     disch_then (drule_at (Pat `lookup_callable_function _ _ _ = _`)) >>
     simp[Abbr `R`]) >>
  `EVERY (expr_writes_ok (runtime_write_root R)) dflts /\
   stmts_writes_ok (runtime_write_root R) body'` by
    (drule_all checked_singleton_constructor_constant_writes >> simp[Abbr `R`]) >>
  qpat_x_assum `!R K cx es. _`
    (qspecl_then [`R`,`protected`,`cx`,
      `DROP (LENGTH dflts - (LENGTH args - LENGTH deploy_tx.args)) dflts`] mp_tac) >>
  (impl_tac >- (simp[] >> conj_tac
    >- (qpat_x_assum `!sid fn ts mut nr args dflts ret bdy. _` mp_tac >> simp[])
    >> irule EVERY_DROP >> simp[])) >> disch_tac >>
  qpat_x_assum `!R K cx ss. _`
    (qspecl_then [`R`,`protected`,`cx`,`body'`] mp_tac) >>
  (impl_tac >- (simp[] >>
    qpat_x_assum `!sid fn ts mut nr args dflts ret bdy. _` mp_tac >> simp[])) >> disch_tac >>
  `!sid nm. protected sid nm ==>
    lookup_immutable cx (initial_state am_ctor []) sid nm =
    lookup_immutable cx (initial_state am_c []) sid nm` by
    (rpt gen_tac >> strip_tac >>
     drule_at (Pat `call_external_function _ _ _ _ _ _ _ _ _ _ _ _ _ = _`)
       call_external_function_protected_lookup >>
     disch_then irule >> simp[] >>
     conj_tac >> rpt gen_tac >> strip_tac >>
     first_x_assum drule >> simp[]) >>
  suspend "transport"
QED

Resume load_contract_constants_fold_from_frames[transport]:
  `evaluate_all_constants cx am0 cx.txn.target [(NONE,tops)] = SOME am_c` by simp[] >>
  drule_all call_external_function_deploy_immutables_address >>
  disch_then (qspec_then `cx.txn.target` mp_tac) >> simp[] >> strip_tac >>
  Cases_on `ALOOKUP am_ctor.immutables deploy_tx.target` >> gvs[] >>
  rename1 `ALOOKUP am_ctor.immutables deploy_tx.target = SOME deployed_imms` >>
  qexists_tac `cenv` >> simp[] >>
  conj_tac
  >- (drule constants_fold_module_imms_independent >>
      disch_then (qspecl_then [`tops`,`NONE`,`deployed_imms`,`imms`] mp_tac) >>
      simp[]) >>
  rw[SUBMAP_FLOOKUP_EQN] >>
  rename1 `FLOOKUP cenv id = SOME cell` >>
  PairCases_on `cell` >>
  drule_all constant_fmap_declared_typed_lookup >> strip_tac >> gvs[] >>
  qpat_x_assum `!sid nm. protected sid nm ==> _`
    (qspecl_then [`NONE`,`id`] mp_tac) >>
  simp[Abbr `protected`] >>
  impl_tac >- metis_tac[] >>
  simp[lookup_immutable_def, initial_state_def, merge_constant_imms_def,
       vyperTypeInitialStateTheory.get_source_immutables_set_same, FLOOKUP_FUNION]
QED

Finalise load_contract_constants_fold_from_frames
