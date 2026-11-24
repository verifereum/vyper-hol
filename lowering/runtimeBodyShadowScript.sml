(* The selected external body's shadow placement: the runtime unit's GAS
   shadow (gas_shadow_run_lowering) holds the shadow body's code at the
   compile states paired with the actual body's. *)
Theory runtimeBodyShadow
Ancestors
  runtimeBodyStartDefs gasShadowRunLowering gasShadowUnit gasShadowState
  gasShadow fragExec loweringPosts bodySim supportedStmts compileVyper
  moduleLowering vyperCompiler actualRegistrationCode
  actualDecoderPackaging rawEntryCode loweringShapeProps loweringShapeDefs
  loweringShapeRules compileEnv venomInst list gasShadowShape
  gasShadowStmtEnv gasShadowRuntimeRegisterEnv gasShadowCompileStmtBase
  externalCallSelected supportedProgram supportedProgramProps supportedNames
  loweringShapeSource gasShadowRuntimeBodies gasShadowRuntimeOps
  gasShadowModuleOps gasShadowCompileContext gasShadowModuleDefs gasShadowUnitGuards
  nonreentrantEntryPath entryRejectCode entryCompileIntervals entryCodeOwnership
  runtimeBodyRetainedInterval

val _ = Parse.hide "body";

Theorem runtime_external_package_labels[local]:
  EVERY (\(lbl,ce,pos,mincd,pay,nr,key,ut,iv,body,rt). jump_label_ok lbl)
    (MAP (set_external_package_target target o
          package_external_fn tops T (K global_nonreentrant_slot)) exts)
Proof
  rw[EVERY_MAP, EVERY_MEM] >>
  PairCases_on `x` >>
  simp[package_external_fn_def, set_external_package_target_def,
       jump_label_ok_def]
QED

Theorem runtime_shadow_package_labels[local]:
  EVERY (\(lbl,ce,pos,mincd,pay,nr,key,ut,iv,body,rt). jump_label_ok lbl)
      (MAP gas_shadow_external_package packs) <=>
  EVERY (\(lbl,ce,pos,mincd,pay,nr,key,ut,iv,body,rt). jump_label_ok lbl) packs
Proof
  Induct_on `packs` >> simp[] >> gen_tac >> PairCases_on `h` >>
  simp[gas_shadow_external_package_def]
QED

(* The legacy dispatcher reaches the same registration labels in the real
   and shadow units.  Match the compilers step by step from the dispatcher,
   and use entry-prefix retention for the resulting intervals in each unit. *)
Theorem runtime_selected_body_shadow_with_shadow_nr:
  !tops rpolicy unit lbl ce pos mincd pay nr key ut iv fbody rt st cenv sa sl st'
   bindings ctx cx env env' ret.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
    runtime_selected_body_start tops rpolicy
      (lbl,ce,pos,mincd,pay,nr,key,ut,iv,fbody,rt) st /\
    compile_register_positional_args ce pos 4 st = (cenv,sa) /\
    (if nr then compile_nonreentrant_lock key ut iv else comp_return ()) sa =
      ((),sl) /\
    compile_guarded_body cenv nr key ut iv fbody rt sa = ((),st') /\
    supported_stmts tops bindings fbody /\ body_inv tops ctx cenv cx /\
    rt = (if ret = NoneT then NONE else SOME ret) /\
    type_stmts env ret fbody = SOME env' ==>
    ?func shadow_ctx shadow_func cenv' sb shadow_sl shadow_sb shadow_unit
     shadow_sa shadow_st'.
      runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
      shadow_ctx = shadow_unit.cu_context /\
      lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
      gas_shadow_context unit.cu_context shadow_ctx /\
      gas_shadow_function func shadow_func /\
      MEM func unit.cu_context.ctx_functions /\
      MEM shadow_func shadow_ctx.ctx_functions /\
      stmts_env cenv NoLoop ret fbody sl = (cenv',sb) /\
      stmts_env (gas_shadow_env T cenv) NoLoop ret (MAP gas_shadow_stmt fbody) shadow_sl =
        (gas_shadow_env T cenv',shadow_sb) /\
      gas_shadow_state sl shadow_sl /\ gas_shadow_state sb shadow_sb /\
      fn_has_code sl sb func /\ fn_has_code sb st' func /\
      fn_has_code shadow_sl shadow_sb shadow_func /\
      gas_shadow_state sa shadow_sa /\
      compile_guarded_body (gas_shadow_env T cenv) nr key ut iv (MAP gas_shadow_stmt fbody) rt
        shadow_sa = ((), shadow_st') /\
      fn_has_code shadow_sa shadow_st' shadow_func
Proof
  rpt gen_tac >> strip_tac >>
  `ALL_DISTINCT (MAP (\p. FST (SND (SND (SND p))))
    (FST (SND (classify_functions tops))))` by
    (irule supported_names_internal_names_distinct >>
     fs[supported_program_def, supported_declaration_names_def]) >>
  fs[runtime_selected_body_start_def] >>
  `~EXISTS external_has_defaults exts` by fs[] >>
  qpat_x_assum `lower_vyper_runtime_unit _ _ = _` mp_tac >>
  simp[lower_vyper_runtime_unit_def] >> strip_tac >>
  qspecl_then [`tops`, `F`] mp_tac internal_descriptors_ok >>
  impl_tac >- fs[] >>
  rewrite_tac[pairTheory.FST, pairTheory.SND] >> strip_tac >>
  qpat_assum `classify_functions tops = _`
    (fn th => rule_assum_tac (REWRITE_RULE [th]) >> assume_tac th) >>
  `EVERY (\(lbl,ce,pos,mincd,pay,nr,key,ut,iv,body,rt). jump_label_ok lbl)
    (MAP (set_external_package_target rpolicy.rpol_target o
      package_external_fn tops T (K global_nonreentrant_slot)) exts)` by
    irule runtime_external_package_labels >>
  `EVERY (\(lbl,ce,pos,mincd,pay,nr,key,ut,iv,body,rt). jump_label_ok lbl)
    (pre ++ (lbl,ce,pos,mincd,pay,nr,key,ut,iv,fbody,rt)::post)` by
    (qpat_assum `rt = _` (fn ret_eq => PURE_REWRITE_TAC [ret_eq]) >>
     qpat_assum `MAP (set_external_package_target _ o _) _ = _` (fn packs =>
       qpat_assum `EVERY _ (MAP (set_external_package_target _ o _) _)`
         (ACCEPT_TAC o PURE_REWRITE_RULE [packs, GSYM APPEND_ASSOC, APPEND]))) >>
  `lowering_policy_ok rpolicy` by
    (qpat_x_assum `run_lowering _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     rw[run_lowering_def]) >>
  `rpolicy.rpol_frontend_dispatch = Linear` by fs[lowering_policy_ok_def] >>
  qpat_x_assum `rt = _` SUBST_ALL_TAC >>
  rule_assum_tac (PURE_REWRITE_RULE [APPEND, APPEND_ASSOC]) >>
  `ALL_DISTINCT (MAP FST (MAP (source_internal_fn_descriptor tops F)
     (order_internals (runtime_internal_order tops ints) ints)))`
    by (`PERM (MAP FST (MAP (source_internal_fn_descriptor tops F)
                (order_internals (runtime_internal_order tops ints) ints)))
              (MAP FST (MAP (source_internal_fn_descriptor tops F) ints))`
          by (irule sortingTheory.PERM_MAP >> irule sortingTheory.PERM_MAP >>
              simp[PERM_order_runtime_internals]) >>
        drule sortingTheory.ALL_DISTINCT_PERM >> simp[]) >>
  `EVERY (\d. internal_label_ok (FST d))
     (internal_fn_descriptors
       (MAP (set_internal_package_target rpolicy.rpol_target o
         package_internal_fn tops T (K global_nonreentrant_slot) F 0)
         (order_internals (runtime_internal_order tops ints) ints))) /\
   ALL_DISTINCT (MAP FST (internal_fn_descriptors
       (MAP (set_internal_package_target rpolicy.rpol_target o
         package_internal_fn tops T (K global_nonreentrant_slot) F 0)
         (order_internals (runtime_internal_order tops ints) ints))))` by
    (gvs[GSYM MAP_MAP_o, internal_fn_descriptors_set_internal_package_target,
         internal_fn_descriptors_MAP_package_internal_fn,
         EVERY_MAP, EVERY_MEM] >>
     fs[MEM_MAP, PULL_EXISTS]) >>
  rule_assum_tac (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >>
  qpat_x_assum `(_,_) = fresh_label _ _` (assume_tac o SYM) >>
  drule_all run_lowering_pinned_body_interval >> strip_tac >>
  drule_all guarded_body_code_from_registration >> strip_tac >> gvs[] >>
  rename1 `compile_stmts cenv NoLoop _ fbody sl = ((),sb)` >>
  `?cenv'. stmts_env cenv NoLoop ret fbody sl = (cenv',sb)` by
    (irule guarded_body_stmts_env >>
     metis_tac[]) >>
  qspec_then `pre` mp_tac gas_shadow_compiles_compile_external_fn_bodies >>
  rewrite_tac[gas_shadow_compiles_def] >>
  disch_then (qspecl_then [`dispatch_st`, `dispatch_st`] mp_tac) >>
  simp[gas_shadow_state_refl] >>
  Cases_on `compile_external_fn_bodies (MAP gas_shadow_external_package pre) dispatch_st` >>
  rename1 `_ = (z,shadow_opened)` >> simp[] >> strip_tac >> gvs[] >>
  `gas_shadow_state checks (SND (new_block lbl shadow_opened))` by
    (mp_tac (Q.INST [`label` |-> `lbl`] gas_shadow_compiles_new_block) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`opened`, `shadow_opened`] mp_tac) >> simp[]) >>
  Cases_on `new_block lbl shadow_opened` >>
  rename1 `_ = (oldbb,shadow_checks)` >> gvs[] >>
  `oldbb = shadow_opened.cs_current_bb` by
    (qpat_x_assum `new_block lbl shadow_opened = _` mp_tac >> simp[new_block_def]) >>
  `gas_shadow_state st (SND (compile_entry_checks mincd pay shadow_checks))` by
    (mp_tac (Q.INST [`min_cds` |-> `mincd`, `payable` |-> `pay`] gas_shadow_compiles_compile_entry_checks) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`checks`, `shadow_checks`] mp_tac) >> simp[]) >>
  Cases_on `compile_entry_checks mincd pay shadow_checks` >>
  rename1 `_ = (v,shadow_st)` >> Cases_on `v` >> gvs[] >>
  Cases_on `compile_register_positional_args (gas_shadow_env T ce) pos 4 shadow_st` >>
  rename1 `_ = (shadow_cenv,shadow_sa)` >>
  qspecl_then [`pos`, `ce`, `4`]
    (drule_then (mp_tac o SPEC_ALL) o Q.SPECL [`st`, `shadow_st`] o REWRITE_RULE [gas_shadow_compiles_env_def])
    (Q.INST [`sd` |-> `T`] gas_shadow_compiles_env_register_positional_args) >>
  simp[] >> strip_tac >> gvs[] >>
  `gas_shadow_state
     (SND (compile_guarded_body cenv nr key ut iv fbody
       (if ret = NoneT then NONE else SOME ret) sa))
     (SND (compile_guarded_body (gas_shadow_env T cenv) nr key ut iv (MAP gas_shadow_stmt fbody)
       (if ret = NoneT then NONE else SOME ret) shadow_sa))` by
    (irule (cj 2 (REWRITE_RULE [gas_shadow_compiles_def]
       gas_shadow_compiles_compile_guarded_body)) >> simp[]) >>
  Cases_on `compile_guarded_body (gas_shadow_env T cenv) nr key ut iv (MAP gas_shadow_stmt fbody)
    (if ret = NoneT then NONE else SOME ret) shadow_sa` >>
  rename1 `_ = (v,shadow_end)` >> Cases_on `v` >> gvs[] >>
  `gas_shadow_compiles
    (if nr then compile_nonreentrant_lock key ut iv else comp_return ())
    (if nr then compile_nonreentrant_lock key ut iv else comp_return ())` by
    (Cases_on `nr` >> simp[gas_shadow_compiles_nonreentrant_lock,
                           gas_shadow_compiles_return]) >>
  Cases_on `(if nr then compile_nonreentrant_lock key ut iv
             else comp_return ()) shadow_sa` >>
  rename1 `_ = (answer,shadow_sl)` >> Cases_on `answer` >>
  qpat_x_assum `gas_shadow_compiles _ _` (mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
  disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >> simp[] >> strip_tac >>
  Cases_on `stmts_env (gas_shadow_env T cenv) NoLoop ret (MAP gas_shadow_stmt fbody) shadow_sl` >>
  rename1 `_ = (ec,shadow_sb)` >>
  qspecl_then [`fbody`, `cenv`, `NoLoop`, `ret`]
    (drule_then (mp_tac o SPEC_ALL) o Q.SPECL [`sl`, `shadow_sl`] o REWRITE_RULE [gas_shadow_compiles_env_def])
    (Q.INST [`sd` |-> `T`] gas_shadow_stmts_env_env) >>
  simp[] >> strip_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac `run_lowering sels packs ips fall rpolicy 0 0 [] info "__entry"` >>
  `OPTREL gas_shadow_unit (SOME unit)
    (run_lowering sels (MAP gas_shadow_external_package packs)
      (MAP gas_shadow_internal_package ips)
      (OPTION_MAP gas_shadow_fallback_package fall) rpolicy 0 0 [] info "__entry")` by
    (qpat_x_assum `run_lowering sels packs ips fall _ _ _ _ _ _ = SOME unit`
       (SUBST1_TAC o SYM) >> irule gas_shadow_run_lowering) >>
  Cases_on `run_lowering sels (MAP gas_shadow_external_package packs)
      (MAP gas_shadow_internal_package ips)
      (OPTION_MAP gas_shadow_fallback_package fall) rpolicy 0 0 [] info "__entry"` >>
  gvs[optionTheory.OPTREL_def] >> rename1 `gas_shadow_unit unit shadow_unit` >>
  `EVERY (\(lbl,ce,pos,mincd,pay,nr,key,ut,iv,body,rt). jump_label_ok lbl)
    (MAP gas_shadow_external_package packs)` by
    simp[runtime_shadow_package_labels, Abbr `packs`, runtime_external_package_labels] >>
  `EVERY (\d. internal_label_ok (FST d))
      (internal_fn_descriptors (MAP gas_shadow_internal_package ips)) /\
    ALL_DISTINCT (MAP FST (internal_fn_descriptors (MAP gas_shadow_internal_package ips)))` by
    simp[] >>
  qpat_x_assum `run_lowering sels packs ips fall _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `run_lowering _ _ _ _ _ _ _ _ _ _ = SOME shadow_unit` mp_tac >>
  simp_tac (srw_ss()) [Abbr `packs`, MAP_APPEND, gas_shadow_external_package_def] >>
  strip_tac >>
  qpat_x_assum `(_,_) = fresh_label _ _` (assume_tac o SYM) >>
  rule_assum_tac (PURE_REWRITE_RULE [MAP_APPEND, MAP, gas_shadow_external_package_def]) >>
  drule_all run_lowering_pinned_body_interval >> strip_tac >>
  `stmts_env (gas_shadow_env T cenv) NoLoop ret (MAP gas_shadow_stmt fbody) =
   stmts_env (gas_shadow_env T cenv) NoLoop
     (case (if ret = NoneT then NONE else SOME ret) of
        NONE => BaseT BoolT | SOME t => t) (MAP gas_shadow_stmt fbody)` by
    (Cases_on `ret = NoneT` >- (
       gvs[] >>
       `~stmts_valued_return (MAP gas_shadow_stmt fbody)` by
         metis_tac[type_stmts_none_valued_return, gas_shadow_valued_return] >>
       `supported_stmts tops bindings (MAP gas_shadow_stmt fbody)` by
         metis_tac[gas_shadow_supported_stmts] >>
       irule stmtsEnvRetTyTheory.stmts_env_ret_ty_no_valued_return >> simp[] >>
       qexistsl_tac [`bindings`, `tops`] >> simp[]) >> simp[]) >>
  `compile_stmts (gas_shadow_env T cenv) NoLoop
     (case (if ret = NoneT then NONE else SOME ret) of
        NONE => BaseT BoolT | SOME t => t) (MAP gas_shadow_stmt fbody) shadow_sl =
      ((),shadow_sb)` by
    (simp[stmtSimPropsTheory.compile_stmts_env] >> gvs[]) >>
  qpat_assum `compile_guarded_body _ _ _ _ _ (MAP _ _) _ _ = _`
    (fn built => qpat_assum `fn_has_code shadow_sa shadow_end func'`
      (strip_assume_tac o MATCH_MP guarded_body_code_from_registration o CONJ built)) >>
  gvs[] >> rename1 `gas_shadow_state sb shadow_sb` >>
  `gas_shadow_context unit.cu_context shadow_unit.cu_context` by
    fs[gas_shadow_unit_def] >>
  `gas_shadow_function func func'` by
    (mp_tac gas_shadow_lookup_function >>
     disch_then (qspecl_then [`unit.cu_context.ctx_functions`,
        `shadow_unit.cu_context.ctx_functions`, `"__entry"`] mp_tac) >>
     fs[gas_shadow_context_def]) >>
  `runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit` by
    (`~EXISTS external_has_defaults exts` by
       fs[GSYM EVERY_NOT_EXISTS] >>
     qpat_x_assum `~EXISTS external_has_defaults exts` mp_tac >>
     qpat_assum `classify_functions tops = _` mp_tac >>
     qpat_assum `MAP (set_external_package_target _ o _) _ = _` mp_tac >>
     qpat_assum `run_lowering _ _ _ _ _ _ _ _ _ _ = SOME shadow_unit` mp_tac >>
     rpt (qpat_x_assum `Abbrev _` mp_tac) >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     gvs[runtime_gas_shadow_unit_def, markerTheory.Abbrev_def] >>
     pure_rewrite_tac [gas_shadow_external_package_def, GSYM APPEND_ASSOC, APPEND] >>
     Cases_on `EXISTS external_has_defaults exts` >> simp[] >>
     qpat_x_assum `EXISTS external_has_defaults exts`
       (strip_assume_tac o REWRITE_RULE [EXISTS_MEM]) >>
     qpat_x_assum `EVERY ($~ o external_has_defaults) exts`
       (mp_tac o REWRITE_RULE [EVERY_MEM, combinTheory.o_DEF]) >>
     rename1 `MEM external exts` >>
     disch_then (qspec_then `external` mp_tac) >> simp[]) >>
  qexistsl_tac [`func'`, `shadow_sl`, `shadow_sb`, `shadow_unit`,
                `shadow_sa`, `shadow_end`] >> simp[]
QED

Theorem runtime_selected_body_shadow_with_shadow:
  !tops rpolicy unit lbl ce pos mincd pay key ut iv fbody rt st cenv sa st'
   bindings ctx cx env env' ret.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
    runtime_selected_body_start tops rpolicy
      (lbl,ce,pos,mincd,pay,F,key,ut,iv,fbody,rt) st /\
    compile_register_positional_args ce pos 4 st = (cenv,sa) /\
    compile_guarded_body cenv F key ut iv fbody rt sa = ((),st') /\
    supported_stmts tops bindings fbody /\ body_inv tops ctx cenv cx /\
    rt = (if ret = NoneT then NONE else SOME ret) /\
    type_stmts env ret fbody = SOME env' ==>
    ?func shadow_ctx shadow_func cenv' sb shadow_sa shadow_sb shadow_unit.
      runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
      shadow_ctx = shadow_unit.cu_context /\
      lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
      gas_shadow_context unit.cu_context shadow_ctx /\
      gas_shadow_function func shadow_func /\
      MEM func unit.cu_context.ctx_functions /\
      MEM shadow_func shadow_ctx.ctx_functions /\
      stmts_env cenv NoLoop ret fbody sa = (cenv',sb) /\
      stmts_env (gas_shadow_env T cenv) NoLoop ret (MAP gas_shadow_stmt fbody) shadow_sa =
        (gas_shadow_env T cenv',shadow_sb) /\
      gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
      fn_has_code sa sb func /\ fn_has_code sb st' func /\
      fn_has_code shadow_sa shadow_sb shadow_func
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`tops`,`rpolicy`,`unit`,`lbl`,`ce`,`pos`,`mincd`,`pay`,
    `F`,`key`,`ut`,`iv`,`fbody`,`rt`,`st`,`cenv`,`sa`,`sa`,`st'`,
    `bindings`,`ctx`,`cx`,`env`,`env'`,`ret`] runtime_selected_body_shadow_with_shadow_nr) >>
  fs[comp_return_def, GSYM EVERY_NOT_EXISTS] >>
  disch_then (qx_choosel_then
    [`func`, `shadow_func`, `cenv'`, `sb`, `shadow_sa`,
     `shadow_sb`, `shadow_unit`, `shadow_start`, `shadow_end`] strip_assume_tac) >>
  qexistsl_tac [`func`, `shadow_func`, `cenv'`, `sb`, `shadow_sa`,
                `shadow_sb`, `shadow_unit`] >> simp[]
QED

Theorem runtime_selected_body_shadow:
  !tops rpolicy unit lbl ce pos mincd pay key ut iv fbody rt st cenv sa st'
   bindings ctx cx env env' ret.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
    runtime_selected_body_start tops rpolicy
      (lbl,ce,pos,mincd,pay,F,key,ut,iv,fbody,rt) st /\
    compile_register_positional_args ce pos 4 st = (cenv,sa) /\
    compile_guarded_body cenv F key ut iv fbody rt sa = ((),st') /\
    supported_stmts tops bindings fbody /\ body_inv tops ctx cenv cx /\
    rt = (if ret = NoneT then NONE else SOME ret) /\
    type_stmts env ret fbody = SOME env' ==>
    ?func shadow_ctx shadow_func cenv' sb shadow_sa shadow_sb.
      lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
      gas_shadow_context unit.cu_context shadow_ctx /\
      gas_shadow_function func shadow_func /\
      MEM func unit.cu_context.ctx_functions /\
      MEM shadow_func shadow_ctx.ctx_functions /\
      stmts_env cenv NoLoop ret fbody sa = (cenv',sb) /\
      stmts_env (gas_shadow_env T cenv) NoLoop ret (MAP gas_shadow_stmt fbody) shadow_sa =
        (gas_shadow_env T cenv',shadow_sb) /\
      gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
      fn_has_code sa sb func /\ fn_has_code sb st' func /\
      fn_has_code shadow_sa shadow_sb shadow_func
Proof
  rpt strip_tac >>
  drule_all runtime_selected_body_shadow_with_shadow >>
  disch_then (qx_choosel_then
    [`func`, `shadow_ctx`, `shadow_func`, `cenv'`, `sb`, `shadow_sa`,
     `shadow_sb`, `shadow_unit`] strip_assume_tac) >>
  qexistsl_tac [`func`, `shadow_ctx`, `shadow_func`, `cenv'`, `sb`,
                `shadow_sa`, `shadow_sb`] >> simp[]
QED

(* The fallback's payable check is compile_entry_checks at the minimum
   calldata size 4, where the size check is skipped. *)
Theorem compile_fallback_body_entry_checks[local]:
  compile_entry_checks 4 pay s = ((),st) ==>
  compile_fallback_body cenv pay nr key ut iv body rt s =
    compile_guarded_body cenv nr key ut iv body rt st
Proof
  Cases_on `pay` >>
  simp[compile_fallback_body_def, compile_entry_checks_def,
       comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[])
QED

(* run_lowering_pinned_body_interval for the fallback, compiled at the
   fallback label after every external package's body. *)
Theorem run_lowering_fallback_body_interval[local]:
  run_lowering sels packs ints (SOME (ce,pay,nr,key,ut,iv,body,rt)) rp
    buckets metadata dense info "__entry" = SOME unit /\
  EVERY (\(lbl,ce,pos,mincd,pay,nr,key,ut,iv,body,rt). jump_label_ok lbl) packs /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ints) /\
  fresh_label "fallback" (initial_compile_state "__entry") = (fl,ls) /\
  compile_selector_dispatch_linear (MAP (\(sel,lbl,z). (sel,lbl)) sels)
    fl ls = ((),ds) /\
  compile_external_fn_bodies packs ds = ((),opened) /\
  new_block fl opened = (opened.cs_current_bb,checks) /\
  compile_entry_checks 4 pay checks = ((),st) /\
  compile_guarded_body ce nr key ut iv body rt st = ((),st') ==>
  ?func.
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
    MEM func unit.cu_context.ctx_functions /\
    fn_has_code st st' func
Proof
  strip_tac >> drule_all run_lowering_entry_coverage >> strip_tac >>
  drule runtime_external_internal_phase_split >> strip_tac >>
  gvs[compile_internal_fn_bodies_def, comp_return_def] >>
  drule_then (fn split => rule_assum_tac (REWRITE_RULE [split]))
    compile_fallback_body_entry_checks >>
  gvs[] >> irule fn_has_code_endpoint_coverage >> simp[]
QED

(* runtime_selected_body_shadow for the __default__ fallback: no
   positional arguments, so the body starts right after the payable
   check. *)
Theorem runtime_fallback_body_shadow_with_shadow_nr:
  !tops rpolicy unit lbl ce pos mincd pay nr key ut iv fbody rt st cenv sa sl st'
   bindings ctx cx env env' ret.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
    runtime_fallback_body_start tops rpolicy
      (lbl,ce,pos,mincd,pay,nr,key,ut,iv,fbody,rt) st /\
    compile_register_positional_args ce pos 4 st = (cenv,sa) /\
    compile_guarded_body cenv nr key ut iv fbody rt sa = ((),st') /\
    (if nr then compile_nonreentrant_lock key ut iv else comp_return ()) sa =
      ((),sl) /\
    supported_stmts tops bindings fbody /\ body_inv tops ctx cenv cx /\
    rt = (if ret = NoneT then NONE else SOME ret) /\
    type_stmts env ret fbody = SOME env' ==>
    ?func shadow_ctx shadow_func cenv' sb shadow_sl shadow_sb shadow_unit
     shadow_sa shadow_st'.
      runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
      shadow_ctx = shadow_unit.cu_context /\
      lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
      gas_shadow_context unit.cu_context shadow_ctx /\
      gas_shadow_function func shadow_func /\
      MEM func unit.cu_context.ctx_functions /\
      MEM shadow_func shadow_ctx.ctx_functions /\
      stmts_env cenv NoLoop ret fbody sl = (cenv',sb) /\
      stmts_env (gas_shadow_env T cenv) NoLoop ret (MAP gas_shadow_stmt fbody) shadow_sl =
        (gas_shadow_env T cenv',shadow_sb) /\
      gas_shadow_state sl shadow_sl /\ gas_shadow_state sb shadow_sb /\
      fn_has_code sl sb func /\ fn_has_code sb st' func /\
      fn_has_code shadow_sl shadow_sb shadow_func /\
      gas_shadow_state sa shadow_sa /\
      compile_guarded_body (gas_shadow_env T cenv) nr key ut iv (MAP gas_shadow_stmt fbody) rt
        shadow_sa = ((), shadow_st') /\
      fn_has_code shadow_sa shadow_st' shadow_func
Proof
  rpt gen_tac >> strip_tac >>
  `ALL_DISTINCT (MAP (\p. FST (SND (SND (SND p))))
    (FST (SND (classify_functions tops))))` by
    (irule supported_names_internal_names_distinct >>
     fs[supported_program_def, supported_declaration_names_def]) >>
  fs[runtime_fallback_body_start_def] >>
  gvs[compile_register_positional_args_def, comp_return_def] >>
  rename1 `compile_entry_checks 4 pay checks = ((),st)` >>
  `~EXISTS external_has_defaults exts` by fs[] >>
  qpat_x_assum `lower_vyper_runtime_unit _ _ = _` mp_tac >>
  simp[lower_vyper_runtime_unit_def] >> strip_tac >>
  qspecl_then [`tops`, `F`] mp_tac internal_descriptors_ok >>
  impl_tac >- fs[] >>
  rewrite_tac[pairTheory.FST, pairTheory.SND] >> strip_tac >>
  qpat_assum `classify_functions tops = _`
    (fn th => rule_assum_tac (REWRITE_RULE [th]) >> assume_tac th) >>
  `EVERY (\(lbl,ce,pos,mincd,pay,nr,key,ut,iv,body,rt). jump_label_ok lbl)
    (MAP (set_external_package_target rpolicy.rpol_target o
      package_external_fn tops T (K global_nonreentrant_slot)) exts)` by
    irule runtime_external_package_labels >>
  `lowering_policy_ok rpolicy` by
    (qpat_x_assum `run_lowering _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     rw[run_lowering_def]) >>
  `rpolicy.rpol_frontend_dispatch = Linear` by fs[lowering_policy_ok_def] >>
  `ALL_DISTINCT (MAP FST (MAP (source_internal_fn_descriptor tops F)
     (order_internals (runtime_internal_order tops ints) ints)))` by
    (`PERM (MAP FST (MAP (source_internal_fn_descriptor tops F)
              (order_internals (runtime_internal_order tops ints) ints)))
           (MAP FST (MAP (source_internal_fn_descriptor tops F) ints))` by
       (irule sortingTheory.PERM_MAP >> irule sortingTheory.PERM_MAP >>
        simp[PERM_order_runtime_internals]) >>
     drule sortingTheory.ALL_DISTINCT_PERM >> fs[]) >>
  `EVERY (\d. internal_label_ok (FST d))
     (internal_fn_descriptors
       (MAP (set_internal_package_target rpolicy.rpol_target o
         package_internal_fn tops T (K global_nonreentrant_slot) F 0)
         (order_internals (runtime_internal_order tops ints) ints))) /\
   ALL_DISTINCT (MAP FST (internal_fn_descriptors
       (MAP (set_internal_package_target rpolicy.rpol_target o
         package_internal_fn tops T (K global_nonreentrant_slot) F 0)
         (order_internals (runtime_internal_order tops ints) ints))))` by
    (gvs[GSYM MAP_MAP_o, internal_fn_descriptors_set_internal_package_target,
         internal_fn_descriptors_MAP_package_internal_fn, EVERY_MAP, EVERY_MEM] >>
     fs[MEM_MAP, PULL_EXISTS]) >>
  `fresh_label "fallback" (initial_compile_state "__entry") =
     (fallback_lbl,label_st)` by simp[] >>
  qmatch_asmsub_abbrev_tac
    `run_lowering sels packs ips fall rpolicy 0 0 [] info "__entry"` >>
  `fall = SOME (ce,pay,nr,key,ut,iv,fbody,if ret = NoneT then NONE else SOME ret)` by
    gvs[Abbr `fall`] >>
  qpat_x_assum `Abbrev (fall = _)` kall_tac >> gvs[] >>
  mp_tac (Q.INST
    [`ints` |-> `ips`, `rp` |-> `rpolicy`, `body` |-> `fbody`,
     `rt` |-> `if ret = NoneT then NONE else SOME ret`, `nr` |-> `nr`,
     `buckets` |-> `0`, `metadata` |-> `0`, `dense` |-> `[]`,
     `fl` |-> `fallback_lbl`, `ls` |-> `label_st`, `ds` |-> `dispatch_st`]
    run_lowering_fallback_body_interval) >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule_all guarded_body_code_from_registration >> strip_tac >> gvs[] >>
  rename1 `compile_stmts ce NoLoop _ fbody sl = ((),sb)` >>
  `?cenv'. stmts_env ce NoLoop ret fbody sl = (cenv',sb)` by
    (irule guarded_body_stmts_env >> metis_tac[]) >>
  `fn_has_code sl sb func /\ fn_has_code sb st' func` by
    metis_tac[fn_has_code_split] >>
  qspec_then `packs` mp_tac gas_shadow_compiles_compile_external_fn_bodies >>
  rewrite_tac[gas_shadow_compiles_def] >>
  disch_then (qspecl_then [`dispatch_st`, `dispatch_st`] mp_tac) >>
  simp[gas_shadow_state_refl] >>
  Cases_on `compile_external_fn_bodies (MAP gas_shadow_external_package packs)
    dispatch_st` >>
  rename1 `_ = (z,shadow_opened)` >> simp[] >> strip_tac >> gvs[] >>
  `gas_shadow_state checks (SND (new_block fallback_lbl shadow_opened))` by
    (mp_tac (Q.INST [`label` |-> `fallback_lbl`] gas_shadow_compiles_new_block) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`opened`, `shadow_opened`] mp_tac) >> simp[]) >>
  Cases_on `new_block fallback_lbl shadow_opened` >>
  rename1 `_ = (oldbb,shadow_checks)` >> gvs[] >>
  `oldbb = shadow_opened.cs_current_bb` by
    (qpat_x_assum `new_block fallback_lbl shadow_opened = _` mp_tac >>
     simp[new_block_def]) >>
  `gas_shadow_state st (SND (compile_entry_checks 4 pay shadow_checks))` by
    (mp_tac (Q.INST [`min_cds` |-> `4`, `payable` |-> `pay`]
       gas_shadow_compiles_compile_entry_checks) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`checks`, `shadow_checks`] mp_tac) >> simp[]) >>
  Cases_on `compile_entry_checks 4 pay shadow_checks` >>
  rename1 `_ = (v,shadow_st)` >> Cases_on `v` >> gvs[] >>
  `gas_shadow_state
     (SND (compile_guarded_body ce nr key ut iv fbody
       (if ret = NoneT then NONE else SOME ret) st))
     (SND (compile_guarded_body (gas_shadow_env T ce) nr key ut iv (MAP gas_shadow_stmt fbody)
       (if ret = NoneT then NONE else SOME ret) shadow_st))` by
    (irule (cj 2 (REWRITE_RULE [gas_shadow_compiles_def]
       gas_shadow_compiles_compile_guarded_body)) >> simp[]) >>
  Cases_on `compile_guarded_body (gas_shadow_env T ce) nr key ut iv (MAP gas_shadow_stmt fbody)
    (if ret = NoneT then NONE else SOME ret) shadow_st` >>
  rename1 `_ = (v,shadow_end)` >> Cases_on `v` >> gvs[] >>
  `gas_shadow_compiles
    (if nr then compile_nonreentrant_lock key ut iv else comp_return ())
    (if nr then compile_nonreentrant_lock key ut iv else comp_return ())` by
    (Cases_on `nr` >> simp[gas_shadow_compiles_nonreentrant_lock,
                           gas_shadow_compiles_return]) >>
  Cases_on `(if nr then compile_nonreentrant_lock key ut iv
             else comp_return ()) shadow_st` >>
  rename1 `_ = (answer,shadow_sl)` >> Cases_on `answer` >>
  qpat_x_assum `gas_shadow_compiles _ _` (mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
  disch_then (qspecl_then [`st`, `shadow_st`] mp_tac) >> simp[] >> strip_tac >>
  Cases_on `stmts_env (gas_shadow_env T ce) NoLoop ret (MAP gas_shadow_stmt fbody) shadow_sl` >>
  rename1 `_ = (ec,shadow_sb)` >>
  qspecl_then [`fbody`, `ce`, `NoLoop`, `ret`]
    (drule_then (mp_tac o SPEC_ALL) o Q.SPECL [`sl`, `shadow_sl`] o REWRITE_RULE [gas_shadow_compiles_env_def])
    (Q.INST [`sd` |-> `T`] gas_shadow_stmts_env_env) >>
  simp[] >> strip_tac >> gvs[] >>
  `OPTREL gas_shadow_unit (SOME unit)
    (run_lowering sels (MAP gas_shadow_external_package packs)
      (MAP gas_shadow_internal_package ips)
      (OPTION_MAP gas_shadow_fallback_package
        (SOME (ce,pay,nr,key,ut,iv,fbody,if ret = NoneT then NONE else SOME ret)))
      rpolicy 0 0 [] info "__entry")` by
    (qpat_x_assum `run_lowering sels packs ips _ _ _ _ _ _ _ = SOME unit`
       (SUBST1_TAC o SYM) >> irule gas_shadow_run_lowering) >>
  Cases_on `run_lowering sels (MAP gas_shadow_external_package packs)
      (MAP gas_shadow_internal_package ips)
      (OPTION_MAP gas_shadow_fallback_package
        (SOME (ce,pay,nr,key,ut,iv,fbody,if ret = NoneT then NONE else SOME ret)))
      rpolicy 0 0 [] info "__entry"` >>
  gvs[optionTheory.OPTREL_def] >> rename1 `gas_shadow_unit unit shadow_unit` >>
  `EVERY (\(lbl,ce,pos,mincd,pay,nr,key,ut,iv,body,rt). jump_label_ok lbl)
    (MAP gas_shadow_external_package packs)` by
    simp[runtime_shadow_package_labels, Abbr `packs`, runtime_external_package_labels] >>
  `EVERY (\d. internal_label_ok (FST d))
      (internal_fn_descriptors (MAP gas_shadow_internal_package ips)) /\
    ALL_DISTINCT (MAP FST (internal_fn_descriptors
      (MAP gas_shadow_internal_package ips)))` by
    simp[] >>
  qpat_x_assum `run_lowering sels packs ips _ _ _ _ _ _ _ = _` kall_tac >>
  gvs[gas_shadow_fallback_package_def] >>
  mp_tac (Q.INST
    [`packs` |-> `MAP gas_shadow_external_package packs`,
     `ints` |-> `MAP gas_shadow_internal_package ips`,
     `rp` |-> `rpolicy`, `unit` |-> `shadow_unit`,
     `body` |-> `MAP gas_shadow_stmt fbody`,
     `rt` |-> `if ret = NoneT then NONE else SOME ret`, `nr` |-> `nr`,
     `buckets` |-> `0`, `metadata` |-> `0`, `dense` |-> `[]`,
     `fl` |-> `fallback_lbl`, `ls` |-> `label_st`, `ds` |-> `dispatch_st`,
     `opened` |-> `shadow_opened`, `checks` |-> `shadow_checks`,
     `ce` |-> `gas_shadow_env T ce`,
     `st` |-> `shadow_st`, `st'` |-> `shadow_end`]
    run_lowering_fallback_body_interval) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `stmts_env (gas_shadow_env T ce) NoLoop ret (MAP gas_shadow_stmt fbody) =
   stmts_env (gas_shadow_env T ce) NoLoop
     (case (if ret = NoneT then NONE else SOME ret) of
        NONE => BaseT BoolT | SOME t => t) (MAP gas_shadow_stmt fbody)` by
    (Cases_on `ret = NoneT` >- (
       gvs[] >>
       `~stmts_valued_return (MAP gas_shadow_stmt fbody)` by
         metis_tac[type_stmts_none_valued_return, gas_shadow_valued_return] >>
       `supported_stmts tops bindings (MAP gas_shadow_stmt fbody)` by
         metis_tac[gas_shadow_supported_stmts] >>
       irule stmtsEnvRetTyTheory.stmts_env_ret_ty_no_valued_return >> simp[] >>
       qexistsl_tac [`bindings`, `tops`] >> simp[]) >> simp[]) >>
  `compile_stmts (gas_shadow_env T ce) NoLoop
     (case (if ret = NoneT then NONE else SOME ret) of
        NONE => BaseT BoolT | SOME t => t) (MAP gas_shadow_stmt fbody) shadow_sl =
      ((),shadow_sb)` by
    (simp[stmtSimPropsTheory.compile_stmts_env] >> gvs[]) >>
  qpat_assum `compile_guarded_body _ _ _ _ _ (MAP _ _) _ _ = _`
    (fn built => qpat_assum `fn_has_code shadow_st shadow_end func'`
      (strip_assume_tac o MATCH_MP guarded_body_code_from_registration o CONJ built)) >>
  gvs[] >> rename1 `gas_shadow_state sb shadow_sb` >>
  `gas_shadow_context unit.cu_context shadow_unit.cu_context` by
    fs[gas_shadow_unit_def] >>
  `gas_shadow_function func func'` by
    (mp_tac gas_shadow_lookup_function >>
     disch_then (qspecl_then [`unit.cu_context.ctx_functions`,
        `shadow_unit.cu_context.ctx_functions`, `"__entry"`] mp_tac) >>
     fs[gas_shadow_context_def]) >>
  `runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit` by
    (`~EXISTS external_has_defaults exts` by
       fs[GSYM EVERY_NOT_EXISTS] >>
     qpat_x_assum `~EXISTS external_has_defaults exts` mp_tac >>
     qpat_assum `set_fallback_package_target _ _ = SOME _` mp_tac >>
     qpat_assum `classify_functions tops = _` mp_tac >>
     qpat_assum `run_lowering _ _ _ _ _ _ _ _ _ _ = SOME shadow_unit` mp_tac >>
     rpt (qpat_x_assum `Abbrev _` mp_tac) >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     gvs[runtime_gas_shadow_unit_def, markerTheory.Abbrev_def] >>
     pure_rewrite_tac [gas_shadow_external_package_def,
       gas_shadow_fallback_package_def, GSYM APPEND_ASSOC, APPEND] >>
     Cases_on `EXISTS external_has_defaults exts` >> simp[] >>
     qpat_x_assum `EXISTS external_has_defaults exts`
       (strip_assume_tac o REWRITE_RULE [EXISTS_MEM]) >>
     qpat_x_assum `EVERY ($~ o external_has_defaults) exts`
       (mp_tac o REWRITE_RULE [EVERY_MEM, combinTheory.o_DEF]) >>
     rename1 `MEM external exts` >>
     disch_then (qspec_then `external` mp_tac) >> simp[]) >>
  qexistsl_tac [`func'`, `shadow_sl`, `shadow_sb`, `shadow_unit`,
                `shadow_st`, `shadow_end`] >>
  simp[]
QED

Theorem runtime_fallback_body_shadow_with_shadow:
  !tops rpolicy unit lbl ce pos mincd pay key ut iv fbody rt st cenv sa st'
   bindings ctx cx env env' ret.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
    runtime_fallback_body_start tops rpolicy
      (lbl,ce,pos,mincd,pay,F,key,ut,iv,fbody,rt) st /\
    compile_register_positional_args ce pos 4 st = (cenv,sa) /\
    compile_guarded_body cenv F key ut iv fbody rt sa = ((),st') /\
    supported_stmts tops bindings fbody /\ body_inv tops ctx cenv cx /\
    rt = (if ret = NoneT then NONE else SOME ret) /\
    type_stmts env ret fbody = SOME env' ==>
    ?func shadow_ctx shadow_func cenv' sb shadow_sa shadow_sb shadow_unit.
      runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
      shadow_ctx = shadow_unit.cu_context /\
      lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
      gas_shadow_context unit.cu_context shadow_ctx /\
      gas_shadow_function func shadow_func /\
      MEM func unit.cu_context.ctx_functions /\
      MEM shadow_func shadow_ctx.ctx_functions /\
      stmts_env cenv NoLoop ret fbody sa = (cenv',sb) /\
      stmts_env (gas_shadow_env T cenv) NoLoop ret (MAP gas_shadow_stmt fbody) shadow_sa =
        (gas_shadow_env T cenv',shadow_sb) /\
      gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
      fn_has_code sa sb func /\ fn_has_code sb st' func /\
      fn_has_code shadow_sa shadow_sb shadow_func
Proof
  rpt strip_tac >>
  mp_tac (Q.INST [`nr` |-> `F`, `sl` |-> `sa`] (SPEC_ALL
    runtime_fallback_body_shadow_with_shadow_nr)) >>
  fs[comp_return_def, GSYM EVERY_NOT_EXISTS] >>
  disch_then (qx_choosel_then
    [`func`, `shadow_func`, `cenv'`, `sb`, `shadow_sa`,
     `shadow_sb`, `shadow_unit`, `shadow_start`, `shadow_end`] strip_assume_tac) >>
  qexistsl_tac [`func`, `shadow_func`, `cenv'`, `sb`, `shadow_sa`,
                `shadow_sb`, `shadow_unit`] >> simp[]
QED

(* The body's shadow placement at either entry endpoint: a selected
   external package, or the __default__ fallback. *)
Theorem runtime_entry_body_shadow_with_shadow_nr:
  !tops rpolicy unit lbl ce pos mincd pay nr key ut iv fbody rt st cenv sa sl st'
   bindings ctx cx env env' ret.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
    runtime_entry_body_start tops rpolicy
      (lbl,ce,pos,mincd,pay,nr,key,ut,iv,fbody,rt) st /\
    compile_register_positional_args ce pos 4 st = (cenv,sa) /\
    compile_guarded_body cenv nr key ut iv fbody rt sa = ((),st') /\
    (if nr then compile_nonreentrant_lock key ut iv else comp_return ()) sa =
      ((),sl) /\
    supported_stmts tops bindings fbody /\ body_inv tops ctx cenv cx /\
    rt = (if ret = NoneT then NONE else SOME ret) /\
    type_stmts env ret fbody = SOME env' ==>
    ?func shadow_ctx shadow_func cenv' sb shadow_sl shadow_sb shadow_unit
     shadow_sa shadow_st'.
      runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
      shadow_ctx = shadow_unit.cu_context /\
      lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
      gas_shadow_context unit.cu_context shadow_ctx /\
      gas_shadow_function func shadow_func /\
      MEM func unit.cu_context.ctx_functions /\
      MEM shadow_func shadow_ctx.ctx_functions /\
      stmts_env cenv NoLoop ret fbody sl = (cenv',sb) /\
      stmts_env (gas_shadow_env T cenv) NoLoop ret (MAP gas_shadow_stmt fbody) shadow_sl =
        (gas_shadow_env T cenv',shadow_sb) /\
      gas_shadow_state sl shadow_sl /\ gas_shadow_state sb shadow_sb /\
      fn_has_code sl sb func /\ fn_has_code sb st' func /\
      fn_has_code shadow_sl shadow_sb shadow_func /\
      gas_shadow_state sa shadow_sa /\
      compile_guarded_body (gas_shadow_env T cenv) nr key ut iv (MAP gas_shadow_stmt fbody) rt
        shadow_sa = ((), shadow_st') /\
      fn_has_code shadow_sa shadow_st' shadow_func
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `runtime_entry_body_start _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [runtime_entry_body_start_def])
  >- (drule_all runtime_selected_body_shadow_with_shadow_nr >> simp[])
  >- (drule_all runtime_fallback_body_shadow_with_shadow_nr >> simp[])
QED

Theorem runtime_entry_body_shadow_with_shadow:
  !tops rpolicy unit lbl ce pos mincd pay key ut iv fbody rt st cenv sa st'
   bindings ctx cx env env' ret.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
    runtime_entry_body_start tops rpolicy
      (lbl,ce,pos,mincd,pay,F,key,ut,iv,fbody,rt) st /\
    compile_register_positional_args ce pos 4 st = (cenv,sa) /\
    compile_guarded_body cenv F key ut iv fbody rt sa = ((),st') /\
    supported_stmts tops bindings fbody /\ body_inv tops ctx cenv cx /\
    rt = (if ret = NoneT then NONE else SOME ret) /\
    type_stmts env ret fbody = SOME env' ==>
    ?func shadow_ctx shadow_func cenv' sb shadow_sa shadow_sb shadow_unit.
      runtime_gas_shadow_unit tops rpolicy = SOME shadow_unit /\
      shadow_ctx = shadow_unit.cu_context /\
      lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
      gas_shadow_context unit.cu_context shadow_ctx /\
      gas_shadow_function func shadow_func /\
      MEM func unit.cu_context.ctx_functions /\
      MEM shadow_func shadow_ctx.ctx_functions /\
      stmts_env cenv NoLoop ret fbody sa = (cenv',sb) /\
      stmts_env (gas_shadow_env T cenv) NoLoop ret (MAP gas_shadow_stmt fbody) shadow_sa =
        (gas_shadow_env T cenv',shadow_sb) /\
      gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
      fn_has_code sa sb func /\ fn_has_code sb st' func /\
      fn_has_code shadow_sa shadow_sb shadow_func
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `runtime_entry_body_start _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [runtime_entry_body_start_def])
  >- (drule_all runtime_selected_body_shadow_with_shadow >> simp[])
  >- (drule_all runtime_fallback_body_shadow_with_shadow >> simp[])
QED

Theorem runtime_entry_body_shadow:
  !tops rpolicy unit lbl ce pos mincd pay key ut iv fbody rt st cenv sa st'
   bindings ctx cx env env' ret.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    ~EXISTS external_has_defaults (FST (classify_functions tops)) /\
    runtime_entry_body_start tops rpolicy
      (lbl,ce,pos,mincd,pay,F,key,ut,iv,fbody,rt) st /\
    compile_register_positional_args ce pos 4 st = (cenv,sa) /\
    compile_guarded_body cenv F key ut iv fbody rt sa = ((),st') /\
    supported_stmts tops bindings fbody /\ body_inv tops ctx cenv cx /\
    rt = (if ret = NoneT then NONE else SOME ret) /\
    type_stmts env ret fbody = SOME env' ==>
    ?func shadow_ctx shadow_func cenv' sb shadow_sa shadow_sb.
      lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
      gas_shadow_context unit.cu_context shadow_ctx /\
      gas_shadow_function func shadow_func /\
      MEM func unit.cu_context.ctx_functions /\
      MEM shadow_func shadow_ctx.ctx_functions /\
      stmts_env cenv NoLoop ret fbody sa = (cenv',sb) /\
      stmts_env (gas_shadow_env T cenv) NoLoop ret (MAP gas_shadow_stmt fbody) shadow_sa =
        (gas_shadow_env T cenv',shadow_sb) /\
      gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
      fn_has_code sa sb func /\ fn_has_code sb st' func /\
      fn_has_code shadow_sa shadow_sb shadow_func
Proof
  rpt strip_tac >>
  drule_all runtime_entry_body_shadow_with_shadow >>
  disch_then (qx_choosel_then
    [`func`, `shadow_ctx`, `shadow_func`, `cenv'`, `sb`, `shadow_sa`,
     `shadow_sb`, `shadow_unit`] strip_assume_tac) >>
  qexistsl_tac [`func`, `shadow_ctx`, `shadow_func`, `cenv'`, `sb`,
                `shadow_sa`, `shadow_sb`] >> simp[]
QED
