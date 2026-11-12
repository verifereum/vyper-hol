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
  gasShadowStmtEnv externalCallSelected supportedProgramProps supportedNames
  loweringShapeSource

val _ = Parse.hide "body";

Theorem run_lowering_pinned_body_interval[local]:
  run_lowering sels (pre ++ (lbl,ce,pos,mincd,pay,nr,key,ut,iv,body,rt)::post)
    ints fb rp buckets metadata dense info "__entry" = SOME unit /\
  rp.rpol_frontend_dispatch = Linear /\
  EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl) sels /\
  EVERY external_fn_shape_ok
    (pre ++ (lbl,ce,pos,mincd,pay,nr,key,ut,iv,body,rt)::post) /\
  EVERY internal_fn_shape_ok ints /\ fallback_shape_ok fb /\
  EVERY (\d. internal_label_ok (FST d)) (internal_fn_descriptors ints) /\
  ALL_DISTINCT (MAP FST (internal_fn_descriptors ints)) /\
  fresh_label "fallback" (initial_compile_state "__entry") = (fl,ls) /\
  compile_selector_dispatch_linear (MAP (\(sel,lbl,z). (sel,lbl)) sels)
    fl ls = ((),ds) /\
  compile_external_fn_bodies pre ds = ((),opened) /\
  new_block lbl opened = (opened.cs_current_bb,checks) /\
  compile_entry_checks mincd pay checks = ((),st) /\
  compile_register_positional_args ce pos 4 st = (cenv,sa) /\
  compile_guarded_body cenv nr key ut iv body rt sa = ((),st') ==>
  ?func.
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
    MEM func unit.cu_context.ctx_functions /\
    shape_state sa /\ cs_extends sa st' /\ fn_has_code sa st' func
Proof
  strip_tac >>
  `shape_state (initial_compile_state "__entry")` by
    simp[shape_state_initial_compile_state] >>
  Cases_on `compile_generate_runtime sels
    (pre ++ (lbl,ce,pos,mincd,pay,nr,key,ut,iv,body,rt)::post)
    ints fb Linear buckets metadata dense info (initial_compile_state "__entry")` >>
  rename1 `_ = (u,final)` >> Cases_on `u` >>
  drule_all runtime_dispatch_shape_boundary >> strip_tac >>
  drule_all runtime_external_boundary >> strip_tac >>
  gvs[] >>
  `EVERY external_fn_shape_ok pre` by gvs[EVERY_APPEND] >>
  drule_all external_bodies_run_shape >> strip_tac >>
  `shape_state checks` by metis_tac[shape_state_new_block] >>
  mp_tac compile_entry_checks_shape >> simp[shape_step_def] >>
  disch_then drule >> simp[] >> strip_tac >>
  `compile_external_function_body ce pos nr key ut iv body rt st = ((),st')` by
    simp[compile_external_function_body_def, comp_bind_def] >>
  drule external_function_registration_boundary >>
  impl_tac >- gvs[external_fn_shape_ok_def] >> strip_tac >> gvs[] >>
  `compile_external_fn_bodies
    [(lbl,ce,pos,mincd,pay,nr,key,ut,iv,body,rt)] opened = ((),st')` by
    simp[compile_external_fn_bodies_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def] >>
  `compile_external_fn_bodies post st' = ((),external_st)` by
    (qpat_x_assum `compile_external_fn_bodies (_ ++ _) _ = _` mp_tac >>
     rewrite_tac[external_bodies_append] >> strip_tac >> gvs[] >>
     qpat_x_assum `compile_external_fn_bodies (_::_) _ = _` mp_tac >>
     pure_once_rewrite_tac[external_bodies_cons_split] >> strip_tac >> gvs[]) >>
  `shape_state st'` by
    (irule (cj 1 external_bodies_run_shape) >>
     qexistsl_tac [`[(lbl,ce,pos,mincd,pay,nr,key,ut,iv,body,rt)]`, `opened`] >>
     simp[]) >>
  `shape_state external_st /\ cs_extends st' external_st` by
    (irule external_bodies_run_shape >> simp[] >> qexists_tac `post` >> simp[]) >>
  drule_all external_fallback_suffix_extends >> strip_tac >>
  `MEM (mk_raw_function "__entry" (all_blocks entry_end))
    unit.cu_context.ctx_functions` by
    (irule run_lowering_packaged_entry_member >>
     goal_assum $ drule_at Any >> simp[] >> metis_tac[]) >>
  `?func. lookup_function "__entry" unit.cu_context.ctx_functions = SOME func` by
    (irule lookup_function_exists_for_name >> simp[MEM_MAP] >>
     goal_assum $ drule_at Any >> simp[mk_raw_function_def]) >>
  `cs_extends st' entry_end` by metis_tac[cs_extends_trans] >>
  drule_all run_lowering_entry_interval >> strip_tac >>
  qexists_tac `func` >> simp[] >>
  irule external_decoder_fn_has_code >> simp[] >>
  qexists_tac `registered` >> simp[cs_extends_refl]
QED

(* From the pinned start st, the shadow chain runs the spine's per-step
   gas_shadow_compiles results (fresh_label, dispatch,
   compile_external_fn_bodies of the prefix, new_block, entry checks,
   registration, guarded body) from gas_shadow_state_refl, and the shadow
   unit from gas_shadow_run_lowering holds its code at the same labels.

   Intuition:
   - The actual unit is run_lowering's (supported_program excludes
     defaults; lowering_policy_ok forces Linear dispatch), so st, sa, sb,
     st' are its compile states; source_selected_body_code's chain
     (runtime_external_boundary, external_bodies_append/run_shape,
     run_lowering_entry_interval, fn_has_code_split/mid) gives the actual
     fn_has_code facts at these pinned states.
   - gas_shadow_inst is a relation, not a function, so cs_extends does not
     transfer from the actual to the shadow side: the same generic chain
     has to run on the shadow packages, which needs their shapes
     (expr_shape_root is invariant under gas_shadow_expr: Call targets are
     kept and builtin_arity (Env _) = 0).
   - The shadow body at type ret lands where the shadow guarded body's
     compile at (case rt ...) does: stmts_env_ret_ty on the shadow body,
     which needs supported_stmts preserved by gas_shadow_stmt (Env MsgGas
     and Env GasPrice are both supported env builtins) and
     ~stmts_valued_return preserved.
   - The shadow stmts_env pairs with the actual one through a
     gas_shadow_compiles result for stmts_env (FST equal: same cenv').
   - gas_shadow_lookup_function gives the shadow partner of func. *)
Theorem runtime_selected_body_shadow:
  !tops rpolicy unit lbl ce pos mincd pay key ut iv fbody rt st cenv sa st'
   bindings ctx cx env env' ret.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
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
      stmts_env cenv NoLoop ret (MAP gas_shadow_stmt fbody) shadow_sa =
        (cenv',shadow_sb) /\
      gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
      fn_has_code sa sb func /\ fn_has_code sb st' func /\
      fn_has_code shadow_sa shadow_sb shadow_func
Proof
  rpt gen_tac >> strip_tac >>
  `runtime_bodies_shape_ok tops` by
    metis_tac[supported_program_runtime_bodies_shape_ok] >>
  `ALL_DISTINCT (MAP (\p. FST (SND (SND (SND p))))
    (FST (SND (classify_functions tops))))` by
    (irule supported_names_internal_names_distinct >>
     fs[supported_program_def, supported_declaration_names_def]) >>
  fs[runtime_selected_body_start_def] >>
  `~EXISTS external_has_defaults exts` by
    (drule supported_program_no_external_defaults >> simp[]) >>
  qpat_x_assum `lower_vyper_runtime_unit _ _ = _` mp_tac >>
  simp[lower_vyper_runtime_unit_def] >> strip_tac >>
  qspecl_then [`tops`, `F`] mp_tac internal_descriptors_ok >>
  impl_tac >- fs[] >>
  rewrite_tac[pairTheory.FST, pairTheory.SND] >> strip_tac >>
  `EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl)
    (build_selectors (type_env tops) exts)` by
    rewrite_tac[build_selectors_fn_labels] >>
  `EVERY external_fn_shape_ok
    (pre ++ (lbl,ce,pos,mincd,pay,F,key,ut,iv,fbody,rt)::post)` by
    (qpat_x_assum `MAP _ exts = _` (SUBST1_TAC o SYM) >>
     simp[EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
     irule package_external_fn_shape_ok >> gs[]) >>
  `EVERY internal_fn_shape_ok
    (MAP (set_internal_package_target rpolicy.rpol_target o
      package_internal_fn tops T (K global_nonreentrant_slot) F 0) ints)` by
    (simp[EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
     irule package_internal_fn_shape_ok >> gs[]) >>
  `fallback_shape_ok (set_fallback_package_target rpolicy.rpol_target
    (package_fallback_fn tops T (K global_nonreentrant_slot) fb))` by
    (qspecl_then [`tops`, `T`, `K global_nonreentrant_slot`,
       `rpolicy.rpol_target`] mp_tac package_fallback_fn_shape_ok >> gs[]) >>
  `lowering_policy_ok rpolicy` by
    (qpat_x_assum `run_lowering _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     rw[run_lowering_def]) >>
  `rpolicy.rpol_frontend_dispatch = Linear` by fs[lowering_policy_ok_def] >>
  FAIL_TAC "actual packaging prefix"
QED
