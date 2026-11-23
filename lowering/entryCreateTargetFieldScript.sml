Theory entryCreateTargetField
Ancestors
  bodyFullTargetAttribute bodyFullTargetDefs targetPlaceSimCasesBase
  gasContext targetPlaceSimDefs
  entryCreateFocusSpec entryCreateScopedBind entryCreateNativeFirstExit
  entryCreateIntervalLayout entryCreateRegionLift entryCreatePendingScope
  entryCreateStmtCases entryCreateBodyCut entryCreateCompletedCut
  createSizeCutCode createSizeCutRegion gasShadowCompileStmtHelpers
  gasShadowCompileHelpers gasShadowCompile gasShadowState gasShadow
  gasOutcomeFullCompose gasExemptCert gasStorage gasSummary
  fragGasOriginPtr fragGasOrigin fragGasPath fragExec loweringPosts
  exprLoweringProps emitHelperProps loweringShapeRules abiEncoderProps
  compilerInstructionSuffix createSizePrefixReplay entryCreatePathScope
  fragGasOriginPtrExec exprSimDefs fragFuel vyperStorageTrace
  vyperTypeEnv vyperStorageFootprint vyperInterpreter vyperState venomState
  compileEnv venomInst vyperTypeSystem bodyFullShared stmtLoweringMono list pair
  arithmetic

Theorem attribute_target_layout[local]:
  type_place_target env (AttributeTarget bt fld) = SOME vt /\
  compile_get_target_ptr compile_expr ce (AttributeTarget bt fld) a = (r,b) /\
  compile_get_target_ptr compile_expr (gas_shadow_env T ce)
    (gas_shadow_target (AttributeTarget bt fld)) sa = (r,sb) /\
  gas_shadow_state a sa /\ fn_has_code a b f /\ fn_has_code sa sb sf ==>
  ?bty fty rb m sm dst.
    vt = Type fty /\ type_place_target env bt = SOME (Type bty) /\
    attribute_type env.type_defs bty fld = SOME fty /\
    compile_get_target_ptr compile_expr ce bt a = (rb,m) /\
    compile_get_target_ptr compile_expr (gas_shadow_env T ce)
      (gas_shadow_target bt) sa = (rb,sm) /\ gas_shadow_state m sm /\
    emit_op ADD [FST rb; Lit (n2w (target_field_offset ce (FST (SND rb))
      (SND (SND rb)) fld))] m = (dst,b) /\
    r = (dst,FST (SND rb),target_field_type ce (SND (SND rb)) fld) /\
    cs_extends a m /\ cs_extends m b /\ a.cs_next_var <= m.cs_next_var /\
    a.cs_next_id <= m.cs_next_id /\ m.cs_next_id <= b.cs_next_id /\
    fn_has_code a m f /\ fn_has_code m b f /\ fn_has_code sa sm sf /\
    create_cut_code {} m b
Proof
  strip_tac >>
  qpat_x_assum `type_place_target _ (AttributeTarget _ _) = _` mp_tac >>
  simp[Once well_typed_expr_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  drule compile_get_target_ptr_attr >> strip_tac >> gvs[] >>
  `gas_shadow_compiles (compile_get_target_ptr compile_expr ce bt)
     (compile_get_target_ptr compile_expr (gas_shadow_env T ce)
       (gas_shadow_target bt))` by irule gas_shadow_stmt_get_target_ptr_env >>
  qpat_x_assum `compile_get_target_ptr _ _ (gas_shadow_target _) _ = _`
    (strip_assume_tac o MATCH_MP compile_get_target_ptr_attr o
     SIMP_RULE std_ss [gas_shadow_expr_def]) >>
  drule_all gas_shadow_step >> strip_tac >> gvs[] >>
  `ci_mono a sm /\ ci_mono sa sm' /\ ci_mono sm b /\ ci_mono sm' sb` by
    metis_tac[ci_mono_compile_get_target_ptr, ci_mono_emit_op, SND] >>
  fs[ci_mono_def] >>
  `fn_has_code a sm f /\ fn_has_code sm b f` by metis_tac[fn_has_code_split] >>
  simp[] >> conj_tac >- metis_tac[fn_has_code_split] >>
  qabbrev_tac `args = [FST rb; Lit (n2w (target_field_offset ce
      (FST (SND rb)) (SND (SND rb)) fld))]` >>
  `create_cut_code {} sm (SND (emit_op ADD args sm))` by
    (irule create_cut_code_emit_op >> simp[create_cut_targets_def]) >>
  pop_assum mp_tac >> asm_rewrite_tac[SND]
QED

Theorem attribute_target_source[local]:
  eval_base_place cx (AttributeTarget bt fld) =
    bind (eval_base_place cx bt) (\pv. extend_place cx pv (AttrSubscript fld))
Proof
  simp[FUN_EQ_THM,Once evaluate_def]
QED

Theorem attribute_base_admissible[local]:
  gas_admissible (eval_base_place cx (AttributeTarget bt fld)) target_res_ok es ==>
  gas_admissible (eval_base_place cx bt) target_res_ok es
Proof
  simp[attribute_target_source,gas_admissible_def,bind_def] >> rpt strip_tac >>
  Cases_on `res` >> simp[target_res_ok_def] >>
  first_x_assum (qspec_then `gs` mp_tac) >> simp[target_res_ok_def]
QED

(* The ADD interval has one installed instruction and no pending call. Thus
   a right hit is size-safe even without any hypothesis about its operands. *)
Theorem attribute_add_fetch[local]:
  emit_op ADD args m = (dst,b) /\ fn_has_code m b f /\
  fn_inst_ids_distinct f /\ create_operand_fetch m b f u i ==>
  i.inst_opcode = ADD
Proof
  strip_tac >> drule added_insts_emit_op >> strip_tac >>
  fs[create_operand_fetch_def, ci_mono_def] >>
  irule (BETA_RULE (Q.INST [`P` |-> `\i. i.inst_opcode = ADD`]
    added_insts_function_property)) >>
  qexistsl_tac [`f`,`m`,`b`] >>
  fs[frag_ids_def,mk_inst_def] >>
  metis_tac[lookup_block_get_instruction_fn_insts]
QED

Theorem attribute_target_cut[local]:
  body_inv tops ctx ce cx /\ MEM f ctx.ctx_functions /\
  create_cut_code {} a m /\ fn_has_code a m f /\
  create_cut_code {} m b /\ fn_has_code m b f /\
  emit_op ADD args m = (dst,b) /\ fn_inst_ids_distinct f /\
  create_operand_cut a m E ctx f tops cx st0 (eval_base_place cx bt) (es,s) ==>
  create_operand_cut a b E ctx f tops cx st0
    (eval_base_place cx (AttributeTarget bt fld)) (es,s)
Proof
  simp[create_operand_cut_def, attribute_target_source] >> rpt strip_tac >>
  drule_all create_interior_visit_first_exit >>
  disch_then (DISJ_CASES_THEN strip_assume_tac)
  >- (irule create_cut_bind_left >> simp[storage_trace_frame_extend_place] >>
      metis_tac[]) >>
  qpat_x_assum `create_interior_visit m b _ _ _ _ _ _`
    (strip_assume_tac o MATCH_MP create_interior_visit_cases) >>
  drule_all attribute_add_fetch >> strip_tac >> gvs[] >>
  simp[create_cut_noncreate_visit]
QED

(* The interval starts with the whole base. Separating its pre-exit region
   from the outer exit is sufficient; the following instruction need not
   even be installed at that outer exit. *)
Theorem attribute_target_scopes[local]:
  body_inv tops ctx ce cx /\ MEM f ctx.ctx_functions /\
  create_cut_code {} a m /\ fn_has_code a m f /\
  create_cut_code {} m b /\ fn_has_code m b f /\
  create_layout a b /\ create_operand_at a s ==>
  (!marks. create_operand_focus_scope a m E ctx f s marks ==>
           create_operand_focus_scope a b E ctx f s marks) /\
  (!marks r. exit_result r /\ create_operand_full_scope a m E ctx f s marks r ==>
             create_operand_full_scope a b E ctx f s marks r) /\
  (!left t right. create_operand_full_scope a m E ctx f s left (OK t) /\
                  create_operand_focus_scope m b E ctx f t right ==>
                  create_operand_focus_scope a b E ctx f s (left ++ right)) /\
  (!left t right r. create_operand_full_scope a m E ctx f s left (OK t) /\
                    create_operand_full_scope m b E ctx f t right r ==>
                    create_operand_full_scope a b E ctx f s (left ++ right) r)
Proof
  strip_tac >>
  `create_cut_region a m s` by
    (fs[create_operand_at_def] >> metis_tac[cj 1 create_cut_region_rules]) >>
  `!u. create_cut_region a m u /\ ~create_operand_at m u ==>
       ~create_operand_at b u` by metis_tac[create_cut_code_def,create_layout_left_stop] >>
  `a.cs_next_id <= m.cs_next_id /\ m.cs_next_id <= b.cs_next_id` by
    fs[create_cut_code_def] >>
  conj_tac >- metis_tac[create_left_focus_lift_at] >>
  conj_tac >- metis_tac[create_left_terminal_lift_at] >>
  `!left t. create_expr_prefix a m E ctx f s left t ==>
             create_expr_prefix a b E ctx f s left t` by
    metis_tac[create_left_prefix_lift_at] >>
  `!t right u. create_expr_prefix m b E ctx f t right u ==>
                create_expr_prefix a b E ctx f t right u` by
    (rpt strip_tac >> irule create_expr_prefix_mono >>
     first_assum (irule_at Any) >> simp[create_prefix_step_def,frag_ids_def] >>
     metis_tac[LESS_EQ_TRANS]) >>
  conj_tac >- suspend "right_focus" >> suspend "right_full"
QED

Resume attribute_target_scopes[right_focus]:
  simp[create_operand_full_scope_def,create_operand_focus_scope_def] >>
  rpt gen_tac >> disch_then (map_every strip_assume_tac o CONJUNCTS) >>
  rename1 `create_expr_prefix m b E ctx f t suffix stop` >>
  `create_expr_prefix a b E ctx f s (left ++ suffix) stop` by
    metis_tac[create_expr_prefix_append] >>
  qexistsl_tac [`left ++ suffix`,`stop`,`pending`] >> simp[APPEND_ASSOC] >>
  disj2_tac >> simp[] >> rpt strip_tac >>
  `create_cut_region m b t` by metis_tac[cj 1 create_cut_region_rules] >>
  `create_cut_region m b stop` by metis_tac[create_expr_prefix_cut_region] >>
  drule_all create_cut_region_rules >> disch_then (assume_tac o cj 2) >>
  fs[create_prefix_step_def] >> metis_tac[]
QED

Resume attribute_target_scopes[right_full]:
  Cases_on `r` >> simp[create_operand_full_scope_def] >>
  rpt strip_tac >> metis_tac[APPEND_ASSOC,create_expr_prefix_append]
QED

Finalise attribute_target_scopes

Theorem scoped_target_posts[local]:
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a b source (es,s,G,tn) Q R /\
  (!H res ee gt q. R H res ee gt q ==> ?exc. res = INR exc) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a b source (es,s,G,tn)
    (\H res ee G tn t. Q H res ee G tn t /\ ee.gas_obs = [])
    (\H res ee gt q. (?exc. res = INR exc) /\ R H res ee gt q)
Proof
  simp[scoped_operand_outcome_def] >> metis_tac[]
QED

(* The guard is a property of the concrete installed interval. Restrict it
   to the child's interval before using the paired induction hypothesis. *)
Theorem create_target_attribute_case:
  (!a b arg off out s w u tops cx st0 source es res ee DF lo E C f PG G tn Q R.
    emit_op ADD [arg; Lit (n2w off)] a = (Var out,b) /\
    fn_has_code a b f /\ create_operand_at a s /\ ~s.vs_halted /\
    eval_operand arg s = SOME w /\
    u = (update_var out (w + n2w off) s with vs_inst_idx := SUC s.vs_inst_idx) /\
    storage_trace_domain cx st0 ee.storage_trace /\
    (!tail. source (es with gas_obs := tail) =
      (res : eval_result + exception,ee with gas_obs := tail)) /\
    (?G' tn'. !H. valid_horizon cx st0 H ee.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,E,C,f,PG) (s,G,tn) [] (OK u,G',tn') /\
      Q H res (ee with gas_obs := []) G' tn' u) ==>
    scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a b
      source (es,s,G,tn) Q R) /\
  (!a. create_cut_code {} a (SND (compile_get_target_ptr compile_expr ce bt a))) /\
  body_inv (cx_tops cx) ctx ce cx /\ target_pre ce cx env (AttributeTarget bt fld) es /\
  target_sim_judgment
    (\(D,l,E,C,f,P) tops cx st0 a b source (e,s,G,tn) Q R.
      create_layout a b ==>
      scoped_operand_outcome (D,l,E,C,f,P) tops cx st0 a b source (e,s,G,tn) Q R /\
      create_operand_cut a b E C f tops cx st0 source (e,s))
    (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx env bt es ==>
  target_sim_judgment
    (\(D,l,E,C,f,P) tops cx st0 a b source (e,s,G,tn) Q R.
      create_layout a b ==>
      scoped_operand_outcome (D,l,E,C,f,P) tops cx st0 a b source (e,s,G,tn) Q R /\
      create_operand_cut a b E C f tops cx st0 source (e,s))
    (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx env (AttributeTarget bt fld) es
Proof
  strip_tac >> simp[target_sim_judgment_def] >> rpt gen_tac >> rpt disch_tac >>
  qpat_x_assum `type_place_target _ _ = _ /\ _` strip_assume_tac >>
  drule_all attribute_target_layout >> strip_tac >> gvs[] >>
  `gas_admissible (eval_base_place cx bt) target_res_ok es` by
    metis_tac[attribute_base_admissible] >>
  `create_layout sa m` by metis_tac[create_layout_subinterval,cs_extends_refl] >>
  `create_cut_code {} sa m` by
    (qpat_assum `!a. create_cut_code {} a _` (qspec_then `sa` mp_tac) >>
     qpat_assum `compile_get_target_ptr compile_expr ce bt sa = _`
       (fn th => PURE_REWRITE_TAC[th,SND]) >> simp[]) >>
  `create_operand_at sa s0` by simp[create_operand_at_def] >>
  qpat_x_assum `target_sim_judgment _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE[target_sim_judgment_def]) >>
  disch_then (qspecl_then [`st0`,`Type bty`,`sa`,`m`,`shadow_sa`,
                           `sm`,`rb`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> simp[] >> strip_tac >>
  reverse conj_tac >- metis_tac[attribute_target_cut] >>
  suspend "scoped"
QED

Resume create_target_attribute_case[scoped]:
  qmatch_asmsub_abbrev_tac
    `scoped_operand_outcome _ _ _ _ sa m (eval_base_place cx bt) _ childQ R` >>
  qmatch_goalsub_abbrev_tac
    `scoped_operand_outcome _ _ _ _ sa sb _ _ Q R` >>
  `!H res ee gt q. R H res ee gt q ==> ?exc. res = INR exc` by
    (simp[Abbr `R`] >> Cases_on `res` >> simp[expr_exit_def]) >>
  drule_all scoped_target_posts >> strip_tac >>
  simp[attribute_target_source] >> irule scoped_operand_bind_all >>
  simp[evaluate_storage_trace_frame,storage_trace_frame_extend_place] >>
  conj_tac
  >- (rpt strip_tac >> simp[Once ignore_bind_def, Once bind_assoc,
                             GSYM ignore_bind_def] >>
      irule gas_exempt_cert_bind_result >>
      qexistsl_tac [`mid`,`t`,`v`] >> fs[]) >>
  conj_tac
  >- (rpt strip_tac >> simp[Once ignore_bind_def, Once bind_assoc,
                             GSYM ignore_bind_def] >>
      irule gas_exempt_cert_error_result >> simp[]) >>
  qexistsl_tac [`\H res ee G tn t. childQ H res ee G tn t /\ ee.gas_obs = []`,`m`] >>
  simp[] >> drule_all attribute_target_scopes >>
  disch_then (qspec_then `gas_explicit_sites ctx shadow_ctx` strip_assume_tac) >>
  simp[] >> reverse conj_tac
  >- (conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `~t.vs_halted` by
    (drule gas_origin_ptr_path_exec >> simp[exit_result_def]) >>
  qunabbrev_tac `childQ` >> RULE_ASSUM_TAC BETA_RULE >>
  `gas_admissible (bind (eval_base_place cx bt)
     (\pv. extend_place cx pv (AttrSubscript fld))) target_res_ok es` by
    metis_tac[attribute_target_source] >>
  `(!H. valid_horizon cx st0 H mid.storage_trace ==>
      ((?pv. res = INL pv /\ target_post H ctx func ce cx es sa m s0 mid pv (Type bty) rb t /\
        t.vs_current_bb = m.cs_current_bb /\ t.vs_inst_idx = LENGTH m.cs_current_insts /\
        alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
        s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at (DF H) lo d ce cx mid G1 tn1 t /\
        target_ptr_ok ce pv rb G1 tn1 t /\ ghost_kept_at lo ce es sa G0 tn0 s0 G1 tn1) /\
       ~t.vs_halted /\ mid.gas_obs = []))` by (rpt strip_tac >> res_tac >> simp[]) >>
  drule_all (Q.INST [`explicit` |-> `gas_explicit_sites ctx shadow_ctx`, `PG` |-> `PG`]
    target_attribute_selected_endpoint) >>
  disch_then (qspecl_then [`shadow_ctx`,`PG`] strip_assume_tac) >>
  qexists_tac `pv` >> simp[] >>
  first_assum irule >> simp[] >>
  qexistsl_tac [`FST rb`,`mid`,`target_field_offset ce (FST (SND rb))
    (SND (SND rb)) fld`,`out`,`INL pv'`,`w`] >>
  simp[] >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  qexistsl_tac [`G'`,`tn'`] >>
  qunabbrev_tac `Q` >> BETA_TAC >> qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path _ (t,G1,tn1) [] _ /\ _`
    (qspec_then `H` mp_tac) >>
  qpat_x_assum `u = _` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `dst = Var _` SUBST_ALL_TAC >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  asm_rewrite_tac[] >> qexists_tac `pv'` >> asm_rewrite_tac[]
QED

Finalise create_target_attribute_case
