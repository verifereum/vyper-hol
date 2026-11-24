(* Constructor immutable attribute targets: one scoped base evaluation,
   followed by the singleton ADD at that evaluation's physical exit. *)
Theory entryCreateTargetImmField
Ancestors
  bodyFullTargetAttribute bodyFullTargetRoots bodyFullTargetDefs
  entryCreateScopedBind entryCreateIntervalLayout entryCreateRegionLift
  entryCreateNativeFirstExit entryCreateFocusSpec entryCreateAdminSequence
  entryCreateCompletedCut createSizeCutCode createSizeCutRegion
  targetPlaceSimCasesBase gasShadowCompileStmtHelpers gasShadowState
  gasShadowCompileHelpers stmtLoweringMono exprLoweringProps emitHelperProps
  gasSummaryCompose gasExemptCert fragGasOriginPtr fragGasOrigin
  vyperStorageTrace vyperStorageFootprint venomRunBounded arithmetic pair list
  vyperTypeEnv exprSimHypsDefs exprSimDefs vyperTyping vyperState gasShadow
  bodyFullShared fragExec compileEnv gasSummary targetPlaceSimCases
  vyperTypeInvariants vyperTypeSystem gasContext gasOutcomeFull
  entryCreatePendingScope entryCreatePathScope entryCreateBodyCut entryCreateStmtCases
  createSizePrefixReplay createExprSizeExitDefs fragGasOriginPtrExec
  venomExecSemantics exprSimAbiGasBridge loweringShapeRules venomInst
  abiEncoderProps entryCreateOperandReplay targetPlaceSim allocLimits
  loweringPosts vyperStorageBackend bodyPtrDefs

Theorem imm_field_visit_opcode[local]:
  body_inv tops ctx cenv cx /\ MEM f ctx.ctx_functions /\
  fn_has_code m b f /\ create_cut_code {} m b /\
  emit_op ADD ops m = (dst,b) /\ create_operand_at m t /\
  create_interior_visit m b E ctx f (p,d,k) t (before,(key,g,i,u),after) ==>
  i.inst_opcode = ADD
Proof
  strip_tac >> drule emit_op_facts >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  `!v j. create_cut_region m b v /\ create_operand_fetch m b f v j ==>
          j.inst_opcode = ADD` by
    (simp[create_operand_fetch_def,create_operand_at_def] >> rpt strip_tac >>
     `MEM j (frag_code m b) /\ j.inst_id IN frag_ids m b` by
       (irule (cj 2 create_cut_region_rules) >> simp[] >> metis_tac[]) >>
     `emitted_blocks m b = []` by simp[emitted_blocks_def] >>
     gvs[frag_code_def,mk_inst_def]) >>
  `create_cut_region m b t` by
    (irule (cj 1 create_cut_region_rules) >> fs[create_operand_at_def] >> metis_tac[]) >>
  drule create_interior_visit_cases >> strip_tac
  >- (gvs[] >> drule_all_then assume_tac create_expr_prefix_cut_region >> metis_tac[]) >>
  drule_all_then assume_tac create_expr_prefix_cut_region >>
  `ADD = INVOKE` suffices_by simp[] >> metis_tac[]
QED

(* On a typed base an exceptional outcome is necessarily a source error.
   This changes the post only; it does not introduce a new scoped witness. *)
Theorem imm_field_scope_error[local]:
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a m source (es,s,G,tn) Q R /\
  (!H res ee gt r. R H res ee gt r ==> expr_exit res r) ==>
  scoped_operand_outcome (DF,lo,E,C,f,PG) tops cx st0 a m source (es,s,G,tn)
    Q (\H res ee gt r. (?exc. res = INR exc) /\ R H res ee gt r)
Proof
  simp[scoped_operand_outcome_def] >>
  disch_then (CONJUNCTS_THEN2 (qx_choose_then `marks` assume_tac) assume_tac) >>
  qexists_tac `marks` >>
  pop_assum (fn law =>
    `!H res ee gt r. R H res ee gt r ==> ?exc. res = INR exc` by
      (rpt strip_tac >> drule law >> Cases_on `res` >> simp[expr_exit_def])) >>
  qpat_x_assum `_ \/ _` (DISJ_CASES_THEN2 assume_tac
    (DISJ_CASES_THEN2 strip_assume_tac assume_tac)) >> simp[] >>
  disj2_tac >> disj1_tac >> qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >>
  simp[] >> metis_tac[]
QED

Theorem imm_field_post_gas_obs[local]:
  (imm_target_post H C f ce cx es a b s (ee with gas_obs := gs) id path ty r t <=>
   imm_target_post H C f ce cx es a b s ee id path ty r t) /\
  (ghost_inv_at D lo d ce cx (ee with gas_obs := gs) G tn t <=>
   ghost_inv_at D lo d ce cx ee G tn t)
Proof
  `!p. get_storage cx (ee with gas_obs := gs) p = get_storage cx ee p` by
    (Cases >> simp[get_storage_def]) >>
  simp[imm_target_post_def,stmt_state_rel_start_gas_obs,storage_well_formed_on_def,
       locals_kept_def,popped_kept_def,ghost_inv_at_def]
QED

Theorem imm_field_scope_join[local]:
  body_inv tops C ce cx /\ MEM f C.ctx_functions /\
  create_cut_code {} a m /\ fn_has_code a m f /\
  create_cut_code {} m b /\ fn_has_code m b f /\
  create_layout a b /\ cs_extends a m /\ cs_extends m b /\
  a.cs_next_id <= m.cs_next_id /\ m.cs_next_id <= b.cs_next_id /\
  create_cut_region a m s ==>
  (!marks. create_operand_focus_scope a m E C f s marks ==>
           create_operand_focus_scope a b E C f s marks) /\
  (!marks r. exit_result r /\ create_operand_full_scope a m E C f s marks r ==>
             create_operand_full_scope a b E C f s marks r) /\
  (!left t right. create_operand_full_scope a m E C f s left (OK t) /\
        create_operand_focus_scope m b E C f t right ==>
        create_operand_focus_scope a b E C f s (left ++ right)) /\
  (!left t right r. create_operand_full_scope a m E C f s left (OK t) /\
        create_operand_full_scope m b E C f t right r ==>
        create_operand_full_scope a b E C f s (left ++ right) r)
Proof
  strip_tac >>
  `!v. create_cut_region a m v /\ ~create_operand_at m v ==>
         ~create_operand_at b v` by metis_tac[create_layout_left_stop] >>
  `!left t. create_expr_prefix a m E C f s left t ==>
            create_expr_prefix a b E C f s left t` by metis_tac[create_left_prefix_lift_at] >>
  `!t marks u. create_expr_prefix m b E C f t marks u ==>
               create_expr_prefix a b E C f t marks u` by
    (rpt strip_tac >> irule create_expr_prefix_mono >> first_assum (irule_at Any) >>
     simp[create_prefix_step_def,frag_ids_def] >> metis_tac[LESS_EQ_TRANS]) >>
  rpt conj_tac
  >- metis_tac[create_left_focus_lift_at]
  >- metis_tac[create_left_terminal_lift_at]
  >- (rpt gen_tac >> simp[create_operand_full_scope_def,create_operand_focus_scope_def] >>
      disch_then (map_every strip_assume_tac o CONJUNCTS) >>
      rename1 `create_expr_prefix m b E C f t front stop` >>
      `create_expr_prefix a b E C f s (left ++ front) stop` by
        metis_tac[create_expr_prefix_append] >>
      qexistsl_tac [`left ++ front`,`stop`,`pending`] >> simp[APPEND_ASSOC] >>
      `create_cut_region m b t` by metis_tac[cj 1 create_cut_region_rules] >>
      `create_cut_region m b stop` by metis_tac[create_expr_prefix_cut_region] >>
      disj2_tac >> rpt strip_tac >>
      qpat_x_assum `create_prefix_step a b E C f stop _ _`
        (strip_assume_tac o REWRITE_RULE [create_prefix_step_def]) >>
      qpat_assum `!right v. create_prefix_step m b E C f stop right v ==> _` irule >>
      qexists_tac `v` >> irule (cj 1 operand_cut_region_edge) >>
      simp[] >> metis_tac[]) >>
  rpt gen_tac >> Cases_on `r` >> simp[create_operand_full_scope_def] >> strip_tac >>
  metis_tac[create_expr_prefix_append,APPEND_ASSOC]
QED

Theorem create_immutable_target_attribute_case:
  (!DF' lo' E C f PG' tops' cx' st0' m b arg off out s u w es' ee res G tn
      G' tn' src Q R.
     emit_op ADD [arg; Lit (n2w off)] m = (Var out,b) /\
     fn_has_code m b f /\ create_operand_at m s /\ ~s.vs_halted /\
     eval_operand arg s = SOME w /\
     u = (update_var out (w + n2w off) s with vs_inst_idx := SUC s.vs_inst_idx) /\
     storage_trace_domain cx' st0' ee.storage_trace /\
     (!tail. src (es' with gas_obs := tail) = (res,ee with gas_obs := tail)) /\
     (!H. valid_horizon cx' st0' H ee.storage_trace ==>
       gas_origin_ptr_path (DF' H,lo',E,C,f,PG') (s,G,tn) [] (OK u,G',tn') /\
       Q H res (ee with gas_obs := []) G' tn' u) ==>
     scoped_operand_outcome (DF',lo',E,C,f,PG') tops' cx' st0' m b
       (src : evaluation_state -> place evaluation_result) (es',s,G,tn) Q R) /\
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  target_indices_pre cenv cx env bt /\ immutable_root cx bt /\
  (!sa sm rb. compile_get_target_ptr compile_expr cenv bt sa = (rb,sm) ==>
              create_cut_code {} sa sm) /\
  imm_target_place_sim_judgment
    (\(D,l,E,C,f,P) ts x st0 a b source (e,s,G,tn) Q R.
      create_layout a b ==>
      scoped_operand_outcome (D,l,E,C,f,P) ts x st0 a b source (e,s,G,tn) Q R /\
      create_operand_cut a b E C f ts x st0 source (e,s))
    (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx env bt es ==>
  imm_target_place_sim_judgment
    (\(D,l,E,C,f,P) ts x st0 a b source (e,s,G,tn) Q R.
      create_layout a b ==>
      scoped_operand_outcome (D,l,E,C,f,P) ts x st0 a b source (e,s,G,tn) Q R /\
      create_operand_cut a b E C f ts x st0 source (e,s))
    (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx env
    (AttributeTarget bt fld) es
Proof
  strip_tac >> simp[imm_target_place_sim_judgment_def] >> rpt gen_tac >> strip_tac >>
  fs[type_place_target_AttributeTarget] >>
  rename1 `type_place_target env bt = SOME (Type bty)` >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def,env_consistent_def,env_context_consistent_def] >>
  `?sid. bty = StructT sid` by (Cases_on `bty` >> fs[attribute_type_def]) >>
  gvs[] >>
  drule_then strip_assume_tac compile_get_target_ptr_attr >> gvs[] >>
  qpat_x_assum `compile_get_target_ptr _ _ (gas_shadow_target _) _ = _`
    (strip_assume_tac o MATCH_MP compile_get_target_ptr_attr o
     SIMP_RULE std_ss [gas_shadow_expr_def]) >>
  rename1 `compile_get_target_ptr _ _ (gas_shadow_target bt) shadow_sa =
             (srb,shadow_sm)` >>
  `gas_shadow_compiles (compile_get_target_ptr compile_expr cenv bt)
     (compile_get_target_ptr compile_expr (gas_shadow_env T cenv)
       (gas_shadow_target bt))` by irule gas_shadow_stmt_get_target_ptr_env >>
  drule_all gas_shadow_step >> strip_tac >> gvs[] >> strip_tac >>
  `ci_mono sa sm /\ ci_mono shadow_sa shadow_sm` by
    metis_tac[ci_mono_compile_get_target_ptr,SND] >>
  `ci_mono sm sb /\ ci_mono shadow_sm shadow_sb` by
    metis_tac[ci_mono_emit_op,SND] >>
  `cs_extends sa sm /\ cs_extends sm sb /\ sa.cs_next_var <= sm.cs_next_var /\
   sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id <= sb.cs_next_id /\
   cs_extends shadow_sa shadow_sm /\ cs_extends shadow_sm shadow_sb` by
    fs[ci_mono_def] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func /\
   fn_has_code shadow_sa shadow_sm shadow_func` by metis_tac[fn_has_code_split] >>
  `create_layout sa sm` by metis_tac[create_layout_subinterval, cs_extends_refl] >>
  drule_then (fn th => RULE_ASSUM_TAC (REWRITE_RULE[th]) >> REWRITE_TAC[th])
    immutable_target_attribute_source >>
  `gas_admissible (eval_target_place cx bt) target_place_res_ok es` by
    (qpat_x_assum `gas_admissible (bind _ _) _ _` mp_tac >>
     simp[gas_admissible_def,bind_def] >> rpt strip_tac >>
     Cases_on `res` >> simp[target_place_res_ok_def] >>
     first_x_assum (qspec_then `gs` mp_tac) >> simp[target_place_res_ok_def]) >>
  qpat_x_assum `imm_target_place_sim_judgment _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE[imm_target_place_sim_judgment_def]) >>
  disch_then (qspecl_then [`st0`,`StructT sid`,`sa`,`sm`,`shadow_sa`,
    `shadow_sm`,`rb`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac
    `scoped_operand_outcome _ _ _ _ _ _ (eval_target_place cx bt) _ childQ childR` >>
  qmatch_asmsub_abbrev_tac `emit_op ADD [FST rb; Lit (n2w field_off)] sm` >>
  `create_cut_code {} sa sm` by metis_tac[] >>
  `create_cut_code {} sm sb` by
    (`SND (emit_op ADD [FST rb; Lit (n2w field_off)] sm) = sb` by simp[] >>
     pop_assum (SUBST1_TAC o SYM) >> simp[create_cut_code_emit_op,create_cut_targets_def]) >>
  `create_operand_at sa s0` by simp[create_operand_at_def] >>
  `create_cut_region sa sm s0` by metis_tac[create_cut_region_rules] >>
  qabbrev_tac `E = gas_explicit_sites ctx shadow_ctx` >>
  `!p. storage_trace_frame
     (bind (extend_place cx (PlaceR p) (AttrSubscript fld)) get_place)` by
    simp[storage_trace_frame_bind,storage_trace_frame_extend_place,storage_trace_frame_get_place] >>
  reverse conj_tac
  >- suspend "cut" >>
  suspend "outcome"
QED

Resume create_immutable_target_attribute_case[cut]:
  simp[create_operand_cut_def] >> rpt strip_tac >>
  drule_all_then strip_assume_tac create_interior_visit_first_exit
  >- (irule create_cut_bind_left >> simp[] >>
      qpat_assum `create_operand_cut _ _ _ _ _ _ _ _ _ _`
        (drule_all_then ACCEPT_TAC o REWRITE_RULE[create_operand_cut_def])) >>
  PairCases_on `hit` >>
  drule_all_then assume_tac imm_field_visit_opcode >>
  irule create_cut_noncreate_visit >> simp[]
QED

Resume create_immutable_target_attribute_case[outcome]:
  qmatch_goalsub_abbrev_tac `bind (eval_target_place cx bt) next` >>
  qmatch_goalsub_abbrev_tac `scoped_operand_outcome _ _ _ _ _ _ _ _ Q _` >>
  qpat_assum `Abbrev (childR = _)`
    (fn th => ONCE_REWRITE_TAC [SYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  `scoped_operand_outcome (DF,lo,E,ctx,func,PG) (cx_tops cx) cx st0 sa sm
    (eval_target_place cx bt) (es,s0,G0,tn0) childQ
    (\H res ee gt r. (?exc. res = INR exc) /\ childR H res ee gt r)` by
    (irule imm_field_scope_error >> conj_tac
     >- (qunabbrev_tac `childR` >> simp[])
     >> first_assum ACCEPT_TAC) >>
  drule_all imm_field_scope_join >> disch_then (qspec_then `E` strip_assume_tac) >>
  irule scoped_operand_bind_all >>
  simp[evaluate_storage_trace_frame] >> rpt conj_tac
  >~ [`!v. storage_trace_frame (next v)`]
  >- (qunabbrev_tac `next` >>
      simp[storage_trace_frame_bind,storage_trace_frame_extend_place,
           storage_trace_frame_get_place])
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> fs[ignore_bind_def] >> simp[Once bind_assoc] >>
      irule gas_exempt_cert_bind_place >> metis_tac[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> fs[ignore_bind_def] >> simp[Once bind_assoc] >>
      irule gas_exempt_cert_error_place >> fs[ignore_bind_def]) >>
  qexistsl_tac [`childQ`,`sm`] >> simp[] >>
  reverse (rpt conj_tac) >- first_assum ACCEPT_TAC >- first_assum ACCEPT_TAC >>
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  `~t.vs_halted` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (drule_then strip_assume_tac) >>
     drule gas_origin_ptr_path_exec >> simp[exit_result_def]) >>
  qunabbrev_tac `childQ` >> RULE_ASSUM_TAC BETA_RULE >>
  mp_tac (Q.INST [`mid` |-> `mid with gas_obs := []`, `explicit` |-> `E`]
    immutable_target_field_endpoint) >>
  (impl_tac >- (simp[Abbr `field_off`] >> rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (drule_then strip_assume_tac) >> simp[imm_field_post_gas_obs])) >>
  strip_tac >> qexists_tac `ImmutablePlace NONE id path` >> simp[] >>
  first_assum (irule o SPEC_ALL) >>
  simp[] >>
  qexistsl_tac [`G'`,`FST rb`,`mid with gas_obs := []`,`field_off`,`out`,
               `INL (ImmutablePlace NONE id (path ++ [AttrSubscript fld]))`,`tn'`,`w`] >>
  qunabbrev_tac `next` >>
  simp[Abbr `Q`,target_root_def,target_through_dynarray_def] >> conj_tac
  >- fs[] >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (mp_tac o SIMP_RULE (srw_ss()) []) >>
  disch_then (drule_then strip_assume_tac) >> gvs[]
QED

Finalise create_immutable_target_attribute_case
