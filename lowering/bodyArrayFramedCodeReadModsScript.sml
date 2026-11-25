(* Force the linked runtime-code subscript at its actual unwrap cut. *)
Theory bodyArrayFramedCodeReadMods
Ancestors
  bodySubscriptArrayRouteDefsMods bodySlotCopySavedMods bodyAssignNameLinkedSetup
  exprSimUnwrap exprSimMemorySource exprOperandVar exprLoweringProps
  gasShadowCompile gasShadowState exprLowering compileEnv
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasExemptCertMods
  haltExitProj stmtSimProps exprBodyPreProps vyperTypeEvalCaseProofs
  vyperEvalExprPreservesScopesDom vyperStorageFootprint vyperStorageTrace
  fragExec fragGasOriginPtr loweringPosts exprSimDefs bodyFullPostsMods
  vyperAST vyperInterpreter vyperState bodySimStmtFacts vyperTypeExprSoundness
  exprSimHypsDefs vyperTypeSystem exprSimSubscriptArrayFramed finite_map
  exprSimMemDefs bodyPtrDefs venomState context bodyWriteSubscriptSourceMods
  bodyFullAttributeMods
Libs monadsyntax

Theorem framed_code_read_cuts[local]:
  lower_value compile_expr ce ty e sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e) sha = (op,shb) /\
  gas_shadow_state sa sha /\ fn_has_code sa sb func /\ fn_has_code sha shb shfunc /\
  local_ptrs_reserved ce sa ==>
  ?vv sm shm.
    compile_expr ce ty e sa = (vv,sm) /\
    compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e) sha = (vv,shm) /\
    gas_shadow_state sm shm /\ fn_has_code sa sm func /\ fn_has_code sm sb func /\
    fn_has_code sha shm shfunc /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\ unwrap_value ce vv sm = (op,sb) /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sm x)
Proof
  strip_tac >> Cases_on `compile_expr ce ty e sa` >>
  rename1 `compile_expr ce ty e sa = (vv,sm)` >>
  `gas_shadow_compiles (compile_expr ce ty e)
    (compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e))` by
    irule (cj 1 gas_shadow_compile_expr_env |> SPEC_ALL |>
           Q.INST [`shadow` |-> `T`] |> REWRITE_RULE [COND_CLAUSES]) >>
  qpat_x_assum `gas_shadow_compiles _ _`
    (qspecl_then [`sa`,`sha`] mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
  Cases_on `compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr e) sha` >>
  simp[] >> strip_tac >>
  rename1 `compile_expr _ _ (gas_shadow_expr _) sha = (_,shm)` >>
  gvs[] >> fs[lower_value_def, comp_bind_def] >>
  qpat_assum `compile_expr ce ty e sa = _`
    (strip_assume_tac o MATCH_MP compile_expr_extends) >>
  qpat_assum `compile_expr _ _ (gas_shadow_expr _) sha = _`
    (strip_assume_tac o MATCH_MP compile_expr_extends) >>
  qpat_assum `unwrap_value _ _ sm = _` (strip_assume_tac o MATCH_MP unwrap_value_extends) >>
  qpat_assum `unwrap_value _ _ shm = _` (strip_assume_tac o MATCH_MP unwrap_value_extends) >>
  qspecl_then [`sa`,`sm`,`sb`,`func`] mp_tac fn_has_code_split >> simp[] >>
  qspecl_then [`sha`,`shm`,`shb`,`shfunc`] mp_tac fn_has_code_split >> simp[] >>
  rpt strip_tac >>
  qpat_assum `compile_expr ce ty e sa = _` (mp_then Any mp_tac (cj 1 compiler_compile_var)) >>
  simp[]
QED

Theorem framed_code_read_type[local]:
  expr_body_pre_mods mods ce cx env e es /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee) ==>
  ?rt. evaluate_type (get_tenv cx) (expr_type e) = SOME rt /\ value_has_type rt v /\
       type_memory_bytes ce (expr_type e) = type_memory_size rt
Proof
  strip_tac >>
  `expr_body_pre_mods mods ce cx env e (es with gas_obs := gs)` by simp[] >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_eval_mods) >>
  simp[value_runtime_typed_def] >> strip_tac >>
  qexists `tv` >> simp[] >> drule_all assign_name_memory_bytes_mods >> simp[]
QED

val read_expr = ``Subscript ann obj idx``;

val reached_read = ``
  ~ce.ce_is_ctor /\ p.ptr_location = LocCode /\
  unwrap_value ce (LocatedValue ann p) sm = (op,sb) /\
  read_result cx tv ee = (INL v,ee) /\
  ptr_vv_ok cx ann tv (LocatedValue ann p) ee G tn s /\
  evaluate_type (get_tenv cx) ann = SOME rt /\ value_has_type rt v /\
  type_memory_bytes ce ann = type_memory_size rt /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func ce cx ^read_expr es sa sm s0 ee tv (LocatedValue ann p) s /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  local_ptrs_reserved ce sa /\ sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!x n. ce.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  (!x n. ce.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at sa x) /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts``;

val value_endpoint = ``
  ?z Gf tf. (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
                   (s,G,tn) [] (OK z,Gf,tf)) /\
    z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
    s0.vs_alloca_next <= z.vs_alloca_next /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      expr_post_mods H ctx func ce cx ^read_expr es sa sb s0 ee v op z /\
      ghost_inv_at_mods (DF H) lo d ce cx ee Gf tf z) /\
    ptr_val_ok cx ann v op Gf tf z /\ expr_store_bound cx ann v op z /\
    (~is_word_type ann ==> ptr_buf_ok ce ^read_expr op Gf z) /\
    ghost_kept_at lo ce es sa G0 tn0 s0 Gf tf``;

Theorem framed_code_aggregate_read[local]:
  ^reached_read /\ ~is_word_type ann ==> ^value_endpoint
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `(ce.ce_is_ctor ==> !rt w. evaluate_type (get_tenv cx) ann = SOME rt /\
       eval_operand p.ptr_operand s = SOME w ==> w2n w + type_memory_size rt <= lo /\
       !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory rt v (w2n w) mem)` by simp[] >>
  drule_all (SIMP_RULE (srw_ss()) [post_value_type_def,lowered_value_type_def,expr_type_def]
    (Q.INST [`e` |-> `Subscript ann obj idx`] (SPEC_ALL slot_copy_saved_code_unwrap_mods))) >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shctx`,`PG`] strip_assume_tac) >>
  `s0.vs_alloca_next <= z.vs_alloca_next` by decide_tac >>
  qexistsl [`z`,`Gf`,`tf`] >> asm_rewrite_tac[]
QED

Theorem framed_code_value_from_vv_mods:
  linked_subscript_array_context_mods mods exps cx ann obj idx
    DF lo d PG src tops ctx shctx func shfunc ce env ty es et bd /\
  subscript_array_framed_code_case_mods ce cx obj idx bd /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty ^read_expr es /\
  (!st0 sa sm sb s0 G0 tn0 ee tv v rt p op s G tn.
     ^reached_read /\ is_word_type ann ==> ^value_endpoint) ==>
  expr_sim_full_mods (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty ^read_expr es
Proof
  strip_tac >> rewrite_tac[expr_sim_full_mods_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac framed_code_read_cuts >>
  drule_then assume_tac forced_expr_admissible_raw >>
  qpat_x_assum `expr_vv_sim_full_mods _ _ _ _ _ _`
    (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shm`,`vv`,`s0`,`G0`,`tn0`] mp_tac o
     REWRITE_RULE [expr_vv_sim_full_mods_def]) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_bind_result >>
      qexistsl_tac [`mid`,`t`,`v`] >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_result >> simp[])
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`!v. storage_trace_frame (read_result _ v)`]
  >- simp[storage_trace_frame_read_result] >>
  qexists_tac `\H res ee G tn u. childQ H res ee G tn u /\ ee.gas_obs = [] /\ ~u.vs_halted` >>
  reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >>
      qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` (irule_at Any) >>
      conj_tac >- simp[] >>
      rpt gen_tac >> Cases_on `res` >> simp[Abbr `childR`, expr_exit_def] >>
      ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:value``] expr_exit_INR_type,
        INST_TYPE [beta |-> ``:value``] halt_exit_INR_type] >> simp[]) >>
  suspend "read"
QED

Resume framed_code_value_from_vv_mods[read]:
  qx_genl_tac [`marks`,`res`,`ee`,`G`,`tn`,`s`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qunabbrev_tac `childQ` >>
  qpat_x_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (assume_tac o BETA_RULE) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  qpat_x_assum `res = INL tv` SUBST_ALL_TAC >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  `eval_expr cx ^read_expr (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL tv,ee)` by
    (qpat_assum `!tail. eval_expr _ _ _ = _`
       (qspec_then `[]` (mp_tac o REWRITE_RULE [listTheory.APPEND_NIL])) >> asm_rewrite_tac[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     vv_post_mods H ctx func ce cx ^read_expr es sa sm s0 ee tv vv s /\
     ghost_inv_at_mods (DF H) lo d ce cx ee G tn s` by
    (qx_gen_tac `H` >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> (?r. _ = INL r /\ _) /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `?v. read_result cx tv ee = (INL v,ee)` by
    (qhdtm_assum `vv_post_mods` (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
     drule_then strip_assume_tac attribute_vv_holds_read_operand_mods >> simp[]) >>
  `expr_body_pre_mods mods ce cx env ^read_expr es` by
    fs[linked_subscript_array_context_mods_def] >>
  `bind (eval_expr cx ^read_expr) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,ee)` by simp[bind_def] >>
  drule_all_then strip_assume_tac framed_code_read_type >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule eval_expr_preserves_scopes_dom >> simp[]) >>
  `~ce.ce_is_ctor /\ ~copies_subscript_base ce obj idx /\
   !ty st. vv_location (FST (compile_expr ce ty obj st)) = SOME LocCode` by
    fs[subscript_array_framed_code_case_mods_def] >>
  `place_type ce obj = ValPT (ArrayT et bd)` by fs[linked_subscript_array_context_mods_def] >>
  `?p. vv = LocatedValue ann p /\ p.ptr_location = LocCode` by
    (drule_all_then strip_assume_tac compile_expr_array_subscript >>
     `vv_location bvv = SOME LocCode` by
       (qpat_assum `!ty st. vv_location _ = _` (qspecl_then [`ty`,`sa`] mp_tac) >>
        qpat_assum `compile_expr ce ty obj sa = _` (fn th => simp[NoAsms,th])) >>
     simp[mk_ptr_def]) >>
  qpat_x_assum `vv = LocatedValue _ _` SUBST_ALL_TAC >>
  disj1_tac >> qexists `tv` >> simp[] >>
  qpat_assum `ptr_vv_ok _ _ _ _ _ _ _ _`
    (assume_tac o REWRITE_RULE [post_value_type_def,expr_type_def]) >>
  qpat_assum `evaluate_type _ (expr_type _) = _`
    (assume_tac o REWRITE_RULE [expr_type_def]) >>
  qpat_assum `type_memory_bytes _ (expr_type _) = _`
    (assume_tac o REWRITE_RULE [expr_type_def]) >>
  `^reached_read` by
    (rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[vv_operand_def])) >>
  `^value_endpoint` by
    (Cases_on `is_word_type ann`
     >- (first_x_assum irule >> simp[] >> qexistsl [`p`,`sm`,`tv`] >> simp[]) >>
     irule framed_code_aggregate_read >> simp[] >> qexistsl [`p`,`sm`,`tv`] >> simp[]) >>
  irule gas_outcome_full_mods_pure >> simp[] >>
  qexistsl [`Gf`,`ee`,`INL v`,`z`,`tf`] >> simp[read_result_gas_obs] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >> simp[post_value_type_def,expr_type_def]
QED

Finalise framed_code_value_from_vv_mods
