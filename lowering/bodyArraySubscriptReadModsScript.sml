(* Read the reached array element at the end of the linked VV interval. *)
Theory bodyArraySubscriptReadMods
Ancestors
  bodySubscriptArrayRouteDefsMods bodyFullPostsMods
  bodyIfExpWordReadMods bodyIfExpArmUnwrapMods
  bodyCopyReadPhysicalTypeMods bodyForRangeScalarFrameMods
  exprSimUnwrap exprSimMemorySource exprOperandVar gasShadowCompile
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasExemptCertMods
  haltExitProj stmtSimProps fragExec vyperStorageTrace vyperStorageFootprint
  exprBodyPreProps exprBodyPreTypingProps exprSimHyps exprSimProps
  exprLowering loweringPosts compileEnv vyperState exprSimDefs gasShadowState
  bodySimModsProps exprSimSubscriptArrayFramed bodySimStmtFacts bodyWriteSubscriptSourceMods
  fragGasOriginPtr fragGasOriginPtrDead bodyPtrDefs exprSimUnwrapProps
  stateRelProj exprSimProps bodyPtrSignedConvertSourceFrame
  vyperTypeEvalCaseProofs vyperTypeExprSoundness valueEncodingDefs
  vyperTypeSystem vyperAST venomState finite_map pred_set exprLoweringProps freshWrites
  bodyFullAttributeMods bodyLocalCopyPhysicalRhsMods exprSimCopy context
  loweringStateRelDefs ptrDiscipline exprSimMemDefs bodyFullUnwrapRun
  allocasBelowFmpUpdatesProps
Libs monadsyntax

Theorem array_element_runtime_type[local]:
  expr_body_pre_mods mods ce cx env e es /\
  eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) /\
  read_result cx tv ee = (INL v,ee) ==>
  ?rt. evaluate_type (get_tenv cx) (expr_type e) = SOME rt /\ value_has_type rt v
Proof
  strip_tac >>
  `(do r <- eval_expr cx e; read_result cx r od) (es with gas_obs := gs) = (INL v,ee)` by
    simp[bind_def] >>
  `expr_body_pre_mods mods ce cx env e (es with gas_obs := gs)` by simp[] >>
  drule_at (Pat `bind _ _ _ = _`) expr_body_pre_eval_mods >>
  disch_then (drule_at (Pat `expr_body_pre_mods _ _ _ _ _ (es with gas_obs := gs)`)) >>
  simp[] >> strip_tac >>
  drule expr_sim_inv_mods_env >>
  disch_then (strip_assume_tac o MATCH_MP
    (SPEC_ALL env_consistent_type_defs_get_tenv)) >>
  fs[value_runtime_typed_def]
QED

Theorem array_word_read_post[local]:
  vv_post_mods H ctx func ce cx e es sa sm s0 ee tv vv s /\
  local_ptrs_reserved ce sm /\ sa.cs_next_var <= sm.cs_next_var /\
  is_word_type (expr_type e) /\ evaluate_type (get_tenv cx) (expr_type e) = SOME rt /\
  eval_operand op u = SOME (typed_val_to_w256 rt v) /\
  u = s with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|> /\
  (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) ==>
  expr_post_mods H ctx func ce cx e es sa sb s0 ee v op u
Proof
  strip_tac >>
  qpat_x_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  `stmt_state_rel H ctx func ce cx ee u` by
    (irule stmt_state_rel_readonly_vars_pc >> qexistsl [`s`,`sm`] >> simp[]) >>
  `u.vs_memory = s.vs_memory /\ u.vs_data_section = s.vs_data_section /\
   u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next` by
    (rpt conj_tac >> qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>`
       (fn th => simp[Once th])) >>
  `immutable_frame_mods func ce cx ee u` by
    (irule immutable_frame_mods_exterior_frame >> qexistsl [`ee`,`s`,`sm`] >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s` by
    metis_tac[not_fresh_at_mono] >>
  simp[expr_post_mods_def,expr_post_def,expr_val_rel_def,expr_val_at_def,expr_val_own_def] >>
  conj_tac >- (rpt strip_tac >> first_x_assum irule >>
               conj_tac >- first_assum ACCEPT_TAC >> qexists `aid` >> simp[]) >>
  conj_tac >- (irule locals_kept_mem_tail >> qexists `s` >> simp[]) >>
  strip_tac >> irule pure_frame_mem_tail >> qexists `s` >> fs[]
QED

val read_word_frame = ``
  u = s with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|> /\
  (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s /\
         FLOOKUP (Gf : string |-> num # num) x = FLOOKUP G x /\
         op_taint tf (Var x) = op_taint tn (Var x)) /\
  tf.t_mem = tn.t_mem /\ tf.t_stor = tn.t_stor /\
  tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm``;

val no_dead = ``<|d_stor := K (K {}); d_trans := K (K {});
                    d_imm := K {}; d_ret := K {}|>``;

Theorem array_word_read_run[local]:
  unwrap_value ce (LocatedValue (expr_type e) p) sm = (op,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce sm /\
  copy_old_operand sm p.ptr_operand /\ post_value_type ce e = expr_type e /\
  is_word_type (expr_type e) /\ evaluate_type (get_tenv cx) (expr_type e) = SOME rt /\
  read_result cx tv ee = (INL v,ee) /\ value_has_type rt v /\
  vv_post_mods H ctx func ce cx e es sa sm s0 ee tv (LocatedValue (expr_type e) p) s /\
  ghost_inv_at_mods Dh lo d ce cx ee G tn s /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e)
    ee tv (LocatedValue (expr_type e) p) s /\
  ptr_vv_ok cx (post_value_type ce e) tv (LocatedValue (expr_type e) p) ee G tn s /\
  (ce.ce_is_ctor /\ p.ptr_location = LocCode ==>
      !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
             eval_operand p.ptr_operand s = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
               val_in_memory rt v (w2n w) mem)) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?u Gf tf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gf,tf)) /\
    eval_operand op u = SOME (typed_val_to_w256 rt v) /\
    op_taint tf op = {} /\ op_prov Gf op = NONE /\
    u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func u /\ ^read_word_frame
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `p.ptr_location <> LocCalldata` by (drule_all word_arm_location >> simp[]) >>
  qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >> simp[unwrap_value_def] >> disch_tac >>
  qpat_assum `ghost_inv_at_mods Dh _ _ _ _ _ _ _ _`
    (mp_then (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`)
      (drule_at (Pat `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`))
      (Q.INST [`D` |-> `^no_dead`] word_arm_located_packet)) >>
  disch_then (qspecl_then [`sb`,`rt`,`op`,`PG`] mp_tac) >>
  (impl_tac >- (qpat_assum `post_value_type ce e = expr_type e`
      (fn th => rule_assum_tac (PURE_REWRITE_RULE [th])) >>
    simp[] >> strip_tac >> qexists `v` >> simp[])) >>
  strip_tac >>
  `alloca_inv s` by
    (qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
     drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  `!x. not_fresh_at sm x ==> lookup_var x q = lookup_var x s` by
    (gen_tac >> disch_tac >> qpat_assum `!x. not_fresh_at sm x ==> _ /\ _ /\ _` drule >> simp[]) >>
  drule_all_then (qspec_then `explicit` strip_assume_tac) word_arm_loaded_path >>
  rename1 `gas_origin_ptr_path _ _ [] (OK u,Gf,tf)` >>
  `v' = v` by metis_tac[sumTheory.INL_11,pairTheory.PAIR_EQ] >>
  qexistsl [`u`,`Gf`,`tf`] >> simp[] >>
  gen_tac >> irule gas_origin_ptr_path_from_no_dead >> simp[]
QED

Theorem array_subscript_value_of_located_mods:
  linked_subscript_array_context_mods mods exps cx ann obj idx
    DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es et bd /\
  ~subscript_reads_base cx obj idx /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Subscript ann obj idx) es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Subscript ann obj idx) es
Proof
  strip_tac >> qabbrev_tac `e = Subscript ann obj idx` >>
  `expr_body_pre_mods mods cenv cx env e es` by
    fs[Abbr `e`,linked_subscript_array_context_mods_def] >>
  `place_type cenv obj = ValPT (ArrayT et bd) /\ ~copies_subscript_base cenv obj idx` by
    (fs[linked_subscript_array_context_mods_def] >> drule_all body_inv_copies_subscript_base_mods >> simp[]) >>
  qpat_x_assum `linked_subscript_array_context_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  rewrite_tac[expr_sim_full_mods_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `lower_value compile_expr cenv ty e sa = _` mp_tac >>
  simp[lower_value_def, comp_bind_def] >>
  Cases_on `compile_expr cenv ty e sa` >> rename1 `_ = (vv,sm)` >>
  simp[] >> strip_tac >>
  qpat_x_assum `lower_value compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[lower_value_def, comp_bind_def] >>
  Cases_on `compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) shadow_sa` >>
  rename1 `_ = (vv',shadow_sm)` >>
  simp[gasShadowCompileBaseTheory.unwrap_value_gas_shadow_env] >> strip_tac >>
  `vv' = vv /\ gas_shadow_state sm shadow_sm` by
    (`gas_shadow_compiles (compile_expr cenv ty e)
       (compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e))` by
       irule (cj 1 gas_shadow_compile_expr_env |> SPEC_ALL |>
              Q.INST [`shadow` |-> `T`] |> REWRITE_RULE [COND_CLAUSES]) >>
     qpat_x_assum `gas_shadow_compiles _ _`
       (qspecl_then [`sa`,`shadow_sa`] mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
     simp[]) >>
  gvs[] >>
  qpat_assum `compile_expr cenv ty e sa = _`
    (strip_assume_tac o MATCH_MP compile_expr_extends) >>
  qpat_assum `unwrap_value cenv vv sm = _`
    (strip_assume_tac o MATCH_MP unwrap_value_extends) >>
  qpat_assum `compile_expr _ _ (gas_shadow_expr _) _ = _`
    (strip_assume_tac o MATCH_MP compile_expr_extends) >>
  qpat_assum `unwrap_value _ _ shadow_sm = _`
    (strip_assume_tac o MATCH_MP unwrap_value_extends) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (qspecl_then [`sa`,`sm`,`sb`,`func`] mp_tac fn_has_code_split >> simp[]) >>
  `fn_has_code shadow_sa shadow_sm shadow_func` by
    (qspecl_then [`shadow_sa`,`shadow_sm`,`shadow_sb`,`shadow_func`]
       mp_tac fn_has_code_split >> simp[]) >>
  drule_then assume_tac forced_expr_admissible_raw >>
  qpat_x_assum `expr_vv_sim_full_mods _ _ _ _ _ _`
    (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`vv`,`s0`,`G0`,`tn0`] mp_tac o
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
      rpt gen_tac >> Cases_on `res` >> simp[Abbr `childR`,expr_exit_def] >>
      ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:value``] expr_exit_INR_type,
        INST_TYPE [beta |-> ``:value``] halt_exit_INR_type] >> simp[]) >>
  suspend "read"
QED

Resume array_subscript_value_of_located_mods[read]:
  qx_genl_tac [`marks`,`res`,`ee`,`G`,`tn`,`s`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qunabbrev_tac `childQ` >>
  qpat_x_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (assume_tac o BETA_RULE) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `res = INL tv` SUBST_ALL_TAC >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  `eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL tv,ee)` by
    (qpat_assum `!tail. eval_expr _ _ _ = _`
       (qspec_then `[]` (mp_tac o REWRITE_RULE [listTheory.APPEND_NIL])) >>
     asm_rewrite_tac[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post_mods H ctx func cenv cx e es sa sm s0 ee tv vv s /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s` by
    (qx_gen_tac `H` >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> (?r. _ = INL r /\ _) /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  disj1_tac >> qexists_tac `tv` >> simp[] >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` kall_tac >>
  qpat_x_assum `unwrap_value cenv vv shadow_sm = _` kall_tac >>
  `?p. vv = LocatedValue (expr_type e) p` by
    (unabbrev_all_tac >> simp[expr_type_def] >>
     drule_all_then strip_assume_tac compile_expr_array_subscript >>
     goal_assum (drule_at Any)) >>
  Cases_on `is_word_type (expr_type e)`
  >- suspend "word" >>
  drule_at (Pat `compile_expr _ _ _ _ = _`) ifexp_arm_nonword_unwrap_mods >>
  disch_then (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  disch_then (drule_at (Pat `expr_body_pre_mods _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `eval_expr _ _ _ = _`)) >>
  disch_then (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `vv_store_bound _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (qspecl_then [`st0`,`gas_explicit_sites ctx shadow_ctx`,`d`,`ctx`,`PG`,`DF`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`v`,`u`,`Gf`,`tf`,`pt`,`rt`,`w`]
    (map_every assume_tac o CONJUNCTS)) >>
  `s0.vs_alloca_next <= u.vs_alloca_next` by decide_tac >>
  irule gas_outcome_full_mods_pure >> simp[] >>
  qexistsl_tac [`Gf`,`ee`,`INL v`,`u`,`tf`] >> simp[read_result_gas_obs] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >> simp[]
QED

Resume array_subscript_value_of_located_mods[word]:
  qpat_x_assum `vv = LocatedValue _ _` SUBST_ALL_TAC >>
  `post_value_type cenv e = expr_type e` by simp[Abbr `e`,post_value_type_def] >>
  `?v. read_result cx tv ee = (INL v,ee)` by
    (qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
     drule_then strip_assume_tac attribute_vv_holds_read_operand_mods >> simp[]) >>
  drule_all_then strip_assume_tac array_element_runtime_type >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
    metis_tac[not_fresh_at_mono] >>
  `copy_old_operand sm p.ptr_operand` by
    (drule_at (Pat `compile_expr _ _ _ _ = _`) (cj 1 compiler_compile_var) >>
     simp[copy_old_operand_def,vv_operand_def]) >>
  drule_at (Pat `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`) array_word_read_run >>
  disch_then (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  disch_then (drule_at (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `read_result _ _ _ = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ (expr_type _) = _`)) >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`] mp_tac) >>
  (impl_tac >- (simp[] >> strip_tac >>
    qpat_assum `_ /\ vv_location _ = _ ==> _`
      (mp_tac o PURE_REWRITE_RULE [vv_location_def,vv_operand_def]) >>
    simp[] >> disch_then (qx_choose_then `val` strip_assume_tac) >> gvs[])) >>
  disch_then (qx_choosel_then [`u`,`Gf`,`tf`] strip_assume_tac) >>
  `u.vs_alloca_next = s.vs_alloca_next` by
    (qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>` (fn th => simp[Once th])) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>`
       (fn th => PURE_ONCE_REWRITE_TAC [th] >> simp[allocas_below_fmp_updates,allocas_below_fmp_def]) >>
     fs[allocas_below_fmp_def]) >>
  irule gas_outcome_full_mods_pure >> simp[] >>
  qexistsl_tac [`Gf`,`ee`,`INL v`,`u`,`tf`] >> simp[read_result_gas_obs] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  simp[expr_store_bound_word,ptr_val_ok_word] >>
  rpt conj_tac
  >- (irule array_word_read_post >> simp[] >>
      qexistsl [`s`,`sm`,`tv`,`LocatedValue (expr_type e) p`] >> simp[] >>
      qpat_assum `u.vs_inst_idx = _` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
      first_assum ACCEPT_TAC)
  >- (irule ghost_inv_at_mods_exterior_frame >>
      qexistsl [`G`,`ee`,`s`,`sm`,`tn`] >> simp[] >>
      rpt conj_tac >>
      qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>` (fn th => simp[Once th])) >>
  irule ghost_kept_at_clean_suffix >> qexistsl [`G`,`tn`] >> simp[] >>
  rpt strip_tac >> `not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >> simp[]
QED

Finalise array_subscript_value_of_located_mods
