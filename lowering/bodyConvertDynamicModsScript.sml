(* Linked Convert from a reached bytestring operand to a scalar. *)
Theory bodyConvertDynamicMods
Ancestors
  bodyConvertDynamicEntryMods bodyConvertOperandBufferMods bodyConvertSourceWindowMods
  bodyConvertSelectedSuffixMods bodyConvertSelectedSuffixRevertMods
  bodyConvertZeroCapacityMods bodyConvertWordEndpointMods
  bodyConvertReachedBindMods bodyForcedStorageFrameMods bodyAggregateReadMods
  bodyAggregateReadPostMods bodyCopyReadPhysicalTypeMods bodyPtrSignedConvertLayout
  bodyPtrTypeBuiltinsBytesWordInputs bodyFullPathHistory bodyWriteSubscriptSourceMods
  bodySimStmtFacts exprBodyPreProps exprSimConvert exprSimMemorySource
  gasOutcomeFullPostMods gasSummary gasContext exprSimDefs exprBopLowering
  bodyFullPostsMods bodyFullPredsMods bodyFullShared compileEnv exprLowering exprLoweringProps
  gasShadowCompileStmtHelpers gasShadowState vyperStorageFootprint
  loweringPosts bodyPtrDefs stateRelProj exprSimWordArgs exprSimProps freshWrites
  words vyperTypeEvalCaseProofs vyperTyping vyperTypeExprSoundness
  valueCopyBytes stateFrame fragExec venomState vyperState vyperInterpreter vyperAST
Libs monadsyntax

val convert_expr = ``TypeBuiltin dst Convert dst [e]``;
val convert_action = ``\ee:evaluation_state.
  (sum_CASE (convert_result cx (expr_type e) dst v) (\w. INL (Value w)) INR,ee)``;
val convert_exit = ``\(H:(bool # 256 word # type_value) list # num list)
  (res:eval_result + exception) ee (gt:(string |-> num # num) # taint) r.
  expr_exit res r /\ halt_exit H cx ee res r /\
  (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u)``;
val operand_post = ``\(H:(bool # 256 word # type_value) list # num list) v ee G tn t.
  ?pt rt w.
    expr_post_mods H ctx func ce cx e es sa sm s0 ee v op t /\
    storage_well_formed_on cx ee (FST H) /\
    expr_store_bound cx (post_value_type ce e) v op t /\
    t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn t /\
    ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
    ptr_val_ok cx (post_value_type ce e) v op G tn t /\ ptr_buf_ok ce e op G t /\
    ~is_word_type (post_value_type ce e) /\
    evaluate_type (get_tenv cx) (post_value_type ce e) = SOME pt /\
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
    type_memory_bytes ce (lowered_value_type ce e) = type_memory_size rt /\
    value_has_type pt v /\ value_has_type rt v /\ val_wf rt v /\
    eval_operand op t = SOME w /\ op_taint tn op = {} /\
    (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
      val_in_memory rt v (w2n w) mem) /\
    (type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= t.vs_alloca_next) /\
    w2n w + type_memory_size rt < dimword (:256) /\
    (0 < type_memory_size rt ==>
      ?x. op = Var x /\ not_fresh_at sm x /\ ptr_covers G tn x t (type_memory_size rt))``;
val word_post = ``\(H:(bool # 256 word # type_value) list # num list) (res:eval_result + exception) ee G tn t.
  ?v. res = INL (Value v) /\
    vv_post_mods H ctx func ce cx ^convert_expr es sa sb s0 ee (Value v) (StackValue dst out) t /\
    vv_store_bound cx dst (lowered_value_type ce ^convert_expr) ee (Value v) (StackValue dst out) t /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn t /\
    ptr_vv_ok cx dst (Value v) (StackValue dst out) ee G tn t /\
    ghost_kept_at lo ce es sa G0 tn0 s0 G tn``;

Theorem dynamic_convert_admissible[local]:
  gas_admissible (eval_expr cx ^convert_expr) expr_vv_res_ok es ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  simp[gas_admissible_def] >> rpt strip_tac >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  first_x_assum (qspec_then `gs` mp_tac) >>
  pure_once_rewrite_tac[dynamic_convert_source_action] >>
  gvs[bind_def, expr_vv_res_ok_def, expr_res_ok_def]
QED

Theorem dynamic_convert_stack[local]:
  is_bytestring_type (expr_type e) /\ is_word_type dst /\
  ~is_bytestring_type dst /\ (!n. dst <> FlagT n) ==>
  !sa. ?out sb. compile_expr ce ty ^convert_expr sa = (StackValue dst out,sb)
Proof
  strip_tac >> gen_tac >>
  Cases_on `lower_value compile_expr ce (expr_type e) e sa` >>
  drule_all dynamic_convert_compile_cut >> disch_then (qspec_then `ty` mp_tac) >>
  IF_CASES_TAC >- simp[] >>
  Cases_on `compile_type_convert q (mk_convert_op (expr_type e) dst) r` >>
  simp[as_stack_val_pair]
QED

Theorem dynamic_convert_success[local]:
  convert_result cx (expr_type e) dst v = INL vout /\
  evaluate_type (get_tenv cx) dst = SOME dtv /\ value_has_type dtv vout /\
  eval_operand out u = SOME (typed_val_to_w256 dtv vout) /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK u,Gf,tnf)) /\
  state_frame u = state_frame (t with vs_inst_idx := u.vs_inst_idx) /\
  u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
  (!p. not_fresh_at sm p ==> lookup_var p u = lookup_var p t /\
    FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p)) /\
  tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
  tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
  op_prov Gf out = NONE /\ op_taint tnf out = {} /\
  fn_inst_ids_distinct func /\
  is_word_type dst /\ local_ptrs_reserved ce sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!z sz. ce.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
  (!z sz. ce.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
  ~t.vs_halted /\ ee.gas_obs = [] /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> (^operand_post) H v ee G tn t) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) ce.ce_modules cx st0
    ^convert_action (ee,t,G,tn) ^word_post ^convert_exit
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  irule gas_outcome_full_mods_pure >> simp[] >>
  qexistsl_tac [`Gf`,`ee`,`INL (Value vout)`,`u`,`tnf`] >> simp[] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!h. valid_horizon _ _ h _ ==> _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  `alloca_inv t` by
    (fs[expr_post_mods_def] >> drule expr_post_state >>
     disch_then (strip_assume_tac o MATCH_MP stmt_state_rel_local_ptrs_alloca)) >>
  `alloca_history func u` by
    (irule body_full_path_alloca_history >>
     qpat_assum `!D. gas_origin_ptr_path _ _ _ (OK u,_,_)`
       (irule_at Any o Q.SPEC `DF H`) >> simp[]) >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  simp[] >>
  drule_all convert_word_endpoint_mods >> simp[]
QED

val suffix_frame = ``
  fn_inst_ids_distinct func /\ is_word_type dst /\
  local_ptrs_reserved ce sm /\ sa.cs_next_var <= sm.cs_next_var /\
  (!z sz. ce.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
  (!z sz. ce.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z)``;
val suffix_reached = ``
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee) /\
  storage_trace_domain cx st0 ee.storage_trace /\ ee.gas_obs = [] /\ ~t.vs_halted /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==> (^operand_post) H v ee G tn t)``;
val suffix_source = ``
  expr_body_pre_mods mods ce cx env e es /\ is_bytestring_type (expr_type e) /\
  ~is_bytestring_type dst /\ valid_conversion (expr_type e) dst /\
  well_formed_type env.type_defs dst``;
val zero_layout = ``lowered_value_type ce e = BaseT (BytesT (Dynamic 0)) \/
  lowered_value_type ce e = BaseT (StringT 0)``;

Theorem dynamic_convert_zero[local]:
  ^suffix_source /\ ^suffix_frame /\ ^suffix_reached /\ ^zero_layout /\
  out = Lit 0w /\ sb = sm ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) ce.ce_modules cx st0
    ^convert_action (ee,t,G,tn) ^word_post ^convert_exit
Proof
  BETA_TAC >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then (qx_choosel_then [`pt`,`rt`,`w`] (map_every assume_tac o CONJUNCTS))) >>
  drule_all_then (qx_choosel_then [`vout`,`dtv`] strip_assume_tac)
    convert_zero_capacity_result_mods >>
  irule dynamic_convert_success >> BETA_TAC >>
  asm_simp_tac bool_ss [] >> qexistsl_tac [`G`,`dtv`,`op`,`sm`,`tn`,`t`,`vout`] >>
  simp[stateFrameTheory.state_frame_def,eval_operand_def,
       ptrDisciplineTheory.op_taint_def,ptrDisciplineTheory.op_prov_def,
       cj 1 fragGasOriginPtrTheory.gas_origin_ptr_path_rules] >>
  rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then (qx_choosel_then [`pt`,`rt`,`w`] (map_every assume_tac o CONJUNCTS))) >>
  asm_rewrite_tac[]
QED

Theorem dynamic_convert_failure[local]:
  convert_result cx (expr_type e) dst v = INR (Error (RuntimeError msg)) /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (t,G,tn) [] (Abort Revert_abort u,Gf,tnf)) /\ ~t.vs_halted ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) ce.ce_modules cx st0
    ^convert_action (ee,t,G,tn) ^word_post ^convert_exit
Proof
  strip_tac >> irule gas_outcome_full_mods_exit >> simp[] >>
  qexistsl_tac [`Gf`,`ee`,`Abort Revert_abort u`,`INR (Error (RuntimeError msg))`,`tnf`] >>
  simp[exit_result_def,expr_exit_def,haltExitProjTheory.halt_exit_not_halt]
QED

(* Retag the reached memory value with its source annotation. The footprint
   used by ptr_val_ok fits the covered lowered allocation, not vice versa. *)
Theorem dynamic_convert_retag[local]:
  is_bytestring_type src /\ is_bytestring_type layout /\
  evaluate_type (get_tenv cx) src = SOME rty /\
  evaluate_type (get_tenv cx) layout = SOME rt /\
  value_has_type rty v /\ value_has_type rt v /\ val_wf rt v /\
  eval_operand (Var z) t = SOME w /\ ptr_covers G tn z t (type_memory_size rt) /\
  (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==> val_in_memory rt v (w2n w) mem) ==>
  lookup_var z t = SOME w /\ ptr_val_ok cx src v (Var z) G tn t /\
  (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==> val_in_memory rty v (w2n w) mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `lookup_var z t = SOME w` by fs[eval_operand_def] >>
  `!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==> val_in_memory rty v (w2n w) mem` by
    (rpt strip_tac >> irule bytestring_val_in_memory_transfer >>
     simp[] >> qexistsl_tac [`layout`,`src`,`get_tenv cx`,`rt`] >> simp[]) >>
  `val_store_size rty v = val_store_size rt v` by
    (irule bytestring_val_store_size_eq >> simp[] >>
     qexistsl_tac [`src`,`layout`,`get_tenv cx`] >> simp[]) >>
  drule val_store_size_le >> strip_tac >>
  `~is_word_type src` by simp[eventTopicValuePropsTheory.bytestring_type_not_word] >>
  fs[ptr_val_ok_def,ptr_mem_ok_def,ptr_covers_def] >>
  rpt strip_tac >> gvs[] >> qexistsl_tac [`b`,`sz'`] >> simp[] >> decide_tac
QED

Theorem dynamic_convert_window[local]:
  ^suffix_source /\ ^suffix_reached /\ ~(^zero_layout) ==>
  ?rt rty z a n.
    op = Var z /\ not_fresh_at sm z /\ lookup_var z t = SOME a /\
    well_formed_type (get_tenv cx) dst /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME rty /\ value_has_type rty v /\
    val_in_memory rty v (w2n a) t.vs_memory /\
    ptr_covers G tn z t (type_memory_size rt) /\ 64 <= type_memory_size rt /\
    w2n a + 64 <= t.vs_alloca_next /\ w2n a + 64 <= dimword(:256) /\
    mload (w2n a) t = n2w n /\ n <= 32 /\
    (!i. w2n a <= i /\ i < w2n a + 32 + n ==> i NOTIN tn.t_mem) /\
    allocas_from lo t /\ lo <= t.vs_alloca_next /\ alloca_inv t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then (qx_choosel_then [`pt`,`rt`,`w`] (map_every assume_tac o CONJUNCTS))) >>
  `expr_body_pre_mods mods ce cx env e (es with gas_obs := gs)` by simp[] >>
  drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_eval_mods) >> strip_tac >>
  drule_then (assume_tac o MATCH_MP expr_sim_inv_mods_env) expr_body_pre_mods_inv >>
  drule_then assume_tac vyperTypeEvalCaseProofsTheory.env_consistent_type_defs_get_tenv >>
  qpat_x_assum `!u. INL v = INL u ==> value_runtime_typed _ _ u`
    (qspec_then `v` mp_tac) >> simp[value_runtime_typed_def] >>
  disch_then (qx_choose_then `rty` strip_assume_tac) >>
  `well_formed_type (get_tenv cx) dst` by fs[] >>
  `is_bytestring_type (lowered_value_type ce e)` by
    (irule compileEnvTheory.arg_type_fits_bytestring_source >>
     qexists_tac `expr_type e` >> simp[] >>
     irule copy_lowered_fits_mods >>
     drule expr_body_pre_mods_inv >> disch_then (irule_at Any) >>
     drule expr_body_pre_mods_well_typed >> simp[]) >>
  `64 <= type_memory_size rt` by
    (qpat_assum `type_memory_bytes _ _ = _` (SUBST1_TAC o SYM) >>
     irule bytestring_nonzero_capacity >> fs[]) >>
  `0 < type_memory_size rt` by decide_tac >>
  qpat_x_assum `0 < type_memory_size rt ==> _` (drule_then strip_assume_tac) >>
  qpat_x_assum `op = Var _` SUBST_ALL_TAC >>
  rename1 `eval_operand (Var z) t = SOME w` >>
  `lookup_var z t = SOME w /\ ptr_val_ok cx (expr_type e) v (Var z) G tn t /\
    (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==> val_in_memory rty v (w2n w) mem)` by
    (irule dynamic_convert_retag >> simp[] >>
     qexistsl_tac [`lowered_value_type ce e`,`rt`] >> simp[]) >>
  pop_assum (map_every assume_tac o CONJUNCTS) >>
  `w2n w + type_memory_size rt <= t.vs_alloca_next` by
    (qpat_assum `type_memory_size rt = 0 \/ _` mp_tac >> decide_tac) >>
  suspend "window"
QED

Resume dynamic_convert_window[window]:
  Q.SUBGOAL_THEN
    `?n. n <= 32 /\ ((?bs. v = BytesV bs /\ n = LENGTH bs) \/
                    (?str. v = StringV str /\ n = LENGTH str))`
    (qx_choose_then `n` (map_every assume_tac o CONJUNCTS))
  >- (drule_all bytes_word_source_length >> metis_tac[]) >>
  qpat_assum `expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [expr_post_mods_def]) >>
  drule expr_post_state >> strip_tac >>
  drule stmt_state_rel_alloca_room >> disch_then (assume_tac o MATCH_MP alloca_room_next_lt) >>
  drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by
    fs[bodyFullShadowBodyInvTheory.ghost_inv_at_mods_def] >>
  drule_all (SIMP_RULE bool_ss [] (Q.INST [`x` |-> `Var z`]
    convert_nonzero_source_window_mods)) >> strip_tac >>
  qexistsl_tac [`rt`,`rty`,`z`,`w`,`n`] >> simp[] >>
  gen_tac >> strip_tac >> Cases_on `i < w2n w + 32`
  >- (qpat_assum `!j. w2n w <= j /\ j < w2n w + 32 ==> _` irule >> simp[]) >>
  qpat_assum `!j. w2n w + 32 <= j /\ _ ==> _` irule >> decide_tac
QED
Finalise dynamic_convert_window

Theorem dynamic_convert_nonzero[local]:
  ^suffix_source /\ ^suffix_frame /\ ^suffix_reached /\ ~(^zero_layout) /\
  compile_type_convert op (mk_convert_op (expr_type e) dst) sm = (out,sb) /\
  fn_has_code sm sb func ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) ce.ce_modules cx st0
    ^convert_action (ee,t,G,tn) ^word_post ^convert_exit
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all (BETA_RULE dynamic_convert_window) >>
  disch_then (qx_choosel_then [`rt`,`rty`,`z`,`a`,`n`] (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `op = Var z` SUBST_ALL_TAC >>
  drule_all convert_selected_suffix_revert_mods >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  Cases_on `convert_result cx (expr_type e) dst v`
  >- (qpat_x_assum `!w. INL _ = INL w ==> _`
        (strip_assume_tac o SIMP_RULE bool_ss [sumTheory.INL_11]) >>
      qpat_assum `convert_result _ _ _ _ = INL _` (SUBST1_TAC o SYM) >>
      irule (Q.INST [`op` |-> `Var z`,`sm` |-> `sm`] dynamic_convert_success) >>
      BETA_TAC >> asm_simp_tac bool_ss [] >>
      rename1 `state_frame u = _` >>
      rename1 `gas_origin_ptr_path _ _ _ (OK u,Gf,tnf)` >>
      rename1 `evaluate_type (get_tenv cx) dst = SOME dtv` >>
      rename1 `convert_result cx _ _ v = INL vout` >>
      qexistsl_tac [`Gf`,`dtv`,`sm`,`tnf`,`u`,`vout`,`z`] >> asm_rewrite_tac[] >>
      rpt strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _`
        (drule_then (qx_choosel_then [`pt`,`rt`,`w`] (map_every assume_tac o CONJUNCTS))) >>
      qexistsl_tac [`pt`,`rt`,`w`] >> asm_rewrite_tac[]) >>
  qpat_x_assum `!exc. INR _ = INR exc ==> _`
    (strip_assume_tac o SIMP_RULE bool_ss [sumTheory.INR_11]) >>
  qpat_assum `convert_result _ _ _ _ = INR _` (SUBST1_TAC o SYM) >>
  irule dynamic_convert_failure >>
  goal_assum (drule_at Any) >> simp[] >>
  rename1 `gas_origin_ptr_path _ _ _ (Abort Revert_abort u,Gf,tnf)` >>
  qexistsl_tac [`Gf`,`tnf`,`u`] >> first_assum ACCEPT_TAC
QED

Theorem dynamic_convert_pair_run[local]:
  ^suffix_source /\ is_word_type dst /\ (!n. dst <> FlagT n) /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx (expr_type e) e es ==>
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx ty ^convert_expr es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rewrite_tac[expr_vv_sim_full_mods_def] >>
  qx_genl_tac [`st0`,`sa`,`sb`,`shadow_sa`,`shadow_sb`,`vv`,`s0`,`G0`,`tn0`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then (qx_choosel_then [`op`,`sm`,`shadow_sm`] (map_every assume_tac o CONJUNCTS))
    dynamic_convert_paired_cut_mods >>
  drule_then assume_tac dynamic_convert_admissible >>
  drule_all_then assume_tac convert_operand_buffer_outcome_mods >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (qpat_assum `lower_value _ _ _ e sa = _` (mp_tac o MATCH_MP (cj 2 compile_expr_grows)) >> simp[]) >>
  `^suffix_frame` by
    (simp[] >> conj_tac >- (drule_all local_ptrs_reserved_next_var >> simp[]) >>
     rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  Q.SUBGOAL_THEN `?out. vv = StackValue dst out /\
    (if ^zero_layout then out = Lit 0w /\ sb = sm else
      compile_type_convert op (mk_convert_op (expr_type e) dst) sm = (out,sb) /\
      fn_has_code sm sb func)` (qx_choose_then `out` (map_every assume_tac o CONJUNCTS))
  >- (Cases_on `^zero_layout` >> qpat_x_assum `(if _ then _ else _)` mp_tac >>
      asm_simp_tac bool_ss [] >> metis_tac[]) >>
  qpat_x_assum `vv = StackValue _ _` SUBST_ALL_TAC >>
  suspend "bind"
QED

Resume dynamic_convert_pair_run[bind]:
  simp[post_value_type_def,expr_type_def,contextTheory.vv_location_def] >>
  irule convert_reached_bind_mods >> BETA_TAC >>
  simp[dynamic_convert_source_action,bodyForcedStorageFrameModsTheory.bop_forced_storage_frame] >>
  qexists_tac `^operand_post` >> BETA_TAC >>
  reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >>
      qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ _ _` (irule_at Any) >>
      BETA_TAC >> simp[] >>
      rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
      qpat_x_assum `?v pt rt w. _` (qx_choosel_then [`v`,`pt`,`rt`,`w`]
        (map_every assume_tac o CONJUNCTS)) >>
      qexists_tac `v` >> asm_rewrite_tac[] >>
      qexistsl_tac [`pt`,`rt`,`w`] >> asm_rewrite_tac[]) >>
  qx_genl_tac [`marks`,`v`,`ee`,`G`,`tn`,`t`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,ee)` by
    (`ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
     qpat_assum `!tail. _ = (_,ee with gas_obs := tail)`
       (qspec_then `[]` (mp_tac o REWRITE_RULE [listTheory.APPEND_NIL])) >>
     asm_rewrite_tac[]) >>
  irule gas_outcome_full_mods_post_source >>
  qexistsl_tac [`^word_post`,`^convert_exit`] >> BETA_TAC >>
  conj_tac
  >- (rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
      qpat_x_assum `?v. _ = INL (Value v) /\ _` strip_assume_tac >>
      goal_assum (drule_at Any) >> simp[]) >>
  conj_tac >- simp[] >>
  Cases_on `^zero_layout`
  >- (qpat_x_assum `(if _ then out = Lit 0w /\ _ else _)` mp_tac >>
      asm_simp_tac bool_ss [] >> disch_then (map_every assume_tac o CONJUNCTS) >>
      irule (BETA_RULE dynamic_convert_zero) >> asm_simp_tac bool_ss [] >>
      rpt conj_tac
      >- (qexists_tac `gas_explicit marks s0.vs_gas_readings` >> first_assum ACCEPT_TAC)
      >- (qexists_tac `op` >> asm_rewrite_tac[]) >>
      qexistsl_tac [`env`,`mods`] >> asm_rewrite_tac[]) >>
  qpat_x_assum `(if _ then out = Lit 0w /\ _ else _)` mp_tac >>
  asm_simp_tac bool_ss [] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  irule (BETA_RULE dynamic_convert_nonzero) >> asm_simp_tac bool_ss [] >>
  conj_tac >- (qpat_assum `~(^zero_layout)` mp_tac >> simp[]) >>
  rpt conj_tac
  >- (qexists_tac `gas_explicit marks s0.vs_gas_readings` >> first_assum ACCEPT_TAC)
  >- (qexistsl_tac [`op`,`sm`] >> asm_rewrite_tac[]) >>
  qexistsl_tac [`env`,`mods`] >> asm_rewrite_tac[]
QED
Finalise dynamic_convert_pair_run

(* The scalar result is already materialized on both paths. *)
Theorem dynamic_convert_lower_cuts[local]:
  (!sa. ?out sb. compile_expr ce ty ^convert_expr sa = (StackValue dst out,sb)) /\
  lower_value compile_expr ce ty ^convert_expr sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr ^convert_expr)
    shadow_sa = (op,shadow_sb) /\ gas_shadow_state sa shadow_sa ==>
  compile_expr ce ty ^convert_expr sa = (StackValue dst op,sb) /\
  compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr ^convert_expr)
    shadow_sa = (StackValue dst op,shadow_sb)
Proof
  strip_tac >>
  qpat_x_assum `!sa. ?out sb. _` (qspec_then `sa` strip_assume_tac) >>
  Cases_on `compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr ^convert_expr) shadow_sa` >>
  rename1 `_ = (shadow_vv,shadow_end)` >>
  `gas_shadow_compiles (compile_expr ce ty ^convert_expr)
     (compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr ^convert_expr))` by
    MATCH_ACCEPT_TAC gas_shadow_stmt_compile_expr_env >>
  drule_all_then strip_assume_tac gas_shadow_step >>
  qpat_x_assum `shadow_vv = _` SUBST_ALL_TAC >>
  qpat_x_assum `lower_value _ _ _ (TypeBuiltin _ _ _ _) _ = _` mp_tac >>
  qpat_x_assum `lower_value _ _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[lower_value_def,comp_bind_def,unwrap_value_def,comp_return_def] >>
  rpt strip_tac >> simp[]
QED

Theorem dynamic_convert_read[local]:
  is_word_type dst /\
  (!sa. ?out sb. compile_expr ce ty ^convert_expr sa = (StackValue dst out,sb)) /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx ty ^convert_expr es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx ty ^convert_expr es
Proof
  strip_tac >> irule materialized_value_from_vv_mods >>
  qpat_assum `expr_vv_sim_full_mods _ _ _ _ _ _` (irule_at Any) >>
  reverse conj_tac
  >- (rpt gen_tac >> strip_tac >> drule_then ACCEPT_TAC eval_expr_type_builtin_value) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac dynamic_convert_lower_cuts >>
  qexists_tac `StackValue dst op` >> asm_rewrite_tac[] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `raw = Value _` SUBST_ALL_TAC >>
  `~is_word_type (post_value_type ce ^convert_expr) ==> ptr_buf_ok ce ^convert_expr op G t` by
    simp[post_value_type_def,expr_type_def] >>
  drule_all_then strip_assume_tac stack_value_read_post_mods >> asm_rewrite_tac[]
QED

Theorem convert_dynamic_route_mods:
  contract_inv mods exps ctx ce cx /\
  module_body_inv mods src tops ce cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods ce cx env (TypeBuiltin ann Convert dst [e]) es /\
  body_expr_full_ok_mods mods exps cx e /\
  is_bytestring_type (expr_type e) /\ ~is_bytestring_type dst ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx ty (TypeBuiltin ann Convert dst [e]) es /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx ty (TypeBuiltin ann Convert dst [e]) es /\
  (!sa. ?out sb. compile_expr ce ty (TypeBuiltin ann Convert dst [e]) sa =
                  (StackValue dst out,sb)) /\
  (!s raw mid. eval_expr cx (TypeBuiltin ann Convert dst [e]) s = (INL raw,mid) ==>
     ?v. raw = Value v)
Proof
  strip_tac >> drule_all_then (map_every assume_tac o CONJUNCTS) dynamic_convert_entry_mods >>
  qpat_x_assum `ann = dst` SUBST_ALL_TAC >>
  qpat_x_assum `body_expr_full_ok_mods _ _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_full_ok_mods_def]) >>
  `expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     ce cx (expr_type e) e es` by
    (qpat_assum `!DF lo d PG src tops ctx sh f sf ce env ty st.
       _ ==> expr_sim_full_mods _ _ _ _ _ _ /\ expr_vv_sim_full_mods _ _ _ _ _ _`
       (strip_assume_tac o SIMP_RULE bool_ss [IMP_CONJ_THM,FORALL_AND_THM]) >>
     qpat_assum `!DF lo d PG src tops ctx sh f sf ce env ty st.
       _ ==> expr_vv_sim_full_mods _ _ _ _ _ _` irule >>
     simp[] >> conj_tac >- (qexistsl_tac [`src`,`tops`] >> simp[]) >>
     qexists_tac `env` >> simp[]) >>
  `!sa. ?out sb. compile_expr ce ty ^convert_expr sa = (StackValue dst out,sb)` by
    (irule dynamic_convert_stack >> simp[]) >>
  `expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     ce cx ty ^convert_expr es` by
    (irule dynamic_convert_pair_run >> asm_rewrite_tac[] >>
     qexistsl_tac [`env`,`mods`] >> asm_rewrite_tac[]) >>
  rpt conj_tac
  >- (irule dynamic_convert_read >> asm_rewrite_tac[])
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >> drule_then ACCEPT_TAC eval_expr_type_builtin_value
QED
