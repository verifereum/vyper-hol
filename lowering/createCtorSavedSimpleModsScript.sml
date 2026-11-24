(* Saving a constructor operand that needs no private aggregate copy. *)
Theory createCtorSavedSimpleMods
Ancestors
  createCtorSavedSimple createExprSizeExitDefsMods createCtorSnapshotTypingMods bodyFullPostsMods
  bodyFullExtCallPosList bodyFullExtCallPosAggregate bodyFullExtCallPosTransport
  exprSimFullBundleProps exprBodyPreProps exprSimSource exprSimUnwrap
  exprReasonOperand exprOperandVar exprSimWordArgs exprSimProps exprSimMemDefs
  exprSimHyps exprSimHypsDefs exprLowering exprLoweringProps loweringPosts bodyPtrDefs
  context compileEnv bodyMemoryDefs bodyFullAssign abiEncodeArgsCase abiEncodeArgsSim abiEncodeMaterialize
  aggregateEvaluatedLayout exprPtrUnwrapStorageShape vyperEvalExprPreservesScopesDom
  vyperTypeExprSoundness vyperStorageFootprint vyperState freshWrites
  createCtorSnapshotReadTypeMods createCtorSnapshotByteRetagMods
  exprSimIfExpCompat exprBodyPreTypingProps exprBodyPreCallSafetyProps
  vyperTypeEvalSoundness vyperTypeEvalCaseProofs vyperTypeSystem valueCopyBytes

(* The word snapshot is exactly the scalar child fragment, including
   any instructions emitted by unwrapping a located word. *)

Theorem ctor_snapshot_word_lower_value_mods:
  expr_body_pre_mods mods ce cx env e es /\
  is_word_type (lowered_value_type ce e) /\
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  compile_snapshot_vv ce copy
    (ext_call_arg_value (lowered_value_type ce e) vv) sm = (sv,sb) ==>
  ?op. lower_value compile_expr ce (expr_type e) e sa = (op,sb) /\
       sv = StackValue (expr_type e) op
Proof
  strip_tac >> drule ctor_snapshot_word_types_mods >> strip_tac >> gvs[] >>
  `reason_uniform_shape compile_expr ce (expr_type e) e` by
    (irule compile_expr_reason_uniform >> qexists_tac `env` >>
     drule expr_body_pre_mods_inv >> fs[expr_sim_inv_mods_def] >>
     metis_tac[expr_body_pre_mods_well_typed]) >>
  `vv_type vv = expr_type e` by
    (fs[reason_uniform_shape_def] >> first_x_assum drule >>
     Cases_on `vv` >> gvs[reason_result_shape_def, vv_type_def]) >>
  `ext_call_arg_value (expr_type e) vv = vv` by
    (Cases_on `vv` >> gvs[ext_call_arg_value_def, vv_type_def]) >>
  Cases_on `unwrap_value ce vv sm` >>
  gvs[lower_value_def, compile_snapshot_vv_def, comp_bind_def, comp_return_def]
QED

Theorem ctor_saved_head_word_mods[local]:
  expr_body_pre_mods mods ce cx env e es /\
  is_word_type (lowered_value_type ce e) /\
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  compile_snapshot_vv ce (exprs_can_mutate ce xs)
    (ext_call_arg_value (lowered_value_type ce e) vv) sm = (sv,sb) /\
  lower_value compile_expr ce (expr_type e) e sa = (op,sb) /\
  sv = StackValue (expr_type e) op /\
  vyperState$bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee) /\
  local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d ce sa s0 /\ ~t.vs_halted /\
  expr_sim_full_post_mods (DF,lo,d,ctx,func) ce cx e
    (es,sa,sb,s0,op,G0,tn0) H (INL v : value + exception) ee G tn t ==>
  extcall_positional_post_mods mods T DF lo d ctx func ce cx env xs [e] [sv]
    sa sb es s0 G0 tn0 H (INL [v]) ee G tn t
Proof
  strip_tac >> drule ctor_snapshot_word_types_mods >> strip_tac >> gvs[] >>
  `ci_mono sm sb` by
    (qspecl_then [`ce`, `exprs_can_mutate ce xs`,
       `ext_call_arg_value (expr_type e) vv`, `sm`] mp_tac
       ci_mono_compile_snapshot_vv >> simp[]) >>
  `!id ty. FLOOKUP env.var_types id = SOME ty ==>
            well_formed_type env.type_defs ty` by
    metis_tac[expr_body_pre_mods_inv, expr_sim_inv_mods_env,
              logArgumentTypeEvalTheory.consistent_variable_type_well_formed] >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_all_then strip_assume_tac exprWordOperandTheory.lower_value_word_shape >>
  `expr_body_pre_mods mods ce cx env e (es with gas_obs := gs)` by simp[] >>
  drule_all_then strip_assume_tac ctor_snapshot_source_frame_mods >>
  gvs[expr_sim_full_post_mods_def, expr_sim_full_endpoint_def, expr_post_mods_def] >>
  drule expr_post_frame >> strip_tac >>
  fs[expr_post_def] >>
  `return_buf_frame d ce sb t` by
    (irule return_buf_frame_frame >> qexistsl [`ce`,`s0`,`sa`] >> simp[]) >>
  simp[extcall_positional_post_mods_def, vv_operand_def, vv_location_def] >>
  map_every qexists_tac [`sa`,`sm`,`sb`,`vv`,`Value v`,`exprs_can_mutate ce xs`] >>
  gvs[ci_mono_def, vv_holds_mods_def, vv_holds_def, vv_at_def, ptr_vv_ok_def,
      vv_store_bound_def, read_result_def, return_def]
QED

Theorem ctor_retained_representation_mods[local]:
  expr_body_pre_mods mods ce cx env e es /\
  ~is_word_type (lowered_value_type ce e) /\
  compile_expr ce (expr_type e) e sa = (vv,sb) /\
  eval_expr cx e es = (INL raw,ee) /\ read_result cx raw ee = (INL v,ee) /\
  vv_holds_mods ce cx (post_value_type ce e) raw vv ee t /\
  vv_at ce cx (post_value_type ce e) sa sb ee raw vv t /\
  ptr_vv_ok cx (post_value_type ce e) raw vv ee G tn t /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee raw vv t /\
  (!tv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv ==> val_wf tv v) /\
  sv = ext_call_arg_value (lowered_value_type ce e) vv ==>
  ((?tag op. sv = StackValue tag op) \/
   (?p. sv = LocatedValue (lowered_value_type ce e) p /\ p.ptr_location = LocMemory) \/
   (?p. sv = LocatedValue (lowered_value_type ce e) p /\ p.ptr_location <> LocMemory /\
        lowered_value_type ce e = expr_type e /\ sv = vv)) /\
  ?saved. read_result cx saved ee = (INL v,ee) /\
    vv_holds_mods ce cx (lowered_value_type ce e) saved sv ee t /\
    vv_at ce cx (lowered_value_type ce e) sa sb ee saved sv t /\
    ptr_vv_ok cx (lowered_value_type ce e) saved sv ee G tn t /\
    vv_store_bound cx (lowered_value_type ce e) (lowered_value_type ce e) ee saved sv t
Proof
  strip_tac >> drule ctor_snapshot_word_types_mods >> strip_tac >>
  `~is_word_type (expr_type e)` by metis_tac[] >>
  drule expr_body_pre_mods_inv >> strip_tac >>
  drule expr_body_pre_mods_well_typed >> strip_tac >>
  drule expr_sim_inv_mods_env >> strip_tac >>
  `env.type_defs = get_tenv cx` by metis_tac[env_consistent_type_defs_get_tenv] >>
  `!id ty. FLOOKUP env.var_types id = SOME ty ==> well_formed_type env.type_defs ty` by
    metis_tac[logArgumentTypeEvalTheory.consistent_variable_type_well_formed] >>
  `sfields_tenv_consistent ce.ce_struct_fields env.type_defs` by fs[expr_sim_inv_mods_def] >>
  `!fid sg. FLOOKUP env.fn_sigs fid = SOME sg ==>
            ce.ce_func_return_type (nsid_to_string fid) = sg.ret_ty` by
    metis_tac[expr_sim_inv_mods_return_type] >>
  `arg_type_fits (lowered_value_type ce e) (expr_type e)` by
    (drule_all ifexp_lowered_type_classify >> strip_tac >> simp[] >>
     PairCases_on `fid` >>
     gvs[well_typed_expr_def, lowered_value_type_def, vyperASTTheory.expr_type_def] >>
     qpat_x_assum `!fid sg. _` (drule_then SUBST1_TAC) >>
     fs[type_widens_to_def]) >>
  drule_all_then assume_tac materialize_post_lowered_classify >>
  `~is_word_type (post_value_type ce e)` by metis_tac[is_bytestring_word_type] >>
  `vv_store_bound cx (lowered_value_type ce e) (lowered_value_type ce e) ee raw vv t` by
    (irule extcall_saved_physical_store_bound >> conj_tac
     >- (qexists_tac `v` >> simp[]) >> qexists_tac `post_value_type ce e` >> simp[]) >>
  Cases_on `?tag p. vv = LocatedValue tag p /\ p.ptr_location <> LocMemory`
  >- (gvs[] >>
      `lowered_value_type ce e = expr_type e` by metis_tac[compile_nonmemory_lowered_value_type] >>
      `post_value_type ce e = expr_type e` by simp[post_value_type_lowered] >>
      `tag = expr_type e` by (Cases_on `p.ptr_location = LocCode` >> fs[vv_holds_mods_def, vv_holds_def]) >>
      gvs[ext_call_arg_value_def] >> qexists_tac `raw` >> simp[]) >>
  Cases_on `post_value_type ce e = lowered_value_type ce e`
  >- (Cases_on `vv` >> gvs[ext_call_arg_value_def] >> qexists_tac `raw` >>
      gvs[vv_holds_mods_def, vv_holds_def, vv_at_def, ptr_vv_ok_def, vv_store_bound_def]) >>
  `post_value_type ce e = expr_type e` by
    (Cases_on `?ty fid args drv. e = Call ty (IntCall fid) args drv`
     >- (gvs[vyperASTTheory.expr_type_def] >> IF_CASES_TAC >> gvs[])
     >> metis_tac[post_value_type_not_int_call]) >>
  `vyperState$bind (eval_expr cx e) (read_result cx) es = (INL v,ee)` by simp[bind_def] >>
  `?a. evaluate_type (get_tenv cx) (expr_type e) = SOME a /\ value_has_type a v` by
    (drule expr_body_pre_mods_runtime_typing >> strip_tac >>
     drule expr_body_pre_mods_call_evaluation_safe >> strip_tac >>
     drule_at (Pat `vyperState$bind _ _ _ = _`) (REWRITE_RULE [ETA_AX] eval_expr_read_type_sound) >>
     disch_then (qspec_then `env` mp_tac) >> simp[runtime_consistent_def, value_runtime_typed_def] >>
     fs[runtime_consistent_def]) >>
  drule_all_then strip_assume_tac ctor_snapshot_read_physical_type_mods >>
  `(?tag op. vv = StackValue tag op) \/ (?tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory)` by
    (Cases_on `vv` >> gvs[]) >>
  `vv_holds_mods ce cx (lowered_value_type ce e) (Value v) sv ee t /\
   vv_at ce cx (lowered_value_type ce e) sa sb ee (Value v) sv t /\
   ptr_vv_ok cx (lowered_value_type ce e) (Value v) sv ee G tn t /\
   vv_store_bound cx (lowered_value_type ce e) (lowered_value_type ce e) ee (Value v) sv t` by
    (qpat_x_assum `sv = _` SUBST_ALL_TAC >>
     irule ctor_snapshot_bytes_retag_mods >> metis_tac[]) >>
  Cases_on `vv` >> gvs[ext_call_arg_value_def] >>
  qexists_tac `Value v` >> simp[read_result_def, return_def]
QED

Theorem ctor_retained_storage_live_mods[local]:
  contract_inv mods exps ctx ce cx /\
  module_body_inv mods src tops ce cx /\ expr_body_pre_mods mods ce cx env e (es with gas_obs := gs) /\
  valid_horizon cx (es with gas_obs := gs) H ee.storage_trace /\
  compile_expr ce (expr_type e) e sa = (vv,sb) /\
  eval_expr cx e (es with gas_obs := gs) = (INL raw,ee) /\
  vv_post_mods H ctx func ce cx e es sa sb s0 ee raw vv t ==>
  vv_storage_live H cx vv ee t
Proof
  cheat
QED

Theorem ctor_saved_head_retained_mods:
  contract_inv mods exps ctx ce cx /\
  module_body_inv mods src tops ce cx /\ expr_body_pre_mods mods ce cx env e es /\
  ~is_word_type (lowered_value_type ce e) /\ ~exprs_can_mutate ce xs /\
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  compile_snapshot_vv ce (exprs_can_mutate ce xs)
    (ext_call_arg_value (lowered_value_type ce e) vv) sm = (sv,sb) /\
  eval_expr cx e (es with gas_obs := gs) = (INL raw,ee) /\
  read_result cx raw ee = (INL v,ee) /\
  valid_horizon cx (es with gas_obs := gs) H ee.storage_trace /\
  local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d ce sa s0 /\ ~t.vs_halted /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  vv_post_mods H ctx func ce cx e es sa sm s0 ee raw vv t /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee raw vv t /\
  ptr_vv_ok cx (post_value_type ce e) raw vv ee G tn t /\
  alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at_mods (DF H) lo d ce cx ee G tn t /\
  ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
  (!tag op. vv = StackValue tag op ==> ptr_buf_ok ce e op G t) /\
  (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
           ptr_buf_ok ce e p.ptr_operand G t) /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
           eval_operand (vv_operand vv) t = SOME w ==>
       w2n w + type_memory_size rt <= lo /\
       (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==> val_in_memory rt v (w2n w) mem)) ==>
  extcall_positional_post_mods mods T DF lo d ctx func ce cx env xs [e] [sv]
    sa sb es s0 G0 tn0 H (INL [v]) ee G tn t
Proof
  cheat
QED

Theorem ctor_saved_head_simple_mods:
  contract_inv mods exps ctx ce cx /\
  module_body_inv mods src tops ce cx /\ expr_body_pre_mods mods ce cx env e es /\
  (is_word_type (lowered_value_type ce e) \/ ~exprs_can_mutate ce xs) /\
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  compile_snapshot_vv ce (exprs_can_mutate ce xs)
    (ext_call_arg_value (lowered_value_type ce e) vv) sm = (sv,sb) /\
  vyperState$bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee) /\
  local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d ce sa s0 /\ ~t.vs_halted /\
  t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  (is_word_type (lowered_value_type ce e) ==>
    !op. lower_value compile_expr ce (expr_type e) e sa = (op,sb) ==>
      expr_sim_full_post_mods (DF,lo,d,ctx,func) ce cx e
        (es,sa,sb,s0,op,G0,tn0) H (INL v : value + exception) ee G tn t) /\
  (~is_word_type (lowered_value_type ce e) ==>
    valid_horizon cx (es with gas_obs := gs) H ee.storage_trace /\
    ?raw. eval_expr cx e (es with gas_obs := gs) = (INL raw,ee) /\
      vv_post_mods H ctx func ce cx e es sa sm s0 ee raw vv t /\
      vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee raw vv t /\
      ptr_vv_ok cx (post_value_type ce e) raw vv ee G tn t /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d ce cx ee G tn t /\
      ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
      (!tag op. vv = StackValue tag op /\ ~is_word_type (post_value_type ce e) ==>
               ptr_buf_ok ce e op G t) /\
      (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
               ptr_buf_ok ce e p.ptr_operand G t) /\
      (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
        ?val. read_result cx raw ee = (INL val,ee) /\
          !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
                 eval_operand (vv_operand vv) t = SOME w ==>
            w2n w + type_memory_size rt <= lo /\
            (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
                   val_in_memory rt val (w2n w) mem))) ==>
  extcall_positional_post_mods mods T DF lo d ctx func ce cx env xs [e] [sv]
    sa sb es s0 G0 tn0 H (INL [v]) ee G tn t
Proof
  cheat
QED
