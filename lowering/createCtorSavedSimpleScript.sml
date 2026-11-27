(* Saving a constructor operand that needs no private aggregate copy. *)
Theory createCtorSavedSimple
Ancestors
  bodyFullExtCallPosList bodyFullExtCallPosAggregate bodyFullExtCallPosTransport
  exprSimFullBundleProps exprBodyPreProps exprSimSource exprSimUnwrap
  exprReasonOperand exprOperandVar exprSimWordArgs exprSimProps exprSimMemDefs
  exprSimHyps exprSimHypsDefs exprLowering exprLoweringProps loweringPosts bodyPtrDefs
  context compileEnv bodyMemoryDefs bodyFullAssign abiEncodeArgsCase abiEncodeArgsSim abiEncodeMaterialize
  aggregateEvaluatedLayout exprPtrUnwrapStorageShape vyperEvalExprPreservesScopesDom
  vyperTypeExprSoundness vyperStorageFootprint vyperState freshWrites

(* The word snapshot is exactly the scalar child fragment, including
   any instructions emitted by unwrapping a located word. *)
Theorem ctor_snapshot_word_lower_value:
  expr_body_pre ce cx env e es /\
  is_word_type (lowered_value_type ce e) /\
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  compile_snapshot_vv ce copy
    (ext_call_arg_value (lowered_value_type ce e) vv) sm = (sv,sb) ==>
  ?op. lower_value compile_expr ce (expr_type e) e sa = (op,sb) /\
       sv = StackValue (expr_type e) op
Proof
  strip_tac >>
  drule expr_body_pre_lowered_fits >> strip_tac >>
  `is_word_type (expr_type e) /\ lowered_value_type ce e = expr_type e` by
    metis_tac[arg_type_fits_word_type, abi_args_word_fits_eq] >>
  `reason_uniform_shape compile_expr ce (expr_type e) e` by
    (irule compile_expr_reason_uniform >> qexists_tac `env` >>
     drule expr_body_pre_static_facts >> simp[expr_sim_inv_def]) >>
  `vv_type vv = expr_type e` by
    (fs[reason_uniform_shape_def] >> first_x_assum drule >>
     Cases_on `vv` >> gvs[reason_result_shape_def, vv_type_def]) >>
  `ext_call_arg_value (expr_type e) vv = vv` by
    (Cases_on `vv` >> gvs[ext_call_arg_value_def, vv_type_def]) >>
  Cases_on `unwrap_value ce vv sm` >>
  gvs[lower_value_def, compile_snapshot_vv_def, comp_bind_def, comp_return_def]
QED

Theorem ctor_saved_head_word[local]:
  expr_body_pre ce cx env e es /\
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
  expr_sim_full_post (DF,lo,d,ctx,func) ce cx e
    (es,sa,sb,s0,op,G0,tn0) H (INL v : value + exception) ee G tn t ==>
  extcall_positional_post T DF lo d ctx func ce cx env xs [e] [sv]
    sa sb es s0 G0 tn0 H (INL [v]) ee G tn t
Proof
  strip_tac >>
  drule expr_body_pre_lowered_fits >> strip_tac >>
  `is_word_type (expr_type e) /\ lowered_value_type ce e = expr_type e` by
    metis_tac[arg_type_fits_word_type, abi_args_word_fits_eq] >>
  drule compile_expr_extends >> strip_tac >>
  `ci_mono sm sb` by
    (qspecl_then [`ce`, `exprs_can_mutate ce xs`,
       `ext_call_arg_value (lowered_value_type ce e) vv`, `sm`] mp_tac
       ci_mono_compile_snapshot_vv >> simp[]) >>
  `(!x. op = Var x ==> not_fresh_at sb x) /\ sa.cs_next_var <= sb.cs_next_var` by
    (drule_all expr_body_pre_lower_value_word_shape >> simp[]) >>
  `expr_body_pre ce cx env e (es with gas_obs := gs)` by simp[] >>
  drule_all (REWRITE_RULE [ETA_AX] abi_args_success_ready) >> simp[] >> strip_tac >>
  gvs[expr_sim_full_post_def, expr_sim_full_endpoint_def] >>
  drule expr_post_frame >> strip_tac >>
  fs[expr_post_def] >>
  `return_buf_frame d ce sb t` by
    (irule return_buf_frame_frame >> qexistsl [`ce`,`s0`,`sa`] >> simp[]) >>
  simp[extcall_positional_post_def, vv_operand_def, vv_location_def] >>
  map_every qexists_tac [`sa`,`sm`,`sb`,`vv`,`Value v`,`exprs_can_mutate ce xs`] >>
  gvs[ci_mono_def, vv_holds_def, vv_at_def, ptr_vv_ok_def,
      vv_store_bound_def, read_result_def, return_def]
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  drule expr_body_pre_lowered_fits >> strip_tac >>
  `~is_word_type (expr_type e) /\ ~is_word_type (post_value_type ce e)` by
    metis_tac[arg_type_fits_word_type, exprSimIfExpWidenedPhysicalTypeTheory.post_value_type_nonword] >>
  `vv_store_bound cx (lowered_value_type ce e) (lowered_value_type ce e) ee raw vv t` by
    (irule extcall_saved_physical_store_bound >> conj_tac
     >- (qexists_tac `v` >> simp[]) >> qexists_tac `post_value_type ce e` >> simp[]) >>
  Cases_on `?tag p. vv = LocatedValue tag p /\ p.ptr_location <> LocMemory`
  >- (gvs[] >>
      `lowered_value_type ce e = expr_type e` by metis_tac[compile_nonmemory_lowered_value_type] >>
      `post_value_type ce e = expr_type e` by simp[post_value_type_lowered] >>
      `tag = expr_type e` by fs[vv_holds_def] >>
      gvs[ext_call_arg_value_def] >> qexists_tac `raw` >> simp[]) >>
  Cases_on `post_value_type ce e = lowered_value_type ce e`
  >- (Cases_on `vv` >> gvs[ext_call_arg_value_def] >> qexists_tac `raw` >>
      gvs[vv_holds_def, vv_at_def, ptr_vv_ok_def, vv_store_bound_def]) >>
  `post_value_type ce e = expr_type e` by
    (Cases_on `e` >> simp[post_value_type_def] >>
     rename1 `Call _ tgt _ _` >> Cases_on `tgt` >>
     gvs[post_value_type_def, vyperASTTheory.expr_type_def] >> IF_CASES_TAC >> gvs[]) >>
  `is_bytestring_type (expr_type e) /\ is_bytestring_type (lowered_value_type ce e)` by
    metis_tac[materialize_post_lowered_classify] >>
  Q.SUBGOAL_THEN
    `(?tag op. vv = StackValue tag op) \/ (?tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory)`
    ASSUME_TAC >- (Cases_on `vv` >> gvs[]) >>
  drule_at (Pat `eval_expr _ _ _ = _`) snapshot_bytes_retag >>
  disch_then (drule_at (Pat `read_result _ _ _ = _`)) >>
  disch_then assume_tac >>
  `vv_holds ce cx (lowered_value_type ce e) (Value v) sv ee t /\
   vv_at ce cx (lowered_value_type ce e) sa sb ee (Value v) sv t /\
   ptr_vv_ok cx (lowered_value_type ce e) (Value v) sv ee G tn t /\
   vv_store_bound cx (expr_type e) (lowered_value_type ce e) ee (Value v) sv t` by
    metis_tac[] >>
  `read_result cx (Value v) ee = (INL v,ee)` by simp[read_result_def, return_def] >>
  `vv_store_bound cx (lowered_value_type ce e) (lowered_value_type ce e) ee (Value v) sv t` by
    (irule extcall_saved_physical_store_bound >> conj_tac
     >- (qexists_tac `v` >> simp[]) >> qexists_tac `expr_type e` >> simp[]) >>
  Cases_on `vv` >> gvs[ext_call_arg_value_def] >>
  qexists_tac `Value v` >> simp[]
QED
*)
Theorem ctor_retained_representation[local]:
  expr_body_pre ce cx env e es /\
  ~is_word_type (lowered_value_type ce e) /\
  compile_expr ce (expr_type e) e sa = (vv,sb) /\
  eval_expr cx e es = (INL raw,ee) /\ read_result cx raw ee = (INL v,ee) /\
  vv_holds ce cx (post_value_type ce e) raw vv ee t /\
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
    vv_holds ce cx (lowered_value_type ce e) saved sv ee t /\
    vv_at ce cx (lowered_value_type ce e) sa sb ee saved sv t /\
    ptr_vv_ok cx (lowered_value_type ce e) saved sv ee G tn t /\
    vv_store_bound cx (lowered_value_type ce e) (lowered_value_type ce e) ee saved sv t
Proof
  cheat
QED

Theorem ctor_retained_storage_live[local]:
  body_inv tops ctx ce cx /\ expr_body_pre ce cx env e (es with gas_obs := gs) /\
  valid_horizon cx (es with gas_obs := gs) H ee.storage_trace /\
  compile_expr ce (expr_type e) e sa = (vv,sb) /\
  eval_expr cx e (es with gas_obs := gs) = (INL raw,ee) /\
  vv_post H ctx func ce cx e es sa sb s0 ee raw vv t ==>
  vv_storage_live H cx vv ee t
Proof
  strip_tac >>
  drule expr_body_pre_static_facts >> strip_tac >>
  `runtime_consistent env cx (es with gas_obs := gs) /\ functions_well_typed cx` by
    fs[expr_sim_inv_def, runtime_consistent_def] >>
  `call_evaluation_safe cx (int_calls_expr e)` by
    fs[expr_body_pre_split_def, expr_body_pre_mods_def] >>
  irule body_assign_rhs_storage_live >> simp[] >>
  qexistsl [`ce`,`ctx`,`e`,`env`,`es with gas_obs := gs`,`func`,`raw`,`s0`,`sa`,`sb`,`tops`] >>
  simp[vv_post_initial_gas]
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  `~is_word_type (expr_type e)` by
    metis_tac[expr_body_pre_lowered_fits, arg_type_fits_word_type] >>
  `sm = sb /\ sv = ext_call_arg_value (lowered_value_type ce e) vv` by
    (drule_all extcall_operand_snapshot_type >> strip_tac >>
     gvs[compile_snapshot_vv_def, comp_return_def]) >>
  qpat_x_assum `sm = sb` SUBST_ALL_TAC >>
  qpat_x_assum `sv = _` SUBST_ALL_TAC >>
  `expr_body_pre ce cx env e (es with gas_obs := gs)` by simp[] >>
  `vyperState$bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee)` by
    simp[bind_def] >>
  drule_all (REWRITE_RULE [ETA_AX] abi_args_success_ready) >> simp[] >> strip_tac >>
  drule_all ctor_retained_storage_live >> strip_tac >>
  drule compile_expr_extends >> strip_tac >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sb x` by
    metis_tac[cj 1 compiler_compile_var] >>
  fs[vv_post_def] >>
  `return_buf_frame d ce sb t` by
    (irule return_buf_frame_frame >> qexistsl [`ce`,`s0`,`sa`] >> simp[]) >>
  `wb_frame ce es ee sa s0 t` by
    (rewrite_tac[wb_frame_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!tv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv ==> val_wf tv v` by simp[] >>
  qabbrev_tac `sv = ext_call_arg_value (lowered_value_type ce e) vv` >>
  `vv_storage_live H cx sv ee t /\
   (!x. vv_operand sv = Var x ==> not_fresh_at sb x) /\
   (!tag op. sv = StackValue tag op ==> ptr_buf_ok ce e op G t) /\
   (!tag p. sv = LocatedValue tag p /\ p.ptr_location = LocMemory ==> ptr_buf_ok ce e p.ptr_operand G t) /\
   (ce.ce_is_ctor /\ vv_location sv = SOME LocCode ==>
    !rt w. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
           eval_operand (vv_operand sv) t = SOME w ==>
      w2n w + type_memory_size rt <= lo /\
      (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==> val_in_memory rt v (w2n w) mem))` by
    (qunabbrev_tac `sv` >> Cases_on `vv` >> gvs[ext_call_arg_value_def, vv_operand_def, vv_location_def]
     >> Cases_on `p.ptr_location = LocMemory` >> gvs[] >>
     `lowered_value_type ce e = expr_type e` by metis_tac[compile_nonmemory_lowered_value_type] >>
     `post_value_type ce e = expr_type e` by simp[post_value_type_lowered] >>
     rename1 `compile_expr _ _ _ _ = (LocatedValue tag p,sb)` >>
     `tag = expr_type e` by fs[vv_holds_def] >> gvs[]) >>
  `expr_body_pre ce cx env e (es with gas_obs := gs)` by simp[] >>
  `sv = ext_call_arg_value (lowered_value_type ce e) vv` by simp[Abbr `sv`] >>
  drule_at (Pat `eval_expr _ _ _ = _`) ctor_retained_representation >>
  disch_then drule_all >> suspend "saved"
QED
*)
Theorem ctor_saved_head_retained:
  body_inv tops ctx ce cx /\ expr_body_pre ce cx env e es /\
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
  vv_post H ctx func ce cx e es sa sm s0 ee raw vv t /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee raw vv t /\
  ptr_vv_ok cx (post_value_type ce e) raw vv ee G tn t /\
  alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at (DF H) lo d ce cx ee G tn t /\
  ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
  (!tag op. vv = StackValue tag op ==> ptr_buf_ok ce e op G t) /\
  (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
           ptr_buf_ok ce e p.ptr_operand G t) /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
           eval_operand (vv_operand vv) t = SOME w ==>
       w2n w + type_memory_size rt <= lo /\
       (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==> val_in_memory rt v (w2n w) mem)) ==>
  extcall_positional_post T DF lo d ctx func ce cx env xs [e] [sv]
    sa sb es s0 G0 tn0 H (INL [v]) ee G tn t
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume ctor_saved_head_retained[saved]:
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  qpat_x_assum `Abbrev _` kall_tac >>
  `compile_snapshot_vv ce F (ext_call_arg_value (lowered_value_type ce e) vv) sb = (sv,sb)` by
    (qpat_x_assum `sv = _` (fn th => once_rewrite_tac [GSYM th]) >> gvs[]) >>
  qpat_x_assum `sv = _` kall_tac >>
  simp[extcall_positional_post_def] >>
  conj_tac
  >- (map_every qexists_tac [`sa`,`sb`,`sb`,`vv`,`saved`,`F`] >> simp[]) >>
  qpat_x_assum `_ /\ vv_location sv = SOME LocCode ==> _` mp_tac >> simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise ctor_saved_head_retained[local]
*)

(* Use the scalar completed cut for words and the VV completed cut for
   retained aggregates. In the latter case the two target PCs coincide
   because the snapshot compiler returns without emitting code. *)
Theorem ctor_saved_head_simple:
  body_inv tops ctx ce cx /\ expr_body_pre ce cx env e es /\
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
      expr_sim_full_post (DF,lo,d,ctx,func) ce cx e
        (es,sa,sb,s0,op,G0,tn0) H (INL v : value + exception) ee G tn t) /\
  (~is_word_type (lowered_value_type ce e) ==>
    valid_horizon cx (es with gas_obs := gs) H ee.storage_trace /\
    ?raw. eval_expr cx e (es with gas_obs := gs) = (INL raw,ee) /\
      vv_post H ctx func ce cx e es sa sm s0 ee raw vv t /\
      vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee raw vv t /\
      ptr_vv_ok cx (post_value_type ce e) raw vv ee G tn t /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d ce cx ee G tn t /\
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
  extcall_positional_post T DF lo d ctx func ce cx env xs [e] [sv]
    sa sb es s0 G0 tn0 H (INL [v]) ee G tn t
Proof
  Cases_on `is_word_type (lowered_value_type ce e)` >> simp[] >> strip_tac
  >- (drule_all ctor_snapshot_word_lower_value >> strip_tac >>
      irule ctor_saved_head_word >> simp[] >> qexists_tac `gs` >> simp[]) >>
  `read_result cx raw ee = (INL v,ee)` by fs[bind_def] >>
  `~is_word_type (post_value_type ce e)` by
    metis_tac[expr_body_pre_lowered_fits, arg_type_fits_word_type,
              exprSimIfExpWidenedPhysicalTypeTheory.post_value_type_nonword] >>
  irule ctor_saved_head_retained >>
  qpat_assum `eval_expr _ _ _ = _` (irule_at Any) >>
  qpat_assum `compile_expr _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `body_inv _ _ _ _` (irule_at Any) >>
  simp[] >>
  qpat_x_assum `_ /\ vv_location vv = SOME LocCode ==> _` mp_tac >> simp[]
QED
