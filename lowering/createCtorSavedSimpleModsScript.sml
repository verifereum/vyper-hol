(* Saving a constructor operand that needs no private aggregate copy. *)
Theory createCtorSavedSimpleMods
Ancestors
  createCtorSavedSimple createExprSizeExitDefsMods
  bodyFullExtCallPosList bodyFullExtCallPosAggregate bodyFullExtCallPosTransport
  exprSimFullBundleProps exprBodyPreProps exprSimSource exprSimUnwrap
  exprReasonOperand exprOperandVar exprSimWordArgs exprSimProps exprSimMemDefs
  exprSimHyps exprSimHypsDefs exprLowering exprLoweringProps loweringPosts bodyPtrDefs
  context compileEnv bodyMemoryDefs bodyFullAssign abiEncodeArgsCase abiEncodeArgsSim abiEncodeMaterialize
  aggregateEvaluatedLayout exprPtrUnwrapStorageShape vyperEvalExprPreservesScopesDom
  vyperTypeExprSoundness vyperStorageFootprint vyperState freshWrites

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
  cheat
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
  cheat
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
  cheat
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
