(*
 * Expression simulation: one captured abi_encode argument, counted.
 *
 * A composite argument that a later argument may mutate is compiled and
 * then materialized into a fresh buffer at its lowered type; followed by
 * the counted run of the remaining arguments, the whole list runs as
 * eval_exprs on an actual counted path.
 *)

Theory exprSimAbiEncodeArgsCaptured
Ancestors
  abiEncodeArgsSim exprSimHypsDefs exprSimWordArgs abiDecoderReentry
  exprSimAbiGasBridge

Theorem abi_args_captured_cons_sim:
  expr_vv_sim ctx func ce cx (expr_type e) e es /\
  gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
  expr_body_pre ce cx env e es /\
  compile_expr ce (expr_type e) e sa = (vv,mid) /\
  compile_materialize_vv ce (lowered_value_type ce e) vv mid = (op,sm) /\
  fn_has_code sa mid func /\ fn_has_code mid sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce mid /\ local_ptrs_reserved ce sm /\
  stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!gs v es1.
     bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,es1) ==>
     MAP FDOM es.scopes = MAP FDOM es1.scopes /\
     ?tv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
          value_has_type tv v /\ val_wf tv v /\
          type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
          type_memory_size tv < 2 ** 64 /\
          type_memory_size tv + 64 < dimword (:256)) /\
  (!gs v es1 gs' rr ee.
     bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,es1) /\
     eval_exprs cx args (es1 with gas_obs := gs') = (rr,ee) ==>
     MAP FDOM ee.scopes = MAP FDOM es1.scopes) /\
  ci_mono sa mid /\ ci_mono mid sm /\ ci_mono sm sb /\
  (!x. vv_operand vv = Var x ==> not_fresh_at mid x) /\
  (!x. op = Var x ==> not_fresh_at sm x) /\ (!l. op <> Label l) /\
  ~is_word_type (expr_type e) /\
  (!gs v es1 t.
     bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,es1) /\
     stmt_state_rel ctx func ce cx es1 t /\ ~t.vs_halted /\
     t.vs_current_bb = sm.cs_current_bb /\
     t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
     gas_outcome F (cx_tops cx) (ctx,func) (eval_exprs cx args) (es1,t)
       (\rr ee u. ?vs. rr = INL vs /\
          abi_args_post ctx func ce cx es1 sm sb t ee args ops vs u /\
          u.vs_current_bb = sb.cs_current_bb /\
          u.vs_inst_idx = LENGTH sb.cs_current_insts)
       (\rr ee r. wb_args_exit rr r)) ==>
  gas_outcome F (cx_tops cx) (ctx,func) (eval_exprs cx (e::args)) (es,s0)
    (\rr ee u. ?vs. rr = INL vs /\
       abi_args_post ctx func ce cx es sa sb s0 ee (e::args) (op::ops) vs u /\
       u.vs_current_bb = sb.cs_current_bb /\
       u.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\rr ee r. wb_args_exit rr r)
Proof
  cheat
QED

Theorem abi_args_captured_cons_sim_live:
  expr_vv_sim ctx func ce cx (expr_type e) e es /\
  gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
  expr_body_pre ce cx env e es /\
  compile_expr ce (expr_type e) e sa = (vv,mid) /\
  compile_materialize_vv ce (lowered_value_type ce e) vv mid = (op,sm) /\
  fn_has_code sa mid func /\ fn_has_code mid sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce mid /\ local_ptrs_reserved ce sm /\
  stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!gs v es1.
     bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,es1) ==>
     MAP FDOM es.scopes = MAP FDOM es1.scopes /\
     ?tv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
          value_has_type tv v /\ val_wf tv v /\
          type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
          type_memory_size tv < 2 ** 64 /\
          type_memory_size tv + 64 < dimword (:256)) /\
  (!gs v es1 gs' rr ee.
     bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,es1) /\
     eval_exprs cx args (es1 with gas_obs := gs') = (rr,ee) ==>
     MAP FDOM ee.scopes = MAP FDOM es1.scopes) /\
  ci_mono sa mid /\ ci_mono mid sm /\ ci_mono sm sb /\
  (!x. vv_operand vv = Var x ==> not_fresh_at mid x) /\
  (!x. op = Var x ==> not_fresh_at sm x) /\ (!l. op <> Label l) /\
  ~is_word_type (expr_type e) /\
  (!gs v es1 t.
     bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,es1) /\
     stmt_state_rel ctx func ce cx es1 t /\ ~t.vs_halted /\
     t.vs_current_bb = sm.cs_current_bb /\
     t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
     gas_outcome F (cx_tops cx) (ctx,func) (eval_exprs cx args) (es1,t)
       (\rr ee u. ?vs. rr = INL vs /\
          abi_args_post ctx func ce cx es1 sm sb t ee args ops vs u /\
          EVERY (abi_decoder_operand_live sb.cs_next_var) ops /\
          u.vs_current_bb = sb.cs_current_bb /\
          u.vs_inst_idx = LENGTH sb.cs_current_insts)
       (\rr ee r. wb_args_exit rr r)) ==>
  gas_outcome F (cx_tops cx) (ctx,func) (eval_exprs cx (e::args)) (es,s0)
    (\rr ee u. ?vs. rr = INL vs /\
       abi_args_post ctx func ce cx es sa sb s0 ee (e::args) (op::ops) vs u /\
       EVERY (abi_decoder_operand_live sb.cs_next_var) (op::ops) /\
       u.vs_current_bb = sb.cs_current_bb /\
       u.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\rr ee r. wb_args_exit rr r)
Proof
  cheat
QED
