(* Concrete normal prefixes retain their source construct, compilation,
   full postcondition and exact cursor. No caller-selected post is used. *)
Theory gasNormalPrefix
Ancestors
  loweringPosts gasSummary allocaHistory exprLowering exprLoweringProps
  compileEnv venomState vyperInterpreter vyperState

Definition gas_value_prefix_def:
  gas_value_prefix H memory (ctx, func, cenv, cx) (ty, e)
    (sa, sb, op) (es, s0) marks (v, ee, t) <=>
    storage_well_formed_on cx es (FST H) ∧
    lower_value compile_expr cenv ty e sa = (op, sb) ∧
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    stmt_state_rel H ctx func cenv cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
    gas_marked_exec memory (ctx, func)
      (bind (eval_expr cx e) (read_result cx))
      (es, s0) marks (INL v) ee (OK t) /\
    expr_post H ctx func cenv cx e es sa sb s0
      (ee with gas_obs := []) v op t /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (memory ==>
       alloca_history func s0 /\ alloca_history func t /\
       s0.vs_alloca_next <= t.vs_alloca_next)
End

Theorem gas_value_prefix_start_gas_obs:
  gas_value_prefix H memory (ctx,func,cenv,cx) (ty,e) (sa,sb,op)
    (es,s0) marks out ==>
  gas_value_prefix H memory (ctx,func,cenv,cx) (ty,e) (sa,sb,op)
    (es with gas_obs := gs,s0) marks out
Proof
  PairCases_on `out` >>
  simp[gas_value_prefix_def, gas_marked_exec_def, expr_post_def,
       locals_kept_def, popped_kept_def, stmt_state_rel_start_gas_obs] >>
  strip_tac >>
  `storage_well_formed_on cx (es with gas_obs := gs) (FST H)` by
    (fs[vyperStorageFootprintTheory.storage_well_formed_on_def] >>
     rpt strip_tac >> res_tac >>
     Cases_on `b` >> fs[vyperStorageBackendTheory.get_storage_def]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
