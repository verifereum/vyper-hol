Theory bodyPtrBopInArgsInvariant
Ancestors bodyPtrBopInArgsSim typedWordArgsReadyPtr typedWordArgsPostPtr
  exprSimDefs exprSimWordArgs exprSimPrecompiles bodyPtrDefs gasSummaryComposePtr
  compileEnv list vyperState

(* Specializing the semantic invariant here keeps its gas-observation closure
   out of forward matching at the expression integration boundary. *)
Theorem membership_lower_typed_args_sim_inv:
  !args d ctx PG fn cenv cx arg_ty env es sa xs sb s0 G0 tn0.
    (!e es0. MEM e args /\ expr_sim_inv cenv cx env es0 ==>
      is_word_type (expr_type e) /\
      IS_SOME (evaluate_type (get_tenv cx) (expr_type e)) /\
      (!rr ee. (do r <- eval_expr cx e; read_result cx r od) es0 = (rr,ee) ==>
        expr_res_ok rr) /\
      (!v ee. (do r <- eval_expr cx e; read_result cx r od) es0 = (INL v,ee) ==>
        expr_sim_inv cenv cx env ee)) /\
    ptr_args_ready d ctx PG fn cenv cx arg_ty (expr_sim_inv cenv cx env) args /\
    expr_sim_inv cenv cx env es /\ wb_args_shape cenv arg_ty args /\
    lower_word_args cenv arg_ty args sa = (xs,sb) /\
    fn_has_code sa sb fn /\ fn_inst_ids_distinct fn /\
    local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    stmt_state_rel ctx fn cenv cx es s0 /\
    ghost_inv d cenv cx es G0 tn0 s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,fn) PG
      (eval_exprs cx args) (es,s0,G0,tn0)
      (\rr ee G tn t. ?vs. rr = INL vs /\
        typed_args_post_ptr d ctx fn cenv cx es sa s0 G0 tn0 ee args xs vs G tn t /\
        EVERY (\op. op_prov G op = NONE) xs /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\rr ee ghosts r. wb_args_exit rr r)
Proof
  rpt strip_tac >> irule membership_lower_typed_args >> simp[] >>
  qexistsl_tac [`expr_sim_inv cenv cx env`,`arg_ty`] >> simp[] >>
  first_assum MATCH_ACCEPT_TAC
QED
