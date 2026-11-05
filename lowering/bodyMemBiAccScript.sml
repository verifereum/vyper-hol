(* Memory case of the body induction, one family of bodyMemBuiltinRest's
   builtins: account members such as x.balance (S1: exprSimBuiltins'
   compile_acc_case; a bare x.code is rejected by the allocation check, as
   exprSimAccCode on s1-builtins-aggregates shows). *)
Theory bodyMemBiAcc
Ancestors
  bodyMemoryPreds bodyMemBiAccCompose exprSimSource exprSimHypsDefs vyperContext

Theorem body_builtin_acc_mem:
  !cx ty item es.
    (builtin_args_length_ok (Acc item) (LENGTH es) ==> body_exprs_mem_ok cx es) ==>
    body_expr_mem_ok cx (Builtin ty (Acc item) es)
Proof
  rpt gen_tac >> strip_tac >>
  simp[body_expr_mem_ok_def] >> rpt gen_tac >> strip_tac >>
  drule body_acc_mem_admissible >> strip_tac >> gvs[] >>
  `body_expr_mem_ok cx e` by
    (qpat_x_assum `_ ==> body_exprs_mem_ok _ _` mp_tac >>
     simp[builtin_args_length_ok_def, body_exprs_mem_ok_def]) >>
  `expr_body_pre cenv cx env e es'` by
    (drule expr_body_pre_builtin_arg >> disch_then irule >>
     gvs[expr_body_pre_def]) >>
  `expr_sim_mem ctx func cenv cx (BaseT AddressT) e es'` by
    metis_tac[body_expr_mem_ok_def] >>
  metis_tac[compile_acc_sim_mem, compile_acc_vv_sim_mem]
QED
