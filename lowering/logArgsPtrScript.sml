(* Conditional readiness mirrors evaluate_ind: the tail is required only
   when the head evaluation and its read can succeed. This packaging keeps
   that interface available to the argument-list induction. *)
Theory logArgsPtr
Ancestors
  bodyPtrDefs stmtSimLog stmtSimLogArgs stmtSimLogArgsRun logValueFramePtr
  vyperInterpreter vyperState list
Libs
  monadsyntax

Definition log_args_ready_ptr_def:
  log_args_ready_ptr d ctx PG func cenv cx Inv [] = T /\
  log_args_ready_ptr d ctx PG func cenv cx Inv (e::args) =
    ((!es. Inv es ==>
       expr_sim_ptr d ctx PG func cenv cx (expr_type e) e es /\
       !v es'. (do r <- eval_expr cx e; read_result cx r od) es =
                 (INL v, es') ==>
               Inv es' /\
               ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                    value_has_type tv v) /\
     ((?s tv t s1 v t1. eval_expr cx e s = (INL tv, t) /\
                        read_result cx tv s1 = (INL v, t1)) ==>
      log_args_ready_ptr d ctx PG func cenv cx Inv args))
End

Theorem log_args_ready_ptr_nil:
  log_args_ready_ptr d ctx PG func cenv cx Inv []
Proof
  simp[log_args_ready_ptr_def]
QED

Theorem log_args_ready_ptr_cons:
  log_args_ready_ptr d ctx PG func cenv cx Inv (e::args) /\ Inv es ==>
  expr_sim_ptr d ctx PG func cenv cx (expr_type e) e es
Proof
  simp[log_args_ready_ptr_def] >> metis_tac[]
QED

Theorem log_args_ready_ptr_tail:
  log_args_ready_ptr d ctx PG func cenv cx Inv (e::args) /\ Inv es /\
  bind (eval_expr cx e) (read_result cx) es = (INL v, es') ==>
  Inv es' /\ log_args_ready_ptr d ctx PG func cenv cx Inv args /\
  ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\ value_has_type tv v
Proof
  simp[log_args_ready_ptr_def] >> rpt strip_tac >>
  `?raw mid. eval_expr cx e es = (INL raw, mid) /\
             read_result cx raw mid = (INL v, es')` by
    (gvs[bind_def, AllCaseEqs()] >> metis_tac[]) >>
  metis_tac[]
QED
