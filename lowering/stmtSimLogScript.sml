(* Readiness predicate for pure Log argument evaluation. *)
Theory stmtSimLog
Ancestors
  list rich_list finite_map pred_set
  fragExec   stmtLowering exprLowering compileEnv
  supportedTypes vyperEvent vyperInterpreter vyperState vyperValue
  exprSimDefs
Libs
  monadsyntax

(* The arguments of a log statement, evaluated and read in order: each
   simulates at its own type from every state Inv holds in, and a value it
   reads has that type and leaves Inv holding; a later argument only if
   the ones before it can evaluate, as evaluate_ind gives them. *)
Definition log_args_ready_def:
  log_args_ready ctx func cenv cx Inv [] = T /\
  log_args_ready ctx func cenv cx Inv (e::args) =
    ((!es. Inv es ==>
       expr_sim ctx func cenv cx (expr_type e) e es /\
       !v es'. (do r <- eval_expr cx e; read_result cx r od) es =
                 (INL v, es') ==>
               Inv es' /\
               ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                    value_has_type tv v) /\
     ((?s tv t s1 v t1. eval_expr cx e s = (INL tv, t) /\
                        read_result cx tv s1 = (INL v, t1)) ==>
      log_args_ready ctx func cenv cx Inv args))
End
