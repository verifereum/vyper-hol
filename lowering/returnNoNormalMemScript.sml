(* A counted return whose value-view prefix has no normal post. *)
Theory returnNoNormalMem
Ancestors
  stmtSimForced stmtSimReturn stmtSimDefs exprSimDefs gasOutcome
  vyperInterpreter vyperState fragExec

Theorem return_no_normal_vv_outcome_mem:
  gas_outcome T (cx_tops cx) (ctx,func) (eval_expr cx e) (es,s0)
    (\res ee t. ?raw. res = INL raw /\ P raw ee t)
    (\res ee r. expr_exit res r) /\
  (!raw ee t. ~P raw ee t) ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (eval_stmt cx (Return (SOME e))) (es,s0) Q
    (\res ee r. !tail. stmt_exit RetQ (ee with gas_obs := tail) res r)
Proof
  strip_tac >>
  `eval_stmt cx (Return (SOME e)) =
     bind (eval_expr cx e)
       (\raw. bind (read_result cx raw) (\v. raise (ReturnException v)))` by
    simp[FUN_EQ_THM, eval_return_forced, bind_assoc] >>
  pop_assum SUBST1_TAC >>
  irule forced_vv_then_outcome >> conj_tac
  >- (rpt gen_tac >> Cases_on `r` >> Cases_on `ex` >>
      simp[expr_exit_def, stmt_exit_def] >>
      rename1 `Error err` >> Cases_on `err` >>
      simp[expr_exit_def, stmt_exit_def]) >>
  qexists_tac `P` >> simp[]
QED
