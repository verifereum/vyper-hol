(* A counted return whose value-view prefix has no normal post. *)
Theory returnNoNormalMem
Ancestors
  stmtSimForced stmtSimReturn stmtSimDefs exprSimDefs gasOutcome
  vyperInterpreter vyperState fragExec

Theorem return_no_normal_vv_outcome_mem:
  gas_outcome T (cx_tops cx) (ctx,func) cx st0 (eval_expr cx e) (es,s0)
    (\H res ee t. ?raw. res = INL raw /\ P H raw ee t)
    (\H res ee r. expr_exit res r) /\
  (!H raw ee t. ~P H raw ee t) ==>
  gas_outcome T (cx_tops cx) (ctx,func) cx st0
    (eval_stmt cx (Return (SOME e))) (es,s0) Q
    (\H res ee r. !tail. stmt_exit (RetQ H) (ee with gas_obs := tail) res r)
Proof
  strip_tac >>
  `eval_stmt cx (Return (SOME e)) =
     bind (eval_expr cx e)
       (\raw. bind (read_result cx raw) (\v. raise (ReturnException v)))` by
    simp[FUN_EQ_THM, eval_return_forced, bind_assoc] >>
  pop_assum SUBST1_TAC >>
  irule forced_vv_then_outcome >>
  rpt conj_tac
  >~ [`expr_exit (INR _) _`]
  >- (rpt gen_tac >> Cases_on `r` >> Cases_on `ex` >>
      simp[expr_exit_def, stmt_exit_def] >>
      rename1 `Error err` >> Cases_on `err` >>
      simp[expr_exit_def, stmt_exit_def])
  >~ [`storage_trace_frame _`]
  >- (gen_tac >> BETA_TAC >>
      irule vyperStorageTraceTheory.storage_trace_frame_bind >>
      simp[vyperStorageTraceTheory.storage_trace_frame_read_result,
           vyperStorageTraceTheory.storage_trace_frame_raise]) >>
  qexists_tac `P` >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >> metis_tac[]
QED
