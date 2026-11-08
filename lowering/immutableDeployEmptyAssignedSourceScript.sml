(* Source execution and counted admissibility for the code-compatible fixture. *)
Theory immutableDeployEmptyAssignedSource
Ancestors
  immutableDeployEmptyAssignedCode immutableDeployEmptyValid stmtSimDefs
  vyperInterpreter gasContext

Definition assigned_immutable_cx_def:
  assigned_immutable_cx = empty_immutable_valid_cx with
    sources := [(0w,[(NONE,assigned_immutable_tops)])]
End

Theorem assigned_immutable_eval_stmt:
  !gs. eval_stmt assigned_immutable_cx assigned_immutable_stmt
         (empty_immutable_es with gas_obs := gs) =
       (INL (), empty_immutable_es with gas_obs := gs)
Proof
  gen_tac >> EVAL_TAC >> simp[finite_mapTheory.FLOOKUP_EXT, FUN_EQ_THM,
    finite_mapTheory.FLOOKUP_UPDATE] >>
  gen_tac >> Cases_on `x = "dst"` >> gvs[]
QED

Theorem assigned_immutable_neighbor_lookup:
  !gs. FLOOKUP
    (case ALOOKUP (empty_immutable_es with gas_obs := gs).immutables
                  assigned_immutable_cx.txn.target of
       NONE => FEMPTY
     | SOME imms => get_source_immutables NONE imms) "neighbor" =
    SOME (BaseTV (UintT 256),IntV 1)
Proof
  gen_tac >> EVAL_TAC
QED

Theorem assigned_immutable_gas_admissible:
  !lctx. gas_admissible
    (eval_stmt assigned_immutable_cx assigned_immutable_stmt)
    (stmt_res_ok lctx) empty_immutable_es
Proof
  simp[gas_admissible_def, assigned_immutable_eval_stmt, stmt_res_ok_def]
QED
