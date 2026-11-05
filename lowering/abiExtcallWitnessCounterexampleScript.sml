(* Logical closure of the concrete source/target mismatch. *)
Theory abiExtcallWitnessCounterexample
Ancestors
  abiExtcallWitnessSource abiExtcallWitnessTarget abiExtcallWitnessOperands
  abiExtcallWitnessInvariant abiExtcallErrorPostProbe abiExtcallWitnessProbe
  gasOutcome gasSummary gasExemptCert fragGasMode e2eDefs exprSimHypsDefs exprSimDefs vyperState abiExtcallWitnessEntry

Theorem witness_not_exempt:
  ~unspecified_behaviour_exempt (cx_tops witness_cx)
    (RuntimeError "abi_decode invalid")
Proof
  EVAL_TAC >> simp[]
QED

Theorem witness_no_summary:
  (!res ee t. Q res ee t ==> ?v. res = INL v) ==>
  ~gas_summary_at F (witness_ctx,witness_func) marks
    (eval_expr witness_cx witness_expr) (witness_es,witness_s0) Q
    (\res ee r. expr_exit res r)
Proof
  strip_tac >> rewrite_tac[gas_summary_at_def, gas_marked_exec_def] >>
  strip_tac >>
  first_x_assum (qspec_then `[]` mp_tac) >>
  simp[witness_source_run] >> strip_tac >> gvs[]
  >- (first_x_assum drule >> simp[]) >>
  Cases_on `r` >> gvs[expr_exit_def, gas_marked_path_def] >>
  metis_tac[witness_target_no_abort_path]
QED

Theorem witness_no_exempt_cert:
  ~gas_exempt_cert F (cx_tops witness_cx) (witness_ctx,witness_func)
    (ignore_bind (eval_expr witness_cx witness_expr) (return ()))
    (witness_es,witness_s0) marks (err,ee) (leaf,endpoint)
Proof
  strip_tac >> drule gas_exempt_cert_execution >> strip_tac >>
  first_x_assum (qspec_then `[]` mp_tac) >>
  simp[ignore_bind_def, bind_def, witness_source_run] >> strip_tac >>
  gvs[witness_not_exempt]
QED

Theorem witness_no_outcome:
  (!res ee t. Q res ee t ==> ?v. res = INL v) ==>
  ~gas_outcome F (cx_tops witness_cx) (witness_ctx,witness_func)
    (eval_expr witness_cx witness_expr) (witness_es,witness_s0) Q
    (\res ee r. expr_exit res r)
Proof
  strip_tac >> simp[gas_outcome_def, witness_no_exempt_cert] >>
  metis_tac[witness_no_summary]
QED

Theorem witness_not_vv_sim:
  ~expr_vv_sim witness_ctx witness_func witness_cenv witness_cx
    reach_return witness_expr witness_es
Proof
  rewrite_tac[expr_vv_sim_def] >> strip_tac >>
  first_x_assum (qspecl_then
    [`wrap_probe_start`, `witness_sb`, `witness_vv`, `witness_s0`] mp_tac) >>
  simp[witness_sb_def, witness_vv_def, witness_compile,
       witness_code, witness_ids, witness_reserved, witness_source_admissible,
       witness_stmt_relation, witness_entry_cursor] >>
  strip_tac >>
  pop_assum mp_tac >> rewrite_tac[GSYM IMP_F] >>
  irule witness_no_outcome >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem witness_not_vv_case:
  ~expr_vv_case T witness_ctx witness_func witness_cenv witness_cx witness_expr
Proof
  rewrite_tac[expr_vv_case_def] >> strip_tac >>
  first_x_assum (qspecl_then [`witness_env`, `reach_return`, `witness_es`] mp_tac) >>
  simp[witness_body_pre, witness_no_internal_calls, witness_not_vv_sim]
QED

(* Exact original operand antecedent and negation of the original conclusion,
   at ann=reach_return, static=T, skip=T, no positional arguments, and explicit gas. *)
Theorem compile_extcall_case_counterexample:
  exprs_case T witness_ctx witness_func witness_cenv witness_cx
    (TAKE 1 [witness_target; witness_gas]) /\
  (!s target t.
    eval_exprs witness_cx (TAKE 1 [witness_target; witness_gas]) s = (INL target,t) ==>
    results_case T witness_ctx witness_func witness_cenv witness_cx
      (TAKE (LENGTH (FST (SND ("probe",[],reach_return))))
        (DROP 1 [witness_target;witness_gas]))) /\
  (!s target t s' results t'.
    eval_exprs witness_cx (TAKE 1 [witness_target;witness_gas]) s = (INL target,t) /\
    eval_expr_results witness_cx
      (TAKE (LENGTH (FST (SND ("probe",[],reach_return))))
        (DROP 1 [witness_target;witness_gas])) s' = (INL results,t') ==>
    exprs_case T witness_ctx witness_func witness_cenv witness_cx
      (DROP (1 + LENGTH (FST (SND ("probe",[],reach_return))))
        [witness_target;witness_gas])) /\
  ~(expr_sim_case T witness_ctx witness_func witness_cenv witness_cx
      (Call reach_return (ExtCall T T ("probe",[],reach_return) [EKGas])
        [witness_target;witness_gas] NONE) /\
    expr_vv_case T witness_ctx witness_func witness_cenv witness_cx
      (Call reach_return (ExtCall T T ("probe",[],reach_return) [EKGas])
        [witness_target;witness_gas] NONE))
Proof
  mp_tac (Q.INST [`ctx` |-> `witness_ctx`, `func` |-> `witness_func`]
    witness_case_antecedent) >>
  mp_tac witness_not_vv_case >> rewrite_tac[witness_expr_def] >>
  metis_tac[]
QED

(* Display inherited oracle dependencies for the falsehood audit. *)
val _ = Globals.show_tags := true;
val _ = print_thm witness_not_vv_case;
val _ = print_thm compile_extcall_case_counterexample;
