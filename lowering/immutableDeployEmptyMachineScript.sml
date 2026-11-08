(* Machine-entry audit for the shared source fixture. *)
Theory immutableDeployEmptyMachine
Ancestors
  immutableDeployEmptyStacked exprLoweringProps compileEnv vyperContext

Theorem empty_immutable_stacked_tx_env_fails:
  ~tx_env_ok empty_immutable_stacked_cx.txn
Proof
  EVAL_TAC
QED

Theorem empty_immutable_stacked_no_machine_entry:
  !ctx func ss.
    ~stmt_state_rel ctx func empty_immutable_ce empty_immutable_stacked_cx
       empty_immutable_es ss
Proof
  rpt gen_tac >>
  simp[stmt_state_rel_def, state_rel_def, call_ctx_rel_def,
       empty_immutable_stacked_tx_env_fails]
QED
