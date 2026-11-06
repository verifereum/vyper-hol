Theory exprSimAbiDecodeRealizeTarget
Ancestors
  exprSimAbiDecodeRealizeSource exprSimHyps exprSimLeaves
  exprLoweringProps

Theorem abi_decode_realize_child:
  exprs_case T ctx func ce cx [abi_decode_realize_arg]
Proof
  irule exprs_case_every_ok >>
  simp[abi_decode_realize_arg_def, compile_literal_case_sim]
QED

(* The source-only witness used the empty transaction.  The full simulation
   requires a nonzero block number independently of the decoder fragment. *)
Theorem abi_decode_realize_entry_excluded:
  ~stmt_state_rel ctx func ce (abi_decode_realize_cx k) es ss
Proof
  simp[stmt_state_rel_def, compileEnvTheory.state_rel_def,
       compileEnvTheory.call_ctx_rel_def, compileEnvTheory.tx_env_ok_def,
       abi_decode_realize_cx_def,
       vyperContextTheory.empty_evaluation_context_def,
       vyperContextTheory.empty_call_txn_def]
QED
