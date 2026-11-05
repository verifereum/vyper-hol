(* Check the source frame's compatibility with the stronger lowering relation. *)
Theory bodyPtrBopInCompilerFrame
Ancestors
  bodyPtrBopInSourceFrame exprLoweringProps compileEnv vyperContext

Theorem zero_block_source_has_no_lowering_frame:
  ~stmt_state_rel ctx func cenv probe_cx probe_es s
Proof
  simp[stmt_state_rel_def, state_rel_def, call_ctx_rel_def, tx_env_ok_def,
       probe_cx_def, empty_evaluation_context_def, empty_call_txn_def]
QED
