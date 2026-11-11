Theory internalReturnCopyFwdIndexStatic
Ancestors
  internalReturnCopyFwdIndexProbe o1PassContract venomWf
  invokeCopyFwdCommonDefs ptrDiscipline venomInst list

(* The published fixture is excluded by a frozen static premise. *)
Theorem ircf_index_static_not_ssa:
  ~EVERY wf_ssa ircf_index_ctx.ctx_functions
Proof
  EVAL_TAC
QED

Theorem ircf_index_static_no_dalloca:
  ~ctx_has_dalloca ircf_index_ctx
Proof
  EVAL_TAC
QED

Theorem ircf_index_static_fn_unique_defs:
  ssa_form ircf_index_fn
Proof
  EVAL_TAC
QED

Theorem ircf_index_static_fn_not_dominates:
  ~def_dominates_uses ircf_index_fn
Proof
  EVAL_TAC
QED
