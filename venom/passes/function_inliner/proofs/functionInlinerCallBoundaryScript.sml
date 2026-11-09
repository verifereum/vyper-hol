(* Nonrecursive entry/exit interfaces for the recursive inliner simulation. *)
Theory functionInlinerCallBoundary
Ancestors
  functionInlinerOperational functionInlinerReturnTransport callLayoutDefs
  venomExecProofs venomExecSemantics functionInlinerFrame functionInlinerDefs words list

Theorem inline_call_entry:
  eval_operands ops caller = SOME vals /\
  setup_callee fn vals caller = SOME cs /\ ~caller.vs_halted ==>
  inline_opaque_frame_rel ren {} opaque caller.vs_vars P cs caller /\
  cs.vs_params = vals /\ cs.vs_call_entry_fmp = caller.vs_fmp /\
  cs.vs_fmp = caller.vs_fmp /\
  (!k. k < LENGTH ops ==>
    k < LENGTH cs.vs_params /\
    k < LENGTH (rotate_invoke_ops (Label name::ops)) /\
    eval_operand (EL k (rotate_invoke_ops (Label name::ops))) caller =
      SOME (EL k cs.vs_params)) /\
  LENGTH ops < LENGTH (rotate_invoke_ops (Label name::ops)) /\
  EL (LENGTH ops) (rotate_invoke_ops (Label name::ops)) = Lit 0w
Proof
  strip_tac >>
  drule setup_callee_frame >> strip_tac >>
  `LENGTH vals = LENGTH ops` by metis_tac[eval_operands_length] >>
  simp[inline_opaque_frame_setup_empty, rotate_invoke_ops_def, EL_APPEND_EQN] >>
  conj_tac >- (irule inline_opaque_frame_setup_empty >> metis_tac[]) >>
  metis_tac[eval_operands_index]
QED

(* Physical parameter indices are checked statically; they need not be
   recovered by unfolding the canonical-prefix predicate in execution proofs. *)
Theorem inline_call_parameter_index:
  param_inst_at k inst /\ k < dimword (:256) ==>
  is_param_opcode inst.inst_opcode /\
  inst.inst_operands = [Lit (n2w k)] /\
  w2n ((n2w k):256 word) = k /\ LENGTH inst.inst_outputs = 1
Proof
  simp[param_inst_at_def]
QED

Theorem inline_call_entry_operand_available:
  eval_operands ops caller = SOME vals /\
  k < LENGTH (rotate_invoke_ops (Label name::ops)) ==>
  ?w. eval_operand (EL k (rotate_invoke_ops (Label name::ops))) caller = SOME w
Proof
  strip_tac >>
  Cases_on `k < LENGTH ops`
  >- (drule eval_operands_index >> disch_then (qspec_then `k` mp_tac) >>
      simp[rotate_invoke_ops_def, EL_APPEND_EQN]) >>
  `k = LENGTH ops` by gvs[rotate_invoke_ops_def] >>
  simp[rotate_invoke_ops_def, EL_APPEND_EQN, venomStateTheory.eval_operand_def]
QED

