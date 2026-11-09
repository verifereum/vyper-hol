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


Theorem inline_call_return_exit:
  call_inst.inst_opcode = INVOKE /\ decode_invoke call_inst = SOME (name,arg_ops) /\
  lookup_function name ctx.ctx_functions = SOME callee /\
  eval_operands arg_ops caller = SOME vals /\
  setup_callee callee vals caller = SOME cs /\
  run_blocks call_fuel ctx callee cs = IntRet ir s' /\
  (inst.inst_opcode = RET \/ inst.inst_opcode = RETFMP) /\
  inst.inst_operands = ops ++ [pc] /\
  raw_return_user_arity inst = SOME (LENGTH call_inst.inst_outputs) /\
  step_inst source_fuel ctx inst s = IntRet ir s' /\
  EVERY (\op. (!v. op = Var v ==> v IN V /\ v NOTIN opaque) /\
    ~is_label_op op) ops /\
  (!x v. MEM x call_inst.inst_outputs /\ v IN V ==> STRCAT p v <> x) /\
  inline_opaque_frame_rel (STRCAT p) V opaque caller.vs_vars P s t /\
  bb.bb_instructions = pre ++
    FST (rewrite_inline_inst args call_inst.inst_outputs ret
      (clone_instruction p [] inst) param_idx) /\ ~t.vs_halted ==>
  ?u caller'.
    step_inst call_fuel ctx call_inst caller =
      OK (adopt_return_fmp ir (merge_callee_state caller' s')) /\
    exec_block fuel ctx bb (t with vs_inst_idx := LENGTH pre) = OK (jump_to ret u) /\
    inline_opaque_frame_rel (STRCAT p) V opaque caller'.vs_vars P s' u /\
    (!x. x IN P ==> lookup_var x (jump_to ret u) =
      lookup_var x (adopt_return_fmp ir (merge_callee_state caller' s'))) /\
    merge_callee_state caller u = merge_callee_state caller s' /\
    u.vs_fmp = s'.vs_fmp /\
    (adopt_return_fmp ir (merge_callee_state caller' s')).vs_fmp =
      (if inst.inst_opcode = RETFMP then s'.vs_fmp else caller.vs_fmp) /\
    (jump_to ret u).vs_current_bb = ret /\
    (jump_to ret u).vs_inst_idx = 0 /\
    (jump_to ret u).vs_prev_bb = SOME t.vs_current_bb
Proof
  strip_tac >> drule inline_return_exit >>
  disch_then (drule_at (Pat `inline_opaque_frame_rel _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `_ .bb_instructions = _`)) >>
  simp[] >> disch_then (qspec_then `fuel` mp_tac) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  qexistsl [`u`, `caller'`] >> simp[Once run_defs]
QED
