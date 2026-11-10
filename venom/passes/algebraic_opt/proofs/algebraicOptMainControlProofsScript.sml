Theory algebraicOptMainControlProofs
Ancestors
  algebraicOptMainScalarProofs algebraicOptCmpChunkProofs
  algebraicOptRelationProofs algebraicOptShapeProofs
  algebraicOptDefs venomExecSemantics venomState

Theorem ao_transform_no_outputs:
  inst.inst_outputs = [] ==>
  ao_transform_inst dfg ra lbl idx targets fr inst =
    [ao_resolve_iszero_inst targets inst]
Proof
  simp[ao_transform_inst_def, ao_resolve_iszero_inst_fields]
QED

Theorem ao_resolved_control_base:
  (inst.inst_opcode = JNZ \/ inst.inst_opcode = ASSERT \/
   inst.inst_opcode = ASSERT_UNREACHABLE) /\
  inst.inst_operands =
    (if inst.inst_opcode = JNZ then [a; Label yes; Label no] else [a]) /\
  eval_operand (ao_resolve_iszero_op targets inst.inst_opcode a) r = SOME z /\
  (z = 0w <=> (w:bytes32) = 0w) ==>
  step_inst_base (ao_resolve_iszero_inst targets inst) r =
    if inst.inst_opcode = JNZ then
      OK (jump_to (if w = 0w then no else yes) r)
    else if w <> 0w then OK r
    else if inst.inst_opcode = ASSERT then
      Abort Revert_abort (revert_state (set_returndata [] r))
    else Abort ExHalt_abort (halt_state (set_returndata [] r))
Proof
  strip_tac >>
  gvs[ao_resolve_iszero_inst_def, step_inst_base_opcode_eqs,
      ao_resolve_iszero_op_def] >>
  Cases_on `w = 0w` >> gvs[]
QED

Theorem ao_main_control_transform_base:
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\ trace <> [] /\
  ao_source_trace ctx fn trace /\ LAST trace = (h,F,s) /\
  (!i x. MEM i (fn_insts fn) /\ MEM x i.inst_outputs ==>
    lookup_var x (SND (SND (HD trace))) = NONE) /\
  MEM inst (fn_insts fn) /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  (inst.inst_opcode = JNZ \/ inst.inst_opcode = ASSERT \/
   inst.inst_opcode = ASSERT_UNREACHABLE) /\
  inst.inst_outputs = [] /\
  inst.inst_operands =
    (if inst.inst_opcode = JNZ then [a; Label yes; Label no] else [a]) /\
  eval_operand a s = SOME w /\
  ao_main_observations fn V s r /\ s.vs_labels = r.vs_labels /\
  (!i x. MEM i (fn_insts fn) /\
     (MEM (Var x) i.inst_operands \/ MEM x i.inst_outputs) ==> x IN V) ==>
  !i. MEM i (ao_transform_inst dfg ra lbl idx
                (ao_compute_fn_iszero_targets fn) fr inst) ==>
  step_inst_base i r =
    if inst.inst_opcode = JNZ then
      OK (jump_to (if w = 0w then no else yes) r)
    else if w <> 0w then OK r
    else if inst.inst_opcode = ASSERT then
      Abort Revert_abort (revert_state (set_returndata [] r))
    else Abort ExHalt_abort (halt_state (set_returndata [] r))
Proof
  strip_tac >>
  `inst.inst_opcode <> PHI /\ is_truthy_inst inst.inst_opcode /\
   MEM a inst.inst_operands` by
    (gvs[is_truthy_inst_def] >> simp[]) >>
  drule_all ao_source_resolved_operand_truth >> strip_tac >>
  drule_at (Pos (el 3)) ao_resolved_control_base >>
  disch_then (qspecl_then [`yes`, `w`, `no`] mp_tac) >>
  simp[ao_transform_no_outputs]
QED

(* Only nonterminating assertions use the chunk runner. JNZ is transferred
   by ao_main_control_transform_base: its index is reset, not advanced. *)
Theorem ao_main_assert_transform_chunk:
  (inst.inst_opcode = ASSERT \/ inst.inst_opcode = ASSERT_UNREACHABLE) /\
  inst.inst_outputs = [] /\
  (!i. MEM i (ao_transform_inst dfg ra lbl idx targets fr inst) ==>
    step_inst_base i r =
      if (w:bytes32) <> 0w then OK r
      else if inst.inst_opcode = ASSERT then
        Abort Revert_abort (revert_state (set_returndata [] r))
      else Abort ExHalt_abort (halt_state (set_returndata [] r))) ==>
  ao_cmp_exec_chunk fuel ctx (ao_transform_inst dfg ra lbl idx targets fr inst) r =
    if w <> 0w then OK (next_inst r)
    else if inst.inst_opcode = ASSERT then
      Abort Revert_abort (revert_state (set_returndata [] r))
    else Abort ExHalt_abort (halt_state (set_returndata [] r))
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE` by gvs[] >>
  gvs[ao_transform_no_outputs, ao_cmp_exec_chunk_single,
      step_inst_non_invoke, ao_resolve_iszero_inst_fields] >>
  Cases_on `w = 0w` >> gvs[next_inst_def, arithmeticTheory.ADD1]
QED

Theorem ao_main_control_observations:
  ao_main_observations fn V s r ==>
  ao_main_observations fn V (jump_to l s) (jump_to l r) /\
  ao_main_observations fn V (next_inst s) (next_inst r) /\
  ao_main_observations fn V
    (revert_state (set_returndata [] s)) (revert_state (set_returndata [] r)) /\
  ao_main_observations fn V
    (halt_state (set_returndata [] s)) (halt_state (set_returndata [] r))
Proof
  simp[ao_main_observations_def, lookup_var_def, jump_to_def,
       next_inst_def, revert_state_def, halt_state_def, set_returndata_def]
QED

Theorem ao_main_control_frames:
  (s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) = r ==>
  ((jump_to l s) with vs_vars := (jump_to l r).vs_vars) = jump_to l r /\
  ((next_inst s) with <|vs_vars := (next_inst r).vs_vars;
                       vs_inst_idx := (next_inst r).vs_inst_idx|>) = next_inst r /\
  ((revert_state (set_returndata [] s)) with
    <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) =
    revert_state (set_returndata [] r) /\
  ((halt_state (set_returndata [] s)) with
    <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|>) =
    halt_state (set_returndata [] r) /\
  (jump_to l r).vs_inst_idx = 0 /\
  (next_inst r).vs_inst_idx = r.vs_inst_idx + 1
Proof
  simp[venom_state_component_equality, jump_to_def, next_inst_def,
       revert_state_def, halt_state_def, set_returndata_def]
QED
