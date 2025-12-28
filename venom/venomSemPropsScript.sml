(*
 * Venom Semantic Properties
 *
 * General semantic lemmas useful for any optimization pass.
 * Contains properties of bool_to_word and instruction behavior lemmas.
 *)

Theory venomSemProps
Ancestors
  venomSem venomInst venomState

(* ==========================================================================
   bool_to_word Properties

   WHY THESE ARE TRUE: bool_to_word is defined as:
     bool_to_word T = 1w
     bool_to_word F = 0w
   So bool_to_word b = 0w iff b = F iff ~b.
   ========================================================================== *)

Theorem bool_to_word_T:
  bool_to_word T = 1w
Proof
  simp[bool_to_word_def]
QED

Theorem bool_to_word_F:
  bool_to_word F = 0w
Proof
  simp[bool_to_word_def]
QED

Theorem bool_to_word_eq_0w:
  (bool_to_word b = 0w) <=> ~b
Proof
  Cases_on `b` >> simp[bool_to_word_def]
QED

Theorem bool_to_word_neq_0w:
  (bool_to_word b <> 0w) <=> b
Proof
  Cases_on `b` >> simp[bool_to_word_def]
QED

(* ==========================================================================
   Instruction Behavior Lemmas
   ========================================================================== *)

(* WHY THIS IS TRUE: By step_inst_def, ISZERO uses exec_unop with
   (\x. bool_to_word (x = 0w)). exec_unop evaluates the single operand,
   applies the function, and updates the output variable. *)
Theorem step_iszero_value:
  !s cond_op out id cond.
    eval_operand cond_op s = SOME cond ==>
    step_inst <| inst_id := id; inst_opcode := ISZERO;
                 inst_operands := [cond_op]; inst_outputs := [out] |> s =
    OK (update_var out (bool_to_word (cond = 0w)) s)
Proof
  rw[step_inst_def, exec_unop_def]
QED

(* WHY THIS IS TRUE: By step_inst_def, ASSERT evaluates its operand.
   If cond = 0w, it returns Revert (revert_state s).
   If cond <> 0w, it returns OK s. *)
Theorem step_assert_behavior:
  !s cond_op id cond.
    eval_operand cond_op s = SOME cond ==>
    step_inst <| inst_id := id; inst_opcode := ASSERT;
                 inst_operands := [cond_op]; inst_outputs := [] |> s =
    if cond = 0w then Revert (revert_state s) else OK s
Proof
  rw[step_inst_def]
QED

(* WHY THIS IS TRUE: By step_inst_def, REVERT unconditionally returns
   Revert (revert_state s) regardless of operands. *)
Theorem step_revert_always_reverts:
  !inst s.
    inst.inst_opcode = REVERT ==>
    step_inst inst s = Revert (revert_state s)
Proof
  rw[step_inst_def]
QED

(* WHY THIS IS TRUE: By step_inst_def, JMP unconditionally jumps to the label. *)
Theorem step_jmp_behavior:
  !s lbl id.
    step_inst <| inst_id := id; inst_opcode := JMP;
                 inst_operands := [Label lbl]; inst_outputs := [] |> s =
    OK (jump_to lbl s)
Proof
  rw[step_inst_def]
QED

(* WHY THIS IS TRUE: By step_inst_def, JNZ evaluates the condition.
   If cond <> 0w, it jumps to if_nonzero; else to if_zero. *)
Theorem step_jnz_behavior:
  !s cond_op if_nonzero if_zero id cond.
    eval_operand cond_op s = SOME cond ==>
    step_inst <| inst_id := id; inst_opcode := JNZ;
                 inst_operands := [cond_op; Label if_nonzero; Label if_zero];
                 inst_outputs := [] |> s =
    if cond <> 0w then OK (jump_to if_nonzero s)
    else OK (jump_to if_zero s)
Proof
  rw[step_inst_def]
QED
