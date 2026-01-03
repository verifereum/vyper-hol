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

(* ==========================================================================
   step_in_block / run_block Properties
   ========================================================================== *)

(*
 * WHY THIS IS TRUE: step_in_block doesn't use fn in its computation.
 * It only uses bb and s to get/execute the current instruction.
 *)
Theorem step_in_block_fn_irrelevant:
  !fn1 fn2 bb s. step_in_block fn1 bb s = step_in_block fn2 bb s
Proof
  simp[step_in_block_def]
QED

(*
 * WHY THIS IS TRUE: run_block is defined recursively using step_in_block.
 * Since step_in_block doesn't depend on fn, run_block doesn't either.
 * The fn parameter is just passed through to recursive calls.
 *)
Theorem run_block_fn_irrelevant:
  !fn bb s. run_block fn bb s = run_block ARB bb s
Proof
  ho_match_mp_tac run_block_ind >> rw[] >>
  simp[Once run_block_def, step_in_block_fn_irrelevant, SimpLHS] >>
  simp[Once run_block_def, step_in_block_fn_irrelevant, SimpRHS] >>
  Cases_on `step_in_block fn bb s` >>
  `step_in_block ARB bb s = step_in_block fn bb s` by simp[step_in_block_fn_irrelevant] >>
  gvs[] >> Cases_on `q` >> simp[]
QED

(* Helper: step_in_block with is_term=F increments vs_inst_idx *)
Theorem step_in_block_increments_idx:
  !fn bb s v.
    step_in_block fn bb s = (OK v, F)
    ==>
    v.vs_inst_idx = SUC s.vs_inst_idx
Proof
  rw[step_in_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> gvs[] >>
  Cases_on `step_inst x s` >> gvs[] >>
  Cases_on `is_terminator x.inst_opcode` >> gvs[next_inst_def] >>
  `v'.vs_inst_idx = s.vs_inst_idx` by (
    drule_all step_inst_preserves_inst_idx >> simp[]
  ) >>
  simp[]
QED

(*
 * Helper: run_block returning OK implies state is not halted.
 *
 * WHY THIS IS TRUE: If vs_halted becomes true during execution,
 * run_block returns Halt, not OK. The OK result only occurs when
 * a jump instruction executes (JMP or JNZ branch taken).
 *)
Theorem run_block_OK_not_halted:
  !fn bb s v. run_block fn bb s = OK v ==> ~v.vs_halted
Proof
  ho_match_mp_tac run_block_ind >> rw[] >>
  qpat_x_assum `run_block _ _ _ = _` mp_tac >>
  simp[Once run_block_def] >>
  Cases_on `step_in_block fn bb s` >> gvs[] >>
  Cases_on `q` >> gvs[] >>
  Cases_on `v'.vs_halted` >> gvs[] >>
  Cases_on `r` >> gvs[] >> rw[] >> gvs[]
QED

(*
 * Helper: run_block returning OK implies vs_inst_idx = 0.
 *
 * WHY THIS IS TRUE: When run_block returns OK, it means a jump instruction
 * executed (JMP, JNZ, or DJMP). All jumps use jump_to which sets vs_inst_idx := 0.
 *)
Theorem run_block_OK_inst_idx_0:
  !fn bb s v. run_block fn bb s = OK v ==> v.vs_inst_idx = 0
Proof
  ho_match_mp_tac run_block_ind >> rw[] >>
  qpat_x_assum `run_block _ _ _ = _` mp_tac >>
  simp[Once run_block_def] >>
  Cases_on `step_in_block fn bb s` >> gvs[] >>
  Cases_on `q` >> gvs[] >>
  Cases_on `v'.vs_halted` >> gvs[] >>
  Cases_on `r` >> gvs[] >> rw[] >> gvs[] >>
  qpat_x_assum `step_in_block _ _ _ = _` mp_tac >>
  simp[step_in_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> gvs[] >>
  Cases_on `step_inst x s` >> gvs[] >>
  Cases_on `is_terminator x.inst_opcode` >> gvs[] >> rw[] >> gvs[] >>
  qpat_x_assum `is_terminator _` mp_tac >> simp[is_terminator_def] >>
  Cases_on `x.inst_opcode` >> gvs[is_terminator_def] >>
  qpat_x_assum `step_inst _ _ = _` mp_tac >>
  simp[step_inst_def, jump_to_def] >>
  gvs[AllCaseEqs(), PULL_EXISTS] >> rw[] >> gvs[]
QED
