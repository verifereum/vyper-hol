(*
 * Pattern 1 Transformation Correctness
 *
 * Pattern 1: jnz %cond @revert @else => iszero; assert; jmp @else
 *)

Theory rtaPattern1
Ancestors
  rtaCorrect rtaProps rtaDefs stateEquiv venomSemProps venomSem venomInst venomState list
Libs
  rtaCorrectTheory venomSemPropsTheory

(* ==========================================================================
   Main Theorem: Pattern 1 cond != 0w case
   ========================================================================== *)

Theorem pattern1_nonzero_execution:
  !fn bb s cond_op if_nonzero if_zero cond.
    MEM bb fn.fn_blocks /\ ~s.vs_halted /\
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    (EL s.vs_inst_idx bb.bb_instructions).inst_opcode = JNZ /\
    (EL s.vs_inst_idx bb.bb_instructions).inst_operands =
      [cond_op; Label if_nonzero; Label if_zero] /\
    is_revert_label fn if_nonzero /\
    eval_operand cond_op s = SOME cond /\
    cond <> 0w /\
    transform_jnz fn (EL s.vs_inst_idx bb.bb_instructions) =
      SOME (transform_pattern1 (EL s.vs_inst_idx bb.bb_instructions) cond_op if_zero) /\
    EVERY (\i. transform_jnz fn i = NONE) (TAKE s.vs_inst_idx bb.bb_instructions)
    ==>
    let bb' = transform_block fn bb in
    let id = (EL s.vs_inst_idx bb.bb_instructions).inst_id in
    let fresh_var = fresh_iszero_var id in
    let fresh_vars = fresh_vars_in_block fn bb in
    let s1 = next_inst (update_var fresh_var 0w s) in
    (* Properties *)
    fresh_var IN fresh_vars /\
    step_inst (EL s.vs_inst_idx bb.bb_instructions) s = OK (jump_to if_nonzero s) /\
    run_block fn bb s = OK (jump_to if_nonzero s) /\
    run_block (transform_function fn) bb' s = Revert (revert_state s1) /\
    (jump_to if_nonzero s).vs_current_bb = if_nonzero /\
    execution_equiv_except fresh_vars (revert_state (jump_to if_nonzero s)) (revert_state s1)
Proof
  rw[LET_THM] >| [
    (* fresh_var IN fresh_vars *)
    irule fresh_var_in_fresh_vars >> simp[] >> metis_tac[],
    (* Original JNZ step *)
    simp[step_inst_def],
    (* Original run_block *)
    simp[Once run_block_def, step_in_block_def, get_instruction_def,
         step_inst_def, EVAL ``is_terminator JNZ``, jump_to_def],
    (* Transformed run_block *)
    drule_all run_block_iszero_assert_reverts >> simp[LET_THM],
    (* vs_current_bb *)
    simp[jump_to_def],
    (* execution_equiv_except - need to derive <> NONE from = SOME *)
    `transform_jnz fn (EL s.vs_inst_idx bb.bb_instructions) <> NONE` by simp[] >>
    drule_all revert_states_equiv_except >> simp[LET_THM]
  ]
QED

(* ==========================================================================
   Main Theorem: Pattern 1 cond = 0w case
   ========================================================================== *)

Theorem pattern1_zero_execution:
  !fn bb s cond_op if_nonzero if_zero.
    MEM bb fn.fn_blocks /\ ~s.vs_halted /\
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    (EL s.vs_inst_idx bb.bb_instructions).inst_opcode = JNZ /\
    (EL s.vs_inst_idx bb.bb_instructions).inst_operands =
      [cond_op; Label if_nonzero; Label if_zero] /\
    is_revert_label fn if_nonzero /\
    eval_operand cond_op s = SOME 0w /\
    transform_jnz fn (EL s.vs_inst_idx bb.bb_instructions) =
      SOME (transform_pattern1 (EL s.vs_inst_idx bb.bb_instructions) cond_op if_zero) /\
    EVERY (\i. transform_jnz fn i = NONE) (TAKE s.vs_inst_idx bb.bb_instructions)
    ==>
    let bb' = transform_block fn bb in
    let id = (EL s.vs_inst_idx bb.bb_instructions).inst_id in
    let fresh_var = fresh_iszero_var id in
    let fresh_vars = fresh_vars_in_block fn bb in
    let s1 = update_var fresh_var 1w s in
    let s2 = jump_to if_zero s1 in
    (* Properties *)
    fresh_var IN fresh_vars /\
    step_inst (EL s.vs_inst_idx bb.bb_instructions) s = OK (jump_to if_zero s) /\
    run_block fn bb s = OK (jump_to if_zero s) /\
    run_block (transform_function fn) bb' s = OK s2 /\
    state_equiv_except fresh_vars (jump_to if_zero s) s2
Proof
  rw[LET_THM] >| [
    (* fresh_var IN fresh_vars *)
    irule fresh_var_in_fresh_vars >> simp[] >> metis_tac[],
    (* Original JNZ step *)
    simp[step_inst_def],
    (* Original run_block *)
    simp[Once run_block_def, step_in_block_def, get_instruction_def,
         step_inst_def, EVAL ``is_terminator JNZ``, jump_to_def],
    (* Transformed run_block *)
    drule_all run_block_iszero_assert_jumps >> simp[LET_THM],
    (* state_equiv_except - need to derive <> NONE from = SOME *)
    `transform_jnz fn (EL s.vs_inst_idx bb.bb_instructions) <> NONE` by simp[] >>
    drule_all jumped_states_equiv_except >> simp[LET_THM]
  ]
QED

val _ = export_theory();
