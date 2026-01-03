(*
 * Pattern 1 Transformation Correctness
 *
 * Pattern 1: jnz %cond @revert @else => iszero; assert; jmp @else
 *)

Theory rtaPattern1
Ancestors
  rtaProofHelpers rtaPassDefs stateEquiv venomSemProps venomSem venomInst venomState list

(* ==========================================================================
   Block Execution Helpers
   ========================================================================== *)

(* run_block for ISZERO -> ASSERT(0w) -> Revert sequence
   Note: s1 includes next_inst from ISZERO step (vs_inst_idx + 1) *)
Theorem run_block_iszero_assert_reverts:
  !fn bb s cond_op if_zero cond.
    ~s.vs_halted /\
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    eval_operand cond_op s = SOME cond /\
    cond <> 0w /\
    EVERY (\i. transform_jnz fn i = NONE) (TAKE s.vs_inst_idx bb.bb_instructions) /\
    transform_jnz fn (EL s.vs_inst_idx bb.bb_instructions) =
      SOME (transform_pattern1 (EL s.vs_inst_idx bb.bb_instructions) cond_op if_zero)
    ==>
    let bb' = transform_block fn bb in
    let id = (EL s.vs_inst_idx bb.bb_instructions).inst_id in
    let fresh_var = fresh_iszero_var id in
    let s1 = next_inst (update_var fresh_var 0w s) in
    run_block bb' s = Revert (revert_state s1)
Proof
  rw[LET_THM, transform_block_def] >>
  (* Establish length bounds *)
  `s.vs_inst_idx < LENGTH (transform_block_insts fn bb.bb_instructions)` by
    (drule_all transform_block_insts_length_pattern1 >> simp[]) >>
  `s.vs_inst_idx + 1 < LENGTH (transform_block_insts fn bb.bb_instructions)` by
    (drule_all transform_block_insts_length_pattern1 >> simp[]) >>
  (* Get instruction facts from pattern1_transformed_instructions *)
  drule_all rtaProofHelpersTheory.transform_block_insts_EL_transformed >>
  simp[LET_THM, transform_pattern1_def] >> strip_tac >>
  drule_all rtaProofHelpersTheory.pattern1_transformed_instructions >>
  simp[LET_THM] >> strip_tac >>
  (* Step 1: Execute ISZERO *)
  simp[Once run_block_def, step_in_block_def, get_instruction_def] >>
  simp[mk_iszero_inst_def, step_inst_def, exec_unop_def, eval_operand_def] >>
  simp[EVAL ``is_terminator ISZERO``, bool_to_word_F] >>
  simp[next_inst_def, update_var_def] >>
  (* Step 2: Execute ASSERT with 0w *)
  simp[Once run_block_def, step_in_block_def, get_instruction_def] >>
  simp[mk_assert_inst_def, step_inst_def] >>
  simp[eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[revert_state_def]
QED

(* run_block for ISZERO -> ASSERT(1w) -> JMP sequence *)
Theorem run_block_iszero_assert_jumps:
  !fn bb s cond_op if_zero.
    ~s.vs_halted /\
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    eval_operand cond_op s = SOME 0w /\
    EVERY (\i. transform_jnz fn i = NONE) (TAKE s.vs_inst_idx bb.bb_instructions) /\
    transform_jnz fn (EL s.vs_inst_idx bb.bb_instructions) =
      SOME (transform_pattern1 (EL s.vs_inst_idx bb.bb_instructions) cond_op if_zero)
    ==>
    let bb' = transform_block fn bb in
    let id = (EL s.vs_inst_idx bb.bb_instructions).inst_id in
    let fresh_var = fresh_iszero_var id in
    let s1 = update_var fresh_var 1w s in
    run_block bb' s = OK (jump_to if_zero s1)
Proof
  rw[LET_THM, transform_block_def] >>
  (* Establish length bounds *)
  `s.vs_inst_idx < LENGTH (transform_block_insts fn bb.bb_instructions)` by
    (drule_all transform_block_insts_length_pattern1 >> simp[]) >>
  `s.vs_inst_idx + 1 < LENGTH (transform_block_insts fn bb.bb_instructions)` by
    (drule_all transform_block_insts_length_pattern1 >> simp[]) >>
  `s.vs_inst_idx + 2 < LENGTH (transform_block_insts fn bb.bb_instructions)` by
    (drule_all transform_block_insts_length_pattern1 >> simp[]) >>
  (* Get instruction facts from pattern1_transformed_instructions *)
  drule_all rtaProofHelpersTheory.transform_block_insts_EL_transformed >>
  simp[LET_THM, transform_pattern1_def] >> strip_tac >>
  drule_all rtaProofHelpersTheory.pattern1_transformed_instructions >>
  simp[LET_THM] >> strip_tac >>
  (* Step 1: Execute ISZERO - produces bool_to_word T = 1w *)
  simp[Once run_block_def, step_in_block_def, get_instruction_def] >>
  simp[mk_iszero_inst_def, step_inst_def, exec_unop_def, eval_operand_def] >>
  simp[EVAL ``is_terminator ISZERO``, bool_to_word_T] >>
  simp[next_inst_def, update_var_def] >>
  (* Step 2: Execute ASSERT with 1w - passes *)
  simp[Once run_block_def, step_in_block_def, get_instruction_def] >>
  simp[mk_assert_inst_def, step_inst_def] >>
  simp[eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[EVAL ``is_terminator ASSERT``, next_inst_def] >>
  (* Step 3: Execute JMP *)
  simp[Once run_block_def, step_in_block_def, get_instruction_def] >>
  simp[mk_jmp_inst_def, step_inst_def] >>
  simp[EVAL ``is_terminator JMP``, jump_to_def]
QED

(* ==========================================================================
   State Equivalence Helpers
   ========================================================================== *)

(* execution_equiv_except for revert states
   Compares original path (JNZ to revert block) with transformed path (ISZERO+ASSERT reverts)
   The two revert_states differ in vs_inst_idx, vs_current_bb, vs_prev_bb and fresh_var,
   but execution_equiv_except ignores control flow and allows fresh_vars to differ *)
Theorem revert_states_equiv_except:
  !fn bb s n cond_op if_nonzero if_zero.
    n < LENGTH bb.bb_instructions /\
    (EL n bb.bb_instructions).inst_operands = [cond_op; Label if_nonzero; Label if_zero] /\
    is_revert_label fn if_nonzero /\
    transform_jnz fn (EL n bb.bb_instructions) <> NONE
    ==>
    let fresh_var = fresh_iszero_var (EL n bb.bb_instructions).inst_id in
    let fresh_vars = fresh_vars_in_block fn bb in
    execution_equiv_except fresh_vars
      (revert_state (jump_to if_nonzero s))
      (revert_state (next_inst (update_var fresh_var 0w s)))
Proof
  rw[LET_THM] >>
  drule_all rtaProofHelpersTheory.fresh_var_in_fresh_vars >> strip_tac >>
  simp[execution_equiv_except_def, revert_state_def, jump_to_def,
       next_inst_def, update_var_def, lookup_var_def] >>
  rw[] >> simp[finite_mapTheory.FLOOKUP_UPDATE] >> rw[] >> metis_tac[]
QED

(* state_equiv_except for OK states
   The two states differ only in fresh_var (in second state) and maybe vs_inst_idx,
   but jump_to sets vs_inst_idx := 0 for both, so they match except for fresh_var *)
Theorem jumped_states_equiv_except:
  !fn bb s n cond_op if_nonzero if_zero.
    n < LENGTH bb.bb_instructions /\
    (EL n bb.bb_instructions).inst_operands = [cond_op; Label if_nonzero; Label if_zero] /\
    is_revert_label fn if_nonzero /\
    transform_jnz fn (EL n bb.bb_instructions) <> NONE
    ==>
    let fresh_var = fresh_iszero_var (EL n bb.bb_instructions).inst_id in
    let fresh_vars = fresh_vars_in_block fn bb in
    state_equiv_except fresh_vars
      (jump_to if_zero s)
      (jump_to if_zero (update_var fresh_var 1w s))
Proof
  rw[LET_THM] >>
  drule_all rtaProofHelpersTheory.fresh_var_in_fresh_vars >> strip_tac >>
  simp[state_equiv_except_def, execution_equiv_except_def, jump_to_def,
       update_var_def, lookup_var_def] >>
  rw[] >> simp[finite_mapTheory.FLOOKUP_UPDATE] >> rw[] >> metis_tac[]
QED

(* ==========================================================================
   Main Theorems
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
    run_block bb s = OK (jump_to if_nonzero s) /\
    run_block bb' s = Revert (revert_state s1) /\
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
    run_block bb s = OK (jump_to if_zero s) /\
    run_block bb' s = OK s2 /\
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
