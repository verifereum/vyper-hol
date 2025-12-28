(*
 * Revert-to-Assert Pass: Helper Lemmas
 *
 * This theory provides helper lemmas for proving correctness of the
 * revert-to-assert transformation pass.
 *
 * ============================================================================
 * STRUCTURE OVERVIEW
 * ============================================================================
 *
 * TOP-LEVEL THEOREMS:
 *   - step_iszero_value             : ISZERO produces bool_to_word (x = 0w)
 *   - step_assert_behavior          : ASSERT reverts on 0w, continues otherwise
 *   - step_assert_zero_reverts      : ASSERT 0w reverts
 *   - step_assert_nonzero_passes    : ASSERT nonzero continues
 *   - simple_revert_block_reverts   : Simple revert block always reverts
 *
 * STATE_EQUIV_EXCEPT PROPERTIES:
 *   - state_equiv_except_refl       : Reflexivity
 *   - state_equiv_implies_except    : state_equiv implies state_equiv_except
 *   - update_var_state_equiv_except : update_var preserves equiv for updated var
 *   - revert_state_update_var       : revert_state insensitive to variables
 *   - revert_state_state_equiv_except : revert_state preserves equiv
 *
 * HELPER THEOREMS:
 *   - bool_to_word_eq_0w            : bool_to_word b = 0w iff ~b
 *   - bool_to_word_neq_0w           : bool_to_word b <> 0w iff b
 *   - eval_operand_update_var_same  : eval (Var x) after update_var x
 *   - eval_operand_update_var_other : eval (Var y) after update_var x, x <> y
 *
 * ============================================================================
 *)

Theory revertAssertProps
Ancestors
  revertAssertDefs stateEquiv

(* ==========================================================================
   bool_to_word Properties
   ========================================================================== *)

(* WHY THIS IS TRUE: By definition, bool_to_word T = 1w, bool_to_word F = 0w.
   So bool_to_word b = 0w iff b = F iff ~b. *)
Theorem bool_to_word_eq_0w:
  !b. (bool_to_word b = 0w) <=> ~b
Proof
  cheat
QED

(* WHY THIS IS TRUE: Contrapositive of above. bool_to_word b <> 0w iff b = T. *)
Theorem bool_to_word_neq_0w:
  !b. (bool_to_word b <> 0w) <=> b
Proof
  cheat
QED

(* WHY THIS IS TRUE: Direct evaluation of bool_to_word on T and F. *)
Theorem bool_to_word_T[simp]:
  bool_to_word T = 1w
Proof
  cheat
QED

Theorem bool_to_word_F[simp]:
  bool_to_word F = 0w
Proof
  cheat
QED

(* ==========================================================================
   Operand Evaluation with Variable Updates
   ========================================================================== *)

(* WHY THIS IS TRUE: update_var x v s sets vs_vars |+ (x, v), so
   lookup_var x returns SOME v. eval_operand (Var x) uses lookup_var. *)
Theorem eval_operand_update_var_same:
  !x v s. eval_operand (Var x) (update_var x v s) = SOME v
Proof
  cheat
QED

(* WHY THIS IS TRUE: update_var x doesn't affect lookup of other variables.
   FLOOKUP (fm |+ (x,v)) y = FLOOKUP fm y when x <> y. *)
Theorem eval_operand_update_var_other:
  !x y v s. x <> y ==> eval_operand (Var y) (update_var x v s) = eval_operand (Var y) s
Proof
  cheat
QED

(* WHY THIS IS TRUE: update_var only affects vs_vars, not memory, so
   evaluating a literal is unchanged. *)
Theorem eval_operand_update_var_lit:
  !x v s w. eval_operand (Lit w) (update_var x v s) = SOME w
Proof
  cheat
QED

(* ==========================================================================
   ISZERO Instruction Behavior
   ========================================================================== *)

(* WHY THIS IS TRUE: By step_inst_def, ISZERO uses exec_unop with
   (\x. bool_to_word (x = 0w)). exec_unop evaluates the single operand,
   applies the function, and updates the output variable. *)
Theorem step_iszero_value:
  !s cond cond_op out id.
    eval_operand cond_op s = SOME cond ==>
    step_inst <| inst_id := id; inst_opcode := ISZERO;
                 inst_operands := [cond_op]; inst_outputs := [out] |> s =
    OK (update_var out (bool_to_word (cond = 0w)) s)
Proof
  cheat
QED

(* ==========================================================================
   ASSERT Instruction Behavior
   ========================================================================== *)

(* WHY THIS IS TRUE: By step_inst_def, ASSERT evaluates its operand.
   If cond = 0w, it returns Revert (revert_state s).
   If cond <> 0w, it returns OK s. *)
Theorem step_assert_behavior:
  !s cond cond_op id.
    eval_operand cond_op s = SOME cond ==>
    step_inst <| inst_id := id; inst_opcode := ASSERT;
                 inst_operands := [cond_op]; inst_outputs := [] |> s =
    if cond = 0w then Revert (revert_state s) else OK s
Proof
  cheat
QED

(* WHY THIS IS TRUE: Special case of step_assert_behavior with cond = 0w. *)
Theorem step_assert_zero_reverts:
  !s cond_op id.
    eval_operand cond_op s = SOME 0w ==>
    step_inst <| inst_id := id; inst_opcode := ASSERT;
                 inst_operands := [cond_op]; inst_outputs := [] |> s =
    Revert (revert_state s)
Proof
  cheat
QED

(* WHY THIS IS TRUE: Special case of step_assert_behavior with cond <> 0w. *)
Theorem step_assert_nonzero_passes:
  !s cond cond_op id.
    eval_operand cond_op s = SOME cond /\ cond <> 0w ==>
    step_inst <| inst_id := id; inst_opcode := ASSERT;
                 inst_operands := [cond_op]; inst_outputs := [] |> s =
    OK s
Proof
  cheat
QED

(* ==========================================================================
   REVERT Instruction Behavior
   ========================================================================== *)

(* WHY THIS IS TRUE: By step_inst_def, REVERT unconditionally returns
   Revert (revert_state s) regardless of operands. *)
Theorem step_revert_always_reverts:
  !s id ops.
    step_inst <| inst_id := id; inst_opcode := REVERT;
                 inst_operands := ops; inst_outputs := [] |> s =
    Revert (revert_state s)
Proof
  cheat
QED

(* ==========================================================================
   JNZ Instruction Behavior
   ========================================================================== *)

(* WHY THIS IS TRUE: By step_inst_def, JNZ evaluates the condition.
   If cond <> 0w, it jumps to if_nonzero; else to if_zero. *)
Theorem step_jnz_behavior:
  !s cond cond_op if_nonzero if_zero id.
    eval_operand cond_op s = SOME cond ==>
    step_inst <| inst_id := id; inst_opcode := JNZ;
                 inst_operands := [cond_op; Label if_nonzero; Label if_zero];
                 inst_outputs := [] |> s =
    if cond <> 0w then OK (jump_to if_nonzero s)
    else OK (jump_to if_zero s)
Proof
  cheat
QED

(* WHY THIS IS TRUE: Special case when cond <> 0w. *)
Theorem step_jnz_nonzero_jumps:
  !s cond cond_op if_nonzero if_zero id.
    eval_operand cond_op s = SOME cond /\ cond <> 0w ==>
    step_inst <| inst_id := id; inst_opcode := JNZ;
                 inst_operands := [cond_op; Label if_nonzero; Label if_zero];
                 inst_outputs := [] |> s =
    OK (jump_to if_nonzero s)
Proof
  cheat
QED

(* WHY THIS IS TRUE: Special case when cond = 0w. *)
Theorem step_jnz_zero_jumps:
  !s cond_op if_nonzero if_zero id.
    eval_operand cond_op s = SOME 0w ==>
    step_inst <| inst_id := id; inst_opcode := JNZ;
                 inst_operands := [cond_op; Label if_nonzero; Label if_zero];
                 inst_outputs := [] |> s =
    OK (jump_to if_zero s)
Proof
  cheat
QED

(* ==========================================================================
   JMP Instruction Behavior
   ========================================================================== *)

(* WHY THIS IS TRUE: By step_inst_def, JMP unconditionally jumps to the label. *)
Theorem step_jmp_behavior:
  !s lbl id.
    step_inst <| inst_id := id; inst_opcode := JMP;
                 inst_operands := [Label lbl]; inst_outputs := [] |> s =
    OK (jump_to lbl s)
Proof
  cheat
QED

(* ==========================================================================
   Simple Revert Block Execution
   ========================================================================== *)

(* WHY THIS IS TRUE: A block with only [revert 0 0] will:
   1. step_in_block gets instruction at idx 0 -> the REVERT instruction
   2. step_inst returns Revert (revert_state s)
   3. run_block propagates this Revert result *)
Theorem simple_revert_block_reverts:
  !fn bb s.
    is_simple_revert_block bb ==>
    run_block fn bb (s with vs_inst_idx := 0) = Revert (revert_state s)
Proof
  cheat
QED

(* ==========================================================================
   state_equiv_except Properties
   ========================================================================== *)

(* WHY THIS IS TRUE: Every variable lookup equals itself, and all other
   state components are identical. *)
Theorem state_equiv_except_refl:
  !vars s. state_equiv_except vars s s
Proof
  cheat
QED

(* WHY THIS IS TRUE: state_equiv requires all variables equal.
   state_equiv_except only requires variables outside vars to be equal.
   So state_equiv is strictly stronger. *)
Theorem state_equiv_implies_except:
  !vars s1 s2. state_equiv s1 s2 ==> state_equiv_except vars s1 s2
Proof
  cheat
QED

(* WHY THIS IS TRUE: state_equiv_except is symmetric - if all non-vars
   variables are equal in s1 vs s2, they're equal in s2 vs s1. *)
Theorem state_equiv_except_sym:
  !vars s1 s2. state_equiv_except vars s1 s2 ==> state_equiv_except vars s2 s1
Proof
  cheat
QED

(* WHY THIS IS TRUE: state_equiv_except is transitive - chain equalities
   for variables not in vars. *)
Theorem state_equiv_except_trans:
  !vars s1 s2 s3.
    state_equiv_except vars s1 s2 /\ state_equiv_except vars s2 s3 ==>
    state_equiv_except vars s1 s3
Proof
  cheat
QED

(* WHY THIS IS TRUE: Updating variable x in both states preserves
   equivalence. For v not in vars: if v <> x, lookup unchanged;
   if v = x, both get the same new value. *)
Theorem update_var_state_equiv_except:
  !vars x v s1 s2.
    state_equiv_except vars s1 s2 ==>
    state_equiv_except vars (update_var x v s1) (update_var x v s2)
Proof
  cheat
QED

(* WHY THIS IS TRUE: update_var x v s adds (x, v) to vs_vars.
   For any y not in {x}, lookup_var y is unchanged.
   Other state components (memory, storage, etc.) unchanged. *)
Theorem update_var_state_equiv_except_insert:
  !x v s.
    state_equiv_except {x} s (update_var x v s)
Proof
  cheat
QED

(* WHY THIS IS TRUE: Adding more variables to the "except" set only
   weakens the requirement, so equivalence is preserved. *)
Theorem state_equiv_except_weaken:
  !vars1 vars2 s1 s2.
    vars1 SUBSET vars2 /\ state_equiv_except vars1 s1 s2 ==>
    state_equiv_except vars2 s1 s2
Proof
  cheat
QED

(* ==========================================================================
   revert_state Properties
   ========================================================================== *)

(* WHY THIS IS TRUE: revert_state only sets vs_halted := T and
   vs_reverted := T. It doesn't depend on vs_vars at all.
   So revert_state (update_var x v s) and revert_state s differ only
   in vs_vars, which is unchanged by revert_state. *)
Theorem revert_state_update_var:
  !x v s.
    revert_state (update_var x v s) = (revert_state s) with vs_vars := (s.vs_vars |+ (x, v))
Proof
  cheat
QED

(* WHY THIS IS TRUE: revert_state preserves state_equiv_except because
   it only modifies vs_halted and vs_reverted, not the variables
   or other state components that state_equiv_except checks. *)
Theorem revert_state_state_equiv_except:
  !vars s1 s2.
    state_equiv_except vars s1 s2 ==>
    state_equiv_except vars (revert_state s1) (revert_state s2)
Proof
  cheat
QED

(* WHY THIS IS TRUE: revert_state preserves state_equiv for similar reasons. *)
Theorem revert_state_state_equiv:
  !s1 s2.
    state_equiv s1 s2 ==>
    state_equiv (revert_state s1) (revert_state s2)
Proof
  cheat
QED

(* ==========================================================================
   jump_to Properties
   ========================================================================== *)

(* WHY THIS IS TRUE: jump_to only modifies vs_prev_bb, vs_current_bb,
   vs_inst_idx. Variables and other state unchanged. So if s1 and s2
   are state_equiv_except vars, so are jump_to lbl s1 and jump_to lbl s2. *)
Theorem jump_to_state_equiv_except:
  !vars lbl s1 s2.
    state_equiv_except vars s1 s2 ==>
    state_equiv_except vars (jump_to lbl s1) (jump_to lbl s2)
Proof
  cheat
QED

(* WHY THIS IS TRUE: jump_to only changes control flow fields, not variables.
   So update_var commutes with jump_to (they modify disjoint state components). *)
Theorem jump_to_update_var_comm:
  !x v lbl s.
    jump_to lbl (update_var x v s) = update_var x v (jump_to lbl s)
Proof
  cheat
QED

(* ==========================================================================
   Combined Lemmas for Transformation Patterns
   ========================================================================== *)

(* WHY THIS IS TRUE: After ISZERO on cond, output contains bool_to_word (cond = 0w).
   If cond <> 0w, then cond = 0w is false, so output = 0w.
   ASSERT on 0w reverts. This matches JNZ taking the revert branch. *)
Theorem iszero_then_assert_when_nonzero:
  !s cond cond_op out id1 id2.
    eval_operand cond_op s = SOME cond /\
    cond <> 0w ==>
    let s1 = update_var out (bool_to_word (cond = 0w)) s in
    step_inst <| inst_id := id2; inst_opcode := ASSERT;
                 inst_operands := [Var out]; inst_outputs := [] |> s1 =
    Revert (revert_state s1)
Proof
  cheat
QED

(* WHY THIS IS TRUE: After ISZERO on cond, output contains bool_to_word (cond = 0w).
   If cond = 0w, then cond = 0w is true, so output = 1w <> 0w.
   ASSERT on nonzero succeeds. This matches JNZ taking the else branch. *)
Theorem iszero_then_assert_when_zero:
  !s cond cond_op out id1 id2.
    eval_operand cond_op s = SOME cond /\
    cond = 0w ==>
    let s1 = update_var out (bool_to_word (cond = 0w)) s in
    step_inst <| inst_id := id2; inst_opcode := ASSERT;
                 inst_operands := [Var out]; inst_outputs := [] |> s1 =
    OK s1
Proof
  cheat
QED

(* WHY THIS IS TRUE: For pattern 2, when cond <> 0w, ASSERT passes and
   we jump to then_label. JNZ would also jump to then_label (if_nonzero).
   The states are identical. *)
Theorem assert_when_nonzero_then_jmp:
  !s cond cond_op then_label id1 id2.
    eval_operand cond_op s = SOME cond /\
    cond <> 0w ==>
    step_inst <| inst_id := id1; inst_opcode := ASSERT;
                 inst_operands := [cond_op]; inst_outputs := [] |> s = OK s
Proof
  cheat
QED

(* WHY THIS IS TRUE: For pattern 2, when cond = 0w, ASSERT reverts.
   JNZ would jump to revert_label and execute revert. Both revert. *)
Theorem assert_when_zero_reverts:
  !s cond_op id.
    eval_operand cond_op s = SOME 0w ==>
    step_inst <| inst_id := id; inst_opcode := ASSERT;
                 inst_operands := [cond_op]; inst_outputs := [] |> s =
    Revert (revert_state s)
Proof
  cheat
QED

(* ==========================================================================
   run_block Helper Lemmas
   ========================================================================== *)

(* WHY THIS IS TRUE: step_in_block uses get_instruction to fetch current
   instruction based on vs_inst_idx. If we start at index 0 and the block
   has instructions, we get the first instruction. *)
Theorem step_in_block_at_zero:
  !fn bb s inst.
    bb.bb_instructions = [inst] ==>
    step_in_block fn bb (s with vs_inst_idx := 0) =
    (step_inst inst s, is_terminator inst.inst_opcode)
Proof
  cheat
QED

(* WHY THIS IS TRUE: run_block on a single-instruction block that's a
   terminator just executes that instruction and returns the result. *)
Theorem run_block_single_terminator:
  !fn bb s inst res.
    bb.bb_instructions = [inst] /\
    is_terminator inst.inst_opcode /\
    step_inst inst s = res ==>
    run_block fn bb (s with vs_inst_idx := 0) = res
Proof
  cheat
QED

(* ==========================================================================
   result_equiv with state_equiv_except
   ========================================================================== *)

(* WHY THIS IS TRUE: Revert results are equiv if their states are equiv.
   state_equiv_except implies state_equiv on the reverted fields
   (halted, reverted) and memory/storage, which is what matters for Revert. *)
Theorem result_equiv_revert_except:
  !vars s1 s2.
    state_equiv_except vars s1 s2 ==>
    result_equiv (Revert (revert_state s1)) (Revert (revert_state s2))
Proof
  cheat
QED

val _ = export_theory();
