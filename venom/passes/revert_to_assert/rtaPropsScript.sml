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
 * STATE_EQUIV_EXCEPT PROPERTIES (in rtaDefsTheory):
 *   - state_equiv_except_refl/sym/trans, state_equiv_implies_except
 *   - update_var_same_preserves, jump_to_except_preserves, revert_state_except_preserves
 *
 * ADDITIONAL PROPERTIES (this file):
 *   - update_var_state_equiv_except_insert : update_var x creates {x}-equiv
 *   - revert_state_update_var       : revert_state insensitive to variables
 *   - revert_state_state_equiv      : revert_state preserves state_equiv
 *   - jump_to_update_var_comm       : jump_to and update_var commute
 *
 * HELPER THEOREMS:
 *   - bool_to_word_eq_0w            : bool_to_word b = 0w iff ~b
 *   - bool_to_word_neq_0w           : bool_to_word b <> 0w iff b
 *   - eval_operand_update_var_same  : eval (Var x) after update_var x
 *   - eval_operand_update_var_other : eval (Var y) after update_var x, x <> y
 *
 * ============================================================================
 *)

Theory rtaProps
Ancestors
  rtaDefs stateEquiv venomSemProps
Libs
  finite_mapTheory venomStateTheory venomSemTheory venomInstTheory venomSemPropsTheory

(* ==========================================================================
   NOTE: bool_to_word properties and basic instruction behavior lemmas
   (step_iszero_value, step_assert_behavior, step_revert_always_reverts,
   step_jnz_behavior, step_jmp_behavior) are now in venomSemPropsTheory.
   ========================================================================== *)

(* ==========================================================================
   Operand Evaluation with Variable Updates
   ========================================================================== *)

(* WHY THIS IS TRUE: update_var x v s sets vs_vars |+ (x, v), so
   lookup_var x returns SOME v. eval_operand (Var x) uses lookup_var. *)
Theorem eval_operand_update_var_same:
  !x v s. eval_operand (Var x) (update_var x v s) = SOME v
Proof
  rw[eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

(* WHY THIS IS TRUE: update_var x doesn't affect lookup of other variables.
   FLOOKUP (fm |+ (x,v)) y = FLOOKUP fm y when x <> y. *)
Theorem eval_operand_update_var_other:
  !x y v s. x <> y ==> eval_operand (Var y) (update_var x v s) = eval_operand (Var y) s
Proof
  rw[eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

(* WHY THIS IS TRUE: update_var only affects vs_vars, not memory, so
   evaluating a literal is unchanged. *)
Theorem eval_operand_update_var_lit:
  !x v s w. eval_operand (Lit w) (update_var x v s) = SOME w
Proof
  rw[eval_operand_def]
QED

(* ==========================================================================
   ASSERT Instruction Behavior - Special Cases
   (Base lemma step_assert_behavior is in venomSemPropsTheory)
   ========================================================================== *)

(* WHY THIS IS TRUE: Special case of step_assert_behavior with cond = 0w. *)
Theorem step_assert_zero_reverts:
  !s cond_op id.
    eval_operand cond_op s = SOME 0w ==>
    step_inst <| inst_id := id; inst_opcode := ASSERT;
                 inst_operands := [cond_op]; inst_outputs := [] |> s =
    Revert (revert_state s)
Proof
  rw[] >> drule step_assert_behavior >> simp[]
QED

(* WHY THIS IS TRUE: Special case of step_assert_behavior with cond <> 0w. *)
Theorem step_assert_nonzero_passes:
  !s cond cond_op id.
    eval_operand cond_op s = SOME cond /\ cond <> 0w ==>
    step_inst <| inst_id := id; inst_opcode := ASSERT;
                 inst_operands := [cond_op]; inst_outputs := [] |> s =
    OK s
Proof
  rw[] >> drule step_assert_behavior >> simp[]
QED

(* ==========================================================================
   JNZ Instruction Behavior - Special Cases
   (Base lemma step_jnz_behavior is in venomSemPropsTheory)
   ========================================================================== *)

(* WHY THIS IS TRUE: Special case when cond <> 0w. *)
Theorem step_jnz_nonzero_jumps:
  !s cond cond_op if_nonzero if_zero id.
    eval_operand cond_op s = SOME cond /\ cond <> 0w ==>
    step_inst <| inst_id := id; inst_opcode := JNZ;
                 inst_operands := [cond_op; Label if_nonzero; Label if_zero];
                 inst_outputs := [] |> s =
    OK (jump_to if_nonzero s)
Proof
  rw[] >> drule step_jnz_behavior >> simp[]
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
  rw[] >> drule step_jnz_behavior >> simp[]
QED

(* ==========================================================================
   run_block Helper Lemmas
   ========================================================================== *)

(* WHY THIS IS TRUE: step_in_block on a single-instruction terminator block
   returns the result of step_inst with is_term = T. *)
Theorem step_in_block_single_terminator:
  !fn bb s inst.
    bb.bb_instructions = [inst] /\
    is_terminator inst.inst_opcode ==>
    step_in_block fn bb (s with vs_inst_idx := 0) =
    (step_inst inst (s with vs_inst_idx := 0), T)
Proof
  rw[step_in_block_def, get_instruction_def] >>
  Cases_on `step_inst inst (s with vs_inst_idx := 0)` >> simp[]
QED

(* WHY THIS IS TRUE: run_block on a single-instruction REVERT block returns Revert. *)
Theorem run_block_single_revert:
  !fn bb s inst.
    bb.bb_instructions = [inst] /\
    inst.inst_opcode = REVERT ==>
    run_block fn bb (s with vs_inst_idx := 0) =
    Revert (revert_state (s with vs_inst_idx := 0))
Proof
  rpt strip_tac >>
  simp[Once run_block_def, step_in_block_def, get_instruction_def,
       step_inst_def, is_terminator_def]
QED

(* ==========================================================================
   Simple Revert Block Execution
   (step_jmp_behavior is in venomSemPropsTheory)
   ========================================================================== *)

(* WHY THIS IS TRUE: A block with only [revert 0 0] will:
   1. step_in_block gets instruction at idx 0 -> the REVERT instruction
   2. step_inst returns Revert (revert_state s)
   3. run_block propagates this Revert result *)
Theorem simple_revert_block_reverts:
  !fn bb s.
    is_simple_revert_block bb ==>
    run_block fn bb (s with vs_inst_idx := 0) =
    Revert (revert_state (s with vs_inst_idx := 0))
Proof
  rw[is_simple_revert_block_def] >>
  `bb.bb_instructions = [HD bb.bb_instructions]` by (
    Cases_on `bb.bb_instructions` >> fs[]
  ) >>
  irule run_block_single_revert >>
  qexists_tac `HD bb.bb_instructions` >>
  simp[]
QED

(* ==========================================================================
   state_equiv_except Properties

   NOTE: Basic properties (refl, sym, trans, state_equiv_implies_except,
   update_var_same_preserves, jump_to_except_preserves, revert_state_except_preserves,
   state_equiv_except_subset) are proven in rtaDefsTheory.
   ========================================================================== *)

(* WHY THIS IS TRUE: update_var x v s adds (x, v) to vs_vars.
   For any y not in {x}, lookup_var y is unchanged.
   Other state components (memory, storage, etc.) unchanged. *)
Theorem update_var_state_equiv_except_insert:
  !x v s.
    state_equiv_except {x} s (update_var x v s)
Proof
  rw[state_equiv_except_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
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
  rw[revert_state_def, update_var_def]
QED

(* NOTE: revert_state_state_equiv is available from stateEquivTheory *)

(* ==========================================================================
   jump_to Properties
   ========================================================================== *)

(* WHY THIS IS TRUE: jump_to only changes control flow fields, not variables.
   So update_var commutes with jump_to (they modify disjoint state components). *)
Theorem jump_to_update_var_comm:
  !x v lbl s.
    jump_to lbl (update_var x v s) = update_var x v (jump_to lbl s)
Proof
  rw[jump_to_def, update_var_def]
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
  rw[] >>
  `(cond = 0w) = F` by gvs[] >>
  pop_assum (fn th => simp[th, bool_to_word_F]) >>
  simp[eval_operand_update_var_same] >>
  irule step_assert_zero_reverts >>
  simp[eval_operand_update_var_same]
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
  rw[] >>
  simp[bool_to_word_T] >>
  irule step_assert_nonzero_passes >>
  simp[eval_operand_update_var_same]
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
  rw[] >> drule step_assert_behavior >> simp[]
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
  rw[] >> drule step_assert_behavior >> simp[]
QED

val _ = export_theory();
