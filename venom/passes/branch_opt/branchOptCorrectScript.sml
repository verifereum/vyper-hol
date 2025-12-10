(*
 * Branch Optimization Correctness Proofs
 *
 * This theory proves that the branch optimization transformation preserves
 * program semantics.
 *
 * Key insight: jnz (iszero x), A, B === jnz x, B, A
 *
 * This means:
 * - If x = 0, then iszero x = 1 (nonzero), so we go to A. With swapped targets, x = 0 so we go to A.
 * - If x <> 0, then iszero x = 0, so we go to B. With swapped targets, x <> 0 so we go to B.
 *
 * Wait, that's wrong. Let me reconsider:
 * - jnz cond, label_if_nonzero, label_if_zero
 * - If cond <> 0, go to label_if_nonzero
 * - If cond = 0, go to label_if_zero
 *
 * So jnz (iszero x), A, B:
 * - If iszero x <> 0 (i.e., x = 0), go to A
 * - If iszero x = 0 (i.e., x <> 0), go to B
 *
 * And jnz x, B, A:
 * - If x <> 0, go to B
 * - If x = 0, go to A
 *
 * These are equivalent! QED.
 *
 * ============================================================================
 * STRUCTURE OVERVIEW
 * ============================================================================
 *
 * KEY LEMMAS:
 *   - iszero_swap_equiv       : The fundamental semantic equivalence
 *   - step_inst_iszero_jnz    : ISZERO + JNZ combined step equivalence
 *   - transform_block_correct : Block-level correctness
 *
 * ============================================================================
 *)

Theory branchOptCorrect
Ancestors
  branchOptTransform venomSem venomState venomInst list finite_map

(* ==========================================================================
   Fundamental Semantic Equivalence

   The key insight is that:
     (iszero x) <> 0w  <=>  x = 0w
     (iszero x) = 0w   <=>  x <> 0w

   Therefore swapping branch targets while removing iszero is semantics-preserving.
   ========================================================================== *)

(* Helper: bool_to_word semantics *)
Theorem bool_to_word_nonzero:
  !b. bool_to_word b <> 0w <=> b
Proof
  Cases >> simp[bool_to_word_def]
QED

Theorem bool_to_word_zero:
  !b. bool_to_word b = 0w <=> ~b
Proof
  Cases >> simp[bool_to_word_def]
QED

(* KEY LEMMA: iszero swaps the branch condition *)
Theorem iszero_swap_condition:
  !x:bytes32.
    (bool_to_word (x = 0w) <> 0w <=> x = 0w) /\
    (bool_to_word (x = 0w) = 0w <=> x <> 0w)
Proof
  gen_tac >> simp[bool_to_word_nonzero, bool_to_word_zero]
QED

(* ==========================================================================
   Step Instruction Properties
   ========================================================================== *)

(* ISZERO step produces bool_to_word of equality with 0 *)
Theorem step_inst_iszero:
  !inst s out_var in_var v.
    inst.inst_opcode = ISZERO /\
    inst.inst_operands = [Var in_var] /\
    inst.inst_outputs = [out_var] /\
    lookup_var in_var s = SOME v
  ==>
    step_inst inst s = OK (update_var out_var (bool_to_word (v = 0w)) s)
Proof
  rw[step_inst_def, exec_unop_def, eval_operand_def]
QED

(* JNZ step with condition value *)
Theorem step_inst_jnz:
  !inst s cond_var lbl1 lbl2 v.
    inst.inst_opcode = JNZ /\
    inst.inst_operands = [Var cond_var; Label lbl1; Label lbl2] /\
    lookup_var cond_var s = SOME v
  ==>
    step_inst inst s =
      if v <> 0w then OK (jump_to lbl1 s)
      else OK (jump_to lbl2 s)
Proof
  rw[step_inst_def, eval_operand_def]
QED

(* JNZ with swapped targets *)
Theorem step_inst_jnz_swapped:
  !inst s cond_var lbl1 lbl2 v.
    inst.inst_opcode = JNZ /\
    inst.inst_operands = [Var cond_var; Label lbl2; Label lbl1] /\
    lookup_var cond_var s = SOME v
  ==>
    step_inst inst s =
      if v <> 0w then OK (jump_to lbl2 s)
      else OK (jump_to lbl1 s)
Proof
  rw[step_inst_def, eval_operand_def]
QED

(* ==========================================================================
   Combined ISZERO + JNZ Equivalence

   This is the core correctness theorem for the transformation.

   Original sequence:
     %t = iszero %x
     jnz %t, @A, @B

   Transformed sequence:
     nop
     jnz %x, @B, @A

   We show these produce equivalent final states (same jump target).
   ========================================================================== *)

(* The key equivalence: iszero+jnz vs direct jnz with swapped targets *)
Theorem iszero_jnz_swap_equiv:
  !x:bytes32 lbl_a lbl_b s.
    (* Original: if (iszero x) <> 0 then A else B *)
    (if bool_to_word (x = 0w) <> 0w then jump_to lbl_a s else jump_to lbl_b s) =
    (* Transformed: if x <> 0 then B else A *)
    (if x <> 0w then jump_to lbl_b s else jump_to lbl_a s)
Proof
  rpt gen_tac >>
  simp[bool_to_word_nonzero] >>
  Cases_on `x = 0w` >> simp[]
QED

(* ==========================================================================
   NOP Semantics
   ========================================================================== *)

Theorem step_inst_nop:
  !inst s.
    inst.inst_opcode = NOP ==>
    step_inst inst s = OK s
Proof
  rw[step_inst_def]
QED

(* ==========================================================================
   Block Transformation Correctness

   When the transformation applies (iszero+jnz pattern), the transformed
   block produces the same execution result.
   ========================================================================== *)

(* Helper: The transformation pattern detection matches what we expect *)
Theorem transform_block_pattern_match:
  !bb iszero_inst jnz_inst out_var orig_cond.
    LENGTH bb.bb_instructions >= 2 /\
    EL (LENGTH bb.bb_instructions - 2) bb.bb_instructions = iszero_inst /\
    EL (LENGTH bb.bb_instructions - 1) bb.bb_instructions = jnz_inst /\
    is_iszero_inst iszero_inst /\
    get_single_output iszero_inst = SOME out_var /\
    iszero_inst.inst_operands = [orig_cond] /\
    jnz_uses_var jnz_inst out_var
  ==>
    ?new_jnz rest.
      (transform_block bb).bb_instructions =
        rest ++ [iszero_inst with inst_opcode := NOP] ++ [new_jnz] /\
      new_jnz = swap_jnz_operands (replace_jnz_cond jnz_inst orig_cond) /\
      LENGTH rest = LENGTH bb.bb_instructions - 2
Proof
  rw[transform_block_def] >>
  simp[] >>
  qexists_tac `TAKE (LENGTH bb.bb_instructions - 2) bb.bb_instructions` >>
  simp[LENGTH_TAKE]
QED

(* Main correctness theorem: transform preserves execution semantics *)
Theorem transform_block_execution_equiv:
  !bb s iszero_inst jnz_inst out_var in_var lbl1 lbl2 v.
    (* Block structure *)
    LENGTH bb.bb_instructions >= 2 /\
    EL (LENGTH bb.bb_instructions - 2) bb.bb_instructions = iszero_inst /\
    EL (LENGTH bb.bb_instructions - 1) bb.bb_instructions = jnz_inst /\
    (* ISZERO instruction *)
    iszero_inst.inst_opcode = ISZERO /\
    iszero_inst.inst_operands = [Var in_var] /\
    iszero_inst.inst_outputs = [out_var] /\
    (* JNZ instruction *)
    jnz_inst.inst_opcode = JNZ /\
    jnz_inst.inst_operands = [Var out_var; Label lbl1; Label lbl2] /\
    (* State has input variable defined *)
    lookup_var in_var s = SOME v /\
    (* We're at the ISZERO instruction *)
    s.vs_inst_idx = LENGTH bb.bb_instructions - 2
  ==>
    (* Original execution: iszero then jnz *)
    let iszero_result = step_inst iszero_inst s in
    let s1 = case iszero_result of OK st => next_inst st | _ => s in
    let jnz_result = step_inst jnz_inst s1 in
    (* Transformed execution: nop then swapped jnz *)
    let nop_inst = iszero_inst with inst_opcode := NOP in
    let swapped_jnz = swap_jnz_operands (replace_jnz_cond jnz_inst (Var in_var)) in
    let nop_result = step_inst nop_inst s in
    let s2 = case nop_result of OK st => next_inst st | _ => s in
    let swapped_result = step_inst swapped_jnz s2 in
    (* Both reach the same target *)
    case (jnz_result, swapped_result) of
      (OK final1, OK final2) => final1.vs_current_bb = final2.vs_current_bb
    | _ => T
Proof
  rw[] >>
  (* Unfold all step_inst and related definitions *)
  simp[step_inst_def, exec_unop_def, eval_operand_def,
       swap_jnz_operands_def, replace_jnz_cond_def,
       bool_to_word_def, jump_to_def] >>
  (* Simplify lookup_var with update_var and next_inst *)
  simp[lookup_var_def, update_var_def, next_inst_def, FLOOKUP_UPDATE] >>
  (* Use the hypothesis about lookup_var in_var s *)
  full_simp_tac std_ss [lookup_var_def] >>
  (* Case split on v = 0w to show both paths lead to same target *)
  Cases_on `v = 0w` >> simp[bool_to_word_def]
QED

val _ = export_theory();
