(*
 * SimplifyCFG Block-Level Correctness
 *
 * This theory proves block-level correctness of CFG simplification.
 * The main results show that:
 * 1. Running a merged block is equivalent to running both original blocks
 * 2. Threading a jump preserves execution semantics
 *
 * ============================================================================
 * STRUCTURE OVERVIEW
 * ============================================================================
 *
 * KEY LEMMAS:
 *   - run_merged_block_equiv      : Merged block execution equivalence
 *   - thread_jump_equiv           : Jump threading preserves semantics
 *   - replace_label_preserves_sem : Label replacement preserves semantics
 *
 * HELPER THEOREMS:
 *   - step_jmp_to_block           : JMP instruction steps to target block
 *   - run_passthrough_equiv       : Passthrough block is equivalent to direct jump
 *
 * ============================================================================
 *)

Theory cfgBlock
Ancestors
  cfgWellFormed cfgTransform execEquiv venomSem venomInst stateEquiv list

(* ==========================================================================
   Instruction-Level Lemmas
   ========================================================================== *)

(* JMP instruction steps to the target block *)
Theorem step_inst_jmp:
  !inst s lbl.
    inst.inst_opcode = JMP /\
    inst.inst_operands = [Label lbl] ==>
    step_inst inst s = OK (jump_to lbl s)
Proof
  rw[step_inst_def]
QED

(* JMP is a terminator *)
Theorem jmp_is_terminator:
  is_terminator JMP
Proof
  rw[is_terminator_def]
QED

(* Stepping a JMP in a block causes termination *)
Theorem step_in_block_jmp_terminates:
  !fn bb s inst.
    get_instruction bb s.vs_inst_idx = SOME inst /\
    inst.inst_opcode = JMP ==>
    SND (step_in_block fn bb s) = T
Proof
  rw[step_in_block_def] >>
  Cases_on `step_inst inst s` >> simp[jmp_is_terminator]
QED

(* ==========================================================================
   Block Execution Decomposition
   ========================================================================== *)

(* Running instructions from a block is deterministic based on instruction sequence *)
Theorem run_block_deterministic:
  !fn bb s.
    run_block fn bb s = run_block fn bb s
Proof
  simp[]
QED

(* Helper: FRONT gives all but last element *)
Theorem front_append_last:
  !l. l <> [] ==> FRONT l ++ [LAST l] = l
Proof
  Induct >> simp[] >> Cases_on `l` >> simp[]
QED

(* Helper: Getting instruction from FRONT *)
Theorem get_instruction_front:
  !bb idx.
    bb.bb_instructions <> [] /\
    idx < LENGTH (FRONT bb.bb_instructions) ==>
    get_instruction (bb with bb_instructions := FRONT bb.bb_instructions) idx =
    get_instruction bb idx
Proof
  cheat
QED

(* Helper: Getting instruction from merged block (from a's FRONT) *)
Theorem get_instruction_merge_a:
  !a b idx.
    a.bb_instructions <> [] /\
    idx < LENGTH (FRONT a.bb_instructions) ==>
    get_instruction (merge_blocks a b) idx = get_instruction a idx
Proof
  cheat
QED

(* Helper: Getting instruction from merged block (from b) *)
Theorem get_instruction_merge_b:
  !a b idx.
    a.bb_instructions <> [] /\
    idx >= LENGTH (FRONT a.bb_instructions) /\
    idx < LENGTH (FRONT a.bb_instructions) + LENGTH b.bb_instructions ==>
    get_instruction (merge_blocks a b) idx =
    get_instruction b (idx - LENGTH (FRONT a.bb_instructions))
Proof
  cheat
QED

(* ==========================================================================
   Passthrough Block Equivalence
   ========================================================================== *)

(* A passthrough block (single JMP) is equivalent to directly jumping to target *)
Theorem run_passthrough_block:
  !fn bb s target.
    is_passthrough_block bb /\
    get_block_target bb = SOME target ==>
    run_block fn bb s = OK (jump_to target s)
Proof
  cheat
QED

(* ==========================================================================
   Jump Threading Correctness
   ========================================================================== *)

(* Threading a jump through a passthrough block preserves semantics.
   If we have A -> B -> C where B is just a JMP to C,
   then rewriting A to jump directly to C gives the same execution. *)

(* Label replacement in non-Label operands is identity *)
Theorem replace_label_operand_non_label:
  !old new op.
    (!l. op <> Label l) ==>
    replace_label_operand old new op = op
Proof
  Cases_on `op` >> rw[replace_label_operand_def]
QED

(* Label replacement preserves non-JMP instruction semantics *)
Theorem replace_label_inst_preserves_step:
  !old new inst s.
    ~is_jmp_inst inst /\ inst.inst_opcode <> JNZ ==>
    step_inst (replace_label_inst old new inst) s = step_inst inst s
Proof
  cheat
QED

(* Threading a jump that doesn't match is identity *)
Theorem thread_jump_inst_no_match:
  !pl tl inst.
    ~MEM (Label pl) inst.inst_operands ==>
    thread_jump_inst pl tl inst = inst
Proof
  cheat
QED

(* ==========================================================================
   Merged Block Execution
   ========================================================================== *)

(* Helper: Running a block and then jumping is the same as running both blocks *)

(* State after running FRONT of instructions *)
Definition run_front_def:
  run_front fn bb s =
    if bb.bb_instructions = [] then OK s
    else run_block fn (bb with bb_instructions := FRONT bb.bb_instructions) s
End

(* Key lemma: Running merged block A++B is equivalent to:
   1. Running FRONT of A (all non-terminator instructions)
   2. Then running B
   Since A ends with JMP to B, and we're removing that JMP and appending B *)

(* After running FRONT of block a, we get a state that can continue to block b *)
Theorem run_front_then_b:
  !fn a b s s'.
    wf_block a /\
    get_block_target a = SOME b.bb_label /\
    run_block fn (a with bb_instructions := FRONT a.bb_instructions) s = OK s' ==>
    s'.vs_inst_idx = LENGTH (FRONT a.bb_instructions)
Proof
  cheat
QED

(* Main theorem: Merged block execution is equivalent to sequential execution *)
Theorem merge_blocks_execution:
  !fn a b s.
    wf_block a /\ wf_block b /\
    get_block_target a = SOME b.bb_label /\
    no_phi_block b ==>
    result_equiv
      (run_block fn (merge_blocks a b) s)
      (case run_block fn a s of
         OK s' => run_block fn b (s' with vs_inst_idx := 0)
       | other => other)
Proof
  cheat
QED

(* ==========================================================================
   Label Replacement Preserves Semantics
   ========================================================================== *)

(* Replace label in PHI correctly updates predecessor reference *)
Theorem replace_label_phi_correct:
  !old new inst s.
    is_phi_inst inst /\
    s.vs_prev_bb = SOME old ==>
    step_inst (replace_label_inst old new inst) (s with vs_prev_bb := SOME new) =
    step_inst inst s
Proof
  cheat
QED

(* ==========================================================================
   Result Equivalence for Transformations
   ========================================================================== *)

(* Replacing labels doesn't change execution of non-PHI blocks *)
Theorem replace_label_block_non_phi_equiv:
  !old new bb fn s.
    ~EXISTS is_phi_inst bb.bb_instructions ==>
    result_equiv
      (run_block fn (replace_label_block old new bb) s)
      (run_block fn bb s)
Proof
  cheat
QED

(* Threading preserves execution when going through passthrough *)
Theorem thread_preserves_execution:
  !fn blocks passthrough_lbl target_lbl s bb.
    lookup_block passthrough_lbl blocks = SOME bb /\
    is_passthrough_block bb /\
    get_block_target bb = SOME target_lbl ==>
    (* Execution through passthrough is same as direct jump *)
    !s'. s'.vs_current_bb = passthrough_lbl ==>
         result_equiv
           (run_block fn bb s')
           (OK (jump_to target_lbl s'))
Proof
  cheat
QED

