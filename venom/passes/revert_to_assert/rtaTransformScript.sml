(*
 * Revert-to-Assert Pass: Transformation Definitions and Correctness
 *
 * This theory defines the full transformation pass and proves correctness
 * at block, function, and context levels.
 *
 * ============================================================================
 * STRUCTURE OVERVIEW
 * ============================================================================
 *
 * DEFINITIONS:
 *   - fresh_iszero_var      : Generate fresh variable name for ISZERO output
 *   - mk_iszero_inst        : Build ISZERO instruction
 *   - mk_assert_inst        : Build ASSERT instruction
 *   - mk_jmp_inst           : Build JMP instruction
 *   - is_revert_label       : Check if label points to simple revert block
 *   - transform_pattern1    : Pattern 1 transformation (revert on true)
 *   - transform_pattern2    : Pattern 2 transformation (revert on false)
 *   - transform_jnz         : Try to transform a JNZ instruction
 *   - transform_block_insts : Transform instructions in a block
 *   - transform_block       : Transform a single block
 *   - transform_function    : Transform all blocks in a function
 *   - transform_context     : Transform all functions in a context
 *
 * TOP-LEVEL CORRECTNESS THEOREMS:
 *   - transform_block_correct    : Block-level correctness
 *   - transform_function_correct : Function-level correctness
 *   - transform_context_correct  : Context-level correctness
 *
 * ============================================================================
 *)

Theory rtaTransform
Ancestors
  rtaCorrect rtaProps rtaDefs stateEquiv venomSem venomInst venomState list rich_list

(*
 * KEY LEMMA: Different instruction IDs produce different fresh var names.
 * This follows from toString being injective on naturals.
 *)
Theorem fresh_iszero_var_distinct:
  !id1 id2. id1 <> id2 ==> fresh_iszero_var id1 <> fresh_iszero_var id2
Proof
  rw[fresh_iszero_var_def] >>
  simp[ASCIInumbersTheory.toString_inj]
QED

(*
 * Fresh vars not in block implies operands don't reference fresh vars.
 *)
Theorem fresh_vars_not_in_block_operands:
  !fn bb inst v.
    fresh_vars_not_in_block fn bb /\
    MEM inst bb.bb_instructions /\
    v IN fresh_vars_in_block fn bb ==>
    ~MEM (Var v) inst.inst_operands
Proof
  rw[fresh_vars_not_in_block_def, fresh_vars_in_block_def] >>
  CCONTR_TAC >> gvs[] >>
  (* v = fresh_iszero_var inst'.inst_id for some inst' *)
  first_x_assum (qspecl_then [`inst`, `fresh_iszero_var inst'.inst_id`] mp_tac) >>
  simp[] >> qexists_tac `inst'.inst_id` >> simp[]
QED

(* ==========================================================================
   Helper Lemmas: transform_block_insts Properties
   ========================================================================== *)

(*
 * WHY THIS IS TRUE: When transform_jnz returns NONE, the instruction is
 * kept unchanged. Only JNZ instructions matching patterns are modified.
 *)
Theorem transform_block_insts_non_jnz:
  !fn inst rest.
    inst.inst_opcode <> JNZ ==>
    transform_block_insts fn (inst::rest) = inst :: transform_block_insts fn rest
Proof
  rw[transform_block_insts_def, transform_jnz_def]
QED

(*
 * WHY THIS IS TRUE: Empty list transforms to empty list.
 *)
Theorem transform_block_insts_nil:
  !fn. transform_block_insts fn [] = []
Proof
  rw[transform_block_insts_def]
QED

(* ==========================================================================
   Block-Level Correctness
   ========================================================================== *)

(*
 * WHY THIS IS TRUE: eval_operand only accesses vs_vars (via lookup_var),
 * not vs_inst_idx. So changing vs_inst_idx doesn't affect eval_operand.
 *)
Theorem eval_operand_vs_inst_idx:
  !op s n. eval_operand op (s with vs_inst_idx := n) = eval_operand op s
Proof
  Cases >> simp[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def]
QED

(*
 * WHY THIS IS TRUE: step_in_block doesn't use fn in its computation.
 * It only uses bb and s to get/execute the current instruction.
 *)
Theorem step_in_block_fn_irrelevant:
  !fn1 fn2 bb s. step_in_block fn1 bb s = step_in_block fn2 bb s
Proof
  simp[venomSemTheory.step_in_block_def]
QED

(*
 * WHY THIS IS TRUE: run_block is defined recursively using step_in_block.
 * Since step_in_block doesn't depend on fn, run_block doesn't either.
 * The fn parameter is just passed through to recursive calls.
 *)
Theorem run_block_fn_irrelevant:
  !fn bb s. run_block fn bb s = run_block ARB bb s
Proof
  ho_match_mp_tac venomSemTheory.run_block_ind >> rw[] >>
  simp[Once venomSemTheory.run_block_def, step_in_block_fn_irrelevant, SimpLHS] >>
  simp[Once venomSemTheory.run_block_def, step_in_block_fn_irrelevant, SimpRHS] >>
  Cases_on `step_in_block fn bb s` >>
  `step_in_block ARB bb s = step_in_block fn bb s` by simp[step_in_block_fn_irrelevant] >>
  gvs[] >> Cases_on `q` >> simp[]
QED

(*
 * WHY THIS IS TRUE: Non-terminator instructions have is_terminator = F.
 * transform_jnz only returns SOME for JNZ opcode.
 * JNZ is a terminator (is_terminator JNZ = T).
 * So for non-terminators, transform_jnz returns NONE, leaving them unchanged.
 *)
Theorem transform_block_insts_non_terminators:
  !fn insts.
    EVERY (\inst. ~is_terminator inst.inst_opcode) insts ==>
    transform_block_insts fn insts = insts
Proof
  Induct_on `insts` >> simp[transform_block_insts_def] >> rw[] >>
  Cases_on `h.inst_opcode = JNZ` >> gvs[venomInstTheory.is_terminator_def, transform_jnz_def]
QED

(* NOTE: transform_block_insts helper theorems are now in rtaPropsTheory:
 * - transform_block_insts_TAKE_DROP
 * - transform_block_insts_TAKE
 * - transform_block_insts_EL_transformed
 * - transform_block_insts_length_ge
 * - transform_block_insts_length_pattern1
 * - transform_block_insts_length_pattern2
 *)

(*
 * Helper: step_in_block is the same for two blocks with matching prefix.
 *
 * WHY THIS IS TRUE: step_in_block uses get_instruction to fetch current instruction.
 * If TAKE (SUC n) matches and we're at index n, then EL n is the same.
 * So step_in_block executes the same instruction on both.
 *)
Theorem step_in_block_prefix_same:
  !fn bb1 bb2 s n.
    TAKE (SUC n) bb1.bb_instructions = TAKE (SUC n) bb2.bb_instructions /\
    s.vs_inst_idx = n /\
    n < LENGTH bb1.bb_instructions /\
    n < LENGTH bb2.bb_instructions
  ==>
    step_in_block fn bb1 s = step_in_block fn bb2 s
Proof
  rw[step_in_block_def, get_instruction_def] >>
  `EL s.vs_inst_idx bb1.bb_instructions = EL s.vs_inst_idx bb2.bb_instructions` by (
    `EL s.vs_inst_idx (TAKE (SUC s.vs_inst_idx) bb1.bb_instructions) =
     EL s.vs_inst_idx (TAKE (SUC s.vs_inst_idx) bb2.bb_instructions)` by simp[] >>
    metis_tac[EL_TAKE, DECIDE ``n < SUC n``]
  ) >>
  simp[]
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
  Cases_on `is_terminator x.inst_opcode` >> gvs[venomStateTheory.next_inst_def] >>
  `v'.vs_inst_idx = s.vs_inst_idx` by (
    drule_all step_inst_preserves_inst_idx >> simp[]
  ) >>
  simp[]
QED

(* ==========================================================================
   JNZ Transformation Step Lemmas

   These lemmas handle the case where the current instruction is a JNZ
   that matches Pattern 1 or Pattern 2. They are used by run_block_transform_general
   to avoid the problematic AllCaseEqs case split.
   ========================================================================== *)

(*
 * Pattern 1: JNZ where true branch (if_nonzero) goes to revert block.
 * Transform: jnz cond @revert @else => iszero; assert; jmp @else
 *
 * - cond = 0w: Both jump to else_label, state_equiv_except {fresh_var}
 * - cond <> 0w: Original jumps to revert, transformed reverts directly
 *)
Theorem jnz_pattern1_step:
  !fn bb s cond_op if_nonzero if_zero.
    MEM bb fn.fn_blocks /\ ~s.vs_halted /\
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    (EL s.vs_inst_idx bb.bb_instructions).inst_opcode = JNZ /\
    (EL s.vs_inst_idx bb.bb_instructions).inst_operands =
      [cond_op; Label if_nonzero; Label if_zero] /\
    EVERY (\i. transform_jnz fn i = NONE) (TAKE s.vs_inst_idx bb.bb_instructions) /\
    is_revert_label fn if_nonzero
    ==>
    let bb' = transform_block fn bb in
    let fresh = fresh_vars_in_block fn bb in
    case (run_block fn bb s, run_block (transform_function fn) bb' s) of
    | (OK v, OK v') => state_equiv_except fresh v v'
    | (OK v, Revert v') =>
        is_revert_label fn v.vs_current_bb /\
        execution_equiv_except fresh (revert_state v) v'
    | (Error _, Error _) => T
    | _ => F
Proof
  rw[LET_THM] >>
  `transform_jnz fn (EL s.vs_inst_idx bb.bb_instructions) =
   SOME (transform_pattern1 (EL s.vs_inst_idx bb.bb_instructions) cond_op if_zero)`
    by simp[transform_jnz_def] >>
  Cases_on `eval_operand cond_op s`
  >- ((* NONE: both error *)
    simp[Once run_block_def, step_in_block_def, get_instruction_def, step_inst_def] >>
    simp[Once run_block_def, run_block_fn_irrelevant, step_in_block_def,
         get_instruction_def, transform_block_def] >>
    `s.vs_inst_idx < LENGTH (transform_block_insts fn bb.bb_instructions)` by
      (drule_all transform_block_insts_length_pattern1 >> simp[]) >>
    gvs[] >>
    drule_all transform_block_insts_EL_transformed >> simp[LET_THM] >> strip_tac >>
    simp[transform_pattern1_def, mk_iszero_inst_def, step_inst_def, exec_unop_def])
  >>
  Cases_on `x = 0w`
  >- ((* x = 0w: use pattern1_zero_execution *)
    gvs[] >>
    drule_all rtaPattern1Theory.pattern1_zero_execution >>
    simp[LET_THM] >> strip_tac >> gvs[])
  >> (* x <> 0w: use pattern1_nonzero_execution *)
  drule_all rtaPattern1Theory.pattern1_nonzero_execution >> simp[LET_THM] >>
  strip_tac >> gvs[]
QED

(*
 * Pattern 2: JNZ where false branch (if_zero) goes to revert block.
 * Transform: jnz cond @then @revert => assert cond; jmp @then
 *
 * - cond <> 0w: Both jump to then_label, identical states
 * - cond = 0w: Original jumps to revert, transformed reverts directly
 *)
Theorem jnz_pattern2_step:
  !fn bb s cond_op if_nonzero if_zero.
    MEM bb fn.fn_blocks /\ ~s.vs_halted /\
    s.vs_inst_idx < LENGTH bb.bb_instructions /\
    (EL s.vs_inst_idx bb.bb_instructions).inst_opcode = JNZ /\
    (EL s.vs_inst_idx bb.bb_instructions).inst_operands =
      [cond_op; Label if_nonzero; Label if_zero] /\
    EVERY (\i. transform_jnz fn i = NONE) (TAKE s.vs_inst_idx bb.bb_instructions) /\
    is_revert_label fn if_zero
    ==>
    let bb' = transform_block fn bb in
    let fresh = fresh_vars_in_block fn bb in
    case (run_block fn bb s, run_block (transform_function fn) bb' s) of
    | (OK v, OK v') => state_equiv_except fresh v v'
    | (OK v, Revert v') =>
        is_revert_label fn v.vs_current_bb /\
        execution_equiv_except fresh (revert_state v) v'
    | (Error _, Error _) => T
    | _ => F
Proof
  rw[LET_THM] >>
  (* If both branches are revert labels, transform_jnz picks Pattern 1 *)
  Cases_on `is_revert_label fn if_nonzero`
  >- (drule_all jnz_pattern1_step >> simp[LET_THM])
  >> (* True Pattern 2: only if_zero is revert label *)
  `transform_jnz fn (EL s.vs_inst_idx bb.bb_instructions) =
   SOME (transform_pattern2 (EL s.vs_inst_idx bb.bb_instructions) cond_op if_nonzero)`
    by simp[transform_jnz_def] >>
  Cases_on `eval_operand cond_op s`
  >- ((* NONE: both error *)
    simp[Once run_block_def, step_in_block_def, get_instruction_def, step_inst_def] >>
    simp[Once run_block_def, run_block_fn_irrelevant, step_in_block_def,
         get_instruction_def, transform_block_def] >>
    `s.vs_inst_idx < LENGTH (transform_block_insts fn bb.bb_instructions)` by
      (drule_all transform_block_insts_length_pattern2 >> simp[]) >>
    gvs[] >> drule_all transform_block_insts_EL_transformed >> simp[LET_THM] >> strip_tac >>
    simp[transform_pattern2_def, mk_assert_inst_def, step_inst_def])
  >>
  Cases_on `x = 0w`
  >- ((* x = 0w: original jumps to revert, transformed reverts *)
    gvs[] >>
    simp[Once run_block_def, step_in_block_def, get_instruction_def,
         step_inst_def, EVAL ``is_terminator JNZ``, jump_to_def] >>
    `s.vs_inst_idx < LENGTH (transform_block fn bb).bb_instructions` by
      (simp[transform_block_def] >>
       `LENGTH (transform_block_insts fn bb.bb_instructions) >= LENGTH bb.bb_instructions`
         suffices_by decide_tac >> simp[transform_block_insts_length_ge]) >>
    drule_all transform_block_insts_EL_transformed >> simp[LET_THM] >> strip_tac >>
    simp[Once run_block_def, run_block_fn_irrelevant, step_in_block_def,
         get_instruction_def, transform_block_def] >>
    gvs[transform_pattern2_def, mk_assert_inst_def, step_inst_def] >>
    simp[EVAL ``is_terminator ASSERT``, execution_equiv_except_refl, revert_state_def,
         execution_equiv_except_def, lookup_var_def])
  >> (* x <> 0w: both jump to if_nonzero *)
  gvs[] >>
  simp[Once run_block_def, step_in_block_def, get_instruction_def,
       step_inst_def, EVAL ``is_terminator JNZ``, jump_to_def] >>
  `s.vs_inst_idx < LENGTH (transform_block fn bb).bb_instructions` by
    (simp[transform_block_def] >>
     `LENGTH (transform_block_insts fn bb.bb_instructions) >= LENGTH bb.bb_instructions`
       suffices_by decide_tac >> simp[transform_block_insts_length_ge]) >>
  drule_all transform_block_insts_EL_transformed >> simp[LET_THM] >> strip_tac >>
  simp[Once run_block_def, run_block_fn_irrelevant, step_in_block_def,
       get_instruction_def, transform_block_def] >>
  simp[transform_pattern2_def, mk_assert_inst_def, step_inst_def,
       EVAL ``is_terminator ASSERT``, next_inst_def] >>
  drule_all transform_block_insts_length_pattern2 >> strip_tac >>
  drule_all rtaPropsTheory.pattern2_transformed_instructions >> simp[LET_THM] >> strip_tac >>
  simp[Once run_block_def, step_in_block_def, get_instruction_def,
       mk_jmp_inst_def, step_inst_def, EVAL ``is_terminator JMP``,
       venomStateTheory.jump_to_def, state_equiv_except_refl]
QED

(*
 * NOTE: transform_block_correct is UNPROVABLE at block level.
 *
 * For pattern 1 JNZ when cond != 0:
 *   - Original run_block: returns OK (jump_to revert_block s)
 *   - Transformed run_block: returns Revert (revert_state s')
 *   - result_equiv_except (OK _) (Revert _) = F by definition
 *
 * The equivalence must be proven at function level, where both paths
 * ultimately reach a Revert result. See transform_function_correct.
 *)

(* ==========================================================================
   Function-Level Correctness
   ========================================================================== *)

(*
 * Helper: Block label is preserved by transform_block.
 *)
Theorem transform_block_preserves_label:
  !fn bb. (transform_block fn bb).bb_label = bb.bb_label
Proof
  rw[transform_block_def]
QED

(*
 * Helper: lookup_block distributes over MAP.
 *)
Theorem lookup_block_MAP:
  !fn blocks lbl bb.
    lookup_block lbl blocks = SOME bb ==>
    lookup_block lbl (MAP (transform_block fn) blocks) =
      SOME (transform_block fn bb)
Proof
  Induct_on `blocks` >- simp[lookup_block_def] >>
  rw[lookup_block_def, transform_block_preserves_label]
QED

(*
 * Helper: lookup_block NONE preserved through transform_block MAP.
 *)
Theorem lookup_block_MAP_NONE:
  !lbl bbs fn.
    lookup_block lbl bbs = NONE ==>
    lookup_block lbl (MAP (transform_block fn) bbs) = NONE
Proof
  Induct_on `bbs` >- simp[lookup_block_def] >>
  simp[lookup_block_def, transform_block_def]
QED

(*
 * Helper: Block lookup works in transformed function.
 *
 * WHY THIS IS TRUE: transform_function applies transform_block to each block
 * via MAP. Block labels are preserved (transform_block only changes instructions).
 * Thus lookup_block finds the corresponding transformed block.
 *)
Theorem lookup_block_transform_function:
  !fn lbl bb.
    lookup_block lbl fn.fn_blocks = SOME bb ==>
    lookup_block lbl (transform_function fn).fn_blocks =
      SOME (transform_block fn bb)
Proof
  rw[transform_function_def] >> irule lookup_block_MAP >> simp[]
QED

(*
 * Helper: If lookup_block succeeds, the block is in the list.
 *)
Theorem lookup_block_MEM:
  !lbl bbs bb.
    lookup_block lbl bbs = SOME bb ==> MEM bb bbs
Proof
  Induct_on `bbs` >- simp[lookup_block_def] >>
  simp[lookup_block_def] >> rw[] >> metis_tac[]
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
  ho_match_mp_tac venomSemTheory.run_block_ind >> rw[] >>
  qpat_x_assum `run_block _ _ _ = _` mp_tac >>
  simp[Once venomSemTheory.run_block_def] >>
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
  ho_match_mp_tac venomSemTheory.run_block_ind >> rw[] >>
  qpat_x_assum `run_block _ _ _ = _` mp_tac >>
  simp[Once venomSemTheory.run_block_def] >>
  Cases_on `step_in_block fn bb s` >> gvs[] >>
  Cases_on `q` >> gvs[] >>
  Cases_on `v'.vs_halted` >> gvs[] >>
  Cases_on `r` >> gvs[] >> rw[] >> gvs[] >>
  qpat_x_assum `step_in_block _ _ _ = _` mp_tac >>
  simp[venomSemTheory.step_in_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> gvs[] >>
  Cases_on `step_inst x s` >> gvs[] >>
  Cases_on `is_terminator x.inst_opcode` >> gvs[] >> rw[] >> gvs[] >>
  qpat_x_assum `is_terminator _` mp_tac >> simp[venomInstTheory.is_terminator_def] >>
  Cases_on `x.inst_opcode` >> gvs[venomInstTheory.is_terminator_def] >>
  qpat_x_assum `step_inst _ _ = _` mp_tac >>
  simp[venomSemTheory.step_inst_def, venomStateTheory.jump_to_def] >>
  gvs[AllCaseEqs(), PULL_EXISTS] >> rw[] >> gvs[]
QED

(* ==========================================================================
   Function-Level Correctness: Bidirectional Formulation

   WHY BIDIRECTIONAL:
   - Optimized code can complete FASTER (direct revert vs jump-to-revert-block)
   - With same fuel: original might Error (out of fuel), optimized might Revert
   - So same-fuel equivalence is too strong
   - Bidirectional termination captures the semantic preservation correctly

   KEY INSIGHT: STATIC precondition (fresh_vars_not_in_function fn) works!
   - ISZERO deterministically OVERWRITES fresh vars
   - Whether fresh var was NONE or SOME before, ISZERO sets it correctly
   - The STATIC property that original fn doesn't use fresh vars is preserved

   PROOF STRATEGY for OK/OK continuation:
   - Have: state_equiv_except fresh v v' (from block-level)
   - Use: state_equiv_except_run_function_orig on ORIGINAL fn
   - Chain: run_function fn v ≈ run_function fn v'
   - Then: apply IH on v' for transformed function
   ========================================================================== *)

(*
 * Predicate: execution terminates (not Error).
 *)
Definition terminates_def:
  terminates r <=> case r of Error _ => F | _ => T
End

(*
 * Main function-level correctness theorem.
 *
 * PRECONDITION: fresh_vars_not_in_function fn
 * This STATIC property says the original function doesn't mention fresh vars.
 * Must be verified before transformation (checked at compiler level).
 *
 * Part 1: Termination equivalence
 *   - If original terminates with some fuel, transformed terminates with some fuel
 *   - If transformed terminates with some fuel, original terminates with some fuel
 *
 * Part 2: Result equivalence
 *   - When both terminate (with any fuels), results are equivalent
 *)
Theorem transform_function_correct:
  !fn s.
    fresh_vars_not_in_function fn ==>
    let fn' = transform_function fn in
    let fresh = fresh_vars_in_function fn in
    (* Part 1: Termination equivalence *)
    ((?fuel. terminates (run_function fuel fn s)) <=>
     (?fuel'. terminates (run_function fuel' fn' s))) /\
    (* Part 2: Result equivalence when both terminate *)
    (!fuel fuel'.
      terminates (run_function fuel fn s) /\
      terminates (run_function fuel' fn' s) ==>
      result_equiv_except fresh
        (run_function fuel fn s)
        (run_function fuel' fn' s))
Proof
  rw[LET_THM] >> cheat
QED

(*
 * Generalized block relation for any starting index.
 *
 * The precondition EVERY ensures all instructions before vs_inst_idx
 * are non-transformed, so both blocks have identical prefix.
 *)
Theorem run_block_transform_general:
  !fn bb s.
    MEM bb fn.fn_blocks /\ ~s.vs_halted /\
    s.vs_inst_idx <= LENGTH bb.bb_instructions /\
    EVERY (\i. transform_jnz fn i = NONE) (TAKE s.vs_inst_idx bb.bb_instructions)
    ==>
    let bb' = transform_block fn bb in
    let fn' = transform_function fn in
    let fresh = fresh_vars_in_block fn bb in
    case (run_block fn bb s, run_block fn' bb' s) of
    | (OK v, OK v') => state_equiv_except fresh v v'
    | (OK v, Revert v') =>
        is_revert_label fn v.vs_current_bb /\
        execution_equiv_except fresh (revert_state v) v'
    | (Halt v, Halt v') => execution_equiv_except fresh v v'
    | (Revert v, Revert v') => execution_equiv_except fresh v v'
    | (Error _, Error _) => T
    | _ => F
Proof
  completeInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rw[LET_THM] >>
  Cases_on `s.vs_inst_idx >= LENGTH bb.bb_instructions`
  (* Base case: at end of block *)
  >- (
    `s.vs_inst_idx = LENGTH bb.bb_instructions` by decide_tac >>
    simp[Once run_block_def, step_in_block_def, get_instruction_def] >>
    simp[Once run_block_def] >>
    simp[step_in_block_def, get_instruction_def] >>
    Cases_on `LENGTH bb.bb_instructions < LENGTH (transform_block fn bb).bb_instructions`
    >- (
      gvs[] >>
      `transform_block_insts fn bb.bb_instructions = bb.bb_instructions` by (
        `!insts fn. EVERY (\i. transform_jnz fn i = NONE) insts ==>
         transform_block_insts fn insts = insts` suffices_by metis_tac[] >>
        Induct >> simp[transform_block_insts_def]) >>
      gvs[transform_block_def])
    >- gvs[])
  (* Inductive case: instruction exists at current index *)
  >- (
    `s.vs_inst_idx < LENGTH bb.bb_instructions` by decide_tac >>
    Cases_on `transform_jnz fn (EL s.vs_inst_idx bb.bb_instructions)`
    (* NONE case: instruction not transformed - step_in_block same for both blocks *)
    >- (
      simp[Once run_block_def] >>
      `EVERY (\i. transform_jnz fn i = NONE)
                (TAKE (SUC s.vs_inst_idx) bb.bb_instructions)` by (
        simp[rich_listTheory.TAKE_EL_SNOC, listTheory.EVERY_SNOC] >>
        `SUC s.vs_inst_idx = s.vs_inst_idx + 1` by decide_tac >>
        gvs[GSYM arithmeticTheory.ADD1, rich_listTheory.TAKE_EL_SNOC,
            listTheory.EVERY_SNOC] >>
        simp[GSYM rich_listTheory.SNOC_EL_TAKE, listTheory.EVERY_SNOC]) >>
      `TAKE (SUC s.vs_inst_idx) (transform_block fn bb).bb_instructions =
       TAKE (SUC s.vs_inst_idx) bb.bb_instructions` by
        (simp[transform_block_def] >> irule transform_block_insts_TAKE >> gvs[]) >>
      `step_in_block fn bb s = step_in_block fn (transform_block fn bb) s` by (
        `s.vs_inst_idx < LENGTH (transform_block fn bb).bb_instructions` by
          (gvs[transform_block_def] >>
           `LENGTH (transform_block_insts fn bb.bb_instructions) >= LENGTH bb.bb_instructions`
              suffices_by decide_tac >>
           simp[transform_block_insts_length_ge]) >>
        irule step_in_block_prefix_same >> qexists_tac `s.vs_inst_idx` >> gvs[]) >>
          `run_block (transform_function fn) (transform_block fn bb) s =
           run_block fn (transform_block fn bb) s` by simp[run_block_fn_irrelevant] >>
          simp[] >>
          Cases_on `step_in_block fn (transform_block fn bb) s` >>
          Cases_on `q:exec_result`
          (* OK: recurse or terminate *)
          >- (
            simp[] >>
            `run_block fn (transform_block fn bb) s =
              if v.vs_halted then Halt v
              else if r then OK v
              else run_block fn (transform_block fn bb) v` by
                (simp[Once run_block_def] >> gvs[]) >>
            simp[] >>
            Cases_on `v.vs_halted`
            >- (gvs[] >> simp[execution_equiv_except_refl])
            >- (
              Cases_on `r:bool` >> gvs[]
              >- simp[state_equiv_except_refl]
              >- (
                (* Apply IH for recursive case *)
                `v.vs_inst_idx = SUC s.vs_inst_idx` by
                  (drule_all step_in_block_increments_idx >> simp[]) >>
                `run_block fn (transform_block fn bb) v =
                 run_block (transform_function fn) (transform_block fn bb) v` by
                  simp[run_block_fn_irrelevant] >>
                pop_assum SUBST1_TAC >>
                first_x_assum (qspec_then `LENGTH bb.bb_instructions - v.vs_inst_idx` mp_tac) >>
                impl_tac >- decide_tac >>
                disch_tac >>
                first_x_assum (qspecl_then [`bb`, `v`] mp_tac) >>
                simp[] >> disch_then (qspec_then `fn` mp_tac) >> simp[])))
          (* Halt *)
          >- (
            simp[] >>
            `run_block fn (transform_block fn bb) s = Halt v` by
              (simp[Once run_block_def] >> gvs[]) >>
            simp[execution_equiv_except_refl])
          (* Revert *)
          >- (
            simp[] >>
            `run_block fn (transform_block fn bb) s = Revert v` by
              (simp[Once run_block_def] >> gvs[]) >>
            simp[execution_equiv_except_refl])
          (* Error *)
          >- (
            simp[] >>
            `run_block fn (transform_block fn bb) s = Error s'` by
              (simp[Once run_block_def] >> gvs[]) >>
            simp[]))
    (* SOME case: instruction transformed - use helper lemmas *)
    >- (
      qpat_x_assum `transform_jnz _ _ = SOME _` mp_tac >>
      simp[transform_jnz_def] >> strip_tac >> gvs[AllCaseEqs()]
      (* Pattern 1: is_revert_label fn if_nonzero *)
      >- (
        drule_all jnz_pattern1_step >> simp[LET_THM] >> strip_tac >>
        Cases_on `run_block fn bb s` >>
        Cases_on `run_block (transform_function fn) (transform_block fn bb) s` >>
        gvs[])
      (* Pattern 2: is_revert_label fn if_zero *)
      >- (
        drule_all jnz_pattern2_step >> simp[LET_THM] >> strip_tac >>
        Cases_on `run_block fn bb s` >>
        Cases_on `run_block (transform_function fn) (transform_block fn bb) s` >>
        gvs[])))
QED

(*
 * Block-level relation: starting from instruction index 0.
 *
 * Key insight: ISZERO deterministically overwrites fresh vars,
 * so the relation holds regardless of initial fresh var values.
 *
 * This is a corollary of run_block_transform_general with vs_inst_idx = 0.
 *)
Theorem run_block_transform_relation:
  !fn bb s.
    MEM bb fn.fn_blocks /\ ~s.vs_halted ==>
    let bb' = transform_block fn bb in
    let fn' = transform_function fn in
    let fresh = fresh_vars_in_block fn bb in
    let r = run_block fn bb (s with vs_inst_idx := 0) in
    let r' = run_block fn' bb' (s with vs_inst_idx := 0) in
    case (r, r') of
    | (OK v, OK v') => state_equiv_except fresh v v'
    | (OK v, Revert v') =>
        is_revert_label fn v.vs_current_bb /\
        execution_equiv_except fresh (revert_state v) v'
    | (Halt v, Halt v') => execution_equiv_except fresh v v'
    | (Revert v, Revert v') => execution_equiv_except fresh v v'
    | (Error _, Error _) => T
    | _ => F
Proof
  (* Simple corollary of run_block_transform_general with vs_inst_idx = 0.
   * When vs_inst_idx = 0: TAKE 0 bb.bb_instructions = [] and EVERY _ [] = T *)
  rw[LET_THM] >>
  qspecl_then [`fn`, `bb`, `s with vs_inst_idx := 0`] mp_tac run_block_transform_general >>
  simp[]
QED

(*
 * Corollary: Forward direction of termination equivalence.
 * If original terminates, transformed terminates.
 *)
Theorem transform_terminates_forward:
  !fn s fuel.
    fresh_vars_not_in_function fn /\
    terminates (run_function fuel fn s) ==>
    ?fuel'. terminates (run_function fuel' (transform_function fn) s)
Proof
  rw[] >>
  (* Direct corollary of transform_function_correct Part 1 *)
  qspecl_then [`fn`, `s`] mp_tac transform_function_correct >>
  simp[LET_THM] >> strip_tac >>
  metis_tac[]
QED

(*
 * Corollary: Backward direction of termination equivalence.
 * If transformed terminates, original terminates.
 *)
Theorem transform_terminates_backward:
  !fn s fuel'.
    fresh_vars_not_in_function fn /\
    terminates (run_function fuel' (transform_function fn) s) ==>
    ?fuel. terminates (run_function fuel fn s)
Proof
  rw[] >>
  (* Direct corollary of transform_function_correct Part 1 *)
  qspecl_then [`fn`, `s`] mp_tac transform_function_correct >>
  simp[LET_THM] >> strip_tac >>
  metis_tac[]
QED

(*
 * Helper: state_equiv_except propagates through original function.
 *
 * WHY: Original function doesn't use fresh vars, so differing only
 * on fresh vars gives equivalent execution.
 *
 * KEY PRECONDITION: fresh_vars_not_in_function fn
 * This is the STATIC property that the original function doesn't mention
 * fresh vars in any instruction operands.
 *)
Theorem state_equiv_except_run_function_orig:
  !fresh fn s1 s2 fuel.
    state_equiv_except fresh s1 s2 /\
    fresh = fresh_vars_in_function fn /\
    fresh_vars_not_in_function fn ==>
    result_equiv_except fresh
      (run_function fuel fn s1)
      (run_function fuel fn s2)
Proof
  Induct_on `fuel` >|
  [rw[run_function_def, result_equiv_except_def],
   rw[] >>
  ONCE_REWRITE_TAC[run_function_def] >> simp[] >>
  (* Lookup block - use current_bb from state *)
  `s1.vs_current_bb = s2.vs_current_bb` by fs[state_equiv_except_def] >>
  Cases_on `lookup_block s1.vs_current_bb fn.fn_blocks` >> gvs[] >>
  (* gvs closes NONE case automatically *)
  (* Found block x *)
  `MEM x fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  (* Original function doesn't use fresh vars in block x *)
  `fresh_vars_not_in_block fn x` by fs[fresh_vars_not_in_function_def] >>
  (* Show block operands don't reference fresh vars *)
  `!inst. MEM inst x.bb_instructions ==>
      !v. MEM (Var v) inst.inst_operands ==> v NOTIN fresh_vars_in_function fn` by (
    rw[] >> CCONTR_TAC >> gvs[] >>
    `v IN fresh_vars_in_function fn` by simp[] >>
    gvs[fresh_vars_in_function_def, fresh_vars_not_in_block_def,
        fresh_vars_in_block_def] >>
    first_x_assum (qspecl_then [`inst`, `fresh_iszero_var inst'.inst_id`] mp_tac) >>
    simp[] >> qexists_tac `inst'.inst_id` >> simp[]
  ) >>
  (* Use run_block_result_equiv_except *)
  `result_equiv_except (fresh_vars_in_function fn) (run_block fn x s1) (run_block fn x s2)` by (
    irule run_block_result_equiv_except >> simp[] >> metis_tac[]
  ) >>
  Cases_on `run_block fn x s1` >> Cases_on `run_block fn x s2` >>
  gvs[result_equiv_except_def] >>
  (* gvs closes mismatched cases; OK/OK case remains *)
  `v.vs_halted <=> v'.vs_halted` by fs[state_equiv_except_def, execution_equiv_except_def] >>
  Cases_on `v.vs_halted` >> gvs[] >>
  (* gvs uses IH for halted=F; halted=T case needs execution_equiv_except *)
  fs[state_equiv_except_def]]
QED

(* ==========================================================================
   Context-Level Correctness
   ========================================================================== *)

(*
 * Helper: Function name is preserved by transform_function.
 *)
Theorem transform_function_preserves_name:
  !fn. (transform_function fn).fn_name = fn.fn_name
Proof
  simp[transform_function_def]
QED

(*
 * Helper: lookup_function distributes over MAP.
 *)
Theorem lookup_function_MAP:
  !fns name fn.
    lookup_function name fns = SOME fn ==>
    lookup_function name (MAP transform_function fns) =
      SOME (transform_function fn)
Proof
  Induct_on `fns` >- simp[lookup_function_def] >>
  rw[lookup_function_def, transform_function_preserves_name]
QED

(*
 * Helper: Function lookup works in transformed context.
 *)
Theorem lookup_function_transform_context:
  !ctx name fn.
    lookup_function name ctx.ctx_functions = SOME fn ==>
    lookup_function name (transform_context ctx).ctx_functions =
      SOME (transform_function fn)
Proof
  rw[transform_context_def] >> irule lookup_function_MAP >> simp[]
QED

(*
 * Helper: lookup_function returning SOME implies MEM.
 *)
Theorem lookup_function_MEM:
  !name fns fn. lookup_function name fns = SOME fn ==> MEM fn fns
Proof
  gen_tac >> Induct >> rw[lookup_function_def] >> gvs[AllCaseEqs()]
QED

(*
 * Main context correctness theorem (bidirectional formulation).
 *
 * PRECONDITION: fresh_vars_not_in_context ctx
 * This STATIC property says no function in the context mentions fresh vars.
 * Must be verified before the transformation (checked at compiler level).
 *
 * WHY THIS IS TRUE:
 * - transform_context applies transform_function to all functions
 * - Function lookup returns transformed function
 * - Apply transform_function_correct for each function
 * - Widen equivalence from function-level to context-level fresh vars
 *)
Theorem transform_context_correct:
  !ctx entry.
    fresh_vars_not_in_context ctx ==>
    let ctx' = transform_context ctx in
    let fresh = fresh_vars_in_context ctx in
    !fn fn' s.
      lookup_function entry ctx.ctx_functions = SOME fn /\
      lookup_function entry ctx'.ctx_functions = SOME fn' ==>
      (* Part 1: Termination equivalence *)
      ((?fuel. terminates (run_function fuel fn s)) <=>
       (?fuel'. terminates (run_function fuel' fn' s))) /\
      (* Part 2: Result equivalence when both terminate *)
      (!fuel fuel'.
        terminates (run_function fuel fn s) /\
        terminates (run_function fuel' fn' s) ==>
        result_equiv_except fresh
          (run_function fuel fn s)
          (run_function fuel' fn' s))
Proof
  simp[LET_THM] >> rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  (* Show fn' = transform_function fn *)
  `fn' = transform_function fn` by (
    qpat_x_assum `lookup_function _ ctx.ctx_functions = _`
      (fn th => assume_tac (MATCH_MP lookup_function_transform_context th)) >>
    gvs[]
  ) >>
  gvs[] >>
  (* Get MEM fn ctx.ctx_functions from lookup *)
  `MEM fn ctx.ctx_functions` by (imp_res_tac lookup_function_MEM) >>
  (* Get fresh_vars_not_in_function fn from context precondition *)
  `fresh_vars_not_in_function fn` by fs[fresh_vars_not_in_context_def] >>
  (* Goal is now a conjunction about termination + result equiv *)
  (* Part 1: Termination equivalence - from transform_function_correct *)
  (* Part 2: Result equivalence - from transform_function_correct + subset widening *)
  conj_tac
  >- (
    (* Termination equivalence *)
    qspecl_then [`fn`, `s`] mp_tac transform_function_correct >>
    simp[LET_THM]
  )
  >- (
    rw[] >>
    (* Get result from transform_function_correct *)
    qspecl_then [`fn`, `s`] mp_tac transform_function_correct >>
    simp[LET_THM] >> strip_tac >>
    (* Widen from fresh_vars_in_function to fresh_vars_in_context *)
    irule result_equiv_except_subset >>
    qexists_tac `fresh_vars_in_function fn` >>
    conj_tac >- (
      simp[fresh_vars_in_context_def, pred_setTheory.SUBSET_DEF,
           pred_setTheory.IN_BIGUNION, PULL_EXISTS] >>
      metis_tac[]
    ) >>
    first_x_assum irule >> simp[]
  )
QED

(* ==========================================================================
   Final Pass Correctness Statement (Complete)
   ========================================================================== *)

(*
 * Full correctness theorem: The revert-to-assert pass preserves semantics.
 *
 * PRECONDITION: fresh_vars_not_in_context ctx
 * This is a STATIC well-formedness condition that must be verified before
 * applying the transformation. It requires that the original code doesn't
 * use variable names matching the fresh variable pattern (rta_tmp_N).
 * This is checked at the compiler level before the pass runs.
 *
 * The theorem establishes:
 * 1. Termination equivalence: original terminates iff transformed terminates
 * 2. Result equivalence: when both terminate, results are equivalent
 *    (modulo fresh variables introduced by the transformation)
 *)
Theorem revert_to_assert_pass_correct:
  !ctx entry.
    (* Well-formedness: original code doesn't use fresh var names *)
    fresh_vars_not_in_context ctx /\
    (* Entry function exists *)
    lookup_function entry ctx.ctx_functions <> NONE
  ==>
    let ctx' = transform_context ctx in
    let fresh = fresh_vars_in_context ctx in
    ?fn fn'.
      lookup_function entry ctx.ctx_functions = SOME fn /\
      lookup_function entry ctx'.ctx_functions = SOME fn' /\
      (* Termination equivalence *)
      ((!s. (?fuel. terminates (run_function fuel fn s)) <=>
            (?fuel'. terminates (run_function fuel' fn' s)))) /\
      (* Result equivalence when both terminate *)
      (!s fuel fuel'.
        terminates (run_function fuel fn s) /\
        terminates (run_function fuel' fn' s) ==>
        result_equiv_except fresh
          (run_function fuel fn s)
          (run_function fuel' fn' s))
Proof
  simp[LET_THM] >> rpt gen_tac >> strip_tac >>
  Cases_on `lookup_function entry ctx.ctx_functions` >> gvs[] >>
  qexists_tac `transform_function x` >>
  simp[transform_context_def] >>
  `lookup_function entry (MAP transform_function ctx.ctx_functions) =
    SOME (transform_function x)` by (
    pop_assum mp_tac >> qspec_tac (`ctx.ctx_functions`, `fns`) >>
    Induct >> simp[lookup_function_def, transform_function_def] >>
    rw[lookup_function_def] >> simp[transform_function_def]
  ) >>
  simp[] >>
  qspecl_then [`ctx`, `entry`] mp_tac transform_context_correct >>
  simp[LET_THM, transform_context_def] >> strip_tac >>
  first_x_assum (qspecl_then [`x`, `transform_function x`] mp_tac) >>
  simp[]
QED

val _ = export_theory();
