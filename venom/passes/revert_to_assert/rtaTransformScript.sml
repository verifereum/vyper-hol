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
  rtaCorrect rtaProps rtaDefs stateEquiv venomSemProps venomSem venomInst venomState list rich_list

(* ==========================================================================
   Block-Level Correctness
   ========================================================================== *)

(* NOTE: General step_in_block/run_block helpers are in venomSemPropsTheory:
 * - step_in_block_fn_irrelevant
 * - run_block_fn_irrelevant
 * - step_in_block_increments_idx
 * - run_block_OK_not_halted
 * - run_block_OK_inst_idx_0
 * - step_in_block_prefix_same
 * - lookup_block_MEM
 * - lookup_function_MEM
 *
 * NOTE: transform_block_insts helper theorems are now in rtaPropsTheory:
 * - transform_block_insts_TAKE_DROP
 * - transform_block_insts_TAKE
 * - transform_block_insts_EL_transformed
 * - transform_block_insts_length_ge
 * - transform_block_insts_length_pattern1
 * - transform_block_insts_length_pattern2
 *)

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

(* NOTE: lookup_block_MEM is now in venomSemPropsTheory *)

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

(* NOTE: terminates_def is now in rtaDefsTheory *)

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

(*
 * Helper: Forward simulation - if original terminates with fuel n,
 * transformed terminates with fuel n and results are equivalent.
 *
 * PRECONDITIONS:
 * - fresh_vars_not_in_function fn: original function doesn't use fresh vars
 * - s.vs_inst_idx = 0: starting at beginning of block (normal execution)
 * - ~s.vs_halted: not already halted (normal execution)
 *
 * These are maintained by the induction:
 * - After run_block OK v: v.vs_inst_idx = 0 (by run_block_OK_inst_idx_0)
 * - After run_block OK v: ~v.vs_halted (by run_block_OK_not_halted)
 *)
Theorem run_function_forward_simulation:
  !fuel fn s.
    fresh_vars_not_in_function fn /\
    s.vs_inst_idx = 0 /\
    ~s.vs_halted ==>
    let fn' = transform_function fn in
    let fresh = fresh_vars_in_function fn in
    terminates (run_function fuel fn s) ==>
    terminates (run_function fuel fn' s) /\
    result_equiv_except fresh (run_function fuel fn s) (run_function fuel fn' s)
Proof
  Induct_on `fuel`
  >- simp[run_function_def, terminates_def, LET_THM]
  >- (
    simp[LET_THM] >> rpt gen_tac >> strip_tac >>
    strip_tac >> qpat_x_assum `terminates (run_function (SUC _) fn _)` mp_tac >>
    simp[Once run_function_def] >>
    Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >- simp[terminates_def] >>
    simp[] >> Cases_on `run_block fn x s` >> simp[]
    (* OK case *)
    >- (
      strip_tac >> `MEM x fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
      `~v.vs_halted` by (imp_res_tac run_block_OK_not_halted) >> gvs[] >>
      `lookup_block s.vs_current_bb (transform_function fn).fn_blocks =
       SOME (transform_block fn x)` by (irule lookup_block_transform_function >> simp[]) >>
      qspecl_then [`fn`, `x`, `s`] mp_tac run_block_transform_general >>
      impl_tac >- simp[] >>
      simp[LET_THM] >> Cases_on `run_block (transform_function fn) (transform_block fn x) s` >> simp[]
      (* OK/OK: chain through original, apply IH *)
      >- (
        strip_tac >>
        `v'.vs_inst_idx = 0` by (imp_res_tac run_block_OK_inst_idx_0) >>
        `~v'.vs_halted` by (imp_res_tac run_block_OK_not_halted) >>
        `v.vs_inst_idx = 0` by (imp_res_tac run_block_OK_inst_idx_0) >>
        `state_equiv_except (fresh_vars_in_function fn) v v'` by (
          irule state_equiv_except_subset >> qexists_tac `fresh_vars_in_block fn x` >>
          conj_tac >- (
            simp[fresh_vars_in_function_def, pred_setTheory.SUBSET_DEF,
                 pred_setTheory.IN_BIGUNION] >> rpt strip_tac >>
            qexists_tac `fresh_vars_in_block fn x` >> simp[] >>
            qexists_tac `x` >> simp[]
          ) >> simp[]
        ) >>
        `result_equiv_except (fresh_vars_in_function fn)
           (run_function fuel fn v) (run_function fuel fn v')` by (
          qspecl_then [`fresh_vars_in_function fn`, `fn`, `v`, `v'`, `fuel`] mp_tac
            state_equiv_except_run_function_orig >> simp[]
        ) >>
        `terminates (run_function fuel fn v')` by (
          Cases_on `run_function fuel fn v` >> Cases_on `run_function fuel fn v'` >>
          gvs[terminates_def, result_equiv_except_def]
        ) >>
        first_x_assum (qspecl_then [`fn`, `v'`] mp_tac) >> simp[] >> strip_tac >>
        conj_tac
        >- simp[Once run_function_def]
        >- (
          `result_equiv_except (fresh_vars_in_function fn)
             (run_function fuel fn v) (run_function fuel (transform_function fn) v')` by (
            irule result_equiv_except_trans >> qexists_tac `run_function fuel fn v'` >> simp[]
          ) >>
          PURE_ONCE_REWRITE_TAC[run_function_def] >> simp[]
        )
      )
      (* OK/Revert: original jumps to revert block, transformed reverts directly *)
      >- (
        strip_tac >>
        Cases_on `fuel` >- fs[run_function_def, terminates_def] >- (
          `?revert_bb. lookup_block v.vs_current_bb fn.fn_blocks = SOME revert_bb /\
                       is_simple_revert_block revert_bb` by (
            fs[is_revert_label_def] >> Cases_on `lookup_block v.vs_current_bb fn.fn_blocks` >> fs[]
          ) >>
          `v.vs_inst_idx = 0` by (imp_res_tac run_block_OK_inst_idx_0) >>
          qspecl_then [`fn`, `v`, `SUC n`, `revert_bb`] mp_tac run_function_at_simple_revert >> simp[] >>
          `v with vs_inst_idx := 0 = v` by simp[venom_state_component_equality] >>
          pop_assum SUBST_ALL_TAC >> simp[] >> strip_tac >>
          `run_function (SUC (SUC n)) fn s = Revert (revert_state v)` by simp[Once run_function_def] >>
          `run_function (SUC (SUC n)) (transform_function fn) s = Revert v'` by simp[Once run_function_def] >>
          simp[terminates_def, result_equiv_except_def] >>
          irule execution_equiv_except_subset >> qexists_tac `fresh_vars_in_block fn x` >>
          conj_tac >- (
            simp[fresh_vars_in_function_def, pred_setTheory.SUBSET_DEF,
                 pred_setTheory.IN_BIGUNION] >> rpt strip_tac >>
            qexists_tac `fresh_vars_in_block fn x` >> simp[] >> qexists_tac `x` >> simp[]
          ) >> simp[]
        )
      )
    )
    (* Halt case *)
    >- (
      strip_tac >> `MEM x fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
      `lookup_block s.vs_current_bb (transform_function fn).fn_blocks =
       SOME (transform_block fn x)` by (irule lookup_block_transform_function >> simp[]) >>
      qspecl_then [`fn`, `x`, `s`] mp_tac run_block_transform_general >> simp[LET_THM] >>
      Cases_on `run_block (transform_function fn) (transform_block fn x) s` >> simp[] >>
      strip_tac >> simp[Once run_function_def, terminates_def] >>
      simp[Once run_function_def, result_equiv_except_def] >>
      simp[Once run_function_def, result_equiv_except_def] >>
      irule execution_equiv_except_subset >> qexists_tac `fresh_vars_in_block fn x` >>
      conj_tac >- (
        simp[fresh_vars_in_function_def, pred_setTheory.SUBSET_DEF,
             pred_setTheory.IN_BIGUNION] >> rpt strip_tac >>
        qexists_tac `fresh_vars_in_block fn x` >> simp[] >> qexists_tac `x` >> simp[]
      ) >> simp[]
    )
    (* Revert case *)
    >- (
      strip_tac >> `MEM x fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
      `lookup_block s.vs_current_bb (transform_function fn).fn_blocks =
       SOME (transform_block fn x)` by (irule lookup_block_transform_function >> simp[]) >>
      qspecl_then [`fn`, `x`, `s`] mp_tac run_block_transform_general >> simp[LET_THM] >>
      Cases_on `run_block (transform_function fn) (transform_block fn x) s` >> simp[] >>
      strip_tac >> simp[Once run_function_def, terminates_def] >>
      simp[Once run_function_def, result_equiv_except_def] >>
      simp[Once run_function_def, result_equiv_except_def] >>
      irule execution_equiv_except_subset >> qexists_tac `fresh_vars_in_block fn x` >>
      conj_tac >- (
        simp[fresh_vars_in_function_def, pred_setTheory.SUBSET_DEF,
             pred_setTheory.IN_BIGUNION] >> rpt strip_tac >>
        qexists_tac `fresh_vars_in_block fn x` >> simp[] >> qexists_tac `x` >> simp[]
      ) >> simp[]
    )
    (* Error case: terminates(Error) = F, premise false *)
    >- simp[terminates_def]
  )
QED

(* ==========================================================================
   Helper Lemmas for Function-Level Proofs
   ========================================================================== *)

(*
 * Helper: fresh_vars_in_block is subset of fresh_vars_in_function.
 * Used to widen state_equiv_except from block-level to function-level.
 *)
Theorem fresh_vars_in_block_subset_function:
  !fn bb. MEM bb fn.fn_blocks ==>
    fresh_vars_in_block fn bb SUBSET fresh_vars_in_function fn
Proof
  rw[fresh_vars_in_function_def, pred_setTheory.SUBSET_DEF,
     pred_setTheory.IN_BIGUNION] >>
  qexists_tac `fresh_vars_in_block fn bb` >> simp[] >>
  qexists_tac `bb` >> simp[]
QED

(*
 * Helper: result_equiv_except preserves terminates.
 * If results are equivalent and one terminates, so does the other.
 *)
Theorem terminates_result_equiv:
  !fresh r1 r2.
    result_equiv_except fresh r1 r2 ==>
    (terminates r1 <=> terminates r2)
Proof
  rw[] >> Cases_on `r1` >> Cases_on `r2` >>
  gvs[terminates_def, result_equiv_except_def]
QED

(*
 * Helper: Fuel monotonicity - once execution terminates, more fuel doesn't
 * change the result. This is key for transform_function_correct Part 2.
 *
 * WHY: If run_function terminates (Halt/Revert) with fuel n, it will produce
 * the same result with fuel n+k. The execution already finished before
 * using all the fuel.
 *)
Theorem run_function_fuel_mono:
  !fuel fn s k.
    terminates (run_function fuel fn s) ==>
    run_function (fuel + k) fn s = run_function fuel fn s
Proof
  Induct_on `fuel`
  >- simp[run_function_def, terminates_def]
  >- (
    rpt gen_tac >> strip_tac >>
    `SUC fuel + k = SUC (fuel + k)` by decide_tac >> pop_assum SUBST1_TAC >>
    simp[Once run_function_def, SimpLHS] >>
    simp[Once run_function_def, SimpRHS] >>
    Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
    Cases_on `run_block fn x s` >> simp[] >>
    Cases_on `v.vs_halted` >> simp[] >>
    first_x_assum irule >>
    qpat_x_assum `terminates _` mp_tac >> simp[Once run_function_def]
  )
QED

(*
 * Helper: Backward termination - if transformed terminates,
 * original also terminates (possibly with more fuel).
 *
 * PRECONDITIONS: Same as forward_simulation - needed for run_block_transform_general.
 *
 * KEY INSIGHT: Transformed uses <= fuel than original (direct revert saves a step).
 * If transformed terminates with fuel N, original terminates with fuel <= N+1.
 *)
Theorem run_function_backward_terminates:
  !fuel fn s.
    fresh_vars_not_in_function fn /\
    s.vs_inst_idx = 0 /\
    ~s.vs_halted ==>
    let fn' = transform_function fn in
    terminates (run_function fuel fn' s) ==>
    ?fuel'. terminates (run_function fuel' fn s)
Proof
  Induct_on `fuel`
  >- simp[run_function_def, terminates_def, LET_THM]
  >- (
    simp[LET_THM] >> rpt gen_tac >> strip_tac >> strip_tac >>
    qpat_x_assum `terminates (run_function _ _ _)` mp_tac >>
    simp[Once run_function_def] >>
    Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
    >- (
      `lookup_block s.vs_current_bb (transform_function fn).fn_blocks = NONE` by
        (simp[transform_function_def] >> irule lookup_block_MAP_NONE >> simp[]) >>
      simp[terminates_def]
    )
    >- (
      `lookup_block s.vs_current_bb (transform_function fn).fn_blocks =
       SOME (transform_block fn x)` by
        (irule lookup_block_transform_function >> simp[]) >>
      simp[] >>
      `MEM x fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
      qspecl_then [`fn`, `x`, `s`] mp_tac run_block_transform_general >>
      simp[LET_THM] >> strip_tac >>
      Cases_on `run_block (transform_function fn) (transform_block fn x) s` >>
      simp[terminates_def]
      >- ( (* OK case *)
        Cases_on `run_block fn x s` >> gvs[] >>
        strip_tac >> Cases_on `v.vs_halted`
        >- ( (* halted - contradiction *)
          `v'.vs_halted = v.vs_halted` by
            fs[state_equiv_except_def, execution_equiv_except_def] >>
          `~v'.vs_halted` by (imp_res_tac run_block_OK_not_halted) >> gvs[]
        )
        >- ( (* continuation *)
          `~v'.vs_halted` by (imp_res_tac run_block_OK_not_halted) >>
          `v.vs_inst_idx = 0` by (imp_res_tac run_block_OK_inst_idx_0) >>
          `v'.vs_inst_idx = 0` by (imp_res_tac run_block_OK_inst_idx_0) >>
          `terminates (run_function fuel (transform_function fn) v)` by
            gvs[terminates_def] >>
          first_x_assum (qspecl_then [`fn`, `v`] mp_tac) >> simp[] >>
          strip_tac >>
          `state_equiv_except (fresh_vars_in_function fn) v' v` by (
            irule state_equiv_except_subset >>
            qexists_tac `fresh_vars_in_block fn x` >>
            conj_tac >- (imp_res_tac fresh_vars_in_block_subset_function >> simp[]) >>
            simp[]
          ) >>
          qspecl_then [`fresh_vars_in_function fn`, `fn`, `v'`, `v`, `fuel'`] mp_tac
            state_equiv_except_run_function_orig >>
          impl_tac >- simp[] >> strip_tac >>
          `terminates (run_function fuel' fn v')` by
            (drule_all terminates_result_equiv >> simp[]) >>
          qexists_tac `SUC fuel'` >>
          simp[Once run_function_def, terminates_def] >>
          gvs[terminates_def]
        )
      )
      >- ( (* Halt case *)
        Cases_on `run_block fn x s` >> gvs[] >>
        qexists_tac `SUC 0` >> simp[run_function_def, terminates_def]
      )
      >- ( (* Revert case *)
        Cases_on `run_block fn x s` >> gvs[]
        >- ( (* OK/Revert - original jumps to revert block *)
          `v'.vs_inst_idx = 0` by (imp_res_tac run_block_OK_inst_idx_0) >>
          `?revert_bb. lookup_block v'.vs_current_bb fn.fn_blocks = SOME revert_bb /\
                       is_simple_revert_block revert_bb` by (
            fs[is_revert_label_def] >>
            Cases_on `lookup_block v'.vs_current_bb fn.fn_blocks` >> fs[]
          ) >>
          qspecl_then [`fn`, `v'`, `1`, `revert_bb`] mp_tac
            run_function_at_simple_revert >> simp[] >>
          `v' with vs_inst_idx := 0 = v'` by simp[venom_state_component_equality] >>
          pop_assum SUBST_ALL_TAC >> simp[] >> strip_tac >>
          `~v'.vs_halted` by (imp_res_tac run_block_OK_not_halted) >>
          qexists_tac `SUC (SUC 0)` >>
          simp[Once run_function_def, terminates_def]
        )
        >- ( (* Revert/Revert *)
          qexists_tac `SUC 0` >> simp[run_function_def, terminates_def]
        )
      )
    )
  )
QED

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
    fresh_vars_not_in_function fn /\
    s.vs_inst_idx = 0 /\
    ~s.vs_halted ==>
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
  rw[LET_THM]
  >- (
    EQ_TAC
    >- (strip_tac >> drule_all run_function_forward_simulation >>
        simp[LET_THM] >> metis_tac[])
    >- (strip_tac >> drule_all run_function_backward_terminates >>
        simp[LET_THM] >> metis_tac[])
  )
  >- (
    `run_function (fuel + fuel') fn s = run_function fuel fn s` by
      (irule run_function_fuel_mono >> simp[]) >>
    `run_function (fuel' + fuel) (transform_function fn) s =
     run_function fuel' (transform_function fn) s` by
      (irule run_function_fuel_mono >> simp[]) >>
    `fuel + fuel' = fuel' + fuel` by decide_tac >>
    `terminates (run_function (fuel + fuel') fn s)` by metis_tac[] >>
    qspecl_then [`fuel + fuel'`, `fn`, `s`] mp_tac run_function_forward_simulation >>
    simp[LET_THM] >> strip_tac >> gvs[]
  )
QED

(*
 * Corollary: Forward direction of termination equivalence.
 * If original terminates, transformed terminates.
 *)
Theorem transform_terminates_forward:
  !fn s fuel.
    fresh_vars_not_in_function fn /\
    s.vs_inst_idx = 0 /\
    ~s.vs_halted /\
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
    s.vs_inst_idx = 0 /\
    ~s.vs_halted /\
    terminates (run_function fuel' (transform_function fn) s) ==>
    ?fuel. terminates (run_function fuel fn s)
Proof
  rw[] >>
  (* Direct corollary of transform_function_correct Part 1 *)
  qspecl_then [`fn`, `s`] mp_tac transform_function_correct >>
  simp[LET_THM] >> strip_tac >>
  metis_tac[]
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

(* NOTE: lookup_function_MEM is now in venomSemPropsTheory *)

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
      lookup_function entry ctx'.ctx_functions = SOME fn' /\
      s.vs_inst_idx = 0 /\
      ~s.vs_halted ==>
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
      (* Termination equivalence (for states starting at block beginning) *)
      ((!s. s.vs_inst_idx = 0 /\ ~s.vs_halted ==>
            ((?fuel. terminates (run_function fuel fn s)) <=>
             (?fuel'. terminates (run_function fuel' fn' s))))) /\
      (* Result equivalence when both terminate *)
      (!s fuel fuel'.
        s.vs_inst_idx = 0 /\ ~s.vs_halted /\
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
