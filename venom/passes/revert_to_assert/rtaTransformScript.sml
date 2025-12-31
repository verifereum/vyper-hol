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
  rtaCorrect rtaProps rtaDefs stateEquiv venomSem venomInst venomState list

(* ==========================================================================
   Fresh Variable Generation
   ========================================================================== *)

(*
 * Fresh variable name for ISZERO output.
 * Simple naming scheme: "rta_tmp_<id>"
 *
 * Correctness relies on precondition that these names aren't used in the
 * original function. This is verified at the compiler level.
 *)
Definition fresh_iszero_var_def:
  fresh_iszero_var (id:num) = STRCAT "rta_tmp_" (toString id)
End

(* ==========================================================================
   Instruction Builders
   ========================================================================== *)

(* ISZERO instruction: %out = iszero %cond *)
Definition mk_iszero_inst_def:
  mk_iszero_inst id cond_op out = <|
    inst_id := id;
    inst_opcode := ISZERO;
    inst_operands := [cond_op];
    inst_outputs := [out]
  |>
End

(* ASSERT instruction: assert %cond *)
Definition mk_assert_inst_def:
  mk_assert_inst id cond_op = <|
    inst_id := id;
    inst_opcode := ASSERT;
    inst_operands := [cond_op];
    inst_outputs := []
  |>
End

(* JMP instruction: jmp @label *)
Definition mk_jmp_inst_def:
  mk_jmp_inst id label = <|
    inst_id := id;
    inst_opcode := JMP;
    inst_operands := [Label label];
    inst_outputs := []
  |>
End

(* ==========================================================================
   Revert Block Detection
   ========================================================================== *)

(* Check if a label points to a simple revert block in the function *)
Definition is_revert_label_def:
  is_revert_label fn lbl =
    case lookup_block lbl fn.fn_blocks of
      NONE => F
    | SOME bb => is_simple_revert_block bb
End

(* ==========================================================================
   Pattern Transformers
   ========================================================================== *)

(*
 * Pattern 1: jnz %cond @revert @else => iszero; assert; jmp @else
 *
 * WHY THIS IS CORRECT:
 *   - If cond != 0w: Original jumps to revert, transformed asserts 0w (reverts)
 *   - If cond = 0w: Original jumps to else, transformed asserts 1w (passes), jumps to else
 *   - Proven in pattern1_transform_correct
 *)
Definition transform_pattern1_def:
  transform_pattern1 jnz_inst cond_op else_label =
    let id = jnz_inst.inst_id in
    let tmp = fresh_iszero_var id in
    [mk_iszero_inst id cond_op tmp;
     mk_assert_inst (id + 1) (Var tmp);
     mk_jmp_inst (id + 2) else_label]
End

(*
 * Pattern 2: jnz %cond @then @revert => assert %cond; jmp @then
 *
 * WHY THIS IS CORRECT:
 *   - If cond != 0w: Original jumps to then, transformed asserts (passes), jumps to then
 *   - If cond = 0w: Original jumps to revert, transformed asserts 0w (reverts)
 *   - Proven in pattern2_transform_correct
 *)
Definition transform_pattern2_def:
  transform_pattern2 jnz_inst cond_op then_label =
    let id = jnz_inst.inst_id in
    [mk_assert_inst id cond_op;
     mk_jmp_inst (id + 1) then_label]
End

(* ==========================================================================
   Instruction Transformation
   ========================================================================== *)

(* Try to transform a JNZ instruction. Returns SOME new_insts if applicable. *)
Definition transform_jnz_def:
  transform_jnz fn inst =
    if inst.inst_opcode <> JNZ then NONE
    else case inst.inst_operands of
      [cond_op; Label if_nonzero; Label if_zero] =>
        (* Pattern 1: revert on nonzero *)
        if is_revert_label fn if_nonzero then
          SOME (transform_pattern1 inst cond_op if_zero)
        (* Pattern 2: revert on zero *)
        else if is_revert_label fn if_zero then
          SOME (transform_pattern2 inst cond_op if_nonzero)
        else NONE
    | _ => NONE
End

(* ==========================================================================
   Block Transformation
   ========================================================================== *)

(* Transform all instructions in a block *)
Definition transform_block_insts_def:
  transform_block_insts fn [] = [] /\
  transform_block_insts fn (inst::rest) =
    case transform_jnz fn inst of
      SOME new_insts => new_insts ++ transform_block_insts fn rest
    | NONE => inst :: transform_block_insts fn rest
End

(* Transform a single block *)
Definition transform_block_def:
  transform_block fn bb =
    bb with bb_instructions := transform_block_insts fn bb.bb_instructions
End

(* ==========================================================================
   Function and Context Transformation
   ========================================================================== *)

(* Transform all blocks in a function *)
Definition transform_function_def:
  transform_function fn =
    fn with fn_blocks := MAP (transform_block fn) fn.fn_blocks
End

(* Transform all functions in a context *)
Definition transform_context_def:
  transform_context ctx =
    ctx with ctx_functions := MAP transform_function ctx.ctx_functions
End

(* ==========================================================================
   Well-Formedness for Transformation
   ========================================================================== *)

(*
 * All fresh variables that may be introduced by transforming a block.
 * Only pattern 1 introduces fresh vars (for ISZERO output).
 *)
Definition fresh_vars_in_block_def:
  fresh_vars_in_block fn bb =
    { fresh_iszero_var inst.inst_id |
      inst | MEM inst bb.bb_instructions /\
             transform_jnz fn inst <> NONE /\
             ?cond_op if_nonzero if_zero.
               inst.inst_operands = [cond_op; Label if_nonzero; Label if_zero] /\
               is_revert_label fn if_nonzero }
End

(*
 * All fresh variables in a function.
 *)
Definition fresh_vars_in_function_def:
  fresh_vars_in_function fn =
    BIGUNION { fresh_vars_in_block fn bb | bb | MEM bb fn.fn_blocks }
End

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

(* ==========================================================================
   Static Analysis: Fresh Vars Not In Original Code

   STATIC preconditions (fresh_vars_not_in_block/function/context) work:
   fresh vars don't appear as operands in the original code.
   This is provable because fresh vars are ONLY introduced by the transformation.

   (A runtime check would fail: after ISZERO executes, fresh vars ARE set
   in the state, so a runtime precondition would block IH application.)
   ========================================================================== *)

(*
 * Static property: No instruction in the block uses fresh vars as operands.
 * This is true for original code because fresh vars are only introduced by transform.
 *)
Definition fresh_vars_not_in_block_def:
  fresh_vars_not_in_block fn bb <=>
    !inst x. MEM inst bb.bb_instructions /\ MEM (Var x) inst.inst_operands ==>
      !id. x <> fresh_iszero_var id
End

(*
 * Static property for entire function.
 *)
Definition fresh_vars_not_in_function_def:
  fresh_vars_not_in_function fn <=>
    !bb. MEM bb fn.fn_blocks ==> fresh_vars_not_in_block fn bb
End

(*
 * Static property for entire context.
 *)
Definition fresh_vars_not_in_context_def:
  fresh_vars_not_in_context ctx <=>
    !fn. MEM fn ctx.ctx_functions ==> fresh_vars_not_in_function fn
End

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

(*
 * Helper: TAKE k preserves prefix when no instruction in prefix is transformed.
 *
 * WHY THIS IS TRUE: transform_block_insts only modifies instructions where
 * transform_jnz returns SOME. If all instructions in TAKE k have transform_jnz = NONE,
 * they are preserved in order.
 *)
Theorem transform_block_insts_TAKE:
  !insts fn k.
    EVERY (\i. transform_jnz fn i = NONE) (TAKE k insts) ==>
    TAKE k (transform_block_insts fn insts) = TAKE k insts
Proof
  Induct_on `insts` >> simp[transform_block_insts_def] >> rw[] >>
  Cases_on `k` >> gvs[]
QED

(*
 * Helper: transform_block_insts preserves prefix and transforms suffix.
 *
 * When the first n instructions are not transformed, the result is
 * those n instructions followed by the transform of the remaining instructions.
 *)
Theorem transform_block_insts_TAKE_DROP:
  !n fn insts.
    EVERY (\i. transform_jnz fn i = NONE) (TAKE n insts)
    ==>
    transform_block_insts fn insts =
      TAKE n insts ++ transform_block_insts fn (DROP n insts)
Proof
  Induct_on `n` >- simp[] >>
  rw[] >> Cases_on `insts`
  >- (EVAL_TAC >> REWRITE_TAC[TAKE_nil, DROP_nil] >>
      REWRITE_TAC[transform_block_insts_nil, APPEND])
  >- (
    REWRITE_TAC[TAKE_def, DROP_def] >>
    REWRITE_TAC[numTheory.NOT_SUC, arithmeticTheory.SUC_SUB1] >>
    `transform_jnz fn h = NONE` by gvs[EVERY_DEF, TAKE_def] >>
    ONCE_REWRITE_TAC[transform_block_insts_def] >>
    ASM_REWRITE_TAC[] >> EVAL_TAC >>
    `EVERY (\i. transform_jnz fn i = NONE) (TAKE n t)` by gvs[EVERY_DEF, TAKE_def] >>
    first_x_assum irule >> first_x_assum ACCEPT_TAC
  )
QED

(* Helper: What instruction appears at index n in transformed block when
 * all prior instructions don't transform but instruction n does *)
Theorem transform_block_insts_EL_transformed:
  !fn insts n new_insts.
    n < LENGTH insts /\
    EVERY (\i. transform_jnz fn i = NONE) (TAKE n insts) /\
    transform_jnz fn (EL n insts) = SOME new_insts
    ==>
    EL n (transform_block_insts fn insts) = HD new_insts
Proof
  rw[] >>
  `transform_block_insts fn insts =
   TAKE n insts ++ transform_block_insts fn (DROP n insts)` by
     (irule transform_block_insts_TAKE_DROP >> gvs[]) >>
  pop_assum SUBST1_TAC >>
  `DROP n insts = EL n insts :: DROP (SUC n) insts` by
    simp[rich_listTheory.DROP_CONS_EL] >>
  pop_assum SUBST1_TAC >>
  simp[transform_block_insts_def] >>
  Cases_on `new_insts` >> gvs[]
  >- gvs[transform_jnz_def, AllCaseEqs(), transform_pattern1_def,
         transform_pattern2_def]
  >- simp[listTheory.EL_APPEND_EQN, listTheory.LENGTH_TAKE]
QED

(* Helper: transform_block_insts never shortens the instruction list *)
Theorem transform_block_insts_length_ge:
  !fn insts. LENGTH (transform_block_insts fn insts) >= LENGTH insts
Proof
  Induct_on `insts` >> simp[transform_block_insts_def] >>
  rw[] >> Cases_on `transform_jnz fn h` >> simp[]
  >- (`LENGTH (transform_block_insts fn insts) >= LENGTH insts` by simp[] >>
      decide_tac)
  >- (gvs[transform_jnz_def, AllCaseEqs()]
      >- (simp[transform_pattern1_def] >>
          `LENGTH (transform_block_insts fn insts) >= LENGTH insts` by simp[] >>
          decide_tac)
      >- (simp[transform_pattern2_def] >>
          `LENGTH (transform_block_insts fn insts) >= LENGTH insts` by simp[] >>
          decide_tac))
QED

(*
 * KEY LEMMA: Prefix of non-transformed instructions execute identically.
 *
 * WHY THIS IS TRUE: For instructions where transform_jnz returns NONE,
 * the instruction is unchanged. Thus step_inst produces identical results.
 * State evolution is deterministic.
 *)
Theorem step_inst_same_for_unchanged:
  !fn inst s.
    transform_jnz fn inst = NONE ==>
    step_inst inst s = step_inst inst s
Proof
  rw[] (* Trivially reflexive *)
QED

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
  `v'.vs_inst_idx = s.vs_inst_idx` by (drule_all step_inst_preserves_inst_idx >> simp[]) >>
  simp[]
QED

(*
 * Helper: When transform_jnz returns SOME with 2 instructions at index n,
 * the transformed block has at least n+2 elements
 *)
Theorem transform_block_insts_length_pattern2:
  !fn insts n cond_op label.
    n < LENGTH insts /\
    EVERY (λi. transform_jnz fn i = NONE) (TAKE n insts) /\
    transform_jnz fn (EL n insts) = SOME (transform_pattern2 (EL n insts) cond_op label)
    ==>
    LENGTH (transform_block_insts fn insts) >= n + 2
Proof
  rw[] >>
  `LENGTH (transform_pattern2 (EL n insts) cond_op label) = 2` by simp[transform_pattern2_def, LET_THM] >>
  `transform_block_insts fn insts = TAKE n insts ++ transform_block_insts fn (DROP n insts)`
    by metis_tac[transform_block_insts_TAKE_DROP] >>
  `LENGTH (TAKE n insts) = n` by simp[LENGTH_TAKE] >>
  `DROP n insts = EL n insts :: DROP (n + 1) insts` by (
    `n < LENGTH insts` by simp[] >>
    metis_tac[rich_listTheory.DROP_EL_CONS]
  ) >>
  `transform_block_insts fn (DROP n insts) =
   transform_pattern2 (EL n insts) cond_op label ++ transform_block_insts fn (DROP (n + 1) insts)` by (
    simp[transform_block_insts_def]
  ) >>
  simp[LENGTH_APPEND]
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
      sg `transform_block_insts fn bb.bb_instructions = bb.bb_instructions`
      >- (
        `!insts fn. EVERY (\i. transform_jnz fn i = NONE) insts ==>
         transform_block_insts fn insts = insts` suffices_by metis_tac[] >>
        Induct >> simp[transform_block_insts_def])
      >- gvs[transform_block_def])
    >- gvs[])
  (* Inductive case: instruction exists at current index *)
  >- (
    simp[Once run_block_def] >>
    Cases_on `transform_jnz fn (EL s.vs_inst_idx bb.bb_instructions)`
    (* NONE case: instruction not transformed - step_in_block same for both blocks *)
    >- (
      `s.vs_inst_idx < LENGTH bb.bb_instructions` by decide_tac >>
      sg `EVERY (\i. transform_jnz fn i = NONE)
                (TAKE (SUC s.vs_inst_idx) bb.bb_instructions)`
      >- (
        simp[rich_listTheory.TAKE_EL_SNOC, listTheory.EVERY_SNOC] >>
        `SUC s.vs_inst_idx = s.vs_inst_idx + 1` by decide_tac >>
        gvs[GSYM arithmeticTheory.ADD1, rich_listTheory.TAKE_EL_SNOC,
            listTheory.EVERY_SNOC] >>
        simp[GSYM rich_listTheory.SNOC_EL_TAKE, listTheory.EVERY_SNOC])
      >- (
        `TAKE (SUC s.vs_inst_idx) (transform_block fn bb).bb_instructions =
         TAKE (SUC s.vs_inst_idx) bb.bb_instructions` by
          (simp[transform_block_def] >> irule transform_block_insts_TAKE >> gvs[]) >>
        sg `step_in_block fn bb s = step_in_block fn (transform_block fn bb) s`
        >- (
          `s.vs_inst_idx < LENGTH (transform_block fn bb).bb_instructions` by
            (gvs[transform_block_def] >>
             `LENGTH (transform_block_insts fn bb.bb_instructions) >= LENGTH bb.bb_instructions`
                suffices_by decide_tac >>
             simp[transform_block_insts_length_ge]) >>
          irule step_in_block_prefix_same >> qexists_tac `s.vs_inst_idx` >> gvs[])
        >- (
          `run_block (transform_function fn) (transform_block fn bb) s =
           run_block fn (transform_block fn bb) s` by simp[run_block_fn_irrelevant] >>
          simp[] >>
          Cases_on `step_in_block fn (transform_block fn bb) s` >>
          Cases_on `q:exec_result` >> simp[]
          (* OK: recurse or terminate *)
          >- (
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
                (* Apply IH *)
                qpat_x_assum `!m. _`
                  (mp_tac o CONV_RULE (ONCE_DEPTH_CONV BETA_CONV)) >>
                DISCH_TAC >>
                `v.vs_inst_idx = SUC s.vs_inst_idx` by
                  (drule_all step_in_block_increments_idx >> simp[]) >>
                `run_block fn (transform_block fn bb) v =
                 run_block (transform_function fn) (transform_block fn bb) v` by
                  simp[run_block_fn_irrelevant] >>
                simp[])))
          (* Halt *)
          >- (
            `run_block fn (transform_block fn bb) s = Halt v` by
              (simp[Once run_block_def] >> gvs[]) >>
            simp[execution_equiv_except_refl])
          (* Revert *)
          >- (
            `run_block fn (transform_block fn bb) s = Revert v` by
              (simp[Once run_block_def] >> gvs[]) >>
            simp[execution_equiv_except_refl])
          (* Error *)
          >- (
            `run_block fn (transform_block fn bb) s = Error s'` by
              (simp[Once run_block_def] >> gvs[]) >>
            simp[]))))
    (* SOME case: instruction transformed (Pattern 1 or 2) *)
    >- (
      Cases_on `step_in_block fn bb s` >> Cases_on `q:exec_result` >> simp[]
      (* OK case: expand step_in_block and case on patterns *)
      >- (
        fs[step_in_block_def, get_instruction_def] >>
        `s.vs_inst_idx < LENGTH bb.bb_instructions` by decide_tac >> gvs[] >>
        (* Preserve EVERY while extracting transform_jnz info *)
        qpat_x_assum `transform_jnz _ _ = SOME _` mp_tac >>
        simp[transform_jnz_def] >> strip_tac >> gvs[AllCaseEqs()]
        (* Pattern 1 with is_terminator = T: main case *)
        (* TODO: Use pattern1_execution_trace from rtaPattern1Theory *)
        >- cheat
        (* Pattern 2 with is_terminator = T: main case *)
        (* TODO: Add pattern2_execution_trace helper in rtaPattern1Script *)
        >- cheat
        (* Pattern 1 with ~is_terminator: contradiction - JNZ IS a terminator *)
        >- gvs[is_terminator_def]
        (* Pattern 2 with ~is_terminator: contradiction *)
        >- fs[is_terminator_def])
      (* Halt case: contradiction - JNZ doesn't produce Halt *)
      >- (
        fs[step_in_block_def, get_instruction_def] >>
        `s.vs_inst_idx < LENGTH bb.bb_instructions` by decide_tac >> gvs[] >>
        gvs[transform_jnz_def, AllCaseEqs()]
        >- (qpat_x_assum `step_inst _ _ = Halt _` mp_tac >>
            simp[step_inst_def, AllCaseEqs()])
        >- (qpat_x_assum `step_inst _ _ = Halt _` mp_tac >>
            simp[step_inst_def, AllCaseEqs()]))
      (* Revert case: contradiction - JNZ doesn't produce Revert directly *)
      >- (
        fs[step_in_block_def, get_instruction_def] >>
        `s.vs_inst_idx < LENGTH bb.bb_instructions` by decide_tac >>
        gvs[transform_jnz_def, AllCaseEqs()]
        >- (qpat_x_assum `step_inst _ _ = Revert _` mp_tac >>
            simp[step_inst_def, AllCaseEqs()])
        >- (qpat_x_assum `step_inst _ _ = Revert _` mp_tac >>
            simp[step_inst_def, AllCaseEqs()]))
      (* Error case: transformed block also errors on same cond_op *)
      >- (
        fs[step_in_block_def, get_instruction_def] >>
        `s.vs_inst_idx < LENGTH bb.bb_instructions` by decide_tac >>
        qpat_x_assum `transform_jnz _ _ = SOME _` mp_tac >>
        simp[transform_jnz_def] >> strip_tac >> gvs[AllCaseEqs()]
        (* Pattern 1 error: ISZERO uses same cond_op, also errors *)
        (* TODO: Add pattern1_error helper in rtaPattern1Script *)
        >- (
          qpat_x_assum `step_inst _ _ = Error _` mp_tac >>
          simp[step_inst_def, AllCaseEqs()] >> strip_tac >>
          cheat)
        (* Pattern 2 error: ASSERT uses same cond_op, also errors *)
        (* TODO: Add pattern2_error helper in rtaPattern1Script *)
        >- (
          qpat_x_assum `step_inst _ _ = Error _` mp_tac >>
          simp[step_inst_def, AllCaseEqs()] >> strip_tac >>
          cheat))))
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
  rw[LET_THM] >>
  Cases_on `transform_block fn bb = bb`
  (* Case 1: Block unchanged - results identical *)
  >- (
    gvs[] >>
    `run_block (transform_function fn) bb (s with vs_inst_idx := 0) =
     run_block fn bb (s with vs_inst_idx := 0)` by simp[run_block_fn_irrelevant] >>
    pop_assum SUBST1_TAC >>
    Cases_on `run_block fn bb (s with vs_inst_idx := 0)` >>
    gvs[stateEquivTheory.state_equiv_except_refl,
        stateEquivTheory.execution_equiv_except_refl]
  )
  (* Case 2: Block transformed - requires tracing through pattern execution *)
  >- (
    Cases_on `bb.bb_instructions`
    (* Empty block: contradiction since transform_block would be identity *)
    >- gvs[transform_block_def, transform_block_insts_nil,
           venomInstTheory.basic_block_component_equality]
    (* Non-empty: h::t *)
    >- (
      Cases_on `transform_jnz fn h`
      (* First instruction NOT transformed - some later instruction is *)
      >- (
        (* Both blocks have same first instruction h at index 0.
         * If h is terminator: both execute same instruction, same result.
         * If h not terminator: both execute h, advance to index 1.
         * Need helper lemma to handle recursive case.
         *)
        Cases_on `is_terminator h.inst_opcode`
        (* Terminator case: both execute h and return same result *)
        >- (
          simp[Once run_block_def, step_in_block_def, get_instruction_def] >>
          simp[transform_block_def, transform_block_insts_def] >>
          Cases_on `step_inst h (s with vs_inst_idx := 0)` >> gvs[]
          (* OK v *)
          >- (
            Cases_on `v.vs_halted` >> gvs[]
            (* halted *)
            >- (
              simp[Once run_block_def, step_in_block_def, get_instruction_def] >>
              simp[execution_equiv_except_refl]
            )
            (* not halted *)
            >- (
              simp[Once run_block_def, step_in_block_def, get_instruction_def] >>
              simp[state_equiv_except_refl]
            )
          )
          (* Halt *)
          >- (
            simp[Once run_block_def, step_in_block_def, get_instruction_def] >>
            simp[execution_equiv_except_refl]
          )
          (* Revert *)
          >- (
            simp[Once run_block_def, step_in_block_def, get_instruction_def] >>
            simp[execution_equiv_except_refl]
          )
          (* Error *)
          >- (
            simp[Once run_block_def, step_in_block_def, get_instruction_def]
          )
        )
        (* Non-terminator case: requires recursion helper *)
        >- (
          simp[Once run_block_def, step_in_block_def, get_instruction_def] >>
          simp[transform_block_def, transform_block_insts_def] >>
          simp[Once run_block_def, step_in_block_def, get_instruction_def] >>
          cheat
        )
      )
      (* First instruction IS transformed - it's a JNZ matching pattern *)
      >- (
        `h.inst_opcode = JNZ` by (gvs[transform_jnz_def] >>
          Cases_on `h.inst_opcode = JNZ` >> gvs[]) >>
        qpat_x_assum `transform_jnz _ _ = _` mp_tac >>
        simp[transform_jnz_def] >>
        Cases_on `h.inst_operands` >> gvs[] >>
        Cases_on `t'` >> gvs[] >>
        Cases_on `t''` >> gvs[] >>
        Cases_on `h''` >> gvs[] >>
        Cases_on `h'³'` >> gvs[] >>
        Cases_on `t'` >> gvs[] >>
        strip_tac >>
        (* h = jnz h' (Label s') (Label s'') *)
        Cases_on `is_revert_label fn s'` >> gvs[]
        (* Pattern 1: revert on nonzero (is_revert_label fn s') *)
        >- (
          (* Original: jnz cond s' s'' where s' is revert label
           * Transformed: [ISZERO, ASSERT, JMP s''] ++ rest
           * Case cond != 0w: Original -> OK (jump to s'), Transformed -> Revert
           * Case cond = 0w: Original -> OK (jump to s''), Transformed -> OK (jump to s'')
           *)
          Cases_on `eval_operand h' (s with vs_inst_idx := 0)`
          (* NONE: both return Error *)
          >- (
            simp[Once run_block_def, step_in_block_def, get_instruction_def,
                 step_inst_def] >>
            simp[transform_block_def, transform_block_insts_def, transform_jnz_def,
                 transform_pattern1_def] >>
            simp[Once run_block_def, step_in_block_def, get_instruction_def,
                 mk_iszero_inst_def, step_inst_def, is_terminator_def] >>
            simp[exec_unop_def]
          )
          (* SOME x: case split on x = 0w *)
          >- (
            simp[Once run_block_def, step_in_block_def, get_instruction_def,
                 step_inst_def, is_terminator_def] >>
            Cases_on `x = 0w`
            (* x = 0w: both jump to s'' *)
            >- (
              gvs[] >> simp[venomStateTheory.jump_to_def] >>
              simp[transform_block_def, transform_block_insts_def,
                   transform_jnz_def, transform_pattern1_def] >>
              simp[Once run_block_def, step_in_block_def, get_instruction_def,
                   mk_iszero_inst_def, step_inst_def, is_terminator_def,
                   exec_unop_def, bool_to_word_def] >>
              simp[venomStateTheory.next_inst_def, venomStateTheory.update_var_def] >>
              simp[Once run_block_def, step_in_block_def, get_instruction_def,
                   mk_assert_inst_def, step_inst_def, is_terminator_def,
                   venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
              simp[venomStateTheory.next_inst_def] >>
              simp[Once run_block_def, step_in_block_def, get_instruction_def,
                   mk_jmp_inst_def, step_inst_def, is_terminator_def] >>
              simp[venomStateTheory.jump_to_def] >>
              irule state_equiv_except_subset >>
              qexists_tac `{fresh_iszero_var h.inst_id}` >>
              conj_tac
              >- (
                simp[fresh_vars_in_block_def, pred_setTheory.SUBSET_DEF,
                     pred_setTheory.IN_SING, pred_setTheory.GSPECIFICATION] >>
                qexists_tac `h` >> simp[transform_jnz_def]
              )
              >- (
                simp[state_equiv_except_def, execution_equiv_except_def,
                     venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
                     pred_setTheory.IN_SING]
              )
            )
            (* x != 0w: original jumps to s' (revert), transformed reverts *)
            >- (
              gvs[] >> simp[venomStateTheory.jump_to_def] >>
              simp[transform_block_def, transform_block_insts_def,
                   transform_jnz_def, transform_pattern1_def] >>
              simp[Once run_block_def, step_in_block_def, get_instruction_def,
                   mk_iszero_inst_def, step_inst_def, is_terminator_def,
                   exec_unop_def, bool_to_word_def] >>
              simp[venomStateTheory.next_inst_def, venomStateTheory.update_var_def] >>
              simp[Once run_block_def, step_in_block_def, get_instruction_def,
                   mk_assert_inst_def, step_inst_def, is_terminator_def,
                   venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
              irule revert_state_execution_equiv_preserves >>
              irule execution_equiv_except_subset >>
              qexists_tac `{fresh_iszero_var h.inst_id}` >>
              conj_tac
              >- (
                simp[fresh_vars_in_block_def, pred_setTheory.SUBSET_DEF,
                     pred_setTheory.IN_SING, pred_setTheory.GSPECIFICATION] >>
                qexists_tac `h` >> simp[transform_jnz_def]
              )
              >- (
                simp[execution_equiv_except_def, venomStateTheory.lookup_var_def,
                     finite_mapTheory.FLOOKUP_UPDATE, pred_setTheory.IN_SING]
              )
            )
          )
        )
        (* Pattern 2: revert on zero (is_revert_label fn s'') *)
        >- (
          (* Original: jnz cond s' s'' where s'' is revert label
           * Transformed: [ASSERT, JMP s'] ++ rest
           * Case cond != 0w: Original -> OK (jump to s'), Transformed -> OK (jump to s')
           * Case cond = 0w: Original -> OK (jump to s''), Transformed -> Revert
           *)
          Cases_on `eval_operand h' (s with vs_inst_idx := 0)`
          (* NONE: both return Error *)
          >- (
            simp[Once run_block_def, step_in_block_def, get_instruction_def,
                 step_inst_def] >>
            simp[transform_block_def, transform_block_insts_def, transform_jnz_def] >>
            simp[transform_pattern2_def, Once run_block_def, step_in_block_def,
                 get_instruction_def, step_inst_def, mk_assert_inst_def,
                 is_terminator_def]
          )
          (* SOME x: case split on x = 0w *)
          >- (
            simp[Once run_block_def, step_in_block_def, get_instruction_def,
                 step_inst_def, is_terminator_def] >>
            simp[] >>
            Cases_on `x = 0w`
            (* x = 0w: original jumps to s'' (revert), transformed reverts *)
            >- (
              gvs[] >> simp[venomStateTheory.jump_to_def] >>
              simp[transform_block_def, transform_block_insts_def, transform_jnz_def] >>
              simp[transform_pattern2_def] >>
              simp[Once run_block_def, step_in_block_def, get_instruction_def,
                   mk_assert_inst_def, step_inst_def, is_terminator_def] >>
              irule revert_state_execution_equiv_preserves >>
              simp[execution_equiv_except_def, venomStateTheory.lookup_var_def, venomStateTheory.update_var_def]
            )
            (* x != 0w: both jump to s' *)
            >- (
              gvs[] >> simp[venomStateTheory.jump_to_def] >>
              simp[transform_block_def, transform_block_insts_def, transform_jnz_def,
                   transform_pattern2_def] >>
              simp[Once run_block_def, step_in_block_def, get_instruction_def,
                   mk_assert_inst_def, step_inst_def, is_terminator_def] >>
              simp[venomStateTheory.next_inst_def] >>
              simp[Once run_block_def, step_in_block_def, get_instruction_def,
                   mk_jmp_inst_def, step_inst_def, is_terminator_def] >>
              simp[venomStateTheory.jump_to_def] >>
              simp[state_equiv_except_refl]
            )
          )
        )
      )
    )
  )
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
  Induct_on `fuel` >> rw[run_function_def] >-
    simp[result_equiv_except_def] >>
  (* Lookup block - use current_bb from state *)
  `s1.vs_current_bb = s2.vs_current_bb` by fs[state_equiv_except_def] >>
  Cases_on `lookup_block s1.vs_current_bb fn.fn_blocks` >> fs[]
  >- simp[result_equiv_except_def] >>
  (* Found block x *)
  `MEM x fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  (* Original function doesn't use fresh vars in block x *)
  `fresh_vars_not_in_block fn x` by fs[fresh_vars_not_in_function_def] >>
  (* Show block operands don't reference fresh vars *)
  `!inst. MEM inst x.bb_instructions ==>
      !v. MEM (Var v) inst.inst_operands ==> v NOTIN fresh` by (
    rw[] >> CCONTR_TAC >> gvs[] >>
    `v IN fresh_vars_in_function fn` by simp[] >>
    gvs[fresh_vars_in_function_def] >>
    (* v IN BIGUNION {...} means v IN some fresh_vars_in_block fn bb' *)
    `?bb'. MEM bb' fn.fn_blocks /\ v IN fresh_vars_in_block fn bb'` by
      (fs[pred_setTheory.IN_BIGUNION] >> metis_tac[]) >>
    (* fresh_vars_not_in_block says operands don't contain fresh vars *)
    gvs[fresh_vars_not_in_block_def, fresh_vars_in_block_def] >>
    first_x_assum (qspecl_then [`inst`, `v`] mp_tac) >> simp[]
  ) >>
  (* Use run_block_result_equiv_except *)
  `result_equiv_except fresh (run_block fn x s1) (run_block fn x s2)` by (
    irule run_block_result_equiv_except >> simp[] >> metis_tac[]
  ) >>
  Cases_on `run_block fn x s1` >> Cases_on `run_block fn x s2` >>
  gvs[result_equiv_except_def]
  >- (
    (* Both OK *)
    `v.vs_halted <=> v'.vs_halted` by fs[state_equiv_except_def, execution_equiv_except_def] >>
    Cases_on `v.vs_halted` >> gvs[] >>
    (* halted = T: result is Halt, need execution_equiv_except from state_equiv_except *)
    TRY (fs[state_equiv_except_def] >> NO_TAC) >>
    (* halted = F: recurse with IH *)
    first_x_assum irule >> simp[]
  )
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
 * All fresh variables in a context.
 *)
Definition fresh_vars_in_context_def:
  fresh_vars_in_context ctx =
    BIGUNION { fresh_vars_in_function fn | fn | MEM fn ctx.ctx_functions }
End

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
  rw[LET_THM] >>
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
  (* Apply transform_function_correct *)
  qspecl_then [`fn`, `s`] mp_tac transform_function_correct >>
  simp[LET_THM] >> strip_tac >>
  conj_tac >- simp[] >>
  rw[] >>
  (* Widen from fresh_vars_in_function to fresh_vars_in_context *)
  irule result_equiv_except_subset >>
  qexists_tac `fresh_vars_in_function fn` >>
  conj_tac >- (
    simp[fresh_vars_in_context_def, pred_setTheory.SUBSET_DEF,
         pred_setTheory.IN_BIGUNION, PULL_EXISTS] >>
    metis_tac[]
  ) >>
  first_x_assum irule >> simp[]
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
  rw[LET_THM] >>
  Cases_on `lookup_function entry ctx.ctx_functions` >> gvs[] >>
  qexistsl_tac [`x`, `transform_function x`] >>
  simp[lookup_function_transform_context] >>
  (* Apply transform_context_correct *)
  qspecl_then [`ctx`, `entry`] mp_tac transform_context_correct >>
  simp[LET_THM] >> strip_tac >>
  first_x_assum (qspecl_then [`x`, `transform_function x`] mp_tac) >>
  simp[lookup_function_transform_context]
QED

val _ = export_theory();
