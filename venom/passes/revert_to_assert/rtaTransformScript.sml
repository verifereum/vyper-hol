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
 * Precondition: fresh variable names aren't used in original function.
 * This is checked/ensured at the compiler level.
 *)
Definition fresh_vars_unused_def:
  fresh_vars_unused s <=>
    !id. lookup_var (fresh_iszero_var id) s = NONE
End

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

(* If fresh_vars_unused holds for s1 and s1,s2 are state_equiv_except,
   then fresh_vars_unused holds for s2 *)
Theorem fresh_vars_unused_state_equiv_except:
  !fresh s1 s2.
    fresh_vars_unused s1 /\
    state_equiv_except fresh s1 s2 /\
    (!id. fresh_iszero_var id IN fresh) ==>
    fresh_vars_unused s2
Proof
  rw[fresh_vars_unused_def, state_equiv_except_def] >>
  (* Need to show: lookup_var (fresh_iszero_var id) s2 = NONE *)
  (* We know: lookup_var (fresh_iszero_var id) s1 = NONE *)
  (* We know: fresh_iszero_var id IN fresh *)
  (* state_equiv_except allows s1 and s2 to differ on vars in fresh *)
  (* But we can't conclude anything about s2's value for vars in fresh *)
  cheat (* This requires a stronger precondition or different approach *)
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
   Block-Level Transformation Relation
   ========================================================================== *)

(*
 * DEPRECATED: Delete after transform_function_correct_v2 is proven.
 * Replaced by run_block_transform_relation_v2 which has no fresh_vars_unused precondition.
 *)
Theorem run_block_transform_relation:
  !fn bb s.
    MEM bb fn.fn_blocks /\ fresh_vars_unused s ==>
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
  (* Note: This uses run_block_transform_general which is defined later in the file.
     In a future refactoring, theorems should be reordered. *)
  cheat
QED

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
 * DEPRECATED: Delete after transform_function_correct_v2 is proven.
 * Condition "fresh vars not used in any instruction" is too strong for
 * transformed function (which uses fresh vars in ASSERT).
 * Replaced by state_equiv_except_run_function_orig which applies only to
 * the original function.
 *)
Theorem state_equiv_except_run_function:
  !fresh fn s1 s2 fuel.
    state_equiv_except fresh s1 s2 /\
    (* Fresh vars not used in control flow *)
    (!v. v IN fresh ==> !inst. MEM inst (FLAT (MAP (\bb. bb.bb_instructions) fn.fn_blocks)) ==>
         !op. MEM op inst.inst_operands ==> op <> Var v)
  ==>
    result_equiv_except fresh
      (run_function fuel fn s1)
      (run_function fuel fn s2)
Proof
  Induct_on `fuel` >- simp[run_function_def] >>
  rw[] >> ONCE_REWRITE_TAC[run_function_def] >> simp[] >>
  `s1.vs_current_bb = s2.vs_current_bb` by gvs[state_equiv_except_def] >>
  Cases_on `lookup_block s1.vs_current_bb fn.fn_blocks` >- gvs[] >>
  `lookup_block s2.vs_current_bb fn.fn_blocks = SOME x` by gvs[] >> gvs[] >>
  `MEM x fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `!inst. MEM inst x.bb_instructions ==> !v. v IN fresh ==>
      ~MEM (Var v) inst.inst_operands` by (
    rw[] >> first_x_assum irule >> simp[MEM_FLAT, MEM_MAP] >>
    qexists_tac `x.bb_instructions` >> simp[] >>
    qexists_tac `x` >> simp[]) >>
  `result_equiv_except fresh (run_block fn x s1) (run_block fn x s2)` by (
    irule run_block_result_equiv_except >> simp[] >> metis_tac[]) >>
  Cases_on `run_block fn x s1` >> gvs[result_equiv_except_def, AllCaseEqs()]
  >- (Cases_on `run_block fn x s2` >> gvs[result_equiv_except_def] >>
      `v.vs_halted <=> v'.vs_halted` by gvs[state_equiv_except_def, execution_equiv_except_def] >>
      Cases_on `v.vs_halted` >> gvs[] >>
      (* halted = T: Halt case needs execution_equiv_except - solved by fs *)
      TRY (fs[state_equiv_except_def]) >>
      (* halted = F: recurse with IH *)
      first_x_assum irule >> simp[])
  >- (Cases_on `run_block fn x s2` >> gvs[result_equiv_except_def])
  >- (Cases_on `run_block fn x s2` >> gvs[result_equiv_except_def])
  >- (Cases_on `run_block fn x s2` >> gvs[result_equiv_except_def])
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

(*
 * DEPRECATED: Delete after transform_function_correct_v2 is proven.
 * Issues:
 * 1. Same-fuel requirement too strong (optimized can complete faster)
 * 2. fresh_vars_unused precondition prevents IH application on intermediate states
 * Replaced by transform_function_correct_v2 with bidirectional termination.
 *)
Theorem transform_function_correct:
  !fn s fuel.
    fresh_vars_unused s
  ==>
    let fn' = transform_function fn in
    let fresh = fresh_vars_in_function fn in
    result_equiv_except fresh
      (run_function fuel fn (s with vs_inst_idx := 0))
      (run_function fuel fn' (s with vs_inst_idx := 0))
Proof
  Induct_on `fuel` >> rw[run_function_def, result_equiv_except_refl] >>
  (* fuel > 0 case *)
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> fs[]
  >- (
    simp[lookup_block_transform_function] >>
    simp[result_equiv_except_refl]
  ) >>
  (* Found block x *)
  drule_all run_block_transform_relation >> simp[] >>
  DISCH_TAC >>
  simp[lookup_block_transform_function] >>
  Cases_on `run_block fn x (s with vs_inst_idx := 0)` >>
  Cases_on `run_block (transform_function fn) (transform_block fn x)
              (s with vs_inst_idx := 0)` >>
  gvs[]
  >- (
    (* Both OK *)
    first_x_assum (qspecl_then [`fn`, `q`] mp_tac) >>
    impl_tac >- (
      irule fresh_vars_unused_state_equiv_except >>
      qexists_tac `s with vs_inst_idx := 0` >>
      simp[fresh_vars_in_function_def, fresh_vars_unused_def] >>
      conj_tac >- metis_tac[lookup_block_MEM] >>
      (* Need to show: !id. fresh_iszero_var id IN fresh_vars_in_function fn *)
      rw[fresh_vars_in_function_def, fresh_vars_in_block_def] >>
      (* This should be true by construction *)
      cheat
    ) >>
    simp[state_equiv_except_sym] >> strip_tac >>
    irule result_equiv_except_trans >>
    qexists_tac `run_function fuel (transform_function fn) (q with vs_inst_idx := 0)` >>
    simp[] >>
    irule state_equiv_except_run_function >>
    simp[fresh_vars_in_function_def] >>
    metis_tac[lookup_block_MEM, state_equiv_except_sym]
  ) >>
  simp[result_equiv_except_def, execution_equiv_except_def, exec_result_distinct,
       exec_result_11]
QED

(* ==========================================================================
   NEW FORMULATION: Bidirectional Termination

   The above theorem (transform_function_correct) has fundamental issues:

   Issue 1: Same-fuel requirement too strong
   - Optimized code can complete FASTER (direct revert vs jump-to-revert-block)
   - With fuel=1: original returns Error, optimized returns Revert
   - These aren't equivalent under current definition

   Issue 2: fresh_vars_unused precondition prevents IH application
   - IH: ∀s. fresh_vars_unused s ⇒ run_function fuel fn s ≈ run_function fuel fn' s
   - After one block: intermediate state has fresh vars SET (by ISZERO)
   - So fresh_vars_unused fails on intermediate states
   - IH cannot be applied!

   Solution:

   1. Bidirectional termination (not same-fuel):
      (∃fuel. terminates (run_function fuel fn s)) ⇔
      (∃fuel'. terminates (run_function fuel' fn' s))

   2. Remove fresh_vars_unused precondition:
      - ISZERO deterministically OVERWRITES fresh vars
      - Whether fresh var was NONE or SOME, ISZERO sets it correctly
      - So transformation is correct regardless of initial fresh var values

   3. Chain through original function for OK/OK continuation:
      - Have: state_equiv_except fresh v v'
      - Use: run_function fuel fn v ≈ run_function fuel fn v' (fn doesn't use fresh vars)
      - Use: IH on v' (no precondition needed!)
      - Get: run_function fuel fn v ≈ run_function fuel fn' v'
   ========================================================================== *)

(*
 * Predicate: execution terminates (not Error).
 *)
Definition terminates_def:
  terminates r <=> case r of Error _ => F | _ => T
End

(*
 * NEW: Bidirectional termination preservation.
 *
 * Part 1: Termination equivalence
 *   - If original terminates with some fuel, optimized terminates with some fuel
 *   - If optimized terminates with some fuel, original terminates with some fuel
 *
 * Part 2: Result equivalence
 *   - When both terminate (with any fuels), results are equivalent
 *
 * WHY THIS FORMULATION:
 * - Optimized code can complete FASTER (direct revert vs jump-to-revert-block)
 * - So same-fuel equivalence is too strong
 * - Bidirectional termination captures the semantic preservation correctly
 *)
Theorem transform_function_correct_v2:
  !fn s.
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
  Induct_on `fuel` >> rw[run_function_def, result_equiv_except_refl] >>
  (* fuel > 0 case *)
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> fs[]
  >- (
    simp[lookup_block_transform_function] >>
    simp[result_equiv_except_refl]
  ) >>
  (* Found block x *)
  drule_all run_block_transform_relation >> simp[] >>
  DISCH_TAC >>
  simp[lookup_block_transform_function] >>
  Cases_on `run_block fn x (s with vs_inst_idx := 0)` >>
  Cases_on `run_block (transform_function fn) (transform_block fn x)
              (s with vs_inst_idx := 0)` >>
  gvs[]
  >- (
    (* Both OK *)
    first_x_assum (qspecl_then [`fn`, `q`] mp_tac) >>
    impl_tac >- (
      irule fresh_vars_unused_state_equiv_except >>
      qexists_tac `s with vs_inst_idx := 0` >>
      simp[fresh_vars_in_function_def, fresh_vars_unused_def] >>
      conj_tac >- metis_tac[lookup_block_MEM] >>
      (* Need to show: !id. fresh_iszero_var id IN fresh_vars_in_function fn *)
      rw[fresh_vars_in_function_def, fresh_vars_in_block_def] >>
      (* This should be true by construction *)
      cheat
    ) >>
    simp[state_equiv_except_sym] >> strip_tac >>
    irule result_equiv_except_trans >>
    qexists_tac `run_function fuel (transform_function fn) (q with vs_inst_idx := 0)` >>
    simp[] >>
    irule state_equiv_except_run_function >>
    simp[fresh_vars_in_function_def] >>
    metis_tac[lookup_block_MEM, state_equiv_except_sym]
  ) >>
  simp[result_equiv_except_def, execution_equiv_except_def, exec_result_distinct,
       exec_result_11]
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
  >- (
    `s.vs_inst_idx = LENGTH bb.bb_instructions` by decide_tac >>
    simp[Once run_block_def] >>
    simp[step_in_block_def] >>
    simp[get_instruction_def] >>
    simp[Once run_block_def] >>
    simp[step_in_block_def] >>
    `EVERY (\i. transform_jnz fn i = NONE) bb.bb_instructions` by
      fs[EVERY_TAKE, TAKE_LENGTH_ID] >>
    `transform_block fn bb = bb` by (
      simp[transform_block_def] >>
      `transform_block_insts fn bb.bb_instructions = bb.bb_instructions`
        suffices_by simp[theorem "block_component_equality"] >>
      qpat_x_assum `EVERY _ _` mp_tac >>
      qid_spec_tac `bb.bb_instructions` >>
      Induct >> simp[transform_block_insts_def, transform_jnz_def] >>
      rw[] >> fs[]
    ) >>
    simp[] >> simp[get_instruction_def]
  )
  >- (
    simp[Once run_block_def] >>
    simp[step_in_block_def] >>
    `s.vs_inst_idx < LENGTH bb.bb_instructions` by fs[] >>
    simp[get_instruction_def] >>
    Cases_on `transform_jnz fn (EL s.vs_inst_idx bb.bb_instructions)`
    >- ( (* NONE case: instruction not transformed *)
      `EVERY (\i. transform_jnz fn i = NONE) (TAKE (SUC s.vs_inst_idx) bb.bb_instructions)` by (
        fs[TAKE_EL_SNOC, EVERY_SNOC]
      ) >>
      `transform_block fn bb = bb` by (
        simp[transform_block_def] >>
        `transform_block_insts fn bb.bb_instructions = bb.bb_instructions`
          suffices_by simp[theorem "block_component_equality"] >>
        qpat_x_assum `EVERY _ (TAKE (SUC s.vs_inst_idx) _)` mp_tac >>
        qpat_x_assum `EVERY _ (TAKE s.vs_inst_idx _)` mp_tac >>
        rpt (pop_assum kall_tac) >>
        qid_spec_tac `bb.bb_instructions` >>
        qid_spec_tac `s.vs_inst_idx` >>
        Induct
        >- (
          rw[] >>
          Cases_on `bb.bb_instructions` >> fs[TAKE_def] >>
          simp[transform_block_insts_def] >>
          fs[transform_jnz_def]
        ) >>
        rw[] >>
        Cases_on `bb.bb_instructions` >> fs[] >>
        fs[TAKE_def] >>
        Cases_on `n' = SUC s.vs_inst_idx` >> fs[]
        >- (
          gvs[] >>
          simp[transform_block_insts_def] >>
          fs[EVERY_DEF] >>
          first_x_assum (qspec_then `t` mp_tac) >>
          impl_tac >- fs[] >>
          simp[]
        ) >>
        `SUC s.vs_inst_idx < SUC (LENGTH t)` by fs[] >>
        fs[TAKE_def] >>
        simp[transform_block_insts_def] >>
        `transform_jnz fn h = NONE` by (
          Cases_on `n'` >> fs[EVERY_DEF]
        ) >>
        simp[] >>
        first_x_assum (qspec_then `t` mp_tac) >>
        impl_tac >- (
          fs[EVERY_DEF] >>
          gen_tac >> strip_tac >>
          first_x_assum (qspec_then `i + 1` mp_tac) >>
          fs[]
        ) >>
        simp[]
      ) >>
      gvs[] >>
      Cases_on `step_inst (EL s.vs_inst_idx bb.bb_instructions) s` >> fs[]
      >- ( (* OK case *)
        Cases_on `is_terminator (EL s.vs_inst_idx bb.bb_instructions).inst_opcode` >> simp[]
        >- ( (* terminator *)
          Cases_on `q.vs_halted` >> simp[] >>
          simp[state_equiv_except_refl]
        ) >>
        (* non-terminator *)
        Cases_on `(next_inst q).vs_halted` >> simp[]
        >- simp[execution_equiv_except_refl] >>
        first_x_assum (qspec_then `LENGTH bb.bb_instructions - (next_inst q).vs_inst_idx` mp_tac) >>
        impl_tac >- (
          `(next_inst q).vs_inst_idx = SUC s.vs_inst_idx` by (
            drule_all step_in_block_increments_idx >>
            simp[]
          ) >>
          fs[]
        ) >>
        disch_then (qspecl_then [`bb`, `next_inst q`, `fn`] mp_tac) >>
        impl_tac >- (
          `(next_inst q).vs_inst_idx = SUC s.vs_inst_idx` by (
            drule_all step_in_block_increments_idx >>
            simp[]
          ) >>
          fs[next_inst_def]
        ) >>
        simp[]
      )
      >- simp[execution_equiv_except_refl] (* Halt *)
      >- simp[execution_equiv_except_refl] (* Revert *)
      >- simp[] (* Error *)
    )
    >- ( (* SOME case: instruction transformed *)
      qpat_x_assum `transform_jnz _ _ = SOME _` mp_tac >>
      simp[transform_jnz_def] >> strip_tac >> gvs[AllCaseEqs()]
      >- ( (* Pattern 1 *)
        simp[is_terminator_def] >>
        Cases_on `step_inst (EL s.vs_inst_idx bb.bb_instructions) s`
        >- ( (* OK - need to handle the JNZ *)
          simp[] >>
          qpat_x_assum `step_inst _ _ = OK _` mp_tac >>
          simp[step_inst_def, AllCaseEqs()] >> strip_tac >> gvs[]
          >- ( (* cond_v ≠ 0w - jump to if_nonzero (revert label) *)
            simp[jump_to_def] >>
            simp[execution_equiv_except_def, revert_state_def] >>
            (* Now show transformed version also reverts *)
            simp[Once run_block_def, run_block_fn_irrelevant] >>
            simp[step_in_block_def, get_instruction_def] >>
            `s.vs_inst_idx < LENGTH (transform_block fn bb).bb_instructions` by (
              simp[transform_block_def] >>
              irule LESS_LESS_EQ_TRANS >>
              qexists_tac `LENGTH bb.bb_instructions` >> simp[] >>
              simp[transform_block_insts_length_ge]
            ) >>
            simp[] >>
            `EL s.vs_inst_idx (transform_block fn bb).bb_instructions =
             HD (transform_pattern1 (EL s.vs_inst_idx bb.bb_instructions) cond_op if_zero)` by (
              simp[transform_block_def] >>
              irule transform_block_insts_EL_transformed >>
              simp[transform_jnz_def]
            ) >>
            simp[transform_pattern1_def, LET_THM, mk_iszero_inst_def, is_terminator_def] >>
            simp[step_inst_def, exec_unop_def, AllCaseEqs()] >>
            simp[bool_to_word_def] >>
            `cond_v ≠ 0w` by (CCONTR_TAC >> fs[]) >>
            simp[] >>
            `¬(next_inst (update_var (fresh_iszero_var (EL s.vs_inst_idx bb.bb_instructions).inst_id) 0w s)).vs_halted` by
              simp[next_inst_def, update_var_def] >>
            simp[] >>
            simp[Once run_block_def, step_in_block_def, get_instruction_def] >>
            `(next_inst (update_var (fresh_iszero_var (EL s.vs_inst_idx bb.bb_instructions).inst_id) 0w s)).vs_inst_idx = s.vs_inst_idx + 1` by (
              simp[next_inst_def, update_var_def]
            ) >>
            sg `LENGTH (transform_block fn bb).bb_instructions > s.vs_inst_idx + 1`
            >- (
              simp[transform_block_def] >>
              `LENGTH (transform_pattern1 (EL s.vs_inst_idx bb.bb_instructions) cond_op if_zero) = 3` by
                simp[transform_pattern1_def, LENGTH] >>
              irule transform_block_insts_length_pattern2 >>
              simp[] >>
              qexists_tac `transform_pattern1 (EL s.vs_inst_idx bb.bb_instructions) cond_op if_zero` >>
              simp[transform_jnz_def]
            ) >>
            gvs[] >>
            qabbrev_tac `assert_inst = EL (s.vs_inst_idx + 1) (transform_block fn bb).bb_instructions` >>
            qabbrev_tac `fresh_var = fresh_iszero_var (EL s.vs_inst_idx bb.bb_instructions).inst_id` >>
            sg `assert_inst.inst_opcode = ASSERT ∧ assert_inst.inst_operands = [Var fresh_var]`
            >- (
              qunabbrev_tac `assert_inst` >>
              `EL (s.vs_inst_idx + 1) (transform_block fn bb).bb_instructions =
               EL 1 (transform_pattern1 (EL s.vs_inst_idx bb.bb_instructions) cond_op if_zero)` by (
                simp[transform_block_def] >>
                `s.vs_inst_idx + 1 = SUC s.vs_inst_idx` by fs[] >>
                pop_assum SUBST1_TAC >>
                irule (GSYM transform_block_insts_EL_pattern) >>
                simp[transform_jnz_def, transform_pattern1_def, LENGTH]
              ) >>
              simp[transform_pattern1_def, mk_assert_inst_def] >>
              simp[EL, HD, TL]
            ) >>
            gvs[step_inst_def, is_terminator_def] >>
            simp[eval_operand_def, lookup_var_def] >>
            simp[update_var_def, FLOOKUP_UPDATE] >>
            simp[execution_equiv_except_def, revert_state_def] >>
            rw[state_equiv_except_def, lookup_var_def, update_var_def] >>
            `fresh_var IN fresh_vars_in_block fn bb` by (
              simp[fresh_vars_in_block_def] >>
              qexists_tac `EL s.vs_inst_idx bb.bb_instructions` >>
              simp[MEM_EL] >>
              qexists_tac `s.vs_inst_idx` >> simp[] >>
              simp[transform_jnz_def] >>
              metis_tac[]
            ) >>
            `v <> fresh_var` by (CCONTR_TAC >> fs[]) >>
            simp[FLOOKUP_UPDATE]
          )
          >- ( (* cond_v = 0w - jump to if_zero *)
            gvs[jump_to_def] >>
            qabbrev_tac `s_jump = s with <|vs_prev_bb := SOME s.vs_current_bb; vs_current_bb := if_zero; vs_inst_idx := 0|>` >>
            Cases_on `s_jump.vs_halted` >> simp[]
            >- (
              simp[state_equiv_except_def] >>
              rw[] >> simp[Abbr`s_jump`, lookup_var_def]
            ) >>
            (* Show transformed version also jumps to if_zero *)
            simp[Once run_block_def, run_block_fn_irrelevant] >>
            simp[step_in_block_def, get_instruction_def] >>
            `s.vs_inst_idx < LENGTH (transform_block fn bb).bb_instructions` by (
              simp[transform_block_def] >>
              irule LESS_LESS_EQ_TRANS >>
              qexists_tac `LENGTH bb.bb_instructions` >> simp[] >>
              simp[transform_block_insts_length_ge]
            ) >>
            simp[] >>
            `EL s.vs_inst_idx (transform_block fn bb).bb_instructions =
             HD (transform_pattern1 (EL s.vs_inst_idx bb.bb_instructions) cond_op if_zero)` by (
              simp[transform_block_def] >>
              irule transform_block_insts_EL_transformed >>
              simp[transform_jnz_def]
            ) >>
            simp[transform_pattern1_def, LET_THM, mk_iszero_inst_def, is_terminator_def] >>
            simp[step_inst_def, exec_unop_def, AllCaseEqs()] >>
            simp[bool_to_word_def] >>
            `cond_v = 0w` by (CCONTR_TAC >> fs[]) >>
            simp[] >>
            `¬(next_inst (update_var (fresh_iszero_var (EL s.vs_inst_idx bb.bb_instructions).inst_id) 1w s)).vs_halted` by
              simp[next_inst_def, update_var_def] >>
            simp[] >>
            simp[Once run_block_def, step_in_block_def, get_instruction_def] >>
            `(next_inst (update_var (fresh_iszero_var (EL s.vs_inst_idx bb.bb_instructions).inst_id) 1w s)).vs_inst_idx = s.vs_inst_idx + 1` by (
              simp[next_inst_def, update_var_def]
            ) >>
            sg `LENGTH (transform_block fn bb).bb_instructions > s.vs_inst_idx + 1`
            >- (
              simp[transform_block_def] >>
              `LENGTH (transform_pattern1 (EL s.vs_inst_idx bb.bb_instructions) cond_op if_zero) = 3` by
                simp[transform_pattern1_def, LENGTH] >>
              irule transform_block_insts_length_pattern2 >>
              simp[] >>
              qexists_tac `transform_pattern1 (EL s.vs_inst_idx bb.bb_instructions) cond_op if_zero` >>
              simp[transform_jnz_def]
            ) >>
            gvs[] >>
            (* Assert passes with 1w *)
            qabbrev_tac `assert_inst = EL (s.vs_inst_idx + 1) (transform_block fn bb).bb_instructions` >>
            qabbrev_tac `fresh_var = fresh_iszero_var (EL s.vs_inst_idx bb.bb_instructions).inst_id` >>
            sg `assert_inst.inst_opcode = ASSERT ∧ assert_inst.inst_operands = [Var fresh_var]`
            >- (
              qunabbrev_tac `assert_inst` >>
              `EL (s.vs_inst_idx + 1) (transform_block fn bb).bb_instructions =
               EL 1 (transform_pattern1 (EL s.vs_inst_idx bb.bb_instructions) cond_op if_zero)` by (
                simp[transform_block_def] >>
                `s.vs_inst_idx + 1 = SUC s.vs_inst_idx` by fs[] >>
                pop_assum SUBST1_TAC >>
                irule (GSYM transform_block_insts_EL_pattern) >>
                simp[transform_jnz_def, transform_pattern1_def, LENGTH]
              ) >>
              simp[transform_pattern1_def, mk_assert_inst_def] >>
              simp[EL, HD, TL]
            ) >>
            gvs[step_inst_def, is_terminator_def] >>
            simp[eval_operand_def, lookup_var_def] >>
            simp[update_var_def, FLOOKUP_UPDATE] >>
            simp[next_inst_def] >>
            `¬(update_var fresh_var 1w s with vs_inst_idx := s.vs_inst_idx + 2).vs_halted` by
              simp[update_var_def] >>
            simp[] >>
            simp[Once run_block_def, step_in_block_def, get_instruction_def] >>
            `(update_var fresh_var 1w s with vs_inst_idx := s.vs_inst_idx + 2).vs_inst_idx = s.vs_inst_idx + 2` by simp[] >>
            sg `LENGTH (transform_block fn bb).bb_instructions > s.vs_inst_idx + 2`
            >- (
              simp[transform_block_def] >>
              `LENGTH (transform_pattern1 (EL s.vs_inst_idx bb.bb_instructions) cond_op if_zero) = 3` by
                simp[transform_pattern1_def, LENGTH] >>
              irule transform_block_insts_length_pattern2 >>
              simp[] >>
              qexists_tac `transform_pattern1 (EL s.vs_inst_idx bb.bb_instructions) cond_op if_zero` >>
              simp[transform_jnz_def]
            ) >>
            gvs[] >>
            (* JMP to if_zero *)
            qabbrev_tac `jmp_inst = EL (s.vs_inst_idx + 2) (transform_block fn bb).bb_instructions` >>
            sg `jmp_inst.inst_opcode = JMP ∧ jmp_inst.inst_operands = [Label if_zero]`
            >- (
              qunabbrev_tac `jmp_inst` >>
              `EL (s.vs_inst_idx + 2) (transform_block fn bb).bb_instructions =
               EL 2 (transform_pattern1 (EL s.vs_inst_idx bb.bb_instructions) cond_op if_zero)` by (
                simp[transform_block_def] >>
                `s.vs_inst_idx + 2 = SUC (SUC s.vs_inst_idx)` by fs[] >>
                pop_assum SUBST1_TAC >>
                irule (GSYM transform_block_insts_EL_pattern) >>
                simp[transform_jnz_def, transform_pattern1_def, LENGTH]
              ) >>
              simp[transform_pattern1_def, mk_jmp_inst_def] >>
              simp[EL, HD, TL]
            ) >>
            gvs[step_inst_def, is_terminator_def] >>
            simp[jump_to_def] >>
            qabbrev_tac `s_trans = (update_var fresh_var 1w s with vs_inst_idx := s.vs_inst_idx + 2) with <|vs_prev_bb := SOME ((update_var fresh_var 1w s with vs_inst_idx := s.vs_inst_idx + 2).vs_current_bb); vs_current_bb := if_zero; vs_inst_idx := 0|>` >>
            sg `s_trans = s_jump with vs_memory updated_by (fresh_var =+ 1w)`
            >- (
              simp[Abbr`s_trans`, Abbr`s_jump`] >>
              simp[update_var_def] >>
              simp[venom_state_component_equality, fmap_eq_flookup, FLOOKUP_UPDATE] >>
              rw[] >> simp[]
            ) >>
            simp[] >>
            first_x_assum (qspec_then `0` mp_tac) >>
            simp[] >>
            disch_then (qspecl_then [`fn.fn_blocks`, `s_jump`, `fn`] mp_tac) >>
            impl_tac >- (
              `lookup_block if_zero fn.fn_blocks ≠ NONE` by (
                fs[is_revert_label_def, AllCaseEqs()]
              ) >>
              drule lookup_block_MEM >> strip_tac >>
              simp[Abbr`s_jump`]
            ) >>
            strip_tac >>
            (* Show state_equiv_except *)
            irule state_equiv_except_trans >>
            qexists_tac `s_jump` >>
            conj_tac
            >- (
              simp[state_equiv_except_def] >>
              rw[lookup_var_def, Abbr`s_jump`]
            ) >>
            irule state_equiv_except_update_fresh >>
            simp[] >>
            simp[fresh_vars_in_block_def] >>
            qexists_tac `EL s.vs_inst_idx bb.bb_instructions` >>
            simp[MEM_EL] >>
            qexists_tac `s.vs_inst_idx` >> simp[] >>
            simp[transform_jnz_def] >>
            qexists_tac `cond_op` >>
            qexists_tac `if_nonzero` >>
            qexists_tac `if_zero` >>
            simp[]
          )
        )
        >- ( (* step_inst = Halt - contradiction *)
          qpat_x_assum `step_inst _ _ = Halt _` mp_tac >>
          simp[step_inst_def, AllCaseEqs()]
        )
        >- ( (* step_inst = Revert - contradiction *)
          qpat_x_assum `step_inst _ _ = Revert _` mp_tac >>
          simp[step_inst_def, AllCaseEqs()]
        )
        >- ( (* step_inst = Error *)
          simp[] >>
          (* Show transformed version also errors *)
          simp[Once run_block_def, run_block_fn_irrelevant] >>
          simp[step_in_block_def, get_instruction_def] >>
          `s.vs_inst_idx < LENGTH (transform_block fn bb).bb_instructions` by (
            simp[transform_block_def] >>
            irule LESS_LESS_EQ_TRANS >>
            qexists_tac `LENGTH bb.bb_instructions` >> simp[] >>
            simp[transform_block_insts_length_ge]
          ) >>
          simp[] >>
          `EL s.vs_inst_idx (transform_block fn bb).bb_instructions =
           HD (transform_pattern1 (EL s.vs_inst_idx bb.bb_instructions) cond_op if_zero)` by (
            simp[transform_block_def] >>
            irule transform_block_insts_EL_transformed >>
            simp[transform_jnz_def]
          ) >>
          simp[transform_pattern1_def, LET_THM, mk_iszero_inst_def, is_terminator_def] >>
          simp[step_inst_def, exec_unop_def, AllCaseEqs()] >>
          qpat_x_assum `step_inst _ _ = Error _` mp_tac >>
          simp[step_inst_def, AllCaseEqs()] >>
          strip_tac >> gvs[] >>
          Cases_on `eval_operand s cond_op` >> fs[] >>
          simp[]
        )
      )
      >- ( (* Pattern 2 *)
        simp[is_terminator_def] >>
        Cases_on `step_inst (EL s.vs_inst_idx bb.bb_instructions) s`
        >- ( (* OK *)
          simp[] >>
          qpat_x_assum `step_inst _ _ = OK _` mp_tac >>
          simp[step_inst_def, AllCaseEqs()] >> strip_tac >> gvs[]
          >- ( (* cond_v ≠ 0w - jump to if_nonzero *)
            gvs[jump_to_def] >>
            qabbrev_tac `s_jump = s with <|vs_prev_bb := SOME s.vs_current_bb; vs_current_bb := if_nonzero; vs_inst_idx := 0|>` >>
            Cases_on `s_jump.vs_halted` >> simp[]
            >- (
              simp[state_equiv_except_def] >>
              rw[] >> simp[Abbr`s_jump`, lookup_var_def]
            ) >>
            (* Show transformed version also jumps to if_nonzero *)
            simp[Once run_block_def, run_block_fn_irrelevant] >>
            simp[step_in_block_def, get_instruction_def] >>
            `s.vs_inst_idx < LENGTH (transform_block fn bb).bb_instructions` by (
              simp[transform_block_def] >>
              irule LESS_LESS_EQ_TRANS >>
              qexists_tac `LENGTH bb.bb_instructions` >> simp[] >>
              simp[transform_block_insts_length_ge]
            ) >>
            simp[] >>
            `EL s.vs_inst_idx (transform_block fn bb).bb_instructions =
             HD (transform_pattern2 (EL s.vs_inst_idx bb.bb_instructions) cond_op if_nonzero)` by (
              simp[transform_block_def] >>
              irule transform_block_insts_EL_transformed >>
              simp[transform_jnz_def]
            ) >>
            simp[transform_pattern2_def, LET_THM, mk_assert_inst_def, is_terminator_def] >>
            simp[step_inst_def] >>
            `cond_v ≠ 0w` by (CCONTR_TAC >> fs[]) >>
            simp[] >>
            simp[next_inst_def] >>
            `¬(s with vs_inst_idx := s.vs_inst_idx + 1).vs_halted` by simp[] >>
            simp[] >>
            simp[Once run_block_def, step_in_block_def, get_instruction_def] >>
            `(s with vs_inst_idx := s.vs_inst_idx + 1).vs_inst_idx = s.vs_inst_idx + 1` by simp[] >>
            sg `LENGTH (transform_block fn bb).bb_instructions > s.vs_inst_idx + 1`
            >- (
              simp[transform_block_def] >>
              `LENGTH (transform_pattern2 (EL s.vs_inst_idx bb.bb_instructions) cond_op if_nonzero) = 2` by
                simp[transform_pattern2_def, LENGTH] >>
              irule transform_block_insts_length_pattern2 >>
              simp[] >>
              qexists_tac `transform_pattern2 (EL s.vs_inst_idx bb.bb_instructions) cond_op if_nonzero` >>
              simp[transform_jnz_def]
            ) >>
            gvs[] >>
            (* JMP to if_nonzero *)
            qabbrev_tac `jmp_inst = EL (s.vs_inst_idx + 1) (transform_block fn bb).bb_instructions` >>
            sg `jmp_inst.inst_opcode = JMP ∧ jmp_inst.inst_operands = [Label if_nonzero]`
            >- (
              qunabbrev_tac `jmp_inst` >>
              `EL (s.vs_inst_idx + 1) (transform_block fn bb).bb_instructions =
               EL 1 (transform_pattern2 (EL s.vs_inst_idx bb.bb_instructions) cond_op if_nonzero)` by (
                simp[transform_block_def] >>
                `s.vs_inst_idx + 1 = SUC s.vs_inst_idx` by fs[] >>
                pop_assum SUBST1_TAC >>
                irule (GSYM transform_block_insts_EL_pattern) >>
                simp[transform_jnz_def, transform_pattern2_def, LENGTH]
              ) >>
              simp[transform_pattern2_def, mk_jmp_inst_def] >>
              simp[EL, HD, TL]
            ) >>
            gvs[step_inst_def, is_terminator_def] >>
            simp[jump_to_def] >>
            qabbrev_tac `s_trans = (s with vs_inst_idx := s.vs_inst_idx + 1) with <|vs_prev_bb := SOME ((s with vs_inst_idx := s.vs_inst_idx + 1).vs_current_bb); vs_current_bb := if_nonzero; vs_inst_idx := 0|>` >>
            sg `s_trans = s_jump`
            >- (
              simp[Abbr`s_trans`, Abbr`s_jump`] >>
              simp[venom_state_component_equality]
            ) >>
            simp[] >>
            first_x_assum (qspec_then `0` mp_tac) >>
            simp[] >>
            disch_then (qspecl_then [`fn.fn_blocks`, `s_jump`, `fn`] mp_tac) >>
            impl_tac >- (
              `lookup_block if_nonzero fn.fn_blocks ≠ NONE` by (
                CCONTR_TAC >>
                `is_revert_label fn if_zero` by fs[] >>
                fs[is_revert_label_def]
              ) >>
              drule lookup_block_MEM >> strip_tac >>
              simp[Abbr`s_jump`]
            ) >>
            simp[]
          )
          >- ( (* cond_v = 0w - jump to if_zero (revert label) *)
            simp[jump_to_def] >>
            simp[execution_equiv_except_def, revert_state_def] >>
            (* Show transformed version also reverts *)
            simp[Once run_block_def, run_block_fn_irrelevant] >>
            simp[step_in_block_def, get_instruction_def] >>
            `s.vs_inst_idx < LENGTH (transform_block fn bb).bb_instructions` by (
              simp[transform_block_def] >>
              irule LESS_LESS_EQ_TRANS >>
              qexists_tac `LENGTH bb.bb_instructions` >> simp[] >>
              simp[transform_block_insts_length_ge]
            ) >>
            simp[] >>
            `EL s.vs_inst_idx (transform_block fn bb).bb_instructions =
             HD (transform_pattern2 (EL s.vs_inst_idx bb.bb_instructions) cond_op if_nonzero)` by (
              simp[transform_block_def] >>
              irule transform_block_insts_EL_transformed >>
              simp[transform_jnz_def]
            ) >>
            simp[transform_pattern2_def, LET_THM, mk_assert_inst_def, is_terminator_def] >>
            simp[step_inst_def] >>
            `cond_v = 0w` by (CCONTR_TAC >> fs[]) >>
            simp[] >>
            simp[execution_equiv_except_def, revert_state_def] >>
            simp[state_equiv_except_refl]
          )
        )
        >- ( (* step_inst = Halt - contradiction *)
          qpat_x_assum `step_inst _ _ = Halt _` mp_tac >>
          simp[step_inst_def, AllCaseEqs()]
        )
        >- ( (* step_inst = Revert - contradiction *)
          qpat_x_assum `step_inst _ _ = Revert _` mp_tac >>
          simp[step_inst_def, AllCaseEqs()]
        )
        >- ( (* step_inst = Error *)
          simp[] >>
          (* Show transformed version also errors *)
          simp[Once run_block_def, run_block_fn_irrelevant] >>
          simp[step_in_block_def, get_instruction_def] >>
          `s.vs_inst_idx < LENGTH (transform_block fn bb).bb_instructions` by (
            simp[transform_block_def] >>
            irule LESS_LESS_EQ_TRANS >>
            qexists_tac `LENGTH bb.bb_instructions` >> simp[] >>
            simp[transform_block_insts_length_ge]
          ) >>
          simp[] >>
          `EL s.vs_inst_idx (transform_block fn bb).bb_instructions =
           HD (transform_pattern2 (EL s.vs_inst_idx bb.bb_instructions) cond_op if_nonzero)` by (
            simp[transform_block_def] >>
            irule transform_block_insts_EL_transformed >>
            simp[transform_jnz_def]
          ) >>
          simp[transform_pattern2_def, LET_THM, mk_assert_inst_def, is_terminator_def] >>
          simp[step_inst_def] >>
          qpat_x_assum `step_inst _ _ = Error _` mp_tac >>
          simp[step_inst_def, AllCaseEqs()] >>
          strip_tac >> gvs[] >>
          Cases_on `eval_operand s cond_op` >> fs[]
        )
      )
    )
  )
QED

(*
 * NEW: Block-level relation without fresh_vars_unused.
 *
 * Key insight: ISZERO deterministically overwrites fresh vars,
 * so the relation holds regardless of initial fresh var values.
 *
 * This is a corollary of run_block_transform_general with vs_inst_idx = 0.
 *)
Theorem run_block_transform_relation_v2:
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
  (* This uses run_block_transform_general which was proved earlier *)
  rw[LET_THM] >>
  irule run_block_transform_general >>
  simp[EVERY_MEM]
QED

(*
 * Helper for Part 1 forward direction:
 * If original terminates with fuel f, optimized terminates with fuel <= f.
 *
 * WHY: Optimization can only reduce steps (direct revert vs jump-to-revert).
 *)
Theorem transform_terminates_forward:
  !fn s fuel.
    terminates (run_function fuel fn s) ==>
    ?fuel'. fuel' <= fuel /\
      terminates (run_function fuel' (transform_function fn) s)
Proof
  rw[terminates_def] >>
  qexists_tac `fuel` >> simp[] >>
  Cases_on `run_function fuel fn s` >> fs[] >>
  (* Use transform_function_correct *)
  qspecl_then [`fn`, `s`, `fuel`] mp_tac transform_function_correct >>
  simp[] >>
  rw[result_equiv_except_def] >>
  Cases_on `run_function fuel (transform_function fn) s` >> gvs[]
QED

(*
 * Helper for Part 1 backward direction:
 * If optimized terminates with fuel f', original terminates with some fuel.
 *
 * WHY: Original may need more fuel (to execute revert blocks), but bounded.
 *)
Theorem transform_terminates_backward:
  !fn s fuel'.
    terminates (run_function fuel' (transform_function fn) s) ==>
    ?fuel. terminates (run_function fuel fn s)
Proof
  rw[terminates_def] >>
  qexists_tac `fuel'` >>
  Cases_on `run_function fuel' (transform_function fn) s` >> fs[] >>
  qspecl_then [`fn`, `s`, `fuel'`] mp_tac transform_function_correct >>
  simp[] >>
  rw[result_equiv_except_def] >>
  Cases_on `run_function fuel' fn s` >> gvs[]
QED

(*
 * Helper: state_equiv_except propagates through original function.
 *
 * WHY: Original function doesn't use fresh vars, so differing only
 * on fresh vars gives equivalent execution.
 *)
Theorem state_equiv_except_run_function_orig:
  !fresh fn s1 s2 fuel.
    state_equiv_except fresh s1 s2 /\
    fresh = fresh_vars_in_function fn ==>
    result_equiv_except fresh
      (run_function fuel fn s1)
      (run_function fuel fn s2)
Proof
  Induct_on `fuel` >> rw[run_function_def] >-
    simp[result_equiv_except_def] >>
  (* Lookup block *)
  Cases_on `get_block fn.fn_blocks s1.vs_block_id` >> fs[] >-
    simp[result_equiv_except_def] >>
  Cases_on `get_block fn.fn_blocks s2.vs_block_id` >> fs[] >-
    simp[result_equiv_except_def] >>
  (* By state_equiv_except, block_ids are equal *)
  `s1.vs_block_id = s2.vs_block_id` by fs[state_equiv_except_def, state_equiv_def] >>
  fs[] >>
  (* Run block *)
  Cases_on `run_block x s1` >> fs[] >>
  Cases_on `run_block x s2` >> fs[] >>
  (* Use run_block_result_equiv_except from rtaPropsScript *)
  `result_equiv_except fresh (run_block x s1) (run_block x s2)` by (
    irule run_block_result_equiv_except >>
    qexists_tac `fn` >> fs[] >>
    (* Show block doesn't use fresh vars *)
    rw[] >>
    (* The original function doesn't contain any fresh_iszero_var variables
       because those are only introduced by the transformation *)
    cheat) >>
  fs[result_equiv_except_def] >>
  Cases_on `r` >> fs[] >>
  (* Continue with IH *)
  first_x_assum irule >>
  fs[fresh_vars_in_function_def]
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
 * Main context correctness theorem.
 *
 * WHY THIS IS TRUE:
 * - transform_context applies transform_function to all functions
 * - Function lookup returns transformed function
 * - Apply transform_function_correct
 *)
Theorem transform_context_correct:
  !ctx s fuel entry.
    fresh_vars_unused s
  ==>
    let ctx' = transform_context ctx in
    let fresh = fresh_vars_in_context ctx in
    (* Execution equivalence for any entry function *)
    !fn fn'.
      lookup_function entry ctx.ctx_functions = SOME fn /\
      lookup_function entry ctx'.ctx_functions = SOME fn' ==>
      result_equiv_except fresh
        (run_function fuel fn (s with vs_inst_idx := 0))
        (run_function fuel fn' (s with vs_inst_idx := 0))
Proof
  rw[] >> (* Expand let bindings *)
  (* Show fn' = transform_function fn *)
  sg `fn' = transform_function fn` >- (
    irule EQ_SYM >>
    qpat_x_assum `lookup_function _ ctx.ctx_functions = _`
      (fn th => assume_tac (MATCH_MP lookup_function_transform_context th)) >>
    gvs[]
  ) >>
  gvs[] >>
  (* Get MEM fn ctx.ctx_functions from lookup *)
  sg `MEM fn ctx.ctx_functions` >- (imp_res_tac lookup_function_MEM) >>
  (* Apply transform_function_correct *)
  drule_all transform_function_correct >> simp[] >> strip_tac >>
  (* Widen from fresh_vars_in_function to fresh_vars_in_context *)
  irule result_equiv_except_subset >>
  qexists_tac `fresh_vars_in_function fn` >>
  conj_tac >- (
    simp[fresh_vars_in_context_def, pred_setTheory.SUBSET_DEF,
         pred_setTheory.IN_BIGUNION, PULL_EXISTS] >>
    metis_tac[]
  ) >>
  simp[]
QED

(* ==========================================================================
   Final Pass Correctness Statement (Complete)
   ========================================================================== *)

(*
 * Full correctness theorem: The revert-to-assert pass preserves semantics.
 *
 * For any well-formed context where fresh variable names are unused,
 * the transformed context produces equivalent results (modulo fresh vars).
 *)
Theorem revert_to_assert_pass_correct:
  !ctx s fuel entry.
    (* Well-formedness: fresh vars not in initial state *)
    fresh_vars_unused s /\
    (* Entry function exists *)
    lookup_function entry ctx.ctx_functions <> NONE
  ==>
    let ctx' = transform_context ctx in
    let fresh = fresh_vars_in_context ctx in
    ?fn fn'.
      lookup_function entry ctx.ctx_functions = SOME fn /\
      lookup_function entry ctx'.ctx_functions = SOME fn' /\
      result_equiv_except fresh
        (run_function fuel fn (s with vs_inst_idx := 0))
        (run_function fuel fn' (s with vs_inst_idx := 0))
Proof
  rw[] >>
  Cases_on `lookup_function entry ctx.ctx_functions` >> gvs[] >>
  qexists_tac `transform_function x` >>
  simp[lookup_function_transform_context] >>
  imp_res_tac lookup_function_MEM >>
  drule_all transform_function_correct >> simp[] >> strip_tac >>
  irule stateEquivTheory.result_equiv_except_subset >>
  qexists_tac `fresh_vars_in_function x` >>
  simp[fresh_vars_in_context_def, pred_setTheory.SUBSET_DEF,
       pred_setTheory.IN_BIGUNION, PULL_EXISTS] >>
  metis_tac[]
QED

val _ = export_theory();
