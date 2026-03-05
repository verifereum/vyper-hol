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
 * INSTRUCTION BEHAVIOR (base lemmas in venomExecPropsTheory):
 *   - step_assert_zero_reverts      : ASSERT 0w reverts
 *   - step_assert_nonzero_passes    : ASSERT nonzero continues
 *
 * BLOCK/FUNCTION EXECUTION:
 *   - step_in_block_single_terminator : General single-terminator block lemma
 *   - simple_revert_block_reverts     : Simple revert block always reverts
 *   - run_function_at_simple_revert   : run_function at simple revert returns Revert
 *
 * STATE_EQUIV PROPERTIES:
 *   - update_var_state_equiv_insert : update_var x creates {x}-equiv
 *   - revert_state_from_state_equiv : state_equiv → execution_equiv for revert
 *   - halt_state_from_state_equiv   : state_equiv → execution_equiv for halt
 *   (resolve_phi_MEM in venomExecPropsTheory)
 *   (result_equiv_trans in stateEquivPropsTheory)
 *   (step_inst_result_equiv, run_block_result_equiv in execEquivPropsTheory)
 *
 * TRANSFORM_BLOCK_INSTS PROPERTIES:
 *   - transform_block_insts_TAKE_DROP      : Prefix decomposition
 *   - transform_block_insts_EL_transformed : Element at transformed index
 *   - transform_block_insts_length_*       : Length bounds for patterns
 *   - pattern1/2_transformed_instructions  : Instruction facts for patterns
 *
 * ============================================================================
 *)

Theory rtaHelpers
Ancestors
  rtaDefs stateEquiv stateEquivProps execEquivProps venomExecProps
Libs
  finite_mapTheory venomStateTheory venomExecSemanticsTheory venomInstTheory venomExecPropsTheory

(* SOLVE tactical: fails if tactic doesn't completely close the goal *)
fun SOLVE tac (g as (asl, w)) =
  case tac g of
    ([], prf) => ([], prf)
  | _ => raise mk_HOL_ERR "rtaProps" "SOLVE" "subgoals remain";

(* ==========================================================================
   NOTE: bool_to_word properties and basic instruction behavior lemmas
   (step_iszero_value, step_assert_behavior, step_revert_always_reverts,
   step_jnz_behavior, step_jmp_behavior) are now in venomExecPropsTheory.
   ========================================================================== *)

(* ==========================================================================
   ASSERT Instruction Behavior - Special Cases
   (Base lemma step_assert_behavior is in venomExecPropsTheory)
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
   run_block Helper Lemmas
   ========================================================================== *)

(* WHY THIS IS TRUE: step_in_block on a single-instruction terminator block
   returns the result of step_inst with is_term = T. *)
Theorem step_in_block_single_terminator:
  !bb s inst.
    bb.bb_instructions = [inst] /\
    is_terminator inst.inst_opcode ==>
    step_in_block bb (s with vs_inst_idx := 0) =
    (step_inst inst (s with vs_inst_idx := 0), T)
Proof
  rw[step_in_block_def, get_instruction_def] >>
  Cases_on `step_inst inst (s with vs_inst_idx := 0)` >> simp[]
QED

(* ==========================================================================
   Simple Revert Block Execution
   (step_jmp_behavior is in venomExecPropsTheory)
   ========================================================================== *)

(* WHY THIS IS TRUE: A block with only [revert 0 0] will:
   1. step_in_block gets instruction at idx 0 -> the REVERT instruction
   2. step_inst returns Revert (revert_state s)
   3. run_block propagates this Revert result *)
Theorem simple_revert_block_reverts:
  !bb s.
    is_simple_revert_block bb ==>
    run_block bb (s with vs_inst_idx := 0) =
    Revert (revert_state (s with vs_inst_idx := 0))
Proof
  rw[is_simple_revert_block_def] >>
  `bb.bb_instructions = [HD bb.bb_instructions]` by (
    Cases_on `bb.bb_instructions` >> fs[]
  ) >>
  simp[Once run_block_def] >>
  `step_in_block bb (s with vs_inst_idx := 0) =
   (step_inst (HD bb.bb_instructions) (s with vs_inst_idx := 0), T)` by (
    irule step_in_block_single_terminator >> simp[is_terminator_def]
  ) >>
  simp[step_inst_def, is_terminator_def]
QED

(* ==========================================================================
   run_function at Simple Revert Block
   ========================================================================== *)

(* WHY THIS IS TRUE: A simple revert block executes its single REVERT instruction
   and produces Revert result. run_function at fuel > 0 unfolds to run_block. *)
Theorem run_function_at_simple_revert:
  !fn s fuel bb.
    is_simple_revert_block bb /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    fuel > 0 ==>
    run_function fuel fn (s with vs_inst_idx := 0) =
      Revert (revert_state (s with vs_inst_idx := 0))
Proof
  rw[] >>
  `fuel > 0` by simp[] >>
  Cases_on `fuel` >- fs[] >>
  simp[Once run_function_def] >>
  `run_block bb (s with vs_inst_idx := 0) =
   Revert (revert_state (s with vs_inst_idx := 0))`
    by (irule simple_revert_block_reverts >> simp[]) >>
  simp[]
QED

(* ==========================================================================
   state_equiv Properties

   NOTE: Basic properties (refl, sym, trans, state_equiv_implies,
   update_var_preserves, jump_to_preserves, revert_state_preserves,
   state_equiv_subset) are proven in rtaDefsTheory.
   ========================================================================== *)

(* WHY THIS IS TRUE: update_var x v s adds (x, v) to vs_vars.
   For any y not in {x}, lookup_var y is unchanged.
   Other state components (memory, storage, etc.) unchanged. *)
Theorem update_var_state_equiv_insert:
  !x v s.
    state_equiv {x} s (update_var x v s)
Proof
  rw[state_equiv_def, execution_equiv_def,
     update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

(* Bridge: state_equiv → execution_equiv for revert_state.
   revert_state_preserves gives state_equiv → state_equiv, but
   result_equiv for Revert needs execution_equiv. *)
Theorem revert_state_from_state_equiv:
  !vars s1 s2.
    state_equiv vars s1 s2 ==>
    execution_equiv vars (revert_state s1) (revert_state s2)
Proof
  rw[state_equiv_def, execution_equiv_def, revert_state_def, lookup_var_def]
QED

(* Bridge: state_equiv → execution_equiv for halt_state *)
Theorem halt_state_from_state_equiv:
  !vars s1 s2.
    state_equiv vars s1 s2 ==>
    execution_equiv vars (halt_state s1) (halt_state s2)
Proof
  rw[state_equiv_def, execution_equiv_def, halt_state_def, lookup_var_def]
QED

(* ==========================================================================
   state_equiv Preservation Through Execution

   These lemmas show that if fresh vars are not used in operands, then
   state_equiv is preserved through step_inst, run_block, run_function.
   ========================================================================== *)

(* --------------------------------------------------------------------------
   NOTE: resolve_phi_MEM is in venomExecPropsTheory.
   step_inst_result_equiv, run_block_result_equiv are in execEquivPropsTheory.
   -------------------------------------------------------------------------- *)

(* --------------------------------------------------------------------------
   NOTE: result_equiv_trans is in stateEquivPropsTheory.
   -------------------------------------------------------------------------- *)

(* ==========================================================================
   transform_block_insts Properties
   ========================================================================== *)

(* WHY THIS IS TRUE: When EVERY instruction in the prefix has transform_jnz = NONE,
   each is passed through unchanged by transform_block_insts. After n such
   instructions, we have the original TAKE n plus the transformation of DROP n. *)
Theorem transform_block_insts_TAKE_DROP:
  !n fn insts.
    EVERY (\i. transform_jnz fn i = NONE) (TAKE n insts)
    ==>
    transform_block_insts fn insts =
      TAKE n insts ++ transform_block_insts fn (DROP n insts)
Proof
  Induct_on `n` >- simp[rich_listTheory.TAKE, rich_listTheory.DROP] >>
  rpt strip_tac >>
  Cases_on `insts`
  >- REWRITE_TAC[transform_block_insts_def, listTheory.TAKE_nil, listTheory.DROP_nil, listTheory.APPEND]
  >- (
    `transform_jnz fn h = NONE` by (
      pop_assum mp_tac >> REWRITE_TAC[rich_listTheory.TAKE, listTheory.EVERY_DEF] >> simp[]) >>
    ONCE_REWRITE_TAC[transform_block_insts_def] >>
    ASM_REWRITE_TAC[optionTheory.option_case_def] >>
    REWRITE_TAC[rich_listTheory.TAKE, rich_listTheory.DROP, listTheory.APPEND] >>
    AP_TERM_TAC >>
    first_x_assum irule >>
    pop_assum mp_tac >> REWRITE_TAC[rich_listTheory.TAKE, listTheory.EVERY_DEF] >> simp[] >>
    pop_assum mp_tac >> REWRITE_TAC[rich_listTheory.TAKE, listTheory.EVERY_DEF] >> simp[]
  )
QED

(* WHY THIS IS TRUE: transform_block_insts either keeps instructions (NONE case)
   or replaces them with multiple instructions (SOME case). Never fewer. *)
Theorem transform_block_insts_length_ge:
  !fn insts. LENGTH (transform_block_insts fn insts) >= LENGTH insts
Proof
  Induct_on `insts` >- simp[transform_block_insts_def] >>
  rw[] >> Cases_on `transform_jnz fn h`
  >- (
    ONCE_REWRITE_TAC[transform_block_insts_def] >>
    ASM_REWRITE_TAC[optionTheory.option_case_def] >>
    simp[listTheory.LENGTH] >> first_x_assum (qspec_then `fn` mp_tac) >> decide_tac
  )
  >- (
    ONCE_REWRITE_TAC[transform_block_insts_def] >>
    ASM_REWRITE_TAC[optionTheory.option_case_def] >>
    simp[] >>
    gvs[transform_jnz_def, AllCaseEqs()]
    >- (
      simp[transform_pattern1_def, mk_iszero_inst_def, mk_assert_inst_def, mk_jmp_inst_def] >>
      first_x_assum (qspec_then `fn` mp_tac) >> decide_tac
    )
    >- (
      simp[transform_pattern2_def, mk_assert_inst_def, mk_jmp_inst_def] >>
      first_x_assum (qspec_then `fn` mp_tac) >> decide_tac
    )
  )
QED

(* WHY THIS IS TRUE: When EVERY instruction in the prefix has transform_jnz = NONE,
   the transformation preserves the prefix. From TAKE_DROP we have:
   transform_block_insts fn insts = TAKE k insts ++ transform_block_insts fn (DROP k insts)
   So TAKE k (transform_block_insts fn insts) = TAKE k (TAKE k insts ++ ...) = TAKE k insts. *)
Theorem transform_block_insts_TAKE:
  !insts fn k.
    EVERY (\i. transform_jnz fn i = NONE) (TAKE k insts) ==>
    TAKE k (transform_block_insts fn insts) = TAKE k insts
Proof
  rw[] >>
  `transform_block_insts fn insts = TAKE k insts ++ transform_block_insts fn (DROP k insts)`
    by metis_tac[transform_block_insts_TAKE_DROP] >>
  pop_assum SUBST1_TAC >>
  Cases_on `k <= LENGTH insts`
  >- simp[rich_listTheory.TAKE_APPEND1]
  >- simp[listTheory.TAKE_LENGTH_TOO_LONG, listTheory.DROP_LENGTH_TOO_LONG, transform_block_insts_def]
QED

(* WHY THIS IS TRUE: With prefix of NONEs, first n instructions are unchanged.
   At index n, transform_jnz returns SOME new_insts, so HD new_insts is at index n. *)
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

(* WHY THIS IS TRUE: With n NONE transforms followed by pattern1 (which adds 3 insts),
   the result has at least n + 3 elements. *)
Theorem transform_block_insts_length_pattern1:
  !fn insts n cond_op label.
    n < LENGTH insts /\
    EVERY (λi. transform_jnz fn i = NONE) (TAKE n insts) /\
    transform_jnz fn (EL n insts) = SOME (transform_pattern1 (EL n insts) cond_op label)
    ==>
    LENGTH (transform_block_insts fn insts) >= n + 3
Proof
  rw[] >>
  `LENGTH (transform_pattern1 (EL n insts) cond_op label) = 3` by
    simp[transform_pattern1_def, LET_THM, mk_iszero_inst_def,
         mk_assert_inst_def, mk_jmp_inst_def] >>
  `transform_block_insts fn insts = TAKE n insts ++ transform_block_insts fn (DROP n insts)`
    by metis_tac[transform_block_insts_TAKE_DROP] >>
  `LENGTH (TAKE n insts) = n` by simp[listTheory.LENGTH_TAKE] >>
  `DROP n insts = EL n insts :: DROP (n + 1) insts` by (
    `n < LENGTH insts` by simp[] >>
    metis_tac[rich_listTheory.DROP_EL_CONS]
  ) >>
  `transform_block_insts fn (DROP n insts) =
   transform_pattern1 (EL n insts) cond_op label ++ transform_block_insts fn (DROP (n + 1) insts)` by (
    simp[transform_block_insts_def]
  ) >>
  simp[listTheory.LENGTH_APPEND]
QED

(* WHY THIS IS TRUE: With n NONE transforms followed by pattern2 (which adds 2 insts),
   the result has at least n + 2 elements. *)
Theorem transform_block_insts_length_pattern2:
  !fn insts n cond_op label.
    n < LENGTH insts /\
    EVERY (λi. transform_jnz fn i = NONE) (TAKE n insts) /\
    transform_jnz fn (EL n insts) = SOME (transform_pattern2 (EL n insts) cond_op label)
    ==>
    LENGTH (transform_block_insts fn insts) >= n + 2
Proof
  rw[] >>
  `LENGTH (transform_pattern2 (EL n insts) cond_op label) = 2` by
    simp[transform_pattern2_def, LET_THM, mk_assert_inst_def, mk_jmp_inst_def] >>
  `transform_block_insts fn insts = TAKE n insts ++ transform_block_insts fn (DROP n insts)`
    by metis_tac[transform_block_insts_TAKE_DROP] >>
  `LENGTH (TAKE n insts) = n` by simp[listTheory.LENGTH_TAKE] >>
  `DROP n insts = EL n insts :: DROP (n + 1) insts` by (
    `n < LENGTH insts` by simp[] >>
    metis_tac[rich_listTheory.DROP_EL_CONS]
  ) >>
  `transform_block_insts fn (DROP n insts) =
   transform_pattern2 (EL n insts) cond_op label ++ transform_block_insts fn (DROP (n + 1) insts)` by (
    simp[transform_block_insts_def]
  ) >>
  simp[listTheory.LENGTH_APPEND]
QED

(* ==========================================================================
   Fresh Variable Membership
   ========================================================================== *)

(* WHY THIS IS TRUE: The fresh variable for a pattern1 JNZ transformation
   is derived from the instruction ID. If the instruction is in the block
   and matches the pattern, the fresh var is in fresh_vars_in_block. *)
Theorem fresh_var_in_fresh_vars:
  !fn bb n cond_op if_nonzero if_zero.
    n < LENGTH bb.bb_instructions /\
    (EL n bb.bb_instructions).inst_operands = [cond_op; Label if_nonzero; Label if_zero] /\
    is_revert_label fn if_nonzero /\
    transform_jnz fn (EL n bb.bb_instructions) <> NONE
    ==>
    fresh_iszero_var (EL n bb.bb_instructions).inst_id IN fresh_vars_in_block fn bb
Proof
  rw[fresh_vars_in_block_def, pred_setTheory.GSPECIFICATION] >>
  qexists_tac `EL n bb.bb_instructions` >>
  simp[rich_listTheory.EL_MEM]
QED

(* ==========================================================================
   Pattern1: Indices n, n+1, n+2 contain ISZERO, ASSERT, JMP
   ========================================================================== *)

Theorem pattern1_transformed_instructions:
  !fn bb n cond_op if_zero.
    n < LENGTH bb.bb_instructions /\
    EVERY (\i. transform_jnz fn i = NONE) (TAKE n bb.bb_instructions) /\
    transform_jnz fn (EL n bb.bb_instructions) =
      SOME (transform_pattern1 (EL n bb.bb_instructions) cond_op if_zero)
    ==>
    let insts' = transform_block_insts fn bb.bb_instructions in
    let id = (EL n bb.bb_instructions).inst_id in
    let fresh_var = fresh_iszero_var id in
    EL n insts' = mk_iszero_inst id cond_op fresh_var /\
    EL (n + 1) insts' = mk_assert_inst (id + 1) (Var fresh_var) /\
    EL (n + 2) insts' = mk_jmp_inst (id + 2) if_zero
Proof
  rw[LET_THM] >>
  `EL n (transform_block_insts fn bb.bb_instructions) =
   HD (transform_pattern1 (EL n bb.bb_instructions) cond_op if_zero)` by
    (irule transform_block_insts_EL_transformed >> simp[]) >>
  fs[transform_pattern1_def, LET_THM] >>
  `transform_block_insts fn bb.bb_instructions =
   TAKE n bb.bb_instructions ++ transform_block_insts fn (DROP n bb.bb_instructions)`
    by metis_tac[transform_block_insts_TAKE_DROP] >>
  `DROP n bb.bb_instructions = EL n bb.bb_instructions :: DROP (n + 1) bb.bb_instructions`
    by (irule rich_listTheory.DROP_EL_CONS >> simp[]) >>
  gvs[transform_block_insts_def] >>
  simp[listTheory.EL_APPEND_EQN, listTheory.LENGTH_TAKE]
QED

(* Pattern 2: JNZ -> [ASSERT, JMP] *)
Theorem pattern2_transformed_instructions:
  !fn bb n cond_op if_nonzero.
    n < LENGTH bb.bb_instructions /\
    EVERY (\i. transform_jnz fn i = NONE) (TAKE n bb.bb_instructions) /\
    transform_jnz fn (EL n bb.bb_instructions) =
      SOME (transform_pattern2 (EL n bb.bb_instructions) cond_op if_nonzero)
    ==>
    let insts' = transform_block_insts fn bb.bb_instructions in
    let id = (EL n bb.bb_instructions).inst_id in
    EL n insts' = mk_assert_inst id cond_op /\
    EL (n + 1) insts' = mk_jmp_inst (id + 1) if_nonzero
Proof
  rw[LET_THM] >>
  `EL n (transform_block_insts fn bb.bb_instructions) =
   HD (transform_pattern2 (EL n bb.bb_instructions) cond_op if_nonzero)` by
    (irule transform_block_insts_EL_transformed >> simp[]) >>
  fs[transform_pattern2_def, LET_THM] >>
  `transform_block_insts fn bb.bb_instructions =
   TAKE n bb.bb_instructions ++ transform_block_insts fn (DROP n bb.bb_instructions)`
    by metis_tac[transform_block_insts_TAKE_DROP] >>
  `DROP n bb.bb_instructions = EL n bb.bb_instructions :: DROP (n + 1) bb.bb_instructions`
    by (irule rich_listTheory.DROP_EL_CONS >> simp[]) >>
  gvs[transform_block_insts_def] >>
  simp[listTheory.EL_APPEND_EQN, listTheory.LENGTH_TAKE]
QED

