(*
 * SSA Construction Function-Level Correctness
 *
 * This theory proves function-level correctness of SSA construction.
 * Executing a function in non-SSA form gives equivalent results to
 * executing the SSA-transformed function.
 *
 * ============================================================================
 * STRUCTURE OVERVIEW
 * ============================================================================
 *
 * TOP-LEVEL THEOREMS:
 *   - ssa_construction_correct       : Function-level correctness
 *   - ssa_construction_context_correct : Context-level correctness
 *
 * HELPER THEOREMS:
 *   - run_function_ssa_equiv         : Function execution preserves equiv
 *   - run_block_ssa_equiv            : Block execution preserves equiv
 *
 * ============================================================================
 *)

Theory ssaFunction
Ancestors
  ssaDefs ssaTransform ssaStateEquiv ssaWellFormed ssaBlock
  venomState venomInst venomSem list finite_map

(* ==========================================================================
   Function Execution Equivalence
   ========================================================================== *)

(* Theorem: wf_ssa_operand equals ssa_operand (they're defined identically) *)
Theorem wf_ssa_operand_eq_ssa_operand:
  !vm op. wf_ssa_operand vm op = ssa_operand vm op
Proof
  Cases_on `op` >> rw[wf_ssa_operand_def, ssa_operand_def]
QED

(* Theorem: wf_inst_ssa_compatible equals inst_ssa_compatible *)
Theorem wf_inst_ssa_compatible_eq:
  !vm inst inst_ssa.
    wf_inst_ssa_compatible vm inst inst_ssa <=> inst_ssa_compatible vm inst inst_ssa
Proof
  rw[wf_inst_ssa_compatible_def, inst_ssa_compatible_def] >>
  eq_tac >> rpt strip_tac >> fs[MAP_EQ_f, wf_ssa_operand_eq_ssa_operand]
QED

(* Helper: Blocks are SSA compatible *)
Definition blocks_ssa_compatible_def:
  blocks_ssa_compatible vm [] [] = T /\
  blocks_ssa_compatible vm (bb::bbs) (bb_ssa::bbs_ssa) =
    (bb.bb_label = bb_ssa.bb_label /\
     LENGTH bb.bb_instructions = LENGTH bb_ssa.bb_instructions /\
     (!idx. idx < LENGTH bb.bb_instructions ==>
            inst_ssa_compatible vm
              (EL idx bb.bb_instructions)
              (EL idx bb_ssa.bb_instructions)) /\
     blocks_ssa_compatible vm bbs bbs_ssa) /\
  blocks_ssa_compatible vm _ _ = F
End

(* Theorem: wf_blocks_ssa_compatible equals blocks_ssa_compatible *)
Theorem wf_blocks_ssa_compatible_eq:
  !vm blocks blocks_ssa.
    wf_blocks_ssa_compatible vm blocks blocks_ssa <=>
    blocks_ssa_compatible vm blocks blocks_ssa
Proof
  Induct_on `blocks` >>
  simp[wf_blocks_ssa_compatible_def, blocks_ssa_compatible_def] >>
  rpt strip_tac >> Cases_on `blocks_ssa` >>
  simp[wf_blocks_ssa_compatible_def, blocks_ssa_compatible_def] >>
  eq_tac >> rpt strip_tac >> fs[wf_inst_ssa_compatible_eq]
QED

(* Helper: Function is SSA compatible *)
Definition fn_ssa_compatible_def:
  fn_ssa_compatible vm fn fn_ssa <=>
    fn.fn_name = fn_ssa.fn_name /\
    LENGTH fn.fn_blocks = LENGTH fn_ssa.fn_blocks /\
    blocks_ssa_compatible vm fn.fn_blocks fn_ssa.fn_blocks
End

(* Helper: lookup_block failure preserves under SSA compatibility *)
Theorem lookup_block_ssa_compatible_none:
  !vm blocks blocks_ssa lbl.
    blocks_ssa_compatible vm blocks blocks_ssa /\
    lookup_block lbl blocks = NONE ==>
    lookup_block lbl blocks_ssa = NONE
Proof
  Induct_on `blocks` >> simp[lookup_block_def, blocks_ssa_compatible_def] >>
  rpt strip_tac >> Cases_on `blocks_ssa` >> gvs[blocks_ssa_compatible_def] >>
  Cases_on `h.bb_label = lbl` >> gvs[lookup_block_def] >>
  first_x_assum drule_all >> simp[]
QED

(* Helper: lookup_block preserves under SSA compatibility *)
Theorem lookup_block_ssa_compatible:
  !vm blocks blocks_ssa lbl bb.
    blocks_ssa_compatible vm blocks blocks_ssa /\
    lookup_block lbl blocks = SOME bb ==>
    ?bb_ssa.
      lookup_block lbl blocks_ssa = SOME bb_ssa /\
      bb.bb_label = bb_ssa.bb_label /\
      LENGTH bb.bb_instructions = LENGTH bb_ssa.bb_instructions /\
      (!idx. idx < LENGTH bb.bb_instructions ==>
             inst_ssa_compatible vm
               (EL idx bb.bb_instructions)
               (EL idx bb_ssa.bb_instructions))
Proof
  Induct_on `blocks` >> simp[lookup_block_def, blocks_ssa_compatible_def] >>
  rpt strip_tac >> Cases_on `blocks_ssa` >> gvs[blocks_ssa_compatible_def] >>
  Cases_on `h.bb_label = lbl` >> gvs[lookup_block_def] >>
  first_x_assum drule_all >> simp[]
QED

(* Helper: lookup_block success implies membership *)
Theorem lookup_block_MEM:
  !lbl blocks bb.
    lookup_block lbl blocks = SOME bb ==> MEM bb blocks
Proof
  Induct_on `blocks` >> simp[lookup_block_def] >>
  rpt strip_tac >> Cases_on `h.bb_label = lbl` >> fs[] >>
  res_tac >> simp[]
QED

(* run_block ignores the fn parameter *)
Theorem run_block_fn_irrelevant:
  !fn1 bb s fn2. run_block fn1 bb s = run_block fn2 bb s
Proof
  ho_match_mp_tac run_block_ind >> rpt strip_tac >>
  simp[Once run_block_def, step_in_block_def] >>
  CONV_TAC (RHS_CONV (ONCE_REWRITE_CONV [run_block_def])) >>
  simp[step_in_block_def] >>
  rpt (CASE_TAC >> simp[]) >>
  rpt strip_tac >> first_x_assum irule >> simp[step_in_block_def]
QED

(* ==========================================================================
   Main Correctness Theorem
   ========================================================================== *)

(* Helper: Block execution preserves SSA equivalence.
 *
 * PROOF SKETCH:
 * 1. Use ho_match_mp_tac run_block_ind for induction on block execution
 * 2. Base case: When step_in_block returns a terminator (is_term = T) or Halt/Revert
 *    - Apply step_in_block_ssa_result_equiv directly
 * 3. Inductive case: step_in_block returns OK with is_term = F
 *    - Apply step_in_block_ssa_result_equiv to get ssa_state_equiv vm' for intermediate states
 *    - Apply IH on the continuation
 * 4. Key insight: The vm mapping may evolve during execution as new variables
 *    are defined, but the mapping always remains consistent.
 *
 * NOTE: This proof assumes step_inst_non_phi_ssa_equiv returns the updated vm'
 * which extends the original vm. The current statement uses a fixed vm, which
 * may need adjustment to allow vm to evolve through the block.
 *)
Theorem run_block_ssa_equiv:
  !fn fn_ssa bb bb_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    bb.bb_label = bb_ssa.bb_label /\
    LENGTH bb.bb_instructions = LENGTH bb_ssa.bb_instructions /\
    (!idx. idx < LENGTH bb.bb_instructions ==>
           inst_ssa_compatible vm
             (EL idx bb.bb_instructions)
             (EL idx bb_ssa.bb_instructions)) /\
    (* No PHIs in this block - they're handled specially *)
    (!idx. idx < LENGTH bb.bb_instructions ==>
           (EL idx bb.bb_instructions).inst_opcode <> PHI) ==>
    (* Single-output instructions only *)
    (!idx. idx < LENGTH bb.bb_instructions ==>
           LENGTH (EL idx bb.bb_instructions).inst_outputs <= 1) ==>
    ssa_result_equiv vm (run_block fn bb s_orig) (run_block fn_ssa bb_ssa s_ssa)
Proof
  rpt strip_tac >>
  `run_block fn_ssa bb_ssa s_ssa = run_block fn bb_ssa s_ssa` by
    (irule run_block_fn_irrelevant >> simp[]) >>
  rw[] >>
  irule ssaBlockTheory.run_block_ssa_equiv >>
  simp[]
QED

(* TOP-LEVEL: Function execution preserves SSA equivalence.
 *
 * PROOF SKETCH:
 * 1. Induction on fuel
 * 2. Base case (fuel = 0): Both return Error OutOfFuel, trivially equivalent
 * 3. Inductive case:
 *    a. lookup_block on s_orig.vs_current_bb gives bb
 *    b. lookup_block_ssa_compatible gives corresponding bb_ssa
 *    c. run_block_ssa_equiv shows block execution preserves equivalence
 *    d. For OK case with jump: use IH on new current block
 *    e. For Halt/Revert: use halt_state_ssa_equiv / revert_state_ssa_equiv
 *
 * KEY PRECONDITIONS:
 * - fn_ssa_compatible vm fn fn_ssa: blocks correspond under vm
 * - wf_input_fn fn: ensures no PHIs in entry block and other well-formedness
 *
 * The proof follows structure of phi_elimination's run_function_result_equiv,
 * but uses ssa_state_equiv instead of state_equiv.
 *)
Theorem run_function_ssa_equiv:
  !fuel fn fn_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    fn_ssa_compatible vm fn fn_ssa /\
    wf_input_fn fn ==>
    ssa_result_equiv vm
      (run_function fuel fn s_orig)
      (run_function fuel fn_ssa s_ssa)
Proof
  Induct_on `fuel` >> rpt strip_tac
  >- simp[run_function_def, ssa_result_equiv_def] >>
  `s_orig.vs_current_bb = s_ssa.vs_current_bb` by fs[ssa_state_equiv_def] >>
  CONV_TAC (RATOR_CONV (RAND_CONV (ONCE_REWRITE_CONV [run_function_def]))) >>
  CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [run_function_def])) >>
  simp[] >>
  Cases_on `lookup_block s_orig.vs_current_bb fn.fn_blocks` >> gvs[]
  >- (
    `blocks_ssa_compatible vm fn.fn_blocks fn_ssa.fn_blocks` by
      fs[fn_ssa_compatible_def] >>
    `lookup_block s_orig.vs_current_bb fn_ssa.fn_blocks = NONE` by (
      irule lookup_block_ssa_compatible_none >> simp[]
    ) >>
    simp[ssa_result_equiv_def]
  ) >>
  rename1 `lookup_block _ _ = SOME bb` >>
  `blocks_ssa_compatible vm fn.fn_blocks fn_ssa.fn_blocks` by
    fs[fn_ssa_compatible_def] >>
  drule_all lookup_block_ssa_compatible >> strip_tac >>
  gvs[] >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `!idx. idx < LENGTH bb.bb_instructions ==>
         (EL idx bb.bb_instructions).inst_opcode <> PHI` by (
    rpt strip_tac >>
    `get_instruction bb idx = SOME (EL idx bb.bb_instructions)` by
      simp[get_instruction_def] >>
    fs[wf_input_fn_def, no_phi_fn_def]
  ) >>
  `!idx. idx < LENGTH bb.bb_instructions ==>
         LENGTH (EL idx bb.bb_instructions).inst_outputs <= 1` by (
    rpt strip_tac >>
    `get_instruction bb idx = SOME (EL idx bb.bb_instructions)` by
      simp[get_instruction_def] >>
    fs[wf_input_fn_def, single_output_fn_def]
  ) >>
  `ssa_result_equiv vm (run_block fn bb s_orig) (run_block fn_ssa bb_ssa s_ssa)` by (
    irule run_block_ssa_equiv >> simp[]
  ) >>
  Cases_on `run_block fn bb s_orig` >>
  Cases_on `run_block fn_ssa bb_ssa s_ssa` >>
  gvs[ssa_result_equiv_def] >>
  `v.vs_halted = v'.vs_halted` by fs[ssa_state_equiv_def] >>
  Cases_on `v.vs_halted` >> gvs[ssa_result_equiv_def] >>
  first_x_assum irule >> simp[]
QED

(* ==========================================================================
   Main Correctness Theorem
   ========================================================================== *)

(* TOP-LEVEL: SSA construction is correct.
 *
 * If:
 * - The input function is well-formed
 * - The transformation produces fn_ssa with variable mapping vm
 * - The initial states are SSA-equivalent under vm
 *
 * Then executing the original and transformed functions produces
 * equivalent results.
 *)
(* Helper: valid_ssa_transform implies fn_ssa_compatible.
 *
 * PROOF SKETCH:
 * 1. Unfold valid_ssa_transform_def to get wf_blocks_ssa_compatible
 * 2. Use wf_blocks_ssa_compatible_eq to convert to blocks_ssa_compatible
 * 3. Use wf_inst_ssa_compatible_eq to convert to inst_ssa_compatible
 * 4. Build fn_ssa_compatible from the components
 *
 * The connection between wf_* and non-wf_* versions is established
 * by wf_ssa_operand_eq_ssa_operand and wf_inst_ssa_compatible_eq above.
 *)
Theorem valid_ssa_transform_compatible:
  !fn fn_ssa vm.
    valid_ssa_transform fn fn_ssa vm ==>
    fn_ssa_compatible vm fn fn_ssa
Proof
  rw[valid_ssa_transform_def, fn_ssa_compatible_def] >>
  fs[wf_blocks_ssa_compatible_eq]
QED

Theorem ssa_construction_correct:
  !fuel fn fn_ssa vm s_orig s_ssa result.
    valid_ssa_transform fn fn_ssa vm /\
    ssa_state_equiv vm s_orig s_ssa /\
    run_function fuel fn s_orig = result ==>
    ?result_ssa.
      run_function fuel fn_ssa s_ssa = result_ssa /\
      ssa_result_equiv vm result result_ssa
Proof
  rpt strip_tac >>
  fs[valid_ssa_transform_def] >>
  (* Establish fn_ssa_compatible from valid_ssa_transform *)
  `fn_ssa_compatible vm fn fn_ssa` by (
    irule valid_ssa_transform_compatible >> simp[valid_ssa_transform_def]
  ) >>
  (* Use run_function_ssa_equiv *)
  qspecl_then [`fuel`, `fn`, `fn_ssa`, `s_orig`, `s_ssa`, `vm`]
    mp_tac run_function_ssa_equiv >> simp[] >>
  strip_tac >>
  qexists_tac `run_function fuel fn_ssa s_ssa` >> simp[]
QED

(* ==========================================================================
   Context-Level Correctness
   ========================================================================== *)

(* TOP-LEVEL: Context-level correctness *)
Theorem ssa_construction_context_correct:
  !ctx fn_name fuel fn fn_ssa vm s_orig s_ssa result.
    MEM fn ctx.ctx_functions /\
    fn.fn_name = fn_name /\
    valid_ssa_transform fn fn_ssa vm /\
    ssa_state_equiv vm s_orig s_ssa /\
    run_function fuel fn s_orig = result ==>
    ?result_ssa.
      run_function fuel fn_ssa s_ssa = result_ssa /\
      ssa_result_equiv vm result result_ssa
Proof
  rpt strip_tac >>
  irule ssa_construction_correct >>
  qexistsl_tac [`fn`, `s_orig`] >> simp[]
QED
