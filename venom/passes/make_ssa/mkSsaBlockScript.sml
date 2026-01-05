(*
 * SSA Construction Block-Level Correctness: Block Execution
 *
 * TOP-LEVEL:
 *   - step_in_block_ssa_result_equiv
 *   - run_block_ssa_equiv
 *
 * Helpers:
 *   - next_inst_ssa_equiv
 *)

Theory mkSsaBlock
Ancestors
  mkSsaBlockStep mkSsaBlockCompat
  mkSsaStateEquiv venomSem venomState venomInst

(* ==========================================================================
   Block Execution Equivalence
   ========================================================================== *)

Theorem next_inst_ssa_equiv:
  !vm s_orig s_ssa.
    ssa_state_equiv vm s_orig s_ssa ==>
    ssa_state_equiv vm (next_inst s_orig) (next_inst s_ssa)
Proof
  rw[ssa_state_equiv_def, var_map_equiv_def, next_inst_def, lookup_var_def]
QED

(* Block step preserves SSA equivalence - Result version
 *
 * PROOF SKETCH:
 * 1. Unfold step_in_block_def in both states
 * 2. Since s_orig.vs_inst_idx = s_ssa.vs_inst_idx (from ssa_state_equiv),
 *    get_instruction returns the same index in both blocks
 * 3. Use inst_ssa_compatible to establish relationship between instructions
 * 4. Apply step_inst_result_ssa_equiv (requires non-PHI assumption)
 * 5. For matching result types: ssa_result_equiv propagates
 * 6. is_terminator is the same since inst_ssa.inst_opcode = inst.inst_opcode
 * 7. For non-terminator case, next_inst preserves ssa_state_equiv
 *)
Theorem step_in_block_ssa_result_equiv:
  !bb bb_ssa s_orig s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    LENGTH bb_ssa.bb_instructions = LENGTH bb.bb_instructions /\
    (!idx. idx < LENGTH bb.bb_instructions ==>
           inst_ssa_compatible vm
             (EL idx bb.bb_instructions)
             (EL idx bb_ssa.bb_instructions)) /\
    (!idx. idx < LENGTH bb.bb_instructions ==>
           LENGTH (EL idx bb.bb_instructions).inst_outputs <= 1) ==>
    ssa_result_equiv vm
      (FST (step_in_block bb s_orig))
      (FST (step_in_block bb_ssa s_ssa)) /\
    SND (step_in_block bb s_orig) = SND (step_in_block bb_ssa s_ssa)
Proof
  rpt strip_tac >>
  simp[step_in_block_def] >>
  (* Establish inst_idx equality from ssa_state_equiv *)
  `s_orig.vs_inst_idx = s_ssa.vs_inst_idx` by fs[ssa_state_equiv_def] >>
  (* Case split on get_instruction result - creates 4 subgoals *)
  Cases_on `get_instruction bb s_orig.vs_inst_idx` >> simp[] >>
  gvs[get_instruction_def] >>
  (* Now handle both NONE and SOME cases *)
  TRY (
    (* NONE case: both blocks return Error "block not terminated" *)
    `s_ssa.vs_inst_idx >= LENGTH bb_ssa.bb_instructions` by simp[] >>
    simp[ssa_result_equiv_def] >> NO_TAC
  ) >>
  (* SOME x case: x = EL s_orig.vs_inst_idx bb.bb_instructions *)
  (* gvs should have unified x with the EL expression *)
  `s_ssa.vs_inst_idx < LENGTH bb_ssa.bb_instructions` by simp[] >>
  simp[] >>
  (* Get inst_ssa_compatible, non-PHI, and LENGTH <= 1 *)
  `inst_ssa_compatible vm (EL s_ssa.vs_inst_idx bb.bb_instructions)
                          (EL s_ssa.vs_inst_idx bb_ssa.bb_instructions)`
    by (first_x_assum (qspec_then `s_ssa.vs_inst_idx` mp_tac) >> simp[]) >>
  `LENGTH (EL s_ssa.vs_inst_idx bb.bb_instructions).inst_outputs <= 1`
    by (first_x_assum (qspec_then `s_ssa.vs_inst_idx` mp_tac) >> simp[]) >>
  (* Get opcode equality for is_terminator *)
  `(EL s_ssa.vs_inst_idx bb.bb_instructions).inst_opcode =
   (EL s_ssa.vs_inst_idx bb_ssa.bb_instructions).inst_opcode`
    by fs[inst_ssa_compatible_def] >>
  (* Apply step_inst_result_ssa_equiv *)
  `ssa_result_equiv vm
     (step_inst (EL s_ssa.vs_inst_idx bb.bb_instructions) s_orig)
     (step_inst (EL s_ssa.vs_inst_idx bb_ssa.bb_instructions) s_ssa)`
    by (irule step_inst_result_ssa_equiv >> simp[]) >>
  (* Case split on step_inst results - they must match by ssa_result_equiv *)
  Cases_on `step_inst (EL s_ssa.vs_inst_idx bb.bb_instructions) s_orig` >>
  Cases_on `step_inst (EL s_ssa.vs_inst_idx bb_ssa.bb_instructions) s_ssa` >>
  fs[ssa_result_equiv_def] >>
  (* OK-OK case: need to handle is_terminator branch *)
  TRY (
    (* For OK-OK: case split on is_terminator *)
    Cases_on `is_terminator (EL s_ssa.vs_inst_idx bb_ssa.bb_instructions).inst_opcode` >>
    simp[ssa_result_equiv_def] >>
    (* Non-terminator case needs next_inst_ssa_equiv *)
    TRY (irule next_inst_ssa_equiv >> simp[]) >>
    NO_TAC
  ) >>
  (* Contradictory cases (OK vs Halt/Revert/Error) eliminated by ssa_result_equiv_def *)
  simp[]
QED

(* TOP-LEVEL: Full block execution preserves SSA equivalence
 *
 * This is the key theorem: running equivalent blocks with equivalent states
 * produces equivalent results. Uses strong induction on remaining instructions.
 *
 * The run_block function terminates because:
 * - Each non-terminator step increments inst_idx
 * - The measure (LENGTH bb.bb_instructions - s.vs_inst_idx) decreases
 * - Terminator instructions exit immediately
 *
 * We use the same measure for induction. *)
(* NOTE: This theorem is correct but the proof is complex due to the need
 * to carry bb_ssa through the induction while inducting on bb/s_orig.
 * The key insight is that step_in_block_ssa_result_equiv gives us:
 * 1. ssa_result_equiv for the step results
 * 2. SND equality (is_terminator flag)
 * Then for OK-OK case:
 * - vs_halted is equal (from ssa_state_equiv)
 * - is_terminator is equal (SND equality)
 * - For recursive case: apply IH with measure (LENGTH - inst_idx) decreasing
 *   because step_in_block increments inst_idx via next_inst for non-terminators *)
(* Proof strategy: Use recInduct on run_block for the block we're proving
 * ssa_result_equiv about. The IH gives us the result for recursive calls. *)
Theorem run_block_ssa_equiv:
  !bb s_orig bb_ssa s_ssa vm.
    ssa_state_equiv vm s_orig s_ssa /\
    LENGTH bb_ssa.bb_instructions = LENGTH bb.bb_instructions /\
    (!idx. idx < LENGTH bb.bb_instructions ==>
           inst_ssa_compatible vm
             (EL idx bb.bb_instructions)
             (EL idx bb_ssa.bb_instructions)) /\
    (!idx. idx < LENGTH bb.bb_instructions ==>
           LENGTH (EL idx bb.bb_instructions).inst_outputs <= 1) ==>
    ssa_result_equiv vm (run_block bb s_orig) (run_block bb_ssa s_ssa)
Proof
  recInduct run_block_ind >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  simp[Once run_block_def] >>
  Cases_on `step_in_block bb s` >>
  Cases_on `q` >> gvs[] >| [
    (* OK case *)
    qspecl_then [`bb`, `bb_ssa`, `s`, `s_ssa`, `vm`]
      mp_tac step_in_block_ssa_result_equiv >> simp[] >> strip_tac >>
    simp[Once run_block_def] >>
    Cases_on `step_in_block bb_ssa s_ssa` >> gvs[ssa_result_equiv_def] >>
    Cases_on `q` >> gvs[ssa_result_equiv_def] >>
    `v.vs_halted = v'.vs_halted` by fs[ssa_state_equiv_def] >>
    Cases_on `v.vs_halted` >> gvs[ssa_result_equiv_def] >-
    (* vs_halted = T: halted case, close with run_block unfolding *)
    simp[Once run_block_def, ssa_result_equiv_def] >>
    (* vs_halted = F: continue with terminator check *)
    Cases_on `r` >> gvs[ssa_result_equiv_def] >-
    (* r = T: terminator, close with run_block unfolding *)
    simp[Once run_block_def, ssa_result_equiv_def] >>
    (* r = F: Non-terminator recursive case, apply IH *)
    simp[] >>
    CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [run_block_def])) >>
    simp[] >>
    CONV_TAC (RATOR_CONV (RAND_CONV (ONCE_REWRITE_CONV [GSYM run_block_def]))) >>
    first_assum irule >> simp[]
    ,
    (* Halt case *)
    qspecl_then [`bb`, `bb_ssa`, `s`, `s_ssa`, `vm`]
      mp_tac step_in_block_ssa_result_equiv >> simp[] >> strip_tac >>
    simp[Once run_block_def] >>
    Cases_on `step_in_block bb_ssa s_ssa` >> gvs[ssa_result_equiv_def] >>
    Cases_on `q` >> gvs[ssa_result_equiv_def]
    ,
    (* Revert case *)
    qspecl_then [`bb`, `bb_ssa`, `s`, `s_ssa`, `vm`]
      mp_tac step_in_block_ssa_result_equiv >> simp[] >> strip_tac >>
    simp[Once run_block_def] >>
    Cases_on `step_in_block bb_ssa s_ssa` >> gvs[ssa_result_equiv_def] >>
    Cases_on `q` >> gvs[ssa_result_equiv_def]
    ,
    (* Error case *)
    qspecl_then [`bb`, `bb_ssa`, `s`, `s_ssa`, `vm`]
      mp_tac step_in_block_ssa_result_equiv >> simp[] >> strip_tac >>
    simp[Once run_block_def] >>
    Cases_on `step_in_block bb_ssa s_ssa` >> gvs[ssa_result_equiv_def] >>
    Cases_on `q` >> gvs[ssa_result_equiv_def]
  ]
QED
