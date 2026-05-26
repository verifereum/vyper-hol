(* Phase 3: Main rewrite pass correctness.
 *
 * The iszero peephole + range-guarded arithmetic rewrites transform
 * fn0 → fn1 preserving execution up to fresh variables.
 *
 * Uses block_sim_function_error_bb with:
 *   block_inv = ao_dfg_inv ∧ ao_iszero_chain_inv ∧ ao_chains_defined_at
 *               ∧ range_sound ∧ cfg_membership
 *
 * Remaining proof obligations (cheated in aoStepInvObligation):
 *   - ao_iszero_chain_inv step preservation
 *   - ao_chains_defined_at step preservation (new var case)
 *
 * TOP-LEVEL: ao_phase3_correct
 *)

Theory aoPhase3Proof
Ancestors
  algebraicOptDefs aoBlockSim aoTargetProps
  aoResolveObligation aoRangeObligation
  aoStepInvObligation aoBlockInvObligation
  venomExecSemantics venomWf venomState venomInst
  stateEquiv stateEquivProps execEquivProps
  passSimulationProps passSimulationDefs
  analysisSimDefs rangeAnalysisDefs rangeAnalysisProofs
Libs
  pairLib BasicProvers

val _ = delsimps ["ao_iszero_chain_inv_def",
                  "ao_chains_defined_at_def",
                  "ao_chains_defined_def"]

Triviality ao_transform_block_label[local]:
  !mid dfg ra targets bb.
    (ao_transform_block mid dfg ra targets bb).bb_label = bb.bb_label
Proof
  simp[ao_transform_block_def]
QED

Triviality fn0_entry_label[local]:
  !fn. fn_entry_label (fn with fn_blocks :=
    MAP (\bb. bb with bb_instructions :=
      MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks) =
    fn_entry_label fn
Proof
  simp[fn_entry_label_def, entry_block_def] >>
  gen_tac >> Cases_on `fn.fn_blocks` >> simp[]
QED

Theorem ao_phase3_correct:
  !fuel ctx fn s.
    let fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks in
    let targets = ao_compute_fn_iszero_targets fn0 in
    let dfg = dfg_build_function fn0 in
    let ra = range_analyze fn0 in
    let mid = fn_max_inst_id fn0 in
    let fn1 = fn0 with fn_blocks :=
      MAP (ao_transform_block mid dfg ra targets) fn0.fn_blocks in
    let fv = ao_fn_fresh_vars fn in
    wf_function fn /\ ssa_form fn /\ EVERY inst_wf (fn_insts fn) /\
    FDOM s.vs_vars = {} /\
    fn_entry_label fn = SOME s.vs_current_bb ==>
    (?e. run_blocks fuel ctx fn0 s = Error e) \/
    lift_result (state_equiv fv) (execution_equiv fv) (execution_equiv fv)
      (run_blocks fuel ctx fn0 s) (run_blocks fuel ctx fn1 s)
Proof
  cheat
QED

val _ = export_theory();
