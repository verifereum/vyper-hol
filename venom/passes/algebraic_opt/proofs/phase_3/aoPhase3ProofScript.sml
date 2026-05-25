(* Phase 3: Main rewrite pass correctness.
 *
 * The iszero peephole + range-guarded arithmetic rewrites transform
 * fn0 → fn1 preserving execution up to fresh variables.
 *
 * TOP-LEVEL: ao_phase3_correct
 *)

Theory aoPhase3Proof
Ancestors
  algebraicOptDefs algebraicOptBlockSim
  aoResolveObligation aoRangeObligation
  aoStepInvObligation aoBlockInvObligation
  venomExecSemantics venomWf venomState venomInst
  stateEquiv stateEquivProps execEquivProps
  passSimulationProps passSimulationDefs
  analysisSimDefs rangeAnalysisDefs
Libs
  pairLib BasicProvers

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
