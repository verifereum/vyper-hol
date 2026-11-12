(* Initial witness diagnostics; no full-contract falsehood asserted. *)
Theory targetPureWalkWitnessProbe
Ancestors
  targetPureWalkConditionalSim targetPureWalkOracleProbe targetPureWalkCallerProbe
  targetPureWalkSimulationProbe exprLoweringProps venomInst venomExecSemantics

Theorem witness_context_forces_callee:
  !fn s. alloca_room simulation_probe_context fn s ==>
    fn = simulation_probe_callee
Proof
  simp[alloca_room_def, simulation_probe_context_def, mk_venom_context_def,
       lookup_function_def, listTheory.FIND_thm] >>
  rpt strip_tac >> gvs[AllCaseEqs()]
QED
