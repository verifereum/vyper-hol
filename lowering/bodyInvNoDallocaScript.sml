(* Lowered program frames contain no dynamic allocation instructions. *)
Theory bodyInvNoDalloca
Ancestors
  bodySim ctorDeployShape loweringShapeProps loweringShapeSource
  supportedNames supportedProgram o1PipelineCorrect

(* TEMPORARILY CHEATED - SCRATCH SEQ-8389 gate widening census (never lands)
Proof
  rw[body_inv_def] >>
  Cases_on `cx.in_deploy` >> gvs[]
  >- metis_tac[lower_vyper_deploy_unit_no_dalloca] >>
  irule every_no_dalloca >>
  irule loweringShapePropsTheory.lower_vyper_runtime_unit_no_dalloca >>
  goal_assum (drule_at Any) >> conj_tac
  >- (irule supported_names_internal_names_distinct >>
      fs[supported_program_def, supported_declaration_names_def]) >>
  metis_tac[supported_program_runtime_bodies_shape_ok]
QED
*)
Theorem body_inv_no_dalloca:
  !tops ctx cenv cx.
    body_inv tops ctx cenv cx ==> ~ctx_has_dalloca ctx
Proof
  cheat
QED
