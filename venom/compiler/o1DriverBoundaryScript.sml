(* Bounded probes of the actual O1 driver. No general pass certificate. *)
Theory o1DriverBoundary
Ancestors
  unitTransformDefs venomPipelineDriver venomPipelineRunner
  stateEquivProps dftDefs passSimulationDefs

Theorem unit_result_rel_refl_terminal:
  terminates res ==> unit_result_rel res res
Proof
  Cases_on `res` >> simp[terminates_def, unit_result_rel_def,
                         observable_equiv_refl]
QED

Theorem unit_result_rel_trans:
  unit_result_rel x y /\ unit_result_rel y z ==> unit_result_rel x z
Proof
  Cases_on `x` >> Cases_on `y` >> Cases_on `z` >>
  simp[unit_result_rel_def] >> metis_tac[observable_equiv_trans]
QED

Theorem ctx_transform_correct_refl:
  ctx_transform_correct ctx ctx s
Proof
  rw[ctx_transform_correct_def] >> qexists_tac `fuel` >>
  simp[unit_result_rel_refl_terminal]
QED

Theorem ctx_transform_correct_trans:
  ctx_transform_correct a b s /\ ctx_transform_correct b c s ==>
  ctx_transform_correct a c s
Proof
  rw[ctx_transform_correct_def] >>
  first_x_assum drule >> strip_tac >>
  drule unit_result_rel_terminates >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  metis_tac[unit_result_rel_trans]
QED

Theorem checked_identity_pipeline:
  checked_unit_transform_correct
    (\p u. SOME <|po_unit := u; po_final_assembly := p.rpol_final_assembly|>)
    rpolicy unit s
Proof
  simp[checked_unit_transform_correct_def, ctx_transform_correct_refl]
QED

Theorem empty_stages_boundary:
  run_pipeline_stages rpolicy [] unit supply = SOME (unit,supply) /\
  ctx_transform_correct unit.cu_context unit.cu_context s
Proof
  simp[run_pipeline_stages_def, ctx_transform_correct_refl]
QED

Theorem o1_actual_stage_tags:
  pipeline_spec_tags o1_pipeline_spec =
    [VP_SimplifyCFG; VP_DretDesugar; VP_MakeSSA; VP_LowerDload;
     VP_ConcretizeMemLoc; VP_FmpLowering; VP_MakeSSA; VP_SimplifyCFG;
     VP_SingleUseExpansion; VP_DFT; VP_CFGNormalization]
Proof
  simp[pipeline_spec_tags_def, pipeline_stage_tags_def,
       o1_pipeline_spec_def, o1_fn_passes_def, fn_pass_tag_def]
QED
