Theory fmpStageCoverBackScfgShape
Ancestors
  fmpStageCoverBackScfgStructure fmpStageCoverBackMssaLabels
  fmpStageCoverBackCfgArity venomPassDispatcher o1PassContract

(* The actual MakeSSA pass supplies precisely the structural interface used
   by the SimplifyCFG user-parameter count boundary. *)
Theorem fmp_cover_back_scfg_input_shape:
  fmp_stage_lowered infos ctx runner fn lowered /\ o1_fn_shape C fn /\
  fn_pass_step rpolicy (CFP_Simple VP_MakeSSA) observed s lowered out ==>
  ALL_DISTINCT (fn_labels out.fpo_function) /\
  out.fpo_function.fn_blocks <> [] /\
  EVERY bb_well_formed out.fpo_function.fn_blocks /\
  EVERY inst_wf (fn_insts out.fpo_function) /\
  EVERY label_positions_ok (fn_insts out.fpo_function) /\
  first_block_no_preds out.fpo_function /\
  fn_succs_closed out.fpo_function /\
  fn_label_refs_ok out.fpo_function /\
  EVERY (\i. i.inst_opcode <> PHI)
    (HD out.fpo_function.fn_blocks).bb_instructions
Proof
  strip_tac >>
  `execute_configured_fn_pass rpolicy (CFP_Simple VP_MakeSSA)
     observed s lowered = SOME out` by gvs[fn_pass_step_def] >>
  Cases_on `make_ssa_current_fn s lowered` >>
  gvs[execute_configured_fn_pass_make_ssa] >>
  drule_all fmp_cover_back_stage_make_ssa_structure >> strip_tac >>
  drule_all fmp_cover_back_lower_structure >> strip_tac >>
  drule_all fmp_cover_back_make_ssa_label_refs >>
  gvs[first_block_no_phi_def]
QED
