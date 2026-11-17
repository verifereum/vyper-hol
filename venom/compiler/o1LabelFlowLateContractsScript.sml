Theory o1LabelFlowLateContracts
Ancestors
  o1LabelFlowCfgIteration o1LabelFlowSuePreservation
  o1LabelFlowDftPreservation o1LabelFlowSimplifyPreservation
  o1ContractSimplifyCfg simplifyCfgPhiRepair simplifyCfgDefs
  o1PassContract unitShapeDefs venomFnScheduleRunnerProps list

Theorem simplify_cfg_row5_label_flow_ok:
  fn_pass_step rpolicy (CFP_Simple VP_SimplifyCFG) observed s f out /\
  o1_ctx_shape observed.cu_context /\ o1_fn_row 5 f /\
  label_flow_ok (observed.cu_context with ctx_functions := [f]) ==>
  label_flow_ok
    (observed.cu_context with ctx_functions := [out.fpo_function])
Proof
  strip_tac >>
  `MEM f observed.cu_context.ctx_functions` by
    metis_tac[fn_pass_step_def, lookup_unique_function_member] >>
  `o1_fn_shape observed.cu_context f` by
    gvs[o1_ctx_shape_def, EVERY_MEM] >>
  `wf_ssa f /\ wf_function f /\ fn_inst_wf f /\
   first_block_no_preds f /\ first_block_no_phi f /\
   EVERY label_positions_ok (fn_insts f)` by
    (fs[o1_fn_row_def, o1_fn_shape_def, fn_shape_ok_def,
        EVERY_MEM, inst_shape_ok_def] >> metis_tac[]) >>
  `scfg_phi_safe f /\ fn_defs_reach_uses f` by
    metis_tac[simplify_cfg_fn_ok_ssa, simplify_cfg_fn_ok_phi_safe] >>
  `out.fpo_function = FST (simplify_cfg_fn_with_labels f)` by
    metis_tac[simplify_cfg_pass_step_function, simplify_cfg_fn_def] >>
  gvs[] >> irule simplify_cfg_fn_label_flow >> simp[]
QED

(* These are exactly the final four entries of the scheduled function walk.
   Structural and supply hypotheses are the runner's ordinary row package;
   the concrete replay theorems discharge supply coverage internally. *)
Theorem o1_late_row_label_flow_ok:
  ((k = 5 /\ pass = CFP_Simple VP_SimplifyCFG) \/
   (k = 6 /\ pass = CFP_Simple VP_SingleUseExpansion) \/
   (k = 7 /\ pass = CFP_Simple VP_DFT) \/
   (k = 8 /\ pass = CFP_Simple VP_CFGNormalization)) /\
  fn_pass_step rpolicy pass observed s f out /\
  o1_ctx_shape observed.cu_context /\ ir_supply_inst_ok s /\
  o1_fn_row k f /\
  label_flow_ok (observed.cu_context with ctx_functions := [f]) ==>
  label_flow_ok
    (observed.cu_context with ctx_functions := [out.fpo_function])
Proof
  strip_tac >> gvs[]
  >- metis_tac[simplify_cfg_row5_label_flow_ok]
  >- metis_tac[sue_row_label_flow_ok]
  >- metis_tac[dft_row7_label_flow_ok] >>
  `MEM f observed.cu_context.ctx_functions` by
    metis_tac[fn_pass_step_def, lookup_unique_function_member] >>
  `wf_function f` by gvs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >>
  metis_tac[cfg_norm_row_label_flow_ok]
QED
