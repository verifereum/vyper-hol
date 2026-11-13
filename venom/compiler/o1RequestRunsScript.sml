(*
 * The request companions of the O1 runs whose simulation is a bisimulation
 * or the identity: the two pre-walk runs, and walk runs 0 (MakeSSA),
 * 3 (FmpLowering), 4 (MakeSSA), 5 (SimplifyCFG), 6 (SingleUseExpansion)
 * and 8 (CFGNormalization).  A bisimilar stage aborts with the same frame
 * (ctx_bisim_ctx_abort_rq); FmpLowering's output runs as its input does;
 * DretDesugar returns its input.
 *)
Theory o1RequestRuns
Ancestors
  o1RequestContract o1PassContract o1PassLift o1ContractMakeSsa
  o1ContractSimplifyCfg o1ContractSue o1ContractCfgNorm
  o1ContractFmpLowering o1DretDesugarContract venomPassSchedule
  passSimulationDefs unitTransformDefs list

Theorem bisim_stage_abort_rq:
  ctx_bisim C C' /\ ctx_pass_stage rpolicy pass view C C' /\
  o1_run_state_ok vs ==>
  ctx_abort_rq D C C' vs vs
Proof
  strip_tac >> irule ctx_bisim_ctx_abort_rq >>
  gvs[o1_run_state_ok_def, o1_initial_state_ok_def, ctx_pass_stage_def]
QED

(* ===== Pre-walk ===== *)

Theorem simplify_cfg_pre_walk_abort_rq:
  ctx_pass_stage rpolicy (CFP_Simple VP_SimplifyCFG) view C C' /\
  o1_ctx_shape C /\ o1_run_state_ok vs /\ o1_pre_walk_inv D C vs ==>
  ctx_abort_rq D C C' vs vs
Proof
  strip_tac >>
  `EVERY simplify_cfg_fn_ok C.ctx_functions` by
    (gvs[o1_ctx_shape_def, o1_pre_walk_inv_def, EVERY_MEM] >>
     rpt strip_tac >> irule simplify_cfg_fn_ok_no_phi >>
     simp[EVERY_MEM] >> metis_tac[o1_fn_shape_def]) >>
  irule bisim_stage_abort_rq >> metis_tac[simplify_cfg_stage_bisim]
QED

Theorem dret_desugar_abort_rq:
  ctx_pass_stage rpolicy (CFP_Simple VP_DretDesugar) view C C' /\
  o1_ctx_shape C ==>
  ctx_abort_rq D C C' vs vs
Proof
  strip_tac >> drule_all dret_desugar_stage_identity >>
  simp[ctx_abort_rq_refl]
QED

(* ===== The walk ===== *)

Theorem make_ssa_run_rq_1:
  o1_run_rq_contract_gas rpolicy D 0
Proof
  rewrite_tac[o1_run_rq_contract_gas_def] >> irule o1_stage_contract_rq_lift >>
  reverse conj_tac >- metis_tac[make_ssa_run_contract_1, o1_run_contract_def] >>
  `EL 0 o1_fn_passes = CFP_Simple VP_MakeSSA` by simp[o1_fn_passes_def] >>
  simp[o1_inv_def, o1_walk_src_inv_def] >> rpt strip_tac >>
  irule bisim_stage_abort_rq >> metis_tac[make_ssa_stage_bisim]
QED

Theorem fmp_lowering_run_rq:
  o1_run_rq_contract_gas rpolicy D 3
Proof
  rewrite_tac[o1_run_rq_contract_gas_def] >> irule o1_stage_contract_rq_lift >>
  reverse conj_tac >- metis_tac[fmp_lowering_run_contract, o1_run_contract_def] >>
  `EL 3 o1_fn_passes = CFP_Simple VP_FmpLowering` by EVAL_TAC >>
  simp[o1_inv_def, o1_pre_def, o1_static_inv_def, fmp_free_ctx_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all fmp_lowering_stage_seal_only >> strip_tac >>
  simp[ctx_abort_rq_def] >> metis_tac[request_prefix_rel_refl]
QED

Theorem make_ssa_run_rq_2:
  o1_run_rq_contract_gas rpolicy D 4
Proof
  rewrite_tac[o1_run_rq_contract_gas_def] >> irule o1_stage_contract_rq_lift >>
  reverse conj_tac >- metis_tac[make_ssa_run_contract_2, o1_run_contract_def] >>
  `EL 4 o1_fn_passes = CFP_Simple VP_MakeSSA` by simp[o1_fn_passes_def] >>
  simp[o1_inv_def] >> rpt strip_tac >>
  irule bisim_stage_abort_rq >> metis_tac[make_ssa_stage_bisim]
QED

Theorem simplify_cfg_run_rq:
  o1_run_rq_contract_gas rpolicy D 5
Proof
  rewrite_tac[o1_run_rq_contract_gas_def] >> irule o1_stage_contract_rq_lift >>
  reverse conj_tac >- metis_tac[simplify_cfg_stage_walk, o1_run_contract_def] >>
  simp[o1_fn_passes_def, o1_inv_def] >> rpt strip_tac >>
  `EVERY simplify_cfg_fn_ok C.ctx_functions` by
    (gvs[o1_ctx_shape_def, o1_ssa_inv_def, EVERY_MEM] >>
     rpt strip_tac >> irule simplify_cfg_fn_ok_ssa >>
     metis_tac[o1_fn_shape_def]) >>
  irule bisim_stage_abort_rq >> metis_tac[simplify_cfg_stage_bisim]
QED

Theorem sue_run_rq:
  o1_run_rq_contract_gas rpolicy D 6
Proof
  rewrite_tac[o1_run_rq_contract_gas_def] >> irule o1_stage_contract_rq_lift >>
  reverse conj_tac >- metis_tac[sue_stage_walk, o1_run_contract_def] >>
  simp[o1_fn_passes_def, o1_inv_def, o1_pre_def, o1_ssa_inv_def] >>
  rpt strip_tac >>
  irule bisim_stage_abort_rq >> metis_tac[sue_stage_bisim]
QED

Theorem cfg_norm_run_rq:
  o1_run_rq_contract_gas rpolicy D 8
Proof
  rewrite_tac[o1_run_rq_contract_gas_def] >> irule o1_stage_contract_rq_lift >>
  reverse conj_tac >- metis_tac[cfg_norm_stage_walk, o1_run_contract_def] >>
  simp[o1_fn_passes_def, o1_inv_def, o1_ssa_inv_def] >> rpt strip_tac >>
  irule bisim_stage_abort_rq >> metis_tac[cfg_norm_stage_bisim]
QED
