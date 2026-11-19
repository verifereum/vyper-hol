(* Transport cut-guarded lowered memory through the post-FMP stages. *)
Theory gasFocusPostFmpCutLoweredMemory
Ancestors
  o1SafeUpto o1ContractMakeSsa o1ContractSimplifyCfg o1ContractSue
  o1PassLift o1PassContract unitMemInv unitTransformDefs

Theorem post_fmp_stages_cut_lowered_memory:
  ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view4 C4 C5 /\
  ctx_pass_stage rpolicy (CFP_Simple VP_SimplifyCFG) view5 C5 C6 /\
  ctx_pass_stage rpolicy (CFP_Simple VP_SingleUseExpansion) view6 C6 C7 /\
  o1_ctx_shape C4 /\ o1_ctx_shape C5 /\ o1_ctx_shape C6 /\
  EVERY make_ssa_input_ok C4.ctx_functions /\
  EVERY simplify_cfg_fn_ok C5.ctx_functions /\
  EVERY wf_ssa C6.ctx_functions /\ EVERY (o1_fn_row 6) C6.ctx_functions /\
  o1_initial_state_ok vs /\
  mem_inv (\ctx fn inst s. gas_cut n vs s ==> lowered_mem_fact eom ctx fn inst s) C4 vs ==>
  mem_inv (\ctx fn inst s. gas_cut n vs s ==> lowered_mem_fact eom ctx fn inst s) C7 vs
Proof
  strip_tac >>
  `vs.vs_vars = FEMPTY /\ ~vs.vs_halted` by
    fs[o1_initial_state_ok_def] >>
  `mem_corr_closed_rf
      (\ctx fn inst s. gas_cut n vs s ==> lowered_mem_fact eom ctx fn inst s)` by
    (`mem_corr_closed_rf (\ctx fn inst s.
        (\r. LENGTH vs.vs_gas_readings < n + LENGTH r) s.vs_gas_readings ==>
        lowered_mem_fact eom ctx fn inst s)` by
       (irule mem_corr_closed_rf_readings_guard >>
        simp[mem_corr_closed_rf_lowered_mem_fact]) >>
     fs[gas_cut_def]) >>
  `mem_inv (\ctx fn inst s. gas_cut n vs s ==> lowered_mem_fact eom ctx fn inst s)
     C5 vs` by
    (drule_all make_ssa_stage_mem_inv >> simp[]) >>
  `mem_inv (\ctx fn inst s. gas_cut n vs s ==> lowered_mem_fact eom ctx fn inst s)
     C6 vs` by
    (drule_all simplify_cfg_stage_mem_inv_rf_initial >> simp[]) >>
  drule_all sue_stage_mem_inv_rf >> simp[]
QED
