(* Same-filling memory transport at the pre-walk SimplifyCFG boundary. *)
Theory o1SimplifyCfgCutMemory
Ancestors
  o1SafeUpto o1ContractSimplifyCfg o1ContractSimplifyCfgSrcFrame
  o1ContractSimplifyCfgSrcHeadroom o1PassLift o1PassContract
  unitMemInv unitTransformDefs ptrDiscipline lowerDloadDefs
  simplifyCfgControl venomState venomInst stateFrame venomWf list

Theorem simplify_cfg_stage_cut_memory:
  ctx_pass_stage rpolicy (CFP_Simple VP_SimplifyCFG) view C C' /\
  o1_ctx_shape C /\ EVERY simplify_cfg_fn_ok C.ctx_functions /\
  EVERY (\f. EVERY (\i. i.inst_opcode <> PHI) (fn_insts f)) C.ctx_functions /\
  o1_initial_state_ok vs /\ o1_safe_upto D lo n C vs ==>
  mem_inv dload_headroom_ok C' vs /\
  (!fn inst s. raw_reachable vs C' fn inst s /\ gas_cut n vs s ==>
     raw_mem_ok C' fn inst s /\ dload_offset_ok C' fn inst s)
Proof
  strip_tac >>
  conj_tac >- suspend "headroom" >>
  `mem_inv (\ctx fn inst s. gas_cut n vs s ==> raw_mem_ok ctx fn inst s)
     C vs` by
    (fs[o1_safe_upto_def, mem_inv_raw_reachable] >> metis_tac[]) >>
  `mem_corr_closed_rf
     (\ctx fn inst s. gas_cut n vs s ==> raw_mem_ok ctx fn inst s)` by
    (`mem_corr_closed_rf (\ctx fn inst s.
        (\r. LENGTH vs.vs_gas_readings < n + LENGTH r) s.vs_gas_readings ==>
        raw_mem_ok ctx fn inst s)` by
       (irule mem_corr_closed_rf_readings_guard >>
        simp[mem_corr_closed_rf_raw_mem_ok]) >>
     fs[gas_cut_def]) >>
  `mem_inv (\ctx fn inst s. gas_cut n vs s ==> raw_mem_ok ctx fn inst s)
     C' vs` by
    (drule_all simplify_cfg_stage_mem_inv_rf_initial >> simp[]) >>
  rpt gen_tac >> strip_tac >> conj_tac
  >- (fs[mem_inv_raw_reachable] >> metis_tac[]) >>
  suspend "offset"
QED

Resume simplify_cfg_stage_cut_memory[headroom]:
  `EVERY wf_function C.ctx_functions` by
    gvs[o1_ctx_shape_def, o1_fn_shape_def, EVERY_MEM] >>
  `ctx_dload_count C' <= ctx_dload_count C` by
    (irule simplify_cfg_ctx_dload_count_le >>
     simp[] >> irule simplify_cfg_stage_functions >> goal_assum drule) >>
  `ctx_has_dalloca C' ==> ctx_has_dalloca C` by
    (`C' = C with ctx_functions := MAP simplify_cfg_fn C.ctx_functions` by
       (drule simplify_cfg_stage_functions >>
        strip_tac >> fs[ctx_pass_stage_def, venom_context_component_equality]) >>
     metis_tac[scfg_simplify_cfg_no_dalloca]) >>
  irule dload_headroom_mem_inv_decrease >> qexists_tac `C` >>
  fs[ctx_has_dalloca_def] >>
  irule simplify_cfg_stage_mem_inv_rf_initial >>
  simp[dload_headroom_fixed_corr_closed_rf] >>
  qexistsl_tac [`C`, `rpolicy`, `view`] >> simp[] >>
  irule dload_headroom_mem_inv_freeze >> gvs[o1_safe_upto_def]
QED

Resume simplify_cfg_stage_cut_memory[offset]:
  Cases_on `inst.inst_opcode = DLOAD \/ inst.inst_opcode = DLOADBYTES`
  >- (drule_all simplify_cfg_stage_frame_interface >>
      disch_then (qspec_then `vs.vs_labels` strip_assume_tac) >>
      `vs.vs_vars = FEMPTY /\ ~vs.vs_halted` by
        fs[o1_initial_state_ok_def] >>
      drule_all scfg_raw_dload_payload >> strip_tac >>
      rename1 `scfg_payload src s` >>
      `gas_cut n vs src` by
        (irule gas_cut_execution_frame >>
         metis_tac[scfg_payload_frame]) >>
      `dload_offset_ok C f inst src` by
        (fs[o1_safe_upto_def] >> metis_tac[]) >>
      metis_tac[scfg_payload_dload_offset_ok]) >>
  fs[dload_offset_ok_def]
QED

Finalise simplify_cfg_stage_cut_memory
