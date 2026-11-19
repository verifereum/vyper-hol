(* MakeSSA transports memory obligations at the same filling and gas cut. *)
Theory o1MakeSsaCutMemory
Ancestors
  o1SafeUpto o1ContractMakeSsa o1ContractMakeSsaSrc o1PassLift
  o1PassContract unitMemInv unitTransformDefs lowerDloadDefs
  venomWf venomInst venomState stateFrame list

Theorem make_ssa_stage_raw_memory_upto:
  ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' /\
  o1_ctx_shape C /\ EVERY make_ssa_input_ok C.ctx_functions /\
  vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  (!fn inst s. raw_reachable vs C fn inst s /\ gas_cut n vs s ==>
     raw_mem_ok C fn inst s) ==>
  !fn inst s. raw_reachable vs C' fn inst s /\ gas_cut n vs s ==>
     raw_mem_ok C' fn inst s
Proof
  strip_tac >>
  `mem_inv (\ctx fn inst s. gas_cut n vs s ==> raw_mem_ok ctx fn inst s)
     C vs` by
    (simp[mem_inv_raw_reachable] >>
     fs[o1_ctx_shape_def, ctx_wf_def, ctx_has_entry_def, ctx_fn_names_def] >>
     Cases_on `lookup_function entry_name C.ctx_functions`
     >- metis_tac[lookup_function_not_mem] >>
     rename1 `lookup_function _ _ = SOME efn` >>
     `wf_function efn` by
       metis_tac[lookup_function_MEM, EVERY_MEM, o1_fn_shape_def] >>
     Cases_on `efn.fn_blocks` >>
     fs[wf_function_def, fn_has_entry_def, fn_entry_label_def, entry_block_def]) >>
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
    (drule_all make_ssa_stage_mem_inv >> simp[]) >>
  fs[mem_inv_raw_reachable] >> metis_tac[]
QED

Theorem make_ssa_stage_dload_offset_upto:
  ctx_pass_stage rpolicy (CFP_Simple VP_MakeSSA) view C C' /\
  o1_ctx_shape C /\ EVERY make_ssa_input_ok C.ctx_functions /\
  vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\
  (!fn inst s. raw_reachable vs C fn inst s /\ gas_cut n vs s ==>
     dload_offset_ok C fn inst s) ==>
  !fn inst s. raw_reachable vs C' fn inst s /\ gas_cut n vs s ==>
     dload_offset_ok C' fn inst s
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  rename1 `raw_reachable vs C' fn' inst' s'` >>
  reverse (Cases_on
    `inst'.inst_opcode = DLOAD \/ inst'.inst_opcode = DLOADBYTES`)
  >- fs[dload_offset_ok_def] >>
  `inst'.inst_opcode <> ASSIGN /\ inst'.inst_opcode <> NOP` by
    (qpat_x_assum `_ \/ _` strip_assume_tac >> simp[]) >>
  drule_all make_ssa_src_stage_observation >> strip_tac >>
  `gas_cut n vs s` by
    (irule gas_cut_execution_frame >> metis_tac[]) >>
  `dload_offset_ok C fn inst s` by metis_tac[] >>
  `s'.vs_code = s.vs_code /\ s'.vs_data_section = s.vs_data_section` by
    (qpat_x_assum `execution_frame s' = execution_frame s` mp_tac >>
     simp[execution_frame_def, venom_state_component_equality]) >>
  qpat_x_assum `dload_offset_ok C fn inst s`
    (assume_tac o REWRITE_RULE [dload_offset_ok_def]) >>
  rewrite_tac[dload_offset_ok_def] >> rpt gen_tac >> strip_tac >>
  gvs[LIST_REL_CONS2] >> first_x_assum irule >> metis_tac[]
QED
