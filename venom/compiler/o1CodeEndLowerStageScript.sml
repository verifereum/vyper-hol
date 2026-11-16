Theory o1CodeEndLowerStage
Ancestors
  o1CodeEndLowerObservation o1CodeEndLowerProvenance
  o1ContractLowerDloadStage o1ContractLowerDloadMem lowerDloadStageAmbient
  lowerDloadRawCoverage lowerDloadForwardingCoverage lowerDloadPublicTrace
  lowerDloadSafetyAmbient lowerDloadSafetyRelation lowerDloadDefs
  lowerDloadSafetyKernel lowerDloadSafetyValues
  codegenSymRel o1PassContract ptrDiscipline unitMemInv contextCodegenRel
  lowerDloadSupplyProofs unitLabelMapIdentity venomInst list words finite_map
  venomPassSchedule lowerDloadPtrStatic

Theorem lower_dload_stage_code_end[local]:
  ctx_pass_stage rpolicy (CFP_Simple VP_LowerDload) view C C' /\
  dead_wf D /\ o1_ctx_shape C /\ o1_run_state_ok vs /\
  o1_src_inv D C vs /\ callee_first names C.ctx_functions /\
  mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
    s.vs_code = v.vs_code /\ s.vs_data_section = v.vs_data_section) C vs /\
  LENGTH v.vs_data_section < dimword(:256) DIV 2 /\
  (!fn inst. MEM fn C.ctx_functions /\ MEM inst (fn_insts fn) ==>
     ~MEM (Label "code_end") inst.inst_operands) ==>
  code_end_offset_ok (raw_reachable vs) C'
Proof
  rpt strip_tac >>
  drule_all ld_stage_ambient >> strip_tac >>
  `ctx_has_dalloca C' ==> ctx_has_dalloca C` by
    metis_tac[lower_dload_stage_no_dalloca] >>
  `mem_inv raw_mem_ok C vs` by fs[o1_src_inv_def] >>
  RULE_ASSUM_TAC BETA_RULE >>
  rewrite_tac[code_end_offset_ok_def] >> rpt strip_tac >>
  drule_all (BETA_RULE ld_raw_coverage_fixed) >>
  disch_then (DISJ_CASES_THEN assume_tac)
  >- (drule_all (BETA_RULE ld_raw_owned_elim) >> strip_tac >>
      rename1 `ld_sync lo P C vs stk PG G tn source si s t0 A (f::fs) N` >>
      drule ld_sync_active >> simp[] >> strip_tac >>
      `MEM source C.ctx_functions` by
        (gvs[ld_sync_def]) >>
      `ir_supply_covers_fn f.lf_supply source` by gvs[] >>
      `~MEM (Label "code_end") si.inst_operands` by
        (drule ld_sync_source >> strip_tac >>
         `MEM si (fn_insts source)` by
           (gvs[active_inst_def, fn_insts_MEM] >> metis_tac[MEM_EL]) >>
         metis_tac[]) >>
      Cases_on `si.inst_opcode = DLOAD \/ si.inst_opcode = DLOADBYTES`
      >- (irule lower_dload_sync_codecopy_bound >>
          goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
      drule_all ld_sync_fn_shape >> strip_tac >>
      drule o1_fn_shape_components >> strip_tac >>
      drule ld_sync_source >> strip_tac >>
      drule_all ld_active_envelope_origin >> strip_tac >>
      `X = [si]` by
        (gvs[lower_dload_inst_supply_def] >> metis_tac[]) >>
      `h = 0` by (drule ld_prefix_bound >> simp[] >> decide_tac) >>
      `si = inst` by gvs[] >>
      `MEM x (fn_ir_vars source)` by
        (irule ld_inst_input_ir >> metis_tac[MEM]) >>
      `?rest. lower_dload_function_supply (Sigma source.fn_name) source =
          (fn',rest)` by metis_tac[pairTheory.PAIR] >>
      `!i. MEM i (fn_insts source) ==>
          ~MEM (Label "code_end") i.inst_operands` by metis_tac[] >>
      metis_tac[lower_dload_code_end_var_fresh]) >>
  drule (BETA_RULE ld_forward_opcode) >> simp[]
QED

Theorem lower_dload_code_end_stage_contract:
  o1_stage_contract rpolicy D (CFP_Simple VP_LowerDload)
    (o1_walk_view rpolicy 1) (o1_pre 1)
    (\C vs. o1_inv D 1 C vs /\
      mem_inv (\ctx fn inst s. inst_dload_in_section inst s /\
        s.vs_code = v.vs_code /\ s.vs_data_section = v.vs_data_section) C vs /\
      LENGTH v.vs_data_section < dimword(:256) DIV 2 /\
      (!fn inst. MEM fn C.ctx_functions /\ MEM inst (fn_insts fn) ==>
         ~MEM (Label "code_end") inst.inst_operands))
    (\C vs. o1_inv D 2 C vs /\ code_end_offset_ok (raw_reachable vs) C)
Proof
  mp_tac lower_dload_run_contract >>
  simp[o1_run_contract_def, o1_fn_passes_def, o1_stage_contract_def] >>
  rpt strip_tac
  >- metis_tac[] >>
  irule lower_dload_stage_code_end >>
  fs[o1_inv_def] >> metis_tac[]
QED
