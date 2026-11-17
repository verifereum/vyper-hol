Theory o1LabelFlowStaticContracts
Ancestors
  o1PassContract o1ComposeSupport o1ContractLowerDloadStage
  o1ContractLowerDload o1ContractMakeSsaStep concretizeStepContract
  fmpStepContract o1DftStepAt o1ContractSimplifyCfg o1ContractSue
  o1ContractCfgNorm venomPassSchedule
  o1FnScheduleDecompHelpers venomPassDispatcherProps concretizeStageShape
  fmpStepBridge venomPassDispatcher venomInst lowerDloadDefs list
  lowerDloadMakeSsaInput

Theorem label_flow_lower_dload_static[local]:
  o1_step_contract_at 1 rp (CFP_Simple VP_LowerDload)
Proof
  irule o1_step_contract_at_preserve >>
  simp[lower_dload_step_contract] >> metis_tac[lower_dload_fn_row]
QED

Theorem o1_fn_passes_steps:
  o1_step_contracts_from rp 0 o1_fn_passes
Proof
  simp[o1_fn_passes_def, o1_step_contracts_from_def,
    make_ssa_step_contract_at, label_flow_lower_dload_static,
    concretize_step_contract_at, fmp_step_contract_at,
    o1_contract_simplify_cfg, o1_contract_sue,
    dft_step_contract_at, o1_contract_cfg_normalization]
QED

Theorem rows_step_contract_enrich_invariant:
  rows_step_contract o1_fn_row k rp pass /\
  (!j g. P j g ==> fmp_sig_no_param g) /\
  (!observed s f out.
    fn_pass_step rp pass observed s f out /\
    o1_ctx_shape observed.cu_context /\ ir_supply_inst_ok s /\
    EVERY fmp_sig_no_param observed.cu_context.ctx_functions /\
    o1_fn_row k f /\ P k f ==> P (SUC k) out.fpo_function) ==>
  rows_step_contract (\j f. o1_fn_row j f /\ P j f) k rp pass
Proof
  rewrite_tac[rows_step_contract_def] >> rpt strip_tac >>
  `EVERY (\g. ?j. o1_fn_row j g) observed.cu_context.ctx_functions` by
    (gvs[EVERY_MEM] >> metis_tac[]) >>
  `EVERY fmp_sig_no_param observed.cu_context.ctx_functions` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem o1_fn_passes_guard_rows:
  rows_step_contracts_from
    (\k f. o1_fn_row k f /\ (k <= 3 ==> no_raw_fmp_ops f) /\
           fmp_sig_no_param f)
    rp 0 o1_fn_passes
Proof
  mp_tac (Q.SPEC `rp` (GEN_ALL o1_fn_passes_steps)) >>
  disch_then (mp_tac o MATCH_MP o1_step_contracts_from_rows) >>
  rewrite_tac[o1_fn_passes_def, rows_step_contracts_from_def] >> strip_tac >>
  rpt conj_tac >>
  irule (BETA_RULE (Q.INST
    [`P` |-> `\k f. (k <= 3 ==> no_raw_fmp_ops f) /\ fmp_sig_no_param f`]
    rows_step_contract_enrich_invariant)) >> simp[]
  >- (rpt gen_tac >> strip_tac >> conj_tac
      >- (irule (Q.INST [`tag` |-> `VP_MakeSSA`, `rpolicy` |-> `rp`,
                            `fn` |-> `f`, `unit` |-> `observed`, `s` |-> `s`]
              execute_configured_fn_pass_o1_suffix_no_raw_fmp_ops) >>
          fs[fn_pass_step_def] >> metis_tac[]) >>
      drule fn_pass_step_fmp_sig_no_param >>
      simp[fn_pass_tag_def] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >> conj_tac
      >- (drule lower_dload_step_supply >> strip_tac >>
          fs[no_raw_fmp_ops_def] >> rpt strip_tac >>
          drule_all lower_dload_function_supply_member >> strip_tac >>
          rename1 `lower_dload_inst_supply u oldi = (ys,v)` >>
          Cases_on `oldi.inst_opcode = DLOAD` >>
          Cases_on `oldi.inst_opcode = DLOADBYTES` >>
          gvs[lower_dload_inst_supply_def, AllCaseEqs(), is_raw_fmp_opcode_def] >>
          metis_tac[]) >>
      drule fn_pass_step_fmp_sig_no_param >>
      simp[fn_pass_tag_def] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >> conj_tac
      >- metis_tac[concretize_step_no_raw_fmp] >>
      drule fn_pass_step_fmp_sig_no_param >>
      simp[fn_pass_tag_def] >> metis_tac[])
  >- (rpt strip_tac >> drule fmp_fn_pass_step_result >> strip_tac >>
      drule_all fmp_lower_function_no_param >> simp[]) >>
  rpt strip_tac >> drule fn_pass_step_fmp_sig_no_param >>
  simp[fn_pass_tag_def] >> metis_tac[]
QED
