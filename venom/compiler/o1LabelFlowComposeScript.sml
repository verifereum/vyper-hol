Theory o1LabelFlowCompose
Ancestors
  o1LabelFlowSource o1LabelFlowMiddle o1LabelFlowLateContracts
  o1PipelineCorrect o1PipelineCompose o1ScheduleDecomp
  o1PartialSchedule o1FnScheduleDecompHelpers o1ComposeSupport
  venomPassSchedule list irSupply venomPipelineRunner fcgPruning
  codegenSymRel o1LabelFlowSourceBoundary o1LabelFlowSourceSsaStep
  o1LabelFlowLowerDload o1LabelFlowMiddleConcretize o1LabelFlowMiddleFmp venomInst
  concretizeMemLocDefs venomPassDispatcher o1PassContract lowerDloadMakeSsaInput
  o1ContractMakeSsaReplay o1LabelFlowMiddleSsaAssembly unitShapeDefs
  venomFnScheduleRunnerProps

(* A named runner invariant avoids repeating the three phase boundaries in
   every contract. It adds no assumptions to the source or pass contracts. *)
Definition label_flow_row_extra_def:
  label_flow_row_extra ctx k f <=>
    label_flow_ok (ctx with ctx_functions := [f]) /\
    (k <= 1 ==> !i. MEM i (fn_insts f) ==>
      ~MEM (Label "code_end") i.inst_operands) /\
    (2 <= k /\ k <= 4 ==> middle_code_end_lifetime f)
End

Theorem label_flow_singleton_context[local]:
  label_flow_ok (C with ctx_functions := [f]) <=>
  label_flow_ok (D with ctx_functions := [f])
Proof
  simp[label_flow_ok_def]
QED

Theorem rows_step_contract_enrich_invariant[local]:
  rows_step_contract o1_fn_row k rp pass /\
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
    (fs[EVERY_MEM, o1_fn_row_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem compose_first_ssa[local]:
  fn_pass_step rp (CFP_Simple VP_MakeSSA) observed s f out /\
  o1_ctx_shape observed.cu_context /\ ir_supply_inst_ok s /\
  o1_fn_row 0 f /\ label_flow_row_extra ctx 0 f ==>
  label_flow_row_extra ctx 1 out.fpo_function
Proof
  simp[label_flow_row_extra_def] >> strip_tac >>
  `!i. MEM i (fn_insts f) ==> i.inst_opcode <> CODESIZE /\
    (i.inst_opcode = CODECOPY ==>
      ?dst sz. i.inst_operands = [dst; Label "runtime_begin"; sz])` by
    metis_tac[label_flow_ok_seed_free_function] >>
  drule_all first_make_ssa_step_seed_free_flow >> strip_tac >>
  metis_tac[label_flow_ok_seed_free_function]
QED

Theorem compose_lower_dload[local]:
  fn_pass_step rp (CFP_Simple VP_LowerDload) observed s f out /\
  label_flow_row_extra ctx 1 f ==>
  label_flow_row_extra ctx 2 out.fpo_function
Proof
  simp[label_flow_row_extra_def] >> strip_tac >>
  drule lower_dload_step_supply >> strip_tac >> conj_tac
  >- (irule lower_dload_function_label_flow_ok >> metis_tac[]) >>
  rewrite_tac[middle_code_end_lifetime_def] >> rpt strip_tac >>
  irule lower_dload_function_code_end_lifetime >> metis_tac[]
QED

Theorem compose_concretize[local]:
  fn_pass_step rp (CFP_Simple VP_ConcretizeMemLoc) observed s f out /\
  label_flow_row_extra ctx 2 f ==>
  label_flow_row_extra ctx 3 out.fpo_function
Proof
  simp[label_flow_row_extra_def] >> strip_tac >>
  `execute_configured_fn_pass rp (CFP_Simple VP_ConcretizeMemLoc)
    observed s f = SOME out` by fs[fn_pass_step_def] >>
  gvs[execute_configured_fn_pass_concretize, AllCaseEqs()] >>
  gvs[concretize_function_fuel_in_context_def, AllCaseEqs()] >>
  `label_flow_ok (ctx with ctx_functions :=
    [concretize_function_with_positions layout.cl_positions f]) /\
   middle_code_end_lifetime
    (concretize_function_with_positions layout.cl_positions f)` by
    (conj_tac >- metis_tac[concretize_label_flow] >>
     drule (PURE_REWRITE_RULE [GSYM middle_code_end_lifetime_def]
       concretize_function_code_end_lifetime) >> simp[]) >>
  gvs[apply_context_concretize_layout_def, apply_concretize_layout_def] >>
  qmatch_goalsub_abbrev_tac `middle_code_end_lifetime g` >>
  `g.fn_blocks =
    (concretize_function_with_positions layout.cl_positions f).fn_blocks` by
    simp[Abbr `g`] >>
  `!x. code_end_var g x <=>
    code_end_var (concretize_function_with_positions layout.cl_positions f) x` by
    metis_tac[code_end_var_same_blocks] >>
  (conj_tac >- metis_tac[label_flow_ok_same_blocks] >>
   fs[middle_code_end_lifetime_def, fn_insts_def])
QED

Theorem compose_fmp[local]:
  fn_pass_step rp (CFP_Simple VP_FmpLowering) observed s f out /\
  EVERY fmp_sig_no_param observed.cu_context.ctx_functions /\
  o1_fn_row 3 f /\ label_flow_row_extra ctx 3 f ==>
  label_flow_row_extra ctx 4 out.fpo_function
Proof
  simp[label_flow_row_extra_def] >> strip_tac >> conj_tac
  >- metis_tac[fmp_row_label_flow_ok] >>
  irule (PURE_REWRITE_RULE [GSYM middle_code_end_lifetime_def]
    fmp_row_code_end_lifetime) >> metis_tac[]
QED

Theorem compose_second_ssa[local]:
  fn_pass_step rp (CFP_Simple VP_MakeSSA) observed s f out /\
  o1_ctx_shape observed.cu_context /\
  o1_fn_row 4 f /\ label_flow_row_extra ctx 4 f ==>
  label_flow_row_extra ctx 5 out.fpo_function
Proof
  simp[label_flow_row_extra_def] >> strip_tac >>
  `MEM f observed.cu_context.ctx_functions` by
    metis_tac[fn_pass_step_def, lookup_unique_function_member] >>
  `wf_function f /\ fn_inst_wf f /\ make_ssa_input_ok f` by
    (fs[o1_ctx_shape_def, o1_fn_shape_def, o1_fn_row_def, EVERY_MEM,
        fn_shape_ok_def] >> metis_tac[]) >>
  drule make_ssa_pass_step_replay >> strip_tac >>
  irule make_ssa_current_fn_label_flow >> goal_assum $ drule_at Any >>
  fs[middle_code_end_lifetime_def]
QED

Theorem compose_late[local]:
  ((k = 5 /\ pass = CFP_Simple VP_SimplifyCFG) \/
   (k = 6 /\ pass = CFP_Simple VP_SingleUseExpansion) \/
   (k = 7 /\ pass = CFP_Simple VP_DFT) \/
   (k = 8 /\ pass = CFP_Simple VP_CFGNormalization)) /\
  fn_pass_step rp pass observed s f out /\
  o1_ctx_shape observed.cu_context /\ ir_supply_inst_ok s /\
  o1_fn_row k f /\ label_flow_row_extra ctx k f ==>
  label_flow_row_extra ctx (SUC k) out.fpo_function
Proof
  strip_tac >>
  `label_flow_ok (observed.cu_context with ctx_functions := [f])` by
    metis_tac[label_flow_row_extra_def, label_flow_singleton_context] >>
  `label_flow_ok (observed.cu_context with ctx_functions := [out.fpo_function])` by
    metis_tac[o1_late_row_label_flow_ok] >>
  gvs[label_flow_row_extra_def] >>
  metis_tac[label_flow_singleton_context]
QED

Theorem o1_label_flow_enriched_contracts:
  rows_step_contracts_from
    (\k f. o1_fn_row k f /\ label_flow_row_extra ctx k f)
    rp 0 o1_fn_passes
Proof
  mp_tac (Q.SPEC `rp` (GEN_ALL o1_fn_passes_steps)) >>
  disch_then (mp_tac o MATCH_MP o1_step_contracts_from_rows) >>
  rewrite_tac[o1_fn_passes_def, rows_step_contracts_from_def] >> strip_tac >>
  rpt conj_tac >> irule rows_step_contract_enrich_invariant >> simp[]
  >- metis_tac[compose_first_ssa]
  >- metis_tac[compose_lower_dload]
  >- metis_tac[compose_concretize]
  >- metis_tac[compose_fmp]
  >- metis_tac[compose_second_ssa] >>
  rpt strip_tac
  >- (irule (SRULE [] (Q.INST [`k` |-> `5`] compose_late)) >> metis_tac[])
  >- (irule (SRULE [] (Q.INST [`k` |-> `6`] compose_late)) >> metis_tac[])
  >- (irule (SRULE [] (Q.INST [`k` |-> `7`] compose_late)) >> metis_tac[]) >>
  irule (SRULE [] (Q.INST [`k` |-> `8`] compose_late)) >> metis_tac[]
QED
