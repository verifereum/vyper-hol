Theory o1LabelFlowOwnCompose
Ancestors
  codegenSymOwnRel o1LabelFlowCompose o1LabelFlowSourceCfgLabels
  o1LabelReadinessSsa o1LabelFlowStaticContracts
  o1LabelFlowOwnWalk
  o1PipelineCorrect
  o1ComposeSupport
  o1PipelineCompose
  irSupply
  venomFnScheduleRunnerProps
  o1PassContract
  list
  fcgPruning
  venomPipelineRunner

Theorem o1_pipeline_label_flow_own_preserved:
  (!rpolicy unit s unit' s'.
  run_pipeline_stages rpolicy o1_pipeline_spec.ps_pre_walk_stages unit s =
    SOME (unit', s') /\
  o1_ctx_shape unit.cu_context /\
  ALL_DISTINCT (unit_label_namespace unit) /\ ir_supply_inst_ok s /\
  o1_source_unit_ok unit /\ unit_defs_reach_uses unit /\
  unit_fmp_unsealed unit /\ label_flow_own_ok unit.cu_context /\
  (!f i. MEM f unit.cu_context.ctx_functions /\ MEM i (fn_insts f) ==>
    ~MEM (Label "code_end") i.inst_operands) ==>
  label_flow_own_ok unit'.cu_context /\
  (!f i. MEM f unit'.cu_context.ctx_functions /\ MEM i (fn_insts f) ==>
    ~MEM (Label "code_end") i.inst_operands)) /\
(!rp observed s f out ctx.
  fn_pass_step rp (CFP_Simple VP_MakeSSA) observed s f out /\
  o1_ctx_shape observed.cu_context /\ ir_supply_inst_ok s /\
  EVERY fmp_sig_no_param observed.cu_context.ctx_functions /\
  o1_fn_row 0 f /\ (label_flow_own_ok (ctx with ctx_functions := [f]) /\
  (0 <= 1 ==> !i. MEM i (fn_insts f) ==>
    ~MEM (Label "code_end") i.inst_operands) /\
  (2 <= 0 /\ 0 <= 4 ==> middle_code_end_lifetime f) /\
  (0 <= 3 ==> no_raw_fmp_ops f) /\ fmp_sig_no_param f) ==>
  (label_flow_own_ok (ctx with ctx_functions := [out.fpo_function]) /\
  (1 <= 1 ==> !i. MEM i (fn_insts out.fpo_function) ==>
    ~MEM (Label "code_end") i.inst_operands) /\
  (2 <= 1 /\ 1 <= 4 ==> middle_code_end_lifetime out.fpo_function) /\
  (1 <= 3 ==> no_raw_fmp_ops out.fpo_function) /\ fmp_sig_no_param out.fpo_function)) /\
(!rp observed s f out ctx.
  fn_pass_step rp (CFP_Simple VP_LowerDload) observed s f out /\
  o1_ctx_shape observed.cu_context /\ ir_supply_inst_ok s /\
  EVERY fmp_sig_no_param observed.cu_context.ctx_functions /\
  o1_fn_row 1 f /\ (label_flow_own_ok (ctx with ctx_functions := [f]) /\
  (1 <= 1 ==> !i. MEM i (fn_insts f) ==>
    ~MEM (Label "code_end") i.inst_operands) /\
  (2 <= 1 /\ 1 <= 4 ==> middle_code_end_lifetime f) /\
  (1 <= 3 ==> no_raw_fmp_ops f) /\ fmp_sig_no_param f) ==>
  (label_flow_own_ok (ctx with ctx_functions := [out.fpo_function]) /\
  (2 <= 1 ==> !i. MEM i (fn_insts out.fpo_function) ==>
    ~MEM (Label "code_end") i.inst_operands) /\
  (2 <= 2 /\ 2 <= 4 ==> middle_code_end_lifetime out.fpo_function) /\
  (2 <= 3 ==> no_raw_fmp_ops out.fpo_function) /\ fmp_sig_no_param out.fpo_function)) /\
(!rp observed s f out ctx.
  fn_pass_step rp (CFP_Simple VP_ConcretizeMemLoc) observed s f out /\
  o1_ctx_shape observed.cu_context /\ ir_supply_inst_ok s /\
  EVERY fmp_sig_no_param observed.cu_context.ctx_functions /\
  o1_fn_row 2 f /\ (label_flow_own_ok (ctx with ctx_functions := [f]) /\
  (2 <= 1 ==> !i. MEM i (fn_insts f) ==>
    ~MEM (Label "code_end") i.inst_operands) /\
  (2 <= 2 /\ 2 <= 4 ==> middle_code_end_lifetime f) /\
  (2 <= 3 ==> no_raw_fmp_ops f) /\ fmp_sig_no_param f) ==>
  (label_flow_own_ok (ctx with ctx_functions := [out.fpo_function]) /\
  (3 <= 1 ==> !i. MEM i (fn_insts out.fpo_function) ==>
    ~MEM (Label "code_end") i.inst_operands) /\
  (2 <= 3 /\ 3 <= 4 ==> middle_code_end_lifetime out.fpo_function) /\
  (3 <= 3 ==> no_raw_fmp_ops out.fpo_function) /\ fmp_sig_no_param out.fpo_function)) /\
(!rp observed s f out ctx.
  fn_pass_step rp (CFP_Simple VP_FmpLowering) observed s f out /\
  o1_ctx_shape observed.cu_context /\ ir_supply_inst_ok s /\
  EVERY fmp_sig_no_param observed.cu_context.ctx_functions /\
  o1_fn_row 3 f /\ (label_flow_own_ok (ctx with ctx_functions := [f]) /\
  (3 <= 1 ==> !i. MEM i (fn_insts f) ==>
    ~MEM (Label "code_end") i.inst_operands) /\
  (2 <= 3 /\ 3 <= 4 ==> middle_code_end_lifetime f) /\
  (3 <= 3 ==> no_raw_fmp_ops f) /\ fmp_sig_no_param f) ==>
  (label_flow_own_ok (ctx with ctx_functions := [out.fpo_function]) /\
  (4 <= 1 ==> !i. MEM i (fn_insts out.fpo_function) ==>
    ~MEM (Label "code_end") i.inst_operands) /\
  (2 <= 4 /\ 4 <= 4 ==> middle_code_end_lifetime out.fpo_function) /\
  (4 <= 3 ==> no_raw_fmp_ops out.fpo_function) /\ fmp_sig_no_param out.fpo_function)) /\
(!rp observed s f out ctx.
  fn_pass_step rp (CFP_Simple VP_MakeSSA) observed s f out /\
  o1_ctx_shape observed.cu_context /\ ir_supply_inst_ok s /\
  EVERY fmp_sig_no_param observed.cu_context.ctx_functions /\
  o1_fn_row 4 f /\ (label_flow_own_ok (ctx with ctx_functions := [f]) /\
  (4 <= 1 ==> !i. MEM i (fn_insts f) ==>
    ~MEM (Label "code_end") i.inst_operands) /\
  (2 <= 4 /\ 4 <= 4 ==> middle_code_end_lifetime f) /\
  (4 <= 3 ==> no_raw_fmp_ops f) /\ fmp_sig_no_param f) ==>
  (label_flow_own_ok (ctx with ctx_functions := [out.fpo_function]) /\
  (5 <= 1 ==> !i. MEM i (fn_insts out.fpo_function) ==>
    ~MEM (Label "code_end") i.inst_operands) /\
  (2 <= 5 /\ 5 <= 4 ==> middle_code_end_lifetime out.fpo_function) /\
  (5 <= 3 ==> no_raw_fmp_ops out.fpo_function) /\ fmp_sig_no_param out.fpo_function)) /\
(!k pass rp observed s f out ctx.
  ((k = 5 /\ pass = CFP_Simple VP_SimplifyCFG) \/
   (k = 6 /\ pass = CFP_Simple VP_SingleUseExpansion) \/
   (k = 7 /\ pass = CFP_Simple VP_DFT) \/
   (k = 8 /\ pass = CFP_Simple VP_CFGNormalization)) /\
  fn_pass_step rp pass observed s f out /\
  o1_ctx_shape observed.cu_context /\ ir_supply_inst_ok s /\
  EVERY fmp_sig_no_param observed.cu_context.ctx_functions /\
  o1_fn_row k f /\ (label_flow_own_ok (ctx with ctx_functions := [f]) /\
  (k <= 1 ==> !i. MEM i (fn_insts f) ==>
    ~MEM (Label "code_end") i.inst_operands) /\
  (2 <= k /\ k <= 4 ==> middle_code_end_lifetime f) /\
  (k <= 3 ==> no_raw_fmp_ops f) /\ fmp_sig_no_param f) ==>
  (label_flow_own_ok (ctx with ctx_functions := [out.fpo_function]) /\
  ((SUC k) <= 1 ==> !i. MEM i (fn_insts out.fpo_function) ==>
    ~MEM (Label "code_end") i.inst_operands) /\
  (2 <= (SUC k) /\ (SUC k) <= 4 ==> middle_code_end_lifetime out.fpo_function) /\
  ((SUC k) <= 3 ==> no_raw_fmp_ops out.fpo_function) /\ fmp_sig_no_param out.fpo_function)) ==>
!rpolicy unit out.
  o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
  o1_source_unit_ok unit /\ unit_entry_no_params unit /\
  unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
  label_flow_own_ok unit.cu_context /\
  (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
    ~MEM (Label "code_end") inst.inst_operands) ==>
  label_flow_own_ok out.po_unit.cu_context
Proof
  strip_tac >>
  mp_tac o1_label_flow_own_walk >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_tac >>
  ntac 5 (qpat_x_assum
    `!rp observed s f out ctx. fn_pass_step _ _ _ _ _ _ /\ _ ==> _` kall_tac) >>
  qpat_x_assum `!k pass rp observed s f out ctx. _` kall_tac >>
  rpt gen_tac >> strip_tac >> fs[o1_pipeline_def] >>
  drule o1_driver_runs >> strip_tac >>
  `o1_ctx_shape unit.cu_context` by metis_tac[o1_source_unit_ok_ctx_shape] >>
  `ir_supply_inst_ok (init_ir_supply unit)` by simp[init_ir_supply_inst_ok] >>
  drule_all o1_pre_walk_rows >> strip_tac >>
  qpat_x_assum `!rpolicy unit s unit' s'. _` drule_all >> strip_tac >>
  drule_all o1_pre_walk_sim >> strip_tac >>
  `unit.cu_context.ctx_entry = SOME entry` by metis_tac[] >>
  mp_tac (Q.INST [`unit` |-> `pre`, `fcg` |-> `fcg_analyze pre.cu_context`]
    o1_walk_callee_first) >> simp[] >> strip_tac >>
  drule unit_labels_wf_namespace >> strip_tac >>
  `o1_ctx_shape (prune_unit_fcg_unreachable pre
     (fcg_analyze pre.cu_context)).cu_context /\
   ALL_DISTINCT (unit_label_namespace
     (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)))` by
    metis_tac[o1_ctx_shape_prune] >>
  fs[run_callee_first_def] >>
  qpat_x_assum `!rp names u s u' s'. _` drule >>
  (impl_tac
   >- (simp[o1_prune_every] >>
       fs[o1_fn_row_def, EVERY_MEM, label_flow_own_ok_def] >>
       metis_tac[MEM_prune_unit_fcg_unreachable_functions])) >>
  simp[]
QED
