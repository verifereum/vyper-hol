Theory o1LabelFlowOwnFirstSsa
Ancestors
  codegenSymOwnRel
  o1LabelFlowCompose
  o1LabelFlowSourceCfgLabels
  o1LabelReadinessSsa
  o1LabelFlowStaticContracts
  o1ContractMakeSsaStep
  o1FnScheduleDecompHelpers
  o1LabelFlowSourceBoundary
  venomFnScheduleRunnerProps
  venomPassDispatcher
  o1PassContract
  unitShapeDefs
  list

Theorem compose_first_ssa_own:
  !rp observed s f out ctx.
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
  (1 <= 3 ==> no_raw_fmp_ops out.fpo_function) /\ fmp_sig_no_param out.fpo_function)
Proof
  simp[] >> rpt gen_tac >> strip_tac >>
  `fmp_sig_no_param out.fpo_function` by
    (drule fn_pass_step_fmp_sig_no_param >>
     simp[venomPassScheduleTheory.fn_pass_tag_def] >> metis_tac[]) >>
  `no_raw_fmp_ops out.fpo_function` by
    (irule (Q.INST [`tag` |-> `VP_MakeSSA`, `rpolicy` |-> `rp`,
                     `fn` |-> `f`, `unit` |-> `observed`, `s` |-> `s`]
       venomPassDispatcherPropsTheory.execute_configured_fn_pass_o1_suffix_no_raw_fmp_ops) >>
     fs[fn_pass_step_def] >> metis_tac[]) >>
  `o1_step_contract_at 0 rp (CFP_Simple VP_MakeSSA)` by
    simp[make_ssa_step_contract_at] >>
  `o1_fn_shape observed.cu_context out.fpo_function /\
   o1_fn_row 1 out.fpo_function` by
    (fs[o1_step_contract_at_def] >> metis_tac[]) >>
  `MEM f observed.cu_context.ctx_functions` by
    (gvs[fn_pass_step_def] >>
     metis_tac[lookup_unique_function_member]) >>
  `o1_fn_shape observed.cu_context f` by
    (gvs[o1_ctx_shape_def, EVERY_MEM] >> metis_tac[]) >>
  `~MEM "code_end" (fn_labels f)` by
    metis_tac[o1_fn_shape_labels_not_reserved, reserved_label_def] >>
  `wf_function f` by gvs[o1_fn_shape_def] >>
  Cases_on `make_ssa_current_fn s f` >>
  `out.fpo_function = q` by
    gvs[fn_pass_step_def, execute_configured_fn_pass_make_ssa] >>
  `!i. MEM i (fn_insts out.fpo_function) ==>
       ~MEM (Label "code_end") i.inst_operands` by
    metis_tac[make_ssa_current_fn_label_absent] >>
  `!x. ~code_end_var out.fpo_function x` by
    metis_tac[code_end_var_absent] >>
  conj_tac
  >- (irule label_flow_own_ok_from_code_end_use >>
      simp[] >> gvs[o1_fn_shape_def]) >>
  gvs[o1_fn_row_def]
QED
