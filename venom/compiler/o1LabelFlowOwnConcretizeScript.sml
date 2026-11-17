Theory o1LabelFlowOwnConcretize
Ancestors
  codegenSymOwnRel
  o1LabelFlowCompose
  o1LabelFlowSourceCfgLabels
  o1LabelReadinessSsa
  o1LabelFlowStaticContracts
  concretizeStepContract
  o1PassContract
  o1LabelFlowMiddle
  o1LabelFlowMiddleConcretize
  o1LabelFlowMiddleFmp
  concretizeMemLocDefs
  venomPassDispatcher
  unitShapeDefs
  venomInst
  list

Theorem compose_concretize_own:
  !rp observed s f out ctx.
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
  (3 <= 3 ==> no_raw_fmp_ops out.fpo_function) /\ fmp_sig_no_param out.fpo_function)
Proof
  rpt gen_tac >> simp[] >> strip_tac >>
  `fmp_sig_no_param out.fpo_function` by
    (drule fn_pass_step_fmp_sig_no_param >>
     simp[venomPassScheduleTheory.fn_pass_tag_def] >> metis_tac[]) >>
  `no_raw_fmp_ops out.fpo_function` by
    metis_tac[concretizeStageShapeTheory.concretize_step_no_raw_fmp] >>
  `o1_fn_shape observed.cu_context out.fpo_function /\
   o1_fn_row 3 out.fpo_function` by
    (mp_tac (Q.SPEC `rp` (GEN_ALL concretize_step_contract_at)) >>
     simp[o1_step_contract_at_def] >> metis_tac[]) >>
  `middle_code_end_lifetime out.fpo_function` by
    (`execute_configured_fn_pass rp (CFP_Simple VP_ConcretizeMemLoc)
        observed s f = SOME out` by fs[fn_pass_step_def] >>
     gvs[execute_configured_fn_pass_concretize, AllCaseEqs()] >>
     gvs[concretize_function_fuel_in_context_def, AllCaseEqs()] >>
     `middle_code_end_lifetime
        (concretize_function_with_positions layout.cl_positions f)` by
       (drule (PURE_REWRITE_RULE [GSYM middle_code_end_lifetime_def]
         concretize_function_code_end_lifetime) >> simp[]) >>
     gvs[apply_context_concretize_layout_def, apply_concretize_layout_def] >>
     qmatch_goalsub_abbrev_tac `middle_code_end_lifetime g` >>
     `g.fn_blocks =
        (concretize_function_with_positions layout.cl_positions f).fn_blocks` by
       simp[Abbr `g`] >>
     `!x. code_end_var g x <=>
       code_end_var (concretize_function_with_positions layout.cl_positions f) x` by
       metis_tac[code_end_var_same_blocks] >>
     fs[middle_code_end_lifetime_def, fn_insts_def]) >>
  reverse conj_tac >- fs[o1_fn_row_def] >>
  irule label_flow_own_ok_from_code_end_use >> simp[] >>
  reverse conj_tac >- fs[o1_fn_shape_def] >>
  rpt strip_tac >>
  fs[middle_code_end_lifetime_def] >>
  first_x_assum drule >> strip_tac >>
  fs[fn_insts_def, MEM_fn_insts_blocks_iff] >> metis_tac[]
QED
