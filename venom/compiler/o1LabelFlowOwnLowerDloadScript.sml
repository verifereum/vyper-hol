Theory o1LabelFlowOwnLowerDload
Ancestors
  codegenSymOwnRel
  o1LabelFlowCompose
  o1LabelFlowSourceCfgLabels
  o1LabelReadinessSsa
  o1LabelFlowStaticContracts
  o1LabelFlowLowerDload
  lowerDloadMakeSsaInput
  o1LabelFlowMiddle
  o1PassContract
  venomPassSchedule
  venomInst
  list

Theorem compose_lower_dload_own:
  !rp observed s f out ctx.
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
  (2 <= 3 ==> no_raw_fmp_ops out.fpo_function) /\ fmp_sig_no_param out.fpo_function)
Proof
  simp[] >> rpt gen_tac >> strip_tac >>
  `o1_step_contract_at 1 rp (CFP_Simple VP_LowerDload)` by
    (mp_tac (Q.SPEC `rp` (GEN_ALL o1_fn_passes_steps)) >>
     simp[o1_fn_passes_def, o1_step_contracts_from_def] >>
     metis_tac[]) >>
  qpat_x_assum `o1_step_contract_at _ _ _`
    (drule_all o REWRITE_RULE [o1_step_contract_at_def]) >> strip_tac >>
  `middle_code_end_lifetime out.fpo_function` by
    (drule lower_dload_step_supply >> strip_tac >>
     pure_rewrite_tac[middle_code_end_lifetime_def] >> rpt strip_tac >>
     irule lower_dload_function_code_end_lifetime >> metis_tac[]) >>
  `label_flow_own_ok (ctx with ctx_functions := [out.fpo_function])` by
    (fs[o1_fn_shape_def] >>
     irule label_flow_own_ok_from_code_end_use >> simp[] >>
     rpt strip_tac >> disj2_tac >>
     qpat_x_assum `middle_code_end_lifetime _`
       (mp_tac o REWRITE_RULE [middle_code_end_lifetime_def]) >>
     disch_then drule >> strip_tac >>
     gvs[fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[]) >>
  gvs[o1_fn_row_def]
QED
