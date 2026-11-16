Theory o1LabelFlowOwnFmp
Ancestors
  codegenSymOwnRel
  o1LabelFlowCompose
  o1LabelFlowSourceCfgLabels
  o1LabelReadinessSsa
  o1LabelFlowStaticContracts
  o1LabelFlowMiddleFmp
  fmpStepContract
  unitShapeDefs
  venomInst
  o1LabelFlowMiddle
  o1PassContract

Theorem compose_fmp_own:
  !rp observed s f out ctx.
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
  (4 <= 3 ==> no_raw_fmp_ops out.fpo_function) /\ fmp_sig_no_param out.fpo_function)
Proof
  rpt gen_tac >> simp[] >> strip_tac >>
  `o1_fn_shape observed.cu_context out.fpo_function /\
   o1_fn_row 4 out.fpo_function` by
    (mp_tac (Q.INST [`rpolicy` |-> `rp`] fmp_step_contract_at) >>
     simp[o1_step_contract_at_def] >>
     metis_tac[]) >>
  `middle_code_end_lifetime out.fpo_function` by
    (irule (PURE_REWRITE_RULE [GSYM middle_code_end_lifetime_def]
      fmp_row_code_end_lifetime) >> metis_tac[]) >>
  simp[] >> reverse conj_tac >- fs[o1_fn_row_def] >>
  irule label_flow_own_ok_from_code_end_use >>
  reverse conj_tac >- (simp[] >> fs[o1_fn_shape_def]) >>
  simp[] >> rpt strip_tac >>
  fs[middle_code_end_lifetime_def, fn_insts_def,
     MEM_fn_insts_blocks_iff] >> metis_tac[]
QED
