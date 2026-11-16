Theory o1LabelFlowOwnWalk
Ancestors
  codegenSymOwnRel
  o1LabelFlowCompose
  o1LabelFlowSourceCfgLabels
  o1LabelReadinessSsa
  o1LabelFlowStaticContracts
  o1FnScheduleDecompHelpers
  venomPassSchedule
  o1ScheduleDecomp
  o1PartialSchedule
  o1PassContract
  list

Theorem o1_label_flow_own_walk:
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
!rp names u s u' s'.
  run_named_fn_schedules execute_configured_fn_pass rp o1_fn_passes names u s =
    SOME (u',s') /\ o1_ctx_shape u.cu_context /\
  ALL_DISTINCT (unit_label_namespace u) /\ ALL_DISTINCT names /\
  (!n. MEM n names <=> MEM n (ctx_fn_names u.cu_context)) /\
  ir_supply_inst_ok s /\ EVERY (o1_fn_row 0) u.cu_context.ctx_functions /\
  EVERY no_raw_fmp_ops u.cu_context.ctx_functions /\
  EVERY fmp_sig_no_param u.cu_context.ctx_functions /\
  label_flow_own_ok u.cu_context /\
  (!f i. MEM f u.cu_context.ctx_functions /\ MEM i (fn_insts f) ==>
    ~MEM (Label "code_end") i.inst_operands) ==>
  label_flow_own_ok u'.cu_context
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  qabbrev_tac `R = \k f. o1_fn_row k f /\
    label_flow_own_ok (u.cu_context with ctx_functions := [f]) /\
    (k <= 1 ==> !i. MEM i (fn_insts f) ==>
      ~MEM (Label "code_end") i.inst_operands) /\
    (2 <= k /\ k <= 4 ==> middle_code_end_lifetime f) /\
    (k <= 3 ==> no_raw_fmp_ops f) /\ fmp_sig_no_param f` >>
  `rows_step_contracts_from R rp 0 o1_fn_passes` by
    (qpat_x_assum `!k pass rp observed s f out ctx. _`
       (fn th => map_every (fn k =>
         qspec_then k (assume_tac o SIMP_RULE (srw_ss()) []) th)
         [`5`, `6`, `7`, `8`]) >>
     mp_tac (Q.SPEC `rp` (GEN_ALL o1_fn_passes_steps)) >>
     disch_then (mp_tac o MATCH_MP o1_step_contracts_from_rows) >>
     rewrite_tac[o1_fn_passes_def, rows_step_contracts_from_def] >>
     strip_tac >> rpt conj_tac >>
     rewrite_tac[rows_step_contract_def] >> rpt gen_tac >> strip_tac >>
     qpat_x_assum `R _ _` mp_tac >>
     simp[NoAsms, Abbr `R`] >> strip_tac >>
     qpat_x_assum `EVERY (\g. ?j. _ j g) _` mp_tac >>
     simp[NoAsms] >> strip_tac >>
     `EVERY (\g. ?j. o1_fn_row j g) observed.cu_context.ctx_functions` by
       (fs[EVERY_MEM] >> metis_tac[]) >>
     `EVERY fmp_sig_no_param observed.cu_context.ctx_functions` by
       (fs[EVERY_MEM] >> metis_tac[]) >>
     first_assum (drule_all o SIMP_RULE (srw_ss()) [rows_step_contract_def]) >>
     strip_tac >>
     first_assum (drule_all o SIMP_RULE (srw_ss()) []) >>
     strip_tac >> metis_tac[]) >>
  ntac 5 (qpat_x_assum
    `!rp observed s f out ctx. fn_pass_step _ _ _ _ _ _ /\ _ ==> _` kall_tac) >>
  qpat_x_assum `!k pass rp observed s f out ctx. _` kall_tac >>
  drule_at (Pos (el 1)) run_named_fn_schedules_decomp >>
  disch_then (drule_at (Pat `run_named_fn_schedules _ _ _ _ _ _ = _`)) >>
  impl_tac
  >- (simp[Abbr `R`, EVERY_MEM] >> rpt strip_tac >>
      fs[EVERY_MEM, label_flow_own_ok_def] >> metis_tac[]) >>
  disch_then (qx_choose_then `chains` strip_assume_tac) >>
  `!i. i < LENGTH chains ==>
    label_flow_own_ok (u.cu_context with ctx_functions :=
      [EL (LENGTH o1_fn_passes) (FST (EL i chains))])` by
    (rpt strip_tac >>
     qpat_x_assum `!i. i < LENGTH chains ==> chain_facts _ _ _ _ _ _ _`
       (qspec_then `i` mp_tac) >> impl_tac >- simp[] >> strip_tac >>
     drule_at (Pos (el 1)) chain_facts_row >>
     disch_then (qspec_then `LENGTH o1_fn_passes` mp_tac) >>
     simp[Abbr `R`]) >>
  qpat_x_assum `u'.cu_context = _` SUBST1_TAC >>
  simp[stage_ctx_def, stage_fns_def, label_flow_own_ok_def, MEM_MAP] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `MEM _ chains` (mp_tac o REWRITE_RULE [MEM_EL]) >>
  disch_then (qx_choose_then `j` strip_assume_tac) >> gvs[] >>
  qpat_x_assum `!i. _ ==> label_flow_own_ok _` (qspec_then `j` mp_tac) >>
  impl_tac >- simp[] >> simp[label_flow_own_ok_def]
QED
