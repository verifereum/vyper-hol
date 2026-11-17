Theory o1LabelFlowCfgIteration
Ancestors
  o1LabelFlowCfgSplitPreservation o1ContractCfgNormStep o1ContractCfgNorm
  cfgNormSupplySim cfgNormSupplyProofs cfgNormDefs codegenSymRel
  irSupply list

Theorem cfg_norm_round_supply_label_flow_invariants:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  label_flow_ok (ctx with ctx_functions := [fn]) /\
  cfg_norm_round_supply s fn = (fn',changed,s') ==>
  wf_function fn' /\ ir_supply_covers_fn s' fn' /\ ir_supply_inst_ok s' /\
  label_flow_ok (ctx with ctx_functions := [fn'])
Proof
  strip_tac >> drule cfg_norm_round_supply_cases >> strip_tac
  >- gvs[] >>
  `wf_function fn'` by metis_tac[insert_split_supply_wf_function] >>
  `ir_supply_covers_fn s' fn' /\ ir_supply_inst_ok s'` by
    metis_tac[insert_split_supply_ir_covered] >>
  simp[] >>
  drule insert_split_supply_labels >> strip_tac >>
  `MEM fn (ctx with ctx_functions := [fn]).ctx_functions` by simp[] >>
  drule_all cfg_split_label_flow_ok >> simp[]
QED

Theorem cfg_norm_iter_supply_label_flow_invariants:
  !n s fn fn' s'.
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  label_flow_ok (ctx with ctx_functions := [fn]) /\
  cfg_norm_iter_supply n s fn = (fn',s') ==>
  wf_function fn' /\ ir_supply_covers_fn s' fn' /\ ir_supply_inst_ok s' /\
  label_flow_ok (ctx with ctx_functions := [fn'])
Proof
  Induct >- simp[cfg_norm_iter_supply_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `cfg_norm_round_supply s fn` >> PairCases_on `r` >>
  rename1 `cfg_norm_round_supply s fn = (fn1,changed,s1)` >>
  `wf_function fn1 /\ ir_supply_covers_fn s1 fn1 /\ ir_supply_inst_ok s1 /\
   label_flow_ok (ctx with ctx_functions := [fn1])` by
    metis_tac[cfg_norm_round_supply_label_flow_invariants] >>
  Cases_on `changed` >> gvs[cfg_norm_iter_supply_def] >> metis_tac[]
QED

Theorem cfg_norm_function_supply_label_flow_ok:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  label_flow_ok (ctx with ctx_functions := [fn]) /\
  cfg_norm_function_supply s fn = (fn',s') ==>
  label_flow_ok (ctx with ctx_functions := [fn'])
Proof
  simp[cfg_norm_function_supply_def] >>
  metis_tac[cfg_norm_iter_supply_label_flow_invariants]
QED

Theorem cfg_norm_row_label_flow_ok:
  fn_pass_step rpolicy (CFP_Simple VP_CFGNormalization) observed s fn out /\
  wf_function fn /\ label_flow_ok (ctx with ctx_functions := [fn]) ==>
  label_flow_ok (ctx with ctx_functions := [out.fpo_function])
Proof
  strip_tac >> drule cfg_norm_pass_step_replay >> strip_tac >>
  metis_tac[cfg_norm_function_supply_label_flow_ok]
QED
