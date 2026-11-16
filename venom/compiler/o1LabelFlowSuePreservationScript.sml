Theory o1LabelFlowSuePreservation
Ancestors
  o1LabelFlowSuePositive o1LabelFlowSueNegative o1ContractSue
  codegenSymRel

Theorem sue_expand_function_supply_label_flow_ok:
  ir_supply_inst_ok s /\ ir_supply_covers_fn s f /\
  sue_expand_function_supply s f = (g,t) /\
  label_flow_ok (ctx with ctx_functions := [f]) ==>
  label_flow_ok (ctx with ctx_functions := [g])
Proof
  strip_tac >>
  `!j. MEM j (fn_insts g) ==>
    j.inst_opcode <> CODESIZE /\
    (!v. MEM (Var v) j.inst_operands /\ code_end_var g v ==>
      (j.inst_opcode = ASSIGN /\ j.inst_operands = [Var v]) \/
      (j.inst_opcode = CODECOPY /\ ?dst sz.
        j.inst_operands = [dst;Var v;sz] /\ dst <> Var v /\ sz <> Var v))` by
    (metis_tac[sue_expand_function_supply_negative_flow]) >>
  simp[label_flow_ok_def] >> rpt strip_tac >>
  metis_tac[sue_positive_codecopy_source]
QED

Theorem sue_row_label_flow_ok:
  fn_pass_step rpolicy (CFP_Simple VP_SingleUseExpansion) observed s fn out /\
  label_flow_ok (ctx with ctx_functions := [fn]) ==>
  label_flow_ok (ctx with ctx_functions := [out.fpo_function])
Proof
  strip_tac >> drule sue_pass_step_replay >> strip_tac >>
  metis_tac[sue_expand_function_supply_label_flow_ok]
QED
