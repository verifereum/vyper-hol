Theory lowerDloadScratchFreshness
Ancestors
  lowerDloadSupplyProofs lowerDloadDefs irSupply venomInst

Theorem ld_inst_alloca_origin:
  ir_supply_inst_ok a /\ lower_dload_inst_supply a i = (outs,b) /\
  MEM j outs /\ j.inst_opcode = ALLOCA ==>
  j = i \/ (~MEM j.inst_id a.irs_used_inst_ids /\
    j.inst_operands = [Lit 32w] /\ LENGTH j.inst_outputs = 1)
Proof
  simp[lower_dload_inst_supply_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  `ld_supply_extends a s1` by metis_tac[fresh_ir_var_extends] >>
  `ld_supply_extends s1 s2` by
    metis_tac[fresh_ir_var_extends, ld_supply_extends_def] >>
  `ir_supply_inst_ok s2` by gvs[ld_supply_extends_def] >>
  drule_all fresh_inst_id_contract >> strip_tac >>
  disj2_tac >> gvs[ld_supply_extends_def] >> metis_tac[]
QED

Theorem ld_inst_supply_extends_unconditional:
  ir_supply_inst_ok a /\ lower_dload_inst_supply a i = (outs,b) ==>
  ld_supply_extends a b
Proof
  simp[lower_dload_inst_supply_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac fresh_ir_var_extends >> fs[ld_supply_extends_def] >>
  imp_res_tac fresh_ir_var_extends >> fs[ld_supply_extends_def] >>
  imp_res_tac fresh_inst_id_extends >> fs[ld_supply_extends_def] >>
  imp_res_tac fresh_inst_id_extends >> fs[ld_supply_extends_def] >>
  imp_res_tac fresh_inst_id_extends >> fs[ld_supply_extends_def] >>
  imp_res_tac fresh_inst_id_extends >> fs[ld_supply_extends_def] >>
  rpt strip_tac >> metis_tac[]
QED
