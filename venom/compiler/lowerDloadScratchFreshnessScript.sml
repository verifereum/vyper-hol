Theory lowerDloadScratchFreshness
Ancestors
  lowerDloadSupplyProofs lowerDloadDefs irSupply venomInst
  lowerDloadScratchBudget contextCodegenRel list

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

Theorem ld_insts_alloca_origin:
  !ins a outs b. ir_supply_inst_ok a /\
  lower_dload_insts_supply a ins = (outs,b) ==>
  ld_supply_extends a b /\
  !j. MEM j outs /\ j.inst_opcode = ALLOCA ==>
    MEM j ins \/ (~MEM j.inst_id a.irs_used_inst_ids /\
      j.inst_operands = [Lit 32w] /\ LENGTH j.inst_outputs = 1)
Proof
  Induct >- simp[lower_dload_insts_supply_def, ld_supply_extends_refl] >>
  rpt gen_tac >>
  Cases_on `lower_dload_inst_supply a h` >>
  Cases_on `lower_dload_insts_supply r ins` >>
  simp[lower_dload_insts_supply_def] >> strip_tac >> gvs[] >>
  `ld_supply_extends a r` by metis_tac[ld_inst_supply_extends_unconditional] >>
  `ir_supply_inst_ok r` by gvs[ld_supply_extends_def] >>
  first_x_assum drule_all >> strip_tac >>
  conj_tac >- metis_tac[ld_supply_extends_trans] >>
  simp[MEM_APPEND] >> rpt strip_tac
  >- (drule_all ld_inst_alloca_origin >> strip_tac >> gvs[]) >>
  first_x_assum drule_all >> strip_tac >> gvs[ld_supply_extends_def] >>
  metis_tac[]
QED

Theorem ld_blocks_alloca_origin[local]:
  !bs a bs' b. ir_supply_inst_ok a /\
  lower_dload_blocks_supply a bs = (bs',b) ==>
  ld_supply_extends a b /\
  !j. MEM j (fn_insts_blocks bs') /\ j.inst_opcode = ALLOCA ==>
    MEM j (fn_insts_blocks bs) \/ (~MEM j.inst_id a.irs_used_inst_ids /\
      j.inst_operands = [Lit 32w] /\ LENGTH j.inst_outputs = 1)
Proof
  Induct >- simp[lower_dload_blocks_supply_def, fn_insts_blocks_def,
                 ld_supply_extends_refl] >>
  rpt gen_tac >>
  Cases_on `lower_dload_block_supply a h` >>
  Cases_on `lower_dload_blocks_supply r bs` >>
  simp[lower_dload_blocks_supply_def] >> strip_tac >> gvs[] >>
  `lower_dload_insts_supply a h.bb_instructions = (q.bb_instructions,r)` by
    gvs[lower_dload_block_supply_def, AllCaseEqs()] >>
  drule_all ld_insts_alloca_origin >> strip_tac >>
  `ir_supply_inst_ok r` by gvs[ld_supply_extends_def] >>
  first_x_assum drule_all >> strip_tac >>
  conj_tac >- metis_tac[ld_supply_extends_trans] >>
  simp[fn_insts_blocks_def, MEM_APPEND] >> rpt strip_tac >>
  first_x_assum drule_all >> strip_tac >> gvs[ld_supply_extends_def] >>
  metis_tac[]
QED

Theorem ld_function_alloca_origin:
  ir_supply_inst_ok a /\ lower_dload_function_supply a fn = (fn',b) /\
  MEM j (fn_insts fn') /\ j.inst_opcode = ALLOCA ==>
  MEM j (fn_insts fn) \/ (~MEM j.inst_id a.irs_used_inst_ids /\
    j.inst_operands = [Lit 32w] /\ LENGTH j.inst_outputs = 1)
Proof
  simp[lower_dload_function_supply_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[fn_insts_def, GSYM fn_insts_blocks_def] >>
  drule_all ld_blocks_alloca_origin >> strip_tac >>
  first_x_assum drule_all >> simp[]
QED

Theorem ld_function_scratch_cap_fresh:
  ir_supply_inst_ok a /\ lower_dload_function_supply a fn = (fn',b) /\
  id IN (set (MAP (\j. j.inst_id) (FILTER (\j. j.inst_opcode = ALLOCA) (fn_insts fn'))) DIFF
         set (MAP (\j. j.inst_id) (FILTER (\j. j.inst_opcode = ALLOCA) (fn_insts fn)))) ==>
  ~MEM id a.irs_used_inst_ids
Proof
  simp[MEM_MAP, MEM_FILTER] >> rpt strip_tac >> gvs[] >>
  drule_all ld_function_alloca_origin >> strip_tac >> simp[] >>
  metis_tac[]
QED

Theorem ld_function_scratch_alloca_shape:
  ir_supply_inst_ok a /\ lower_dload_function_supply a fn = (fn',b) /\
  active_inst fn' j t /\ j.inst_opcode = ALLOCA /\
  ~MEM j.inst_id (MAP (\i. i.inst_id) (FILTER (\i. i.inst_opcode = ALLOCA) (fn_insts fn))) ==>
  ~MEM j.inst_id a.irs_used_inst_ids /\
  j.inst_operands = [Lit 32w] /\ LENGTH j.inst_outputs = 1
Proof
  strip_tac >>
  `MEM j (fn_insts fn')` by
    (gvs[active_inst_def, fn_insts_def, MEM_FLAT, MEM_MAP] >>
     metis_tac[EL_MEM, o1PassContractTheory.fn_insts_blocks_MEM]) >>
  drule_all ld_function_alloca_origin >> strip_tac >> simp[] >>
  gvs[MEM_MAP, MEM_FILTER] >> metis_tac[]
QED
