Theory lowerDloadPtrSupplyOrigins
Ancestors o1PassContract lowerDloadPtrRel lowerDloadPtrPhase o1ContractLowerDload lowerDloadDefs irSupply
  venomFnScheduleRunner venomInst list pred_set

Theorem lower_dload_inst_supply_counter_mono:
  lower_dload_inst_supply q i = (xs,q') ==>
  q.irs_next_inst <= q'.irs_next_inst
Proof
  simp[lower_dload_inst_supply_def, AllCaseEqs(), fresh_inst_id_def] >>
  rpt strip_tac >> gvs[] >>
  imp_res_tac fresh_ir_var_contract >> gvs[]
QED

Theorem lower_dload_insts_supply_counter_mono:
  !q xs q'. lower_dload_insts_supply q ins = (xs,q') ==>
  q.irs_next_inst <= q'.irs_next_inst
Proof
  Induct_on `ins` >- simp[lower_dload_insts_supply_def] >>
  simp[Once lower_dload_insts_supply_def, AllCaseEqs()] >> rpt strip_tac >>
  drule lower_dload_inst_supply_counter_mono >>
  first_x_assum drule >> decide_tac
QED

Theorem lower_dload_block_supply_counter_mono:
  lower_dload_block_supply q bb = (bb',q') ==>
  q.irs_next_inst <= q'.irs_next_inst
Proof
  simp[lower_dload_block_supply_def, AllCaseEqs()] >> rpt strip_tac >>
  drule lower_dload_insts_supply_counter_mono >> simp[]
QED

Theorem lower_dload_blocks_supply_counter_mono:
  !q bs q'. lower_dload_blocks_supply q bbs = (bs,q') ==>
  q.irs_next_inst <= q'.irs_next_inst
Proof
  Induct_on `bbs` >- simp[lower_dload_blocks_supply_def] >>
  simp[Once lower_dload_blocks_supply_def, AllCaseEqs()] >> rpt strip_tac >>
  drule lower_dload_block_supply_counter_mono >>
  first_x_assum drule >> decide_tac
QED

Theorem dload_control_supply_origins:
  ir_supply_covers_fn q f /\
  dload_control_match q f g s t i emitted phase /\
  i.inst_opcode = DLOAD /\ i.inst_operands = [off] /\ i.inst_outputs = [out] ==>
  ?supply after av cv.
    lower_dload_inst_supply supply i = (emitted,after) /\
    (EL 0 emitted).inst_outputs = [av] /\ (EL 1 emitted).inst_outputs = [cv] /\
    av <> cv /\ av NOTIN set (fn_ir_vars f) /\ cv NOTIN set (fn_ir_vars f) /\
    (EL 0 emitted).inst_id NOTIN {ci.inst_id | MEM ci (fn_insts f)}
Proof
  strip_tac >>
  qpat_x_assum `dload_control_match _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[dload_control_match_def] >> strip_tac >>
  Cases_on `fresh_ir_var is` >> rename1 `fresh_ir_var is = (av,s1)` >>
  Cases_on `fresh_ir_var s1` >> rename1 `fresh_ir_var s1 = (cv,s2)` >>
  `q.irs_next_inst <= is.irs_next_inst` by suspend "counter" >>
  `!v. MEM v (fn_ir_vars f) ==> MEM v is.irs_used_vars` by suspend "reserved" >>
  qpat_x_assum `active_inst g _ _` kall_tac >>
  qpat_x_assum `active_inst f _ _` kall_tac >>
  qexistsl [`is`,`after`,`av`,`cv`] >> simp[] >>
  qpat_x_assum `lower_dload_inst_supply is i = _` mp_tac >>
  simp[lower_dload_inst_supply_def, fresh_inst_id_def] >> strip_tac >> gvs[] >>
  qpat_assum `fresh_ir_var is = _`
    (mp_then Any strip_assume_tac fresh_ir_var_contract) >>
  qpat_assum `fresh_ir_var s1 = _`
    (mp_then Any strip_assume_tac fresh_ir_var_contract) >>
  gvs[] >> conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
  simp[] >> rpt strip_tac >>
  `MEM ci.inst_id (fn_ir_inst_ids f)` by
    (fs[fn_ir_inst_ids_def, block_ir_inst_ids_def, fn_insts_def,
      fn_insts_blocks_MEM, MEM_FLAT, MEM_MAP] >>
     qexists `MAP (\inst. inst.inst_id) bb.bb_instructions` >>
     simp[MEM_MAP] >> metis_tac[]) >>
  fs[ir_supply_covers_fn_def, EVERY_MEM] >>
  qpat_x_assum `!id. MEM id (fn_ir_inst_ids f) ==> _` drule >> decide_tac
QED

Resume dload_control_supply_origins[counter]:
  rpt strip_tac >>
  Cases_on `lower_dload_blocks_supply q (TAKE bi f.fn_blocks)` >> gvs[] >>
  drule lower_dload_blocks_supply_counter_mono >>
  drule lower_dload_insts_supply_counter_mono >> decide_tac
QED

Resume dload_control_supply_origins[reserved]:
  rpt strip_tac >>
  Cases_on `lower_dload_blocks_supply q (TAKE bi f.fn_blocks)` >> gvs[] >>
  drule lower_dload_blocks_supply_reserved_operand >> strip_tac >>
  drule lower_dload_insts_supply_reserved_operand >> strip_tac >>
  fs[ir_supply_covers_fn_def, list_subset_def, EVERY_MEM] >> metis_tac[]
QED

Finalise dload_control_supply_origins
