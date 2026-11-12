Theory lowerDloadConfiguredScratch
Ancestors
  lowerDloadConfiguredCaps lowerDloadAllocation lowerDloadSupplySegment
  o1LowerDloadSuppliedSegmentControl venomFnScheduleRunner irSupply
  lowerDloadDefs o1ContractLowerDload venomInst list pred_set

Theorem configured_block_member[local]:
  !pre a gp a0 bb post gb a3 gs b j.
    lower_dload_blocks_supply a (pre ++ bb::post) = (gs,b) /\
    lower_dload_blocks_supply a pre = (gp,a0) /\
    lower_dload_block_supply a0 bb = (gb,a3) /\
    MEM j gb.bb_instructions ==> MEM j (fn_insts_blocks gs)
Proof
  Induct >- (simp[lower_dload_blocks_supply_def, AllCaseEqs()] >>
    rpt strip_tac >> gvs[fn_insts_blocks_def]) >>
  rpt gen_tac >>
  simp[Once lower_dload_blocks_supply_def, AllCaseEqs()] >>
  strip_tac >>
  qpat_x_assum `lower_dload_blocks_supply a (h::pre) = _` mp_tac >>
  simp[Once lower_dload_blocks_supply_def, AllCaseEqs()] >> strip_tac >>
  gvs[fn_insts_blocks_def] >>
  disj2_tac >> first_x_assum irule >> metis_tac[]
QED

Theorem lower_dload_configured_scratch_member:
  ir_supply_covers_fn a f /\
  lower_dload_function_supply a f = (g,b) /\
  f.fn_blocks = bpre ++ bb::bpost /\
  lower_dload_blocks_supply a bpre = (qpre,a0) /\
  lower_dload_block_supply a0 bb = (gb,a3) /\
  bb.bb_instructions = pre ++ i::post /\
  lower_dload_insts_supply a0 pre = (p,a1) /\
  lower_dload_inst_supply a1 i = (code,a2) /\
  i.inst_opcode = DLOAD /\ i.inst_operands = [op] /\ i.inst_outputs = [out] ==>
  (HD code).inst_id IN
    (set (MAP (\j. j.inst_id) (FILTER (\j. j.inst_opcode = ALLOCA) (fn_insts g))) DIFF
     set (MAP (\j. j.inst_id) (fn_insts f)))
Proof
  strip_tac >>
  `a.irs_next_inst <= a0.irs_next_inst` by
    metis_tac[ld_supply_blocks_reservations] >>
  `a0.irs_next_inst <= a1.irs_next_inst` by
    metis_tac[ld_supply_insts_reservations] >>
  `LENGTH code = 4 /\ (HD code).inst_id = a1.irs_next_inst /\
   (HD code).inst_opcode = ALLOCA /\ (HD code).inst_operands = [Lit 32w]` by
    metis_tac[ld_supply_dload_shape] >>
  `~MEM (HD code).inst_id (fn_ir_inst_ids f)` by
    (gvs[ir_supply_covers_fn_def, EVERY_MEM] >>
     rpt strip_tac >> res_tac >> decide_tac) >>
  `lower_dload_insts_supply a0 (pre ++ i::post) = (gb.bb_instructions,a3)` by
    gvs[lower_dload_block_supply_def, AllCaseEqs()] >>
  drule lower_dload_insts_supply_append >> strip_tac >> gvs[] >>
  `MEM (HD code) gb.bb_instructions` by
    (gvs[lower_dload_insts_supply_def, AllCaseEqs()] >>
     Cases_on `code` >> gvs[]) >>
  `MEM (HD code) (fn_insts g)` by
    (qpat_x_assum `lower_dload_function_supply a f = _` mp_tac >>
     simp[lower_dload_function_supply_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
     simp[fn_insts_def] >> irule configured_block_member >>
     qexistsl_tac [`a`, `a0`, `a3`, `b`, `bb`, `gb`, `qpre`, `bpost`, `bpre`] >>
     rule_assum_tac (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND]) >> simp[]) >>
  `fn_ir_inst_ids f = MAP (\j. j.inst_id) (fn_insts f)` by
    (pure_rewrite_tac[fn_ir_inst_ids_def, fn_insts_def] >>
     qspec_tac (`f.fn_blocks`, `bs`) >> Induct >>
     simp[fn_insts_blocks_def, block_ir_inst_ids_def]) >>
  simp[IN_DIFF, MEM_MAP, MEM_FILTER] >> conj_tac
  >- (qexists_tac `HD code` >> simp[]) >>
  metis_tac[MEM_MAP]
QED

Theorem lower_dload_configured_scratch_account:
  keys = (set (MAP (\j. j.inst_id)
    (FILTER (\j. j.inst_opcode = ALLOCA) (fn_insts g))) DIFF
    set (MAP (\j. j.inst_id) (fn_insts f))) /\
  ir_supply_covers_fn a f /\
  lower_dload_function_supply a f = (g,b) /\
  f.fn_blocks = bpre ++ bb::bpost /\
  lower_dload_blocks_supply a bpre = (qpre,a0) /\
  lower_dload_block_supply a0 bb = (gb,a3) /\
  bb.bb_instructions = pre ++ i::post /\
  lower_dload_insts_supply a0 pre = (p,a1) /\
  lower_dload_inst_supply a1 i = (code,a2) /\
  i.inst_opcode = DLOAD /\ i.inst_operands = [op] /\ i.inst_outputs = [out] /\
  ld_alloc_account keys d A s t /\
  exec_alloca (HD code) t (32w:bytes32) = OK t' ==>
  ld_alloc_account keys d ((HD code).inst_id INSERT A) s t'
Proof
  rpt strip_tac >>
  `(HD code).inst_id IN keys` by
    (drule_all lower_dload_configured_scratch_member >> simp[]) >>
  `?tmp. (HD code).inst_outputs = [tmp]` by
    gvs[lower_dload_inst_supply_def, AllCaseEqs()] >>
  irule ld_alloc_account_scratch >> metis_tac[]
QED

Theorem lower_dload_configured_scratch_count:
  keys = (set (MAP (\j. j.inst_id)
    (FILTER (\j. j.inst_opcode = ALLOCA) (fn_insts g))) DIFF
    set (MAP (\j. j.inst_id) (fn_insts f))) /\
  ir_supply_covers_fn a f /\
  lower_dload_function_supply a f = (g,b) /\
  f.fn_blocks = bpre ++ bb::bpost /\
  lower_dload_blocks_supply a bpre = (qpre,a0) /\
  lower_dload_block_supply a0 bb = (gb,a3) /\
  bb.bb_instructions = pre ++ i::post /\
  lower_dload_insts_supply a0 pre = (p,a1) /\
  lower_dload_inst_supply a1 i = (code,a2) /\
  i.inst_opcode = DLOAD /\ i.inst_operands = [op] /\ i.inst_outputs = [out] /\
  ld_alloc_account keys d A s t /\
  exec_alloca (HD code) t (32w:bytes32) = OK t' ==>
  CARD ((HD code).inst_id INSERT A) <=
    LENGTH (FILTER (\j. j.inst_opcode = DLOAD) (fn_insts f))
Proof
  strip_tac >>
  drule_all lower_dload_configured_scratch_account >> strip_tac >>
  drule ld_alloc_account_card_bound >> strip_tac >>
  drule lower_dload_configured_cap_bound >> strip_tac >>
  gvs[Excl "CARD_DIFF"] >> decide_tac
QED
