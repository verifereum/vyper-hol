Theory algebraicOptSsaSupplyProofs
Ancestors
  algebraicOptDefs venomFnScheduleRunner irSupply venomWf venomInst
  list pred_set

Theorem ao_alloc_fresh_contract:
  ao_alloc_fresh s = (fr,t) ==>
  fr "xor" = fr "not" /\
  FST (fr "not") = s.irs_next_inst /\
  FST (fr "iz") = SUC s.irs_next_inst /\
  t.irs_next_inst = s.irs_next_inst + 2 /\
  SND (fr "not") <> SND (fr "iz") /\
  ~MEM (SND (fr "not")) s.irs_used_vars /\
  ~MEM (SND (fr "iz")) s.irs_used_vars /\
  t.irs_used_vars = SND (fr "iz") :: SND (fr "not") :: s.irs_used_vars
Proof
  rewrite_tac[ao_alloc_fresh_def] >>
  Cases_on `fresh_inst_id s` >>
  rename1 `fresh_inst_id s = (inner_id,s1)` >>
  Cases_on `fresh_ir_var s1` >>
  rename1 `fresh_ir_var s1 = (inner,s2)` >>
  Cases_on `fresh_inst_id s2` >>
  rename1 `fresh_inst_id s2 = (iz_id,s3)` >>
  Cases_on `fresh_ir_var s3` >>
  rename1 `fresh_ir_var s3 = (iz,s4)` >>
  simp[] >> strip_tac >>
  drule fresh_ir_var_contract >> strip_tac >>
  qpat_x_assum `fresh_ir_var s3 = _` kall_tac >>
  drule fresh_ir_var_contract >> strip_tac >>
  gvs[fresh_inst_id_def]
QED

Theorem ao_alloc_fresh_bounds:
  ao_alloc_fresh s = (fr,t) ==>
  set s.irs_used_vars SUBSET set t.irs_used_vars /\
  MEM (SND (fr "not")) t.irs_used_vars /\
  MEM (SND (fr "iz")) t.irs_used_vars /\
  FST (fr "not") <> FST (fr "iz") /\
  s.irs_next_inst <= FST (fr "not") /\
  s.irs_next_inst <= FST (fr "iz") /\
  FST (fr "not") < t.irs_next_inst /\
  FST (fr "iz") < t.irs_next_inst /\
  s.irs_next_inst <= t.irs_next_inst
Proof
  strip_tac >> drule ao_alloc_fresh_contract >> strip_tac >>
  simp[SUBSET_DEF]
QED

Theorem ao_initial_output_coverage:
  ir_supply_covers_fn s fn ==>
  set (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn))) SUBSET
  set s.irs_used_vars
Proof
  `!bbs. FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs)) =
         FLAT (MAP (\bb. FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) bbs)` by
    (Induct >> simp[fn_insts_blocks_def, MAP_APPEND]) >>
  rewrite_tac[fn_insts_def] >>
  first_x_assum (fn th => rewrite_tac[th]) >>
  simp[ir_supply_covers_fn_def, list_subset_def, EVERY_MEM,
       fn_ir_vars_def, block_ir_vars_def, inst_ir_vars_def,
       fn_insts_def, SUBSET_DEF, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
  metis_tac[]
QED

Theorem ao_initial_inst_id_bound:
  ir_supply_covers_fn s fn ==>
  EVERY (\i. i.inst_id < s.irs_next_inst) (fn_insts fn)
Proof
  `!bbs. MAP (\i. i.inst_id) (fn_insts_blocks bbs) =
         FLAT (MAP block_ir_inst_ids bbs)` by
    (Induct >> simp[fn_insts_blocks_def, block_ir_inst_ids_def, MAP_APPEND]) >>
  strip_tac >>
  `EVERY (\id. id < s.irs_next_inst)
     (MAP (\i. i.inst_id) (fn_insts_blocks fn.fn_blocks))` by
    gvs[ir_supply_covers_fn_def, fn_ir_inst_ids_def] >>
  gvs[EVERY_MAP, fn_insts_def]
QED

Theorem ao_initial_inst_ids_distinct:
  wf_function fn ==>
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn))
Proof
  `!bbs. MAP (\i. i.inst_id) (fn_insts_blocks bbs) =
         FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) bbs)` by
    (Induct >> simp[fn_insts_blocks_def, MAP_APPEND]) >>
  simp[wf_function_def, fn_inst_ids_distinct_def, fn_insts_def]
QED

Theorem ao_name_inserts_supply_fresh:
  !inserts s named t.
    ao_name_inserts_supply s inserts = (named,t) ==>
    ALL_DISTINCT (MAP (\(a,(out,id,v)). v) named) /\
    DISJOINT (set (MAP (\(a,(out,id,v)). v) named)) (set s.irs_used_vars)
Proof
  Induct >- simp[ao_name_inserts_supply_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  rewrite_tac[ao_name_inserts_supply_def] >>
  Cases_on `fresh_inst_id s` >>
  rename1 `fresh_inst_id s = (id,s1)` >>
  Cases_on `fresh_ir_var s1` >>
  rename1 `fresh_ir_var s1 = (v,s2)` >>
  Cases_on `ao_name_inserts_supply s2 inserts` >>
  simp[] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule fresh_ir_var_contract >> strip_tac >>
  gvs[fresh_inst_id_def, DISJOINT_DEF, EXTENSION] >>
  metis_tac[]
QED
