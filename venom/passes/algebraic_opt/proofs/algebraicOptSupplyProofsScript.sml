Theory algebraicOptSupplyProofs
Ancestors
  algebraicOptDefs irSupply venomFnScheduleRunner venomWf venomInst
  list pred_set alist passSimulationDefs dfgAnalysisProps

Theorem ao_alloc_fresh_props:
  ao_alloc_fresh s = (fr,t) ==>
  fr "xor" = fr "not" /\
  fr "inner" = fr "not" /\
  FST (fr "not") = s.irs_next_inst /\
  FST (fr "iz") = SUC s.irs_next_inst /\
  t.irs_next_inst = s.irs_next_inst + 2 /\
  SND (fr "not") <> SND (fr "iz") /\
  ~MEM (SND (fr "not")) s.irs_used_vars /\
  ~MEM (SND (fr "iz")) s.irs_used_vars /\
  t.irs_used_inst_ids = FST (fr "iz") :: FST (fr "not") :: s.irs_used_inst_ids /\
  t.irs_used_vars = SND (fr "iz") :: SND (fr "not") :: s.irs_used_vars /\
  s.irs_next_var < t.irs_next_var /\
  t.irs_next_label = s.irs_next_label /\
  t.irs_used_labels = s.irs_used_labels
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
  gvs[fresh_inst_id_def] >> decide_tac
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
  strip_tac >> drule ao_alloc_fresh_props >> strip_tac >>
  simp[SUBSET_DEF]
QED

(* Allocation is independent of execution-state lookups.  Separation from
   any covered source collection follows from separation from the used sets. *)
Theorem ao_alloc_fresh_contract:
  !supply fr supply1.
  ir_supply_inst_ok supply /\ ao_alloc_fresh supply = (fr,supply1) ==>
  FST (fr "inner") = supply.irs_next_inst /\
  FST (fr "iz") = SUC supply.irs_next_inst /\
  FST (fr "inner") <> FST (fr "iz") /\
  SND (fr "inner") <> SND (fr "iz") /\
  ~MEM (FST (fr "inner")) supply.irs_used_inst_ids /\
  ~MEM (FST (fr "iz")) supply.irs_used_inst_ids /\
  ~MEM (SND (fr "inner")) supply.irs_used_vars /\
  ~MEM (SND (fr "iz")) supply.irs_used_vars /\
  supply1.irs_used_inst_ids =
    FST (fr "iz") :: FST (fr "inner") :: supply.irs_used_inst_ids /\
  supply1.irs_used_vars =
    SND (fr "iz") :: SND (fr "inner") :: supply.irs_used_vars /\
  supply1.irs_next_inst = SUC (SUC supply.irs_next_inst) /\
  supply.irs_next_var < supply1.irs_next_var /\
  supply1.irs_next_label = supply.irs_next_label /\
  supply1.irs_used_labels = supply.irs_used_labels /\
  ir_supply_inst_ok supply1
Proof
  rpt gen_tac >> strip_tac >>
  drule ao_alloc_fresh_props >> strip_tac >>
  gvs[ir_supply_inst_ok_def, EVERY_MEM, arithmeticTheory.ADD_CLAUSES] >>
  rpt conj_tac
  >- (strip_tac >> first_x_assum drule >> decide_tac)
  >- (strip_tac >> first_x_assum drule >> decide_tac)
  >- (rpt strip_tac >> gvs[] >> first_x_assum drule >> decide_tac)
QED

(* Set-facing form for arbitrary covered collections, including list tails. *)
Theorem ao_alloc_fresh_covered_sets:
  !supply fr supply1 ids vars.
  ir_supply_inst_ok supply /\ ao_alloc_fresh supply = (fr,supply1) /\
  ids SUBSET set supply.irs_used_inst_ids /\
  vars SUBSET set supply.irs_used_vars ==>
  DISJOINT {FST (fr "inner"); FST (fr "iz")} ids /\
  DISJOINT {SND (fr "inner"); SND (fr "iz")} vars /\
  set supply.irs_used_inst_ids SUBSET set supply1.irs_used_inst_ids /\
  set supply.irs_used_vars SUBSET set supply1.irs_used_vars /\
  {FST (fr "inner"); FST (fr "iz")} SUBSET
    set supply1.irs_used_inst_ids /\
  {SND (fr "inner"); SND (fr "iz")} SUBSET
    set supply1.irs_used_vars
Proof
  rpt gen_tac >> strip_tac >>
  drule_all ao_alloc_fresh_contract >> strip_tac >>
  gvs[SUBSET_DEF, DISJOINT_DEF, EXTENSION] >> metis_tac[]
QED

Theorem ao_alloc_fresh_tags:
  ao_alloc_fresh s = (fr,s1) ==>
  !tag. fr tag = if tag = "iz" then fr "iz" else fr "inner"
Proof
  Cases_on `fresh_inst_id s` >>
  rename1 `fresh_inst_id s = (i,s2)` >>
  Cases_on `fresh_ir_var s2` >>
  rename1 `fresh_ir_var s2 = (v,s3)` >>
  Cases_on `fresh_inst_id s3` >>
  rename1 `fresh_inst_id s3 = (j,s4)` >>
  Cases_on `fresh_ir_var s4` >>
  gvs[ao_alloc_fresh_def] >> strip_tac >> gvs[]
QED

Theorem ao_transform_insts_supply_used_vars:
  !insts s idx outs s'.
    ao_transform_insts_supply dfg ra lbl targets s idx insts = (outs,s') ==>
    set s.irs_used_vars SUBSET set s'.irs_used_vars /\
    s.irs_next_inst <= s'.irs_next_inst
Proof
  Induct >> simp[Once ao_transform_insts_supply_def] >>
  rpt gen_tac >>
  Cases_on `ao_alloc_fresh s` >>
  rename1 `ao_alloc_fresh s = (fr,s1)` >>
  Cases_on `ao_transform_insts_supply dfg ra lbl targets s1 (SUC idx) insts` >>
  simp[] >> strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  drule ao_alloc_fresh_bounds >> strip_tac >>
  metis_tac[SUBSET_TRANS, arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem ao_transform_block_supply_used_vars:
  ao_transform_block_supply dfg ra targets s bb = (bb',s') ==>
  set s.irs_used_vars SUBSET set s'.irs_used_vars /\
  s.irs_next_inst <= s'.irs_next_inst
Proof
  Cases_on `ao_transform_insts_supply dfg ra bb.bb_label targets s 0
    bb.bb_instructions` >>
  simp[ao_transform_block_supply_def] >> strip_tac >> gvs[] >>
  drule ao_transform_insts_supply_used_vars >> simp[]
QED

Theorem ao_transform_blocks_supply_used_vars:
  !bbs s bbs' s'.
    ao_transform_blocks_supply dfg ra targets s bbs = (bbs',s') ==>
    set s.irs_used_vars SUBSET set s'.irs_used_vars /\
    s.irs_next_inst <= s'.irs_next_inst
Proof
  Induct >> simp[Once ao_transform_blocks_supply_def] >>
  rpt gen_tac >>
  Cases_on `ao_transform_block_supply dfg ra targets s h` >>
  rename1 `ao_transform_block_supply dfg ra targets s h = (bb,s1)` >>
  Cases_on `ao_transform_blocks_supply dfg ra targets s1 bbs` >>
  simp[] >> strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  drule ao_transform_block_supply_used_vars >> strip_tac >>
  metis_tac[SUBSET_TRANS, arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem ao_transform_insts_supply_mono:
  !insts s idx outs s'.
    ir_supply_inst_ok s /\
    ao_transform_insts_supply dfg ra lbl targets s idx insts = (outs,s') ==>
    ir_supply_inst_ok s' /\
    set s.irs_used_inst_ids SUBSET set s'.irs_used_inst_ids /\
    set s.irs_used_vars SUBSET set s'.irs_used_vars /\
    s'.irs_used_labels = s.irs_used_labels
Proof
  Induct >> simp[Once ao_transform_insts_supply_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `ao_alloc_fresh s` >> rename1 `ao_alloc_fresh s = (fr,s1)` >>
  Cases_on `ao_transform_insts_supply dfg ra lbl targets s1 (SUC idx) insts` >>
  rename1 `ao_transform_insts_supply dfg ra lbl targets s1 (SUC idx) insts = (tail,s2)` >>
  gvs[Once ao_transform_insts_supply_def] >>
  `ir_supply_inst_ok s1 /\
   set s.irs_used_inst_ids SUBSET set s1.irs_used_inst_ids /\
   set s.irs_used_vars SUBSET set s1.irs_used_vars /\
   s1.irs_used_labels = s.irs_used_labels` by
    (drule_all ao_alloc_fresh_contract >> strip_tac >> gvs[SUBSET_DEF]) >>
  first_x_assum drule_all >> strip_tac >>
  metis_tac[SUBSET_TRANS]
QED

Theorem ao_transform_block_supply_mono:
  ir_supply_inst_ok s /\
  ao_transform_block_supply dfg ra targets s bb = (bb',s') ==>
  ir_supply_inst_ok s' /\
  set s.irs_used_inst_ids SUBSET set s'.irs_used_inst_ids /\
  set s.irs_used_vars SUBSET set s'.irs_used_vars /\
  s'.irs_used_labels = s.irs_used_labels
Proof
  Cases_on `ao_transform_insts_supply dfg ra bb.bb_label targets s 0
    bb.bb_instructions` >>
  gvs[ao_transform_block_supply_def] >>
  metis_tac[ao_transform_insts_supply_mono]
QED

Theorem ao_transform_blocks_supply_mono:
  !bbs s bbs' s'.
    ir_supply_inst_ok s /\
    ao_transform_blocks_supply dfg ra targets s bbs = (bbs',s') ==>
    ir_supply_inst_ok s' /\
    set s.irs_used_inst_ids SUBSET set s'.irs_used_inst_ids /\
    set s.irs_used_vars SUBSET set s'.irs_used_vars /\
    s'.irs_used_labels = s.irs_used_labels
Proof
  Induct >> simp[Once ao_transform_blocks_supply_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `ao_transform_block_supply dfg ra targets s h` >>
  rename1 `ao_transform_block_supply dfg ra targets s h = (bb,s1)` >>
  Cases_on `ao_transform_blocks_supply dfg ra targets s1 bbs` >>
  rename1 `ao_transform_blocks_supply dfg ra targets s1 bbs = (tail,s2)` >>
  gvs[Once ao_transform_blocks_supply_def] >>
  drule_all ao_transform_block_supply_mono >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> metis_tac[SUBSET_TRANS]
QED

Theorem ao_fn_inst_ids_distinct_alt:
  fn_inst_ids_distinct fn <=> ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn))
Proof
  `!bbs. MAP (\i. i.inst_id) (fn_insts_blocks bbs) =
    FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) bbs)` by
    (Induct >> simp[fn_insts_blocks_def]) >>
  simp[fn_inst_ids_distinct_def, fn_insts_def]
QED

Theorem ao_fn_inst_id_injective:
  fn_inst_ids_distinct fn /\ MEM x (fn_insts fn) /\ MEM y (fn_insts fn) /\
  x.inst_id = y.inst_id ==> x = y
Proof
  simp[ao_fn_inst_ids_distinct_alt, fn_insts_def] >> strip_tac >>
  gvs[MEM_EL] >>
  `n < LENGTH (MAP (\i. i.inst_id) (fn_insts_blocks fn.fn_blocks)) /\
   n' < LENGTH (MAP (\i. i.inst_id) (fn_insts_blocks fn.fn_blocks))` by simp[] >>
  `EL n (MAP (\i. i.inst_id) (fn_insts_blocks fn.fn_blocks)) =
   EL n' (MAP (\i. i.inst_id) (fn_insts_blocks fn.fn_blocks))` by simp[EL_MAP] >>
  `n = n'` by metis_tac[ALL_DISTINCT_EL_IMP] >> gvs[]
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
  simp[wf_function_def, ao_fn_inst_ids_distinct_alt]
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

Theorem ao_name_inserts_supply_numeric:
  ao_name_inserts_supply s requests = (named,s') ==>
  s'.irs_next_inst = s.irs_next_inst + LENGTH requests /\
  ALL_DISTINCT (MAP (\(a,out,id,v). id) named) /\
  EVERY (\(a,out,id,v). s.irs_next_inst <= id /\ id < s'.irs_next_inst) named /\
  MAP FST named = MAP FST requests
Proof
  map_every qid_spec_tac [`s'`, `named`, `s`] >>
  Induct_on `requests`
  >- simp[ao_name_inserts_supply_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[ao_name_inserts_supply_def, fresh_inst_id_def,
       fresh_ir_var_def, pairTheory.pair_case_eq] >>
  rpt strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  gvs[EVERY_MEM, MEM_MAP, pairTheory.FORALL_PROD] >>
  rpt strip_tac >> res_tac >> gvs[]
QED

Theorem ao_named_insert_id_injective:
  ALL_DISTINCT (MAP (\(a,out,id,v). id) named) /\
  MEM (a,out,id,v) named /\ MEM (b,out',id,v') named ==> a = b
Proof
  Induct_on `named` >> simp[] >> gen_tac >> PairCases_on `h` >>
  simp[MEM_MAP, pairTheory.EXISTS_PROD] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem ao_name_inserts_supply_lookup_unique:
  ao_name_inserts_supply s requests = (named,s') /\
  ALOOKUP named a = SOME (out,id,v) /\
  ALOOKUP named b = SOME (out',id,v') ==> a = b
Proof
  strip_tac >> drule ao_name_inserts_supply_numeric >> strip_tac >>
  imp_res_tac ALOOKUP_MEM >>
  metis_tac[ao_named_insert_id_injective]
QED

Theorem ao_name_inserts_supply_lookup_bound:
  ao_name_inserts_supply s requests = (named,s') /\
  ALOOKUP named a = SOME (out,id,v) ==>
  s.irs_next_inst <= id /\ id < s'.irs_next_inst
Proof
  strip_tac >> drule ao_name_inserts_supply_numeric >> strip_tac >>
  imp_res_tac ALOOKUP_MEM >>
  gvs[EVERY_MEM, pairTheory.FORALL_PROD] >> metis_tac[]
QED

Theorem ao_name_inserts_supply_lookup_key:
  ao_name_inserts_supply s requests = (named,s') /\
  ALOOKUP named a = SOME (out,id,v) ==> MEM a (MAP FST requests)
Proof
  strip_tac >> drule ao_name_inserts_supply_numeric >> strip_tac >>
  imp_res_tac ALOOKUP_MEM >>
  metis_tac[MEM_MAP, pairTheory.FST]
QED
