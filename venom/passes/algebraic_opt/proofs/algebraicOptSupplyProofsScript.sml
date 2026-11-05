Theory algebraicOptSupplyProofs
Ancestors
  algebraicOptDefs irSupply
Libs
  listTheory pred_setTheory

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
  Cases_on `fresh_inst_id supply` >> rename1 `fresh_inst_id supply = (i,s1)` >>
  drule_all fresh_inst_id_contract >> strip_tac >>
  Cases_on `fresh_ir_var s1` >> rename1 `fresh_ir_var s1 = (v,s2)` >>
  drule fresh_ir_var_contract >> strip_tac >>
  `ir_supply_inst_ok s2` by gvs[ir_supply_inst_ok_def] >>
  Cases_on `fresh_inst_id s2` >> rename1 `fresh_inst_id s2 = (j,s3)` >>
  drule_all fresh_inst_id_contract >> strip_tac >>
  Cases_on `fresh_ir_var s3` >> rename1 `fresh_ir_var s3 = (w,s4)` >>
  drule fresh_ir_var_contract >> strip_tac >>
  gvs[ao_alloc_fresh_def, ir_supply_inst_ok_def] >>
  decide_tac
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
