Theory algebraicOptMainLayoutProofs
Ancestors
  algebraicOptSupplyProofs algebraicOptDefs irSupply
Libs
  listTheory pred_setTheory

Theorem ao_transform_insts_supply_append:
  !dfg ra lbl targets xs supply idx ys outs supply'.
  ao_transform_insts_supply dfg ra lbl targets supply idx (xs ++ ys) = (outs,supply') <=>
  ?pre mid post.
    ao_transform_insts_supply dfg ra lbl targets supply idx xs = (pre,mid) /\
    ao_transform_insts_supply dfg ra lbl targets mid (idx + LENGTH xs) ys = (post,supply') /\
    outs = pre ++ post
Proof
  ntac 4 gen_tac >> Induct >> simp[Once ao_transform_insts_supply_def] >>
  rpt gen_tac >>
  Cases_on `ao_alloc_fresh supply` >>
  rename1 `ao_alloc_fresh supply = (fr,next)` >>
  simp[Once ao_transform_insts_supply_def] >>
  simp[AllCaseEqs()] >>
  first_x_assum (qspecl_then [`next`, `SUC idx`, `ys`] mp_tac) >>
  simp[arithmeticTheory.ADD_CLAUSES] >> metis_tac[APPEND_ASSOC]
QED

Theorem ao_transform_insts_supply_occurrence:
  !dfg ra lbl targets supply idx xs inst ys outs supply' V.
  ir_supply_inst_ok supply /\ V SUBSET set supply.irs_used_vars /\
  ao_transform_insts_supply dfg ra lbl targets supply idx (xs ++ inst::ys) = (outs,supply') ==>
  ?pre mid fr next post.
    ao_transform_insts_supply dfg ra lbl targets supply idx xs = (pre,mid) /\
    ao_alloc_fresh mid = (fr,next) /\
    ao_transform_insts_supply dfg ra lbl targets next (SUC (idx + LENGTH xs)) ys = (post,supply') /\
    outs = pre ++ ao_transform_inst dfg ra lbl (idx + LENGTH xs) targets fr inst ++ post /\
    ir_supply_inst_ok mid /\ V SUBSET set mid.irs_used_vars /\
    set supply.irs_used_vars SUBSET set mid.irs_used_vars /\
    set next.irs_used_vars SUBSET set supply'.irs_used_vars
Proof
  rpt gen_tac >> strip_tac >>
  gvs[ao_transform_insts_supply_append] >>
  Cases_on `ao_alloc_fresh mid` >> rename1 `ao_alloc_fresh mid = (fr,next)` >>
  Cases_on `ao_transform_insts_supply dfg ra lbl targets next (SUC (idx + LENGTH xs)) ys` >>
  rename1 `ao_transform_insts_supply dfg ra lbl targets next (SUC (idx + LENGTH xs)) ys = (post',last)` >>
  gvs[Once ao_transform_insts_supply_def] >>
  drule_all ao_transform_insts_supply_mono >> strip_tac >>
  drule_all ao_alloc_fresh_contract >> strip_tac >>
  drule_all ao_transform_insts_supply_mono >> strip_tac >>
  metis_tac[SUBSET_TRANS]
QED

Theorem ao_alloc_fresh_scalar_separation:
  !mid V fr next.
  ir_supply_inst_ok mid /\ V SUBSET set mid.irs_used_vars /\
  ao_alloc_fresh mid = (fr,next) ==>
  SND (fr "not") <> SND (fr "iz") /\
  SND (fr "not") NOTIN V /\ SND (fr "iz") NOTIN V /\
  fr "xor" = fr "not" /\
  SND (fr "not") IN (set next.irs_used_vars DIFF set mid.irs_used_vars) /\
  SND (fr "iz") IN (set next.irs_used_vars DIFF set mid.irs_used_vars)
Proof
  rpt gen_tac >> strip_tac >>
  drule ao_alloc_fresh_tags >>
  disch_then (fn th => map_every mp_tac [Q.SPEC `"not"` th, Q.SPEC `"xor"` th]) >>
  simp[] >> rpt disch_tac >>
  drule_all ao_alloc_fresh_contract >> strip_tac >>
  gvs[SUBSET_DEF] >> metis_tac[]
QED

Theorem ao_alloc_fresh_scalar_support:
  !mid V fr next p.
  ir_supply_inst_ok mid /\ V SUBSET set mid.irs_used_vars /\
  ao_alloc_fresh mid = (fr,next) /\
  (!x. MEM (Var x) p.inst_operands \/ MEM x p.inst_outputs ==> x IN V) ==>
  !y. y = SND (fr "not") \/ y = SND (fr "iz") ==>
    ~MEM (Var y) p.inst_operands /\ ~MEM y p.inst_outputs
Proof
  rpt gen_tac >> strip_tac >>
  drule_all ao_alloc_fresh_scalar_separation >> strip_tac >>
  metis_tac[]
QED
