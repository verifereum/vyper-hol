(* Preserve a completed recursive tuple prefix at the chosen child endpoint. *)
Theory entryAggregatePrefixMem
Ancestors
  calldataSourceMemberFold calldataMemberResourceFrame calldataChildFrame valueEncodingDefs
  valueEncodingProofs valueEncoding compileEnv venomState finite_map arithmetic list

Theorem entry_member_success_prefix_memory:
  calldata_member_success ctx fn site limit_st first last (d+vo) len tv v s t scratch /\
  (oid < first.cs_next_id \/ last.cs_next_id <= oid) /\
  FLOOKUP s.vs_allocas oid = SOME (base_addr,cap) /\
  base_addr <= d /\ d+vo <= base_addr+cap ==>
  mem_bytes_at d vo t.vs_memory = mem_bytes_at d vo s.vs_memory
Proof
  strip_tac >>
  qhdtm_x_assum `calldata_member_success`
    (strip_assume_tac o REWRITE_RULE [calldata_member_success_def]) >>
  qhdtm_x_assum `calldata_member_resource_frame`
    (strip_assume_tac o REWRITE_RULE [calldata_member_resource_frame_def]) >>
  irule (cj 2 calldata_child_preserves_allocated_region) >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  simp[] >> qexistsl_tac [`base_addr`,`cap`,`last.cs_next_id`,
    `first.cs_next_id`,`oid`] >>
  fs[calldata_member_wit_def] >> rpt strip_tac >>
  first_x_assum irule >> simp[]
QED

Theorem entry_member_success_tuple_prefix:
  calldata_member_success ctx fn site limit_st first last (d+vo) len tv v s t scratch /\
  (oid < first.cs_next_id \/ last.cs_next_id <= oid) /\
  FLOOKUP s.vs_allocas oid = SOME (base_addr,cap) /\
  base_addr <= d /\ d+vo <= base_addr+cap /\
  vo = type_memory_size_list tvs /\ LENGTH vs = LENGTH tvs /\
  tuple_val_wf vs tvs /\ tuple_in_memory vs tvs d s.vs_memory ==>
  tuple_in_memory vs tvs d t.vs_memory
Proof
  strip_tac >>
  `mem_bytes_at d vo t.vs_memory = mem_bytes_at d vo s.vs_memory` by
    (irule entry_member_success_prefix_memory >>
     qhdtm_assum `calldata_member_success` (irule_at Any) >>
     qpat_assum `FLOOKUP _ _ = SOME _` (irule_at Any) >> simp[]) >>
  irule (cj 5 val_in_memory_mem_agree_proof) >>
  simp[] >> qexists_tac `s.vs_memory` >> gvs[]
QED

Theorem entry_member_success_tuple_extend:
  calldata_member_success ctx fn site limit_st first last (d+vo) len tv v s t scratch /\
  (oid < first.cs_next_id \/ last.cs_next_id <= oid) /\
  FLOOKUP s.vs_allocas oid = SOME (base_addr,cap) /\
  base_addr <= d /\ d+vo <= base_addr+cap /\
  vo = type_memory_size_list tvs /\ LENGTH vs = LENGTH tvs /\
  tuple_val_wf vs tvs /\ tuple_in_memory vs tvs d s.vs_memory ==>
  tuple_val_wf (vs ++ [v]) (tvs ++ [tv]) /\
  tuple_in_memory (vs ++ [v]) (tvs ++ [tv]) d t.vs_memory
Proof
  strip_tac >>
  `tuple_in_memory vs tvs d t.vs_memory` by
    (irule entry_member_success_tuple_prefix >>
     qhdtm_assum `calldata_member_success` (irule_at Any) >>
     qpat_assum `FLOOKUP _ _ = SOME _` (irule_at Any) >> simp[]) >>
  `val_wf tv v /\ val_in_memory tv v (d+type_memory_size_list tvs) t.vs_memory` by
    fs[calldata_member_success_def] >>
  qpat_assum `tuple_in_memory vs tvs d t.vs_memory` mp_tac >>
  qpat_assum `tuple_val_wf vs tvs` mp_tac >>
  qpat_assum `LENGTH vs = LENGTH tvs` mp_tac >>
  qpat_assum `val_in_memory tv v _ _` mp_tac >>
  qpat_assum `val_wf tv v` mp_tac >>
  rpt (pop_assum kall_tac) >>
  map_every qid_spec_tac [`d`,`tvs`,`vs`] >>
  Induct >> Cases_on `tvs` >>
  simp_tac (srw_ss()) [cj 18 val_in_memory_def, cj 19 val_in_memory_def,
    cj 18 val_wf_def, cj 19 val_wf_def,
    type_memory_size_def, LET_THM, ADD_ASSOC] >>
  rpt strip_tac >> gvs[] >>
  rename1 `tuple_in_memory tailvals tailtvs (d + type_memory_size headtv) _` >>
  first_x_assum (qspecl_then [`tailtvs`,`d + type_memory_size headtv`] mp_tac) >>
  asm_simp_tac bool_ss [GSYM ADD_ASSOC] >> strip_tac >> asm_rewrite_tac[]
QED
