Theory exprSimAbiDecodeLocalSeparation
Ancestors
  loweringStateRelDefs
  exprSimAbiDecodeCoverageBoundary exprSimAbiDecodeCoverageMutual
  exprSimAbiGasBridge localPtrsProps exprLoweringProps compileEnv
  venomInst venomState venomMemDefs list finite_map arithmetic

Theorem abi_decode_interval_local_disjoint:
  alloca_inv s /\ fn_inst_ids_distinct fn /\
  local_ptrs_rel fn ce scopes s /\ local_region ce scopes s name lo len /\
  (!id. first <= id /\ id < last ==>
    ?i. MEM i (fn_insts fn) /\ i.inst_id = id /\
        !q. MEM q i.inst_outputs ==> not_local_ptr ce scopes q) ==>
  !id b sz. first <= id /\ id < last /\
    FLOOKUP s.vs_allocas id = SOME (b,sz) ==>
    regions_disjoint b sz lo len
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!id. _` drule_all >> strip_tac >>
  fs[local_region_def] >>
  qpat_x_assum `local_ptrs_rel _ _ _ _` mp_tac >>
  simp[local_ptrs_rel_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> gvs[local_backed_def]
  >- (rename1 `inst.inst_outputs = [p]` >>
      `i <> inst` by
        (strip_tac >> gvs[not_local_ptr_def] >> metis_tac[MEM]) >>
      `i.inst_id <> inst.inst_id` by metis_tac[fn_inst_ids_distinct_inj] >>
      fs[alloca_inv_def, allocas_non_overlapping_def, loweringStateRelDefsTheory.regions_disjoint_def] >>
      metis_tac[ADD_COMM]) >>
  first_x_assum drule >> simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem abi_decode_lower_interval_local_disjoint:
  lower_abi_decode data info mn mx outsz a = (out,z) /\
  local_ptrs_reserved ce a /\
  (!i. MEM i (frag_code a z) ==> MEM i (fn_insts fn)) /\
  alloca_inv s /\ fn_inst_ids_distinct fn /\
  local_ptrs_rel fn ce scopes s /\ local_region ce scopes s name lo len ==>
  !id b sz. a.cs_next_id <= id /\ id < z.cs_next_id /\
    FLOOKUP s.vs_allocas id = SOME (b,sz) ==>
    regions_disjoint b sz lo len
Proof
  strip_tac >>
  `!id. a.cs_next_id <= id /\ id < z.cs_next_id ==>
    ?i. MEM i (fn_insts fn) /\ i.inst_id = id /\
        !q. MEM q i.inst_outputs ==> not_local_ptr ce scopes q` by
    (rpt strip_tac >>
     drule_all abi_decode_lower_fresh_interval_instruction >> strip_tac >>
     qexists_tac `i` >> simp[] >> rpt strip_tac >>
     first_x_assum drule >> strip_tac >> gvs[] >>
     metis_tac[local_ptrs_reserved_fresh]) >>
  rpt strip_tac >> drule_all abi_decode_interval_local_disjoint >> simp[]
QED
