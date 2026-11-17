(* Spatial exclusions for a recorded scratch allocation, including reused sites. *)
Theory bodyFullRawCallTupleWriteSeparation
Ancestors
  exprSimProps localPtrsProps exprLoweringProps loweringStateRelDefs
  ptrDiscipline venomMemDefs venomState venomInst compileEnv finite_map

Theorem raw_call_tuple_write_separation:
  stmt_state_rel (H:(bool # 256 word # type_value) list # num list)
    ctx func cenv cx es s /\
  fn_inst_ids_distinct func /\ MEM inst (fn_insts func) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [q] /\
  not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,k) /\
  sf.cs_next_id <= inst.inst_id /\ local_ptrs_reserved cenv sf /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  (!x. not_fresh_at sf x ==> lookup_var x s = lookup_var x s0) /\
  (!aid row. FLOOKUP s0.vs_allocas aid = SOME row ==>
             FLOOKUP s.vs_allocas aid = SOME row) /\
  allocas_from lo s ==>
  lo <= b /\
  (!aid a m. FLOOKUP s.vs_allocas aid = SOME (a,m) /\ aid < inst.inst_id ==>
     a+m <= b \/ b+k <= a) /\
  (!name a m i. local_region cenv es.scopes s name a m /\
     a <= i /\ i < a+m ==> ~(b <= i /\ i < b+k)) /\
  (!aid a m i. FLOOKUP s0.vs_allocas aid = SOME (a,m) /\
     aid < sf.cs_next_id /\ a <= i /\ i < a+m ==>
     ~(b <= i /\ i < b+k)) /\
  (!name a m i. local_region cenv es0.scopes s0 name a m /\
     a <= i /\ i < a+m ==> ~(b <= i /\ i < b+k))
Proof
  rpt gen_tac >> strip_tac >>
  `alloca_inv s /\ local_ptrs_rel func cenv es.scopes s` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  `!aid a m. FLOOKUP s.vs_allocas aid = SOME (a,m) /\ aid < inst.inst_id ==>
     a+m <= b \/ b+k <= a` by
    (rpt strip_tac >>
     `aid <> inst.inst_id` by decide_tac >>
     gvs[alloca_inv_def, allocas_non_overlapping_def] >>
     qpat_x_assum `!a1 a2 b1 sz1 b2 sz2. _`
       (qspecl_then [`aid`, `inst.inst_id`] mp_tac) >> simp[]) >>
  conj_tac >- metis_tac[allocas_from_def] >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (rpt strip_tac >>
      drule_all local_ptrs_rel_alloca_disjoint >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  conj_tac
  >- (rpt strip_tac >>
      `FLOOKUP s.vs_allocas aid = SOME (a,m)` by metis_tac[] >>
      `aid < inst.inst_id` by decide_tac >>
      `a+m <= b \/ b+k <= a` by metis_tac[] >> decide_tac) >>
  rpt strip_tac >>
  `local_region cenv es.scopes s name a m` by
    (irule local_region_frame_fwd >> metis_tac[]) >>
  drule_all local_ptrs_rel_alloca_disjoint >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED
