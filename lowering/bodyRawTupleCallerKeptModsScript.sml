Theory bodyRawTupleCallerKeptMods
Ancestors
  bodyPtrDefs stateRelProj localPtrsProps loweringStateRelDefs
  exprSimProps loweringPosts loweringShapeDefs venomMemDefs venomInst
  finite_map

(* Compare both kinds of protected caller ranges with a row in the same
   post-allocation state. Writeback transports the old row and local region. *)
Theorem raw_tuple_caller_row_excludes[local]:
  stmt_state_rel H ctx func cenv cx es r /\
  wb_frame cenv es0 es sf s0 r /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  local_ptrs_reserved cenv sf /\ fn_inst_ids_distinct func /\
  MEM alloc (fn_insts func) /\ alloc.inst_outputs = [q] /\
  not_local_ptr cenv es.scopes q /\ sf.cs_next_id <= alloc.inst_id /\
  FLOOKUP r.vs_allocas alloc.inst_id = SOME (a,m) ==>
  (!aid b sz. FLOOKUP s0.vs_allocas aid = SOME (b,sz) /\
              aid < sf.cs_next_id ==> b+sz <= a \/ a+m <= b) /\
  (!name b sz. local_region cenv es0.scopes s0 name b sz ==>
               a+m <= b \/ b+sz <= a)
Proof
  strip_tac >>
  drule stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  qpat_assum `wb_frame _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `FLOOKUP r.vs_allocas aid = SOME (b,sz)` by
        (first_x_assum irule >> simp[]) >>
      `aid <> alloc.inst_id` by decide_tac >>
      fs[alloca_inv_def,allocas_non_overlapping_def] >>
      qpat_assum `!a1 a2 b1 sz1 b2 sz2. _`
        (qspecl_then [`aid`,`alloc.inst_id`] mp_tac) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `local_region cenv es.scopes r name b sz` by
    (irule local_region_frame_fwd >>
     qexistsl_tac [`s0`,`sf`,`es0.scopes`] >> simp[]) >>
  drule_all local_ptrs_rel_alloca_disjoint >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def]
QED

Theorem raw_tuple_two_row_caller_kept:
  stmt_state_rel H ctx func cenv cx es r /\
  wb_frame cenv es0 es sf s0 r /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  local_ptrs_reserved cenv sf /\ fn_inst_ids_distinct func /\
  MEM alloc (fn_insts func) /\ alloc.inst_opcode = ALLOCA /\
  alloc.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
  sf.cs_next_id <= alloc.inst_id /\
  FLOOKUP r.vs_allocas alloc.inst_id = SOME (a,L) /\ 32 <= L /\
  MEM alloc' (fn_insts func) /\ alloc'.inst_opcode = ALLOCA /\
  alloc'.inst_outputs = [p] /\ not_local_ptr cenv es.scopes p /\
  sf.cs_next_id <= alloc'.inst_id /\
  FLOOKUP r.vs_allocas alloc'.inst_id = SOME (b,k) /\
  ghost_kept_at lo cenv es0 sf G0 tn0 s0 G tn /\
  (!x. not_fresh_at sf x ==>
       FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
  (!i. ~(a <= i /\ i < a+32) /\ ~(b <= i /\ i < b+k) /\
       i IN tnf.t_mem ==> i IN tn.t_mem) ==>
  ghost_kept_at lo cenv es0 sf G0 tn0 s0 Gf tnf
Proof
  strip_tac >>
  `(!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
      aid < sf.cs_next_id ==> off+sz <= a \/ a+L <= off) /\
   (!name off sz. local_region cenv es0.scopes s0 name off sz ==>
      a+L <= off \/ off+sz <= a)` by
    (qpat_assum `FLOOKUP r.vs_allocas alloc.inst_id = SOME (a,L)`
       (mp_then Any irule raw_tuple_caller_row_excludes) >> simp[] >> metis_tac[]) >>
  `(!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
      aid < sf.cs_next_id ==> off+sz <= b \/ b+k <= off) /\
   (!name off sz. local_region cenv es0.scopes s0 name off sz ==>
      b+k <= off \/ off+sz <= b)` by
    (qpat_assum `FLOOKUP r.vs_allocas alloc'.inst_id = SOME (b,k)`
       (mp_then Any irule raw_tuple_caller_row_excludes) >> simp[] >> metis_tac[]) >>
  qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
  rewrite_tac[ghost_kept_at_def] >> conj_tac
  >- (gen_tac >> strip_tac >>
      qpat_assum `!x. not_fresh_at sf x ==> FLOOKUP Gf x = _ /\ _` drule >>
      strip_tac >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!aid off sz. _ ==> off+sz <= a \/ _` drule_all >>
      qpat_assum `!aid off sz. _ ==> off+sz <= b \/ _` drule_all >>
      rpt (disch_then assume_tac) >>
      `i IN tn.t_mem` by
        (qpat_assum `!i. _ ==> i IN tn.t_mem` irule >> simp[] >> decide_tac) >>
      qpat_assum `!aid off sz i. _ ==> i IN tn0.t_mem`
        (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >>
      disch_then irule >> simp[] >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!name off sz. _ ==> a+L <= off \/ _` drule >>
  qpat_assum `!name off sz. _ ==> b+k <= off \/ _` drule >>
  rpt (disch_then assume_tac) >>
  `i IN tn.t_mem` by
    (qpat_assum `!i. _ ==> i IN tn.t_mem` irule >> simp[] >> decide_tac) >>
  first_x_assum irule >> metis_tac[]
QED
