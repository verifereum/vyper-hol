(* Fixed-endpoint resource transport across the RawCreate snapshot. *)
Theory bodyCreateRawSnapshotFrameMods
Ancestors
  bodyLocalSnapshotResourcesMods placeStoreDynPrepare bodyFullHashKeccakFixed
  bodyFullPathHistory bodyMemoryDefs exprSimHash exprSimWordArgs
  fragGasOriginPtrLoop vyperStorageFootprint stateRelProj freshWrites
  loweringPosts exprLoweringProps venomInst typedMemoryCopy loweringStateRelDefs
  venomMemDefs ptrDiscipline venomState bodyPtrDefs

(* Keep the ALLOCA taint extension separate from the residual copy's
   exterior frame: the latter starts at j, not at the child landing t. *)
Theorem raw_create_snapshot_frame_mods:
  storage_trace_domain cx st0 ee.storage_trace /\
  fn_inst_ids_distinct func /\ alloca_history func t /\
  local_ptrs_reserved cenv a /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at a x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at a x) /\
  return_buf_frame d cenv a t /\ lo <= t.vs_alloca_next /\
  ci_mono a m /\ ci_mono m b /\
  MEM site (fn_insts func) /\ site.inst_opcode = ALLOCA /\
  site.inst_id = a.cs_next_id /\ site.inst_outputs = [owner] /\
  not_local_ptr cenv ee.scopes owner /\ not_fresh_at m owner /\
  t.vs_alloca_next <= pbase /\ pbase+cap < dimword (:256) /\
  pbase+cap <= j.vs_alloca_next /\ allocas_from lo j /\
  FLOOKUP j.vs_allocas site.inst_id = SOME (pbase,cap) /\
  (!aid e. FLOOKUP t.vs_allocas aid = SOME e ==> FLOOKUP j.vs_allocas aid = SOME e) /\
  j.vs_memory = t.vs_memory /\
  (!x. not_fresh_at a x ==> lookup_var x j = lookup_var x t /\
    FLOOKUP Gj x = FLOOKUP G1 x /\ op_taint tj (Var x) = op_taint tn1 (Var x)) /\
  (!i. i IN tj.t_mem <=> i IN tn1.t_mem \/ (t.vs_alloca_next <= i /\ i < pbase+cap)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee t /\ storage_well_formed_on cx ee (FST H) /\
    stmt_state_rel H ctx func cenv cx ee j /\ immutable_frame_mods func cenv cx ee j /\
    ghost_inv_at_mods (DF H) lo d cenv cx ee Gj tj j /\
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G1,tn1) [] (OK j,Gj,tj)) /\
  typed_copy_state_frame m pbase cap j u /\
  (!x. not_fresh_at m x ==> FLOOKUP Gu x = FLOOKUP Gj x /\
    op_taint tu (Var x) = op_taint tj (Var x)) /\
  (!i. ~(pbase <= i /\ i < pbase+cap) ==> (i IN tu.t_mem <=> i IN tj.t_mem)) /\
  tu.t_stor = tj.t_stor /\ tu.t_trans = tj.t_trans /\ tu.t_imm = tj.t_imm /\
  lookup_var owner u = SOME (n2w pbase) /\ ptr_covers Gu tu owner u cap /\
  mload pbase u = n2w (LENGTH bs) /\ read_memory (pbase+32) (LENGTH bs) u = bs /\
  (!i. pbase <= i /\ i < pbase+32+LENGTH bs ==> i NOTIN tu.t_mem) /\
  ~u.vs_halted /\ u.vs_current_bb = b.cs_current_bb /\ u.vs_inst_idx = LENGTH b.cs_current_insts /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (j,Gj,tj) [] (OK u,Gu,tu)) ==>
  MEM site (fn_insts func) /\ site.inst_opcode = ALLOCA /\
  site.inst_id = a.cs_next_id /\ site.inst_outputs = [owner] /\
  not_local_ptr cenv ee.scopes owner /\ not_fresh_at b owner /\
  FLOOKUP u.vs_allocas site.inst_id = SOME (pbase,cap) /\
  eval_operand (Var owner) u = SOME (n2w pbase) /\ ptr_covers Gu tu owner u cap /\
  pbase+cap < dimword (:256) /\ pbase+cap <= u.vs_alloca_next /\
  mload pbase u = n2w (LENGTH bs) /\ read_memory (pbase+32) (LENGTH bs) u = bs /\
  (!i. pbase <= i /\ i < pbase+32+LENGTH bs ==> i NOTIN tu.t_mem) /\
  wb_frame cenv ee ee a t u /\ ghost_kept_at lo cenv ee a G1 tn1 t Gu tu /\
  alloca_history func u /\ t.vs_alloca_next <= u.vs_alloca_next /\ allocas_from lo u /\
  return_buf_frame d cenv b u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  ~u.vs_halted /\ u.vs_current_bb = b.cs_current_bb /\ u.vs_inst_idx = LENGTH b.cs_current_insts /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee u /\ immutable_frame_mods func cenv cx ee u /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx ee Gu tu u /\
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G1,tn1) [] (OK u,Gu,tu))
Proof
  strip_tac >>
  qabbrev_tac `H0 = storage_trace_horizon ee.storage_trace` >>
  `valid_horizon cx st0 H0 ee.storage_trace` by fs[storage_trace_domain_def,Abbr `H0`] >>
  qpat_assum `!H. _ ==> stmt_state_rel H ctx func cenv cx ee t /\ _`
    (drule_then strip_assume_tac) >>
  drule stateRelProjTheory.stmt_state_rel_local_ptrs_alloca >> strip_tac >>
  `alloca_inv t /\ alloca_inv j` by metis_tac[stateRelProjTheory.stmt_state_rel_local_ptrs_alloca] >>
  qpat_assum `typed_copy_state_frame m pbase cap j u`
    (strip_assume_tac o REWRITE_RULE [typed_copy_state_frame_def]) >>
  `u.vs_allocas = j.vs_allocas /\ u.vs_alloca_next = j.vs_alloca_next /\
   u.vs_data_section = j.vs_data_section /\ u.vs_call_ctx = j.vs_call_ctx /\
   u.vs_accounts = j.vs_accounts /\ u.vs_transient = j.vs_transient /\
   u.vs_immutables = j.vs_immutables` by
    (qpat_assum `u with <|vs_vars := _;vs_memory := _;vs_prev_bb := _;
      vs_current_bb := _;vs_inst_idx := _|> = j` (SUBST1_TAC o SYM) >> simp[]) >>
  `!x. not_fresh_at a x ==> not_fresh_at m x` by
    metis_tac[ci_mono_def,not_fresh_at_mono] >>
  `local_ptrs_reserved cenv m` by metis_tac[ci_mono_def,local_ptrs_reserved_next_var] >>
  `!x. not_fresh_at a x ==> lookup_var x u = lookup_var x t /\
     FLOOKUP Gu x = FLOOKUP G1 x /\ op_taint tu (Var x) = op_taint tn1 (Var x)` by
    metis_tac[] >>
  `!name off len. local_region cenv ee.scopes j name off len <=>
    local_region cenv ee.scopes t name off len` by
    (rpt gen_tac >> irule local_region_lookup_cong >> metis_tac[local_ptrs_reserved_def]) >>
  `!name off len. local_region cenv ee.scopes u name off len <=>
    local_region cenv ee.scopes j name off len` by
    (rpt gen_tac >> irule local_region_lookup_cong >> metis_tac[local_ptrs_reserved_def]) >>
  suspend "separation"
QED

Resume raw_create_snapshot_frame_mods[separation]:
  `!name off len. local_region cenv ee.scopes t name off len ==> off+len <= t.vs_alloca_next` by
    (rpt strip_tac >> drule_all body_local_region_frontier >> simp[]) >>
  `!aid off len. FLOOKUP t.vs_allocas aid = SOME (off,len) ==> off+len <= t.vs_alloca_next` by
    (fs[alloca_inv_def,alloca_next_valid_def] >> metis_tac[]) >>
  `!name off len. local_region cenv ee.scopes j name off len ==>
      loweringStateRelDefs$regions_disjoint pbase cap off len` by
    (rpt gen_tac >> strip_tac >>
     `local_region cenv ee.scopes t name off len` by metis_tac[] >>
     qpat_assum `!name off len. local_region cenv ee.scopes t name off len ==> _`
       (drule_then mp_tac) >> simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `!aid off len. aid < a.cs_next_id /\ FLOOKUP j.vs_allocas aid = SOME (off,len) ==>
      loweringStateRelDefs$regions_disjoint pbase cap off len` by
    (rpt gen_tac >> strip_tac >>
     `aid <> site.inst_id` by decide_tac >>
     fs[alloca_inv_def,allocas_non_overlapping_def] >>
     qpat_assum `!a1 a2 b1 sz1 b2 sz2. _ /\ FLOOKUP j.vs_allocas a1 = SOME (b1,sz1) /\ _ ==> _`
       (qspecl_then [`site.inst_id`,`aid`,`pbase`,`cap`,`off`,`len`] mp_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G1,tn1) [] (OK u,Gu,tu)` by
    (gen_tac >> disch_tac >> irule gas_origin_ptr_path_trans >> qexistsl [`Gj`,`j`,`tj`] >> simp[]) >>
  `alloca_history func u` by
    (irule body_full_path_alloca_history >>
     qpat_assum `!H. _ ==> gas_origin_ptr_path _ (t,G1,tn1) [] (OK u,Gu,tu)`
       (drule_then (irule_at Any)) >> simp[]) >>
  `t.vs_alloca_next <= u.vs_alloca_next /\ lo <= pbase /\ lo <= u.vs_alloca_next` by
    (qpat_assum `u.vs_alloca_next = _` SUBST1_TAC >> decide_tac) >>
  `allocas_from lo u` by
    (pure_rewrite_tac[allocas_from_def] >>
     qpat_assum `u.vs_allocas = _` SUBST1_TAC >>
     qpat_assum `allocas_from lo j` (ACCEPT_TAC o REWRITE_RULE [allocas_from_def])) >>
  `return_buf_frame d cenv b u` by
    (irule return_buf_frame_frame >> qexistsl [`cenv`,`t`,`a`] >>
     simp[] >> fs[ci_mono_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  suspend "posts"
QED

Resume raw_create_snapshot_frame_mods[posts]:
  `wb_frame cenv ee ee a t u` by suspend "wb" >>
  `ghost_kept_at lo cenv ee a G1 tn1 t Gu tu` by suspend "kept" >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H ctx func cenv cx ee u /\
     immutable_frame_mods func cenv cx ee u /\ ghost_inv_at_mods (DF H) lo d cenv cx ee Gu tu u` by
    suspend "resources" >>
  `stmt_state_rel H0 ctx func cenv cx ee u` by metis_tac[] >>
  drule_then assume_tac bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >>
  `not_fresh_at b owner` by metis_tac[ci_mono_def,not_fresh_at_mono] >>
  simp[eval_operand_def] >> metis_tac[]
QED

Resume raw_create_snapshot_frame_mods[wb]:
  irule wb_frame_allocating_tail >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`t`,`ee.scopes`,`a`] >>
  simp[wb_frame_refl] >>
  `!off len. off+len <= t.vs_alloca_next ==>
      mem_bytes_at off len u.vs_memory = mem_bytes_at off len t.vs_memory` by
    (rpt gen_tac >> disch_tac >> qpat_assum `j.vs_memory = _` (SUBST1_TAC o SYM) >>
     qpat_assum `typed_copy_frame _ _ _ _`
       (irule o cj 1 o REWRITE_RULE [typed_copy_frame_def]) >> decide_tac) >>
  rpt conj_tac
  >- (rpt strip_tac >> first_x_assum irule >>
      qpat_assum `!name off len. local_region cenv ee.scopes t name off len ==> _`
        (drule_then ACCEPT_TAC)) >>
  rpt strip_tac >> first_x_assum irule >>
  qpat_assum `!aid off len. FLOOKUP t.vs_allocas aid = SOME (off,len) ==> _`
    (drule_then ACCEPT_TAC)
QED

Resume raw_create_snapshot_frame_mods[kept]:
  `!i. i < t.vs_alloca_next ==> (i IN tu.t_mem <=> i IN tn1.t_mem)` by
    (gen_tac >> disch_tac >>
     `~(pbase <= i /\ i < pbase+cap)` by decide_tac >>
     qpat_assum `!i. _ ==> (i IN tu.t_mem <=> _)` (drule_then SUBST1_TAC) >>
     qpat_assum `!i. i IN tj.t_mem <=> _` (qspec_then `i` SUBST1_TAC) >>
     simp[arithmeticTheory.NOT_LESS_EQUAL]) >>
  simp[ghost_kept_at_def] >> rpt conj_tac >> rpt strip_tac
  >- (qpat_assum `!aid off len. FLOOKUP t.vs_allocas aid = SOME (off,len) ==> _`
        (drule_then assume_tac) >>
      `i < t.vs_alloca_next` by decide_tac >> metis_tac[]) >>
  qpat_assum `!name off len. local_region cenv ee.scopes t name off len ==> _`
    (drule_then assume_tac) >>
  `i < t.vs_alloca_next` by decide_tac >> metis_tac[]
QED

Resume raw_create_snapshot_frame_mods[resources]:
  gen_tac >> disch_tac >>
  qpat_assum `!H. _ ==> stmt_state_rel H ctx func cenv cx ee t /\ _`
    (drule_then strip_assume_tac) >>
  conj_tac
  >- (irule place_typed_copy_alloca_state_frame >>
      qpat_assum `typed_copy_state_frame m pbase cap j u` (irule_at Any) >>
      qpat_assum `MEM site (fn_insts func)` (irule_at Any) >> qexists `cap` >>
      simp[] >> rpt strip_tac >>
      qpat_assum `!name off len. local_region cenv ee.scopes j name off len ==> _` irule >>
      metis_tac[]) >>
  `!x. not_fresh_at a x ==> lookup_var x u = lookup_var x j /\
    FLOOKUP Gu x = FLOOKUP Gj x /\ op_taint tu (Var x) = op_taint tj (Var x)` by metis_tac[] >>
  `!aid off len. FLOOKUP u.vs_allocas aid = SOME (off,len) ==>
    FLOOKUP j.vs_allocas aid = SOME (off,len) \/ j.vs_alloca_next <= off` by simp[] >>
  `j.vs_alloca_next <= u.vs_alloca_next /\ FLOOKUP u.vs_allocas site.inst_id = SOME (pbase,cap)` by
    (conj_tac >- simp[] >> qpat_assum `u.vs_allocas = _` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  drule_all local_snapshot_resources_mods >> simp[]
QED

Finalise raw_create_snapshot_frame_mods
