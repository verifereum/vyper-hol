(* Allocation-backed decode frames for caller-owned memory. *)
Theory extcallReturnFrameBridge
Ancestors
  abiValidAllocatedContract abiMalformedRecursiveInterface abiMalformedSiteFrame
  abiCallerLocalScratch abiDecoderReentry localPtrsProps exprSimProps loweringPosts
  robustCopyTransportPtr decoderGhostFramePtr bodyPtrDefs valueEncodingProps ptrDiscipline
  exprLoweringProps compileEnv loweringStateRelDefs venomState finite_map pred_set list arithmetic

Theorem return_allocated_local_frame:
  alloca_inv s /\ fn_inst_ids_distinct func /\
  local_ptrs_rel func ce scopes s /\
  abi_malformed_destination func ce scopes dstid d n s /\
  (!id off len. id IN sites /\ FLOOKUP s.vs_allocas id = SOME (off,len) ==>
    ?inst q. MEM inst (fn_insts func) /\ inst.inst_id = id /\
      inst.inst_outputs = [q] /\ not_local_ptr ce scopes q) /\
  abi_valid_allocated_frame sites d n s t /\
  local_region ce scopes s name lo sz ==>
  mem_bytes_at lo sz t.vs_memory = mem_bytes_at lo sz s.vs_memory
Proof
  strip_tac >>
  `lo + sz <= s.vs_alloca_next` by metis_tac[abi_caller_local_end] >>
  `regions_disjoint d n lo sz` by
    (gvs[abi_malformed_destination_def] >>
     drule_all local_ptrs_rel_alloca_disjoint >>
     simp[regions_disjoint_def] >> decide_tac) >>
  irule abi_valid_allocated_frame_slice >> goal_assum (drule_at Any) >>
  rpt gen_tac >> disch_tac >> conj_tac
  >- (fs[regions_disjoint_def] >> decide_tac) >> strip_tac >>
  fs[abi_malformed_site_range_def]
  >- (qpat_x_assum `!id off len. _` drule >> disch_then drule >> strip_tac >>
      gvs[] >> drule_all local_ptrs_rel_alloca_disjoint >>
      simp[regions_disjoint_def] >> decide_tac) >>
  decide_tac
QED

Theorem return_allocated_wb_frame:
  wb_frame ce es ee sa s0 s /\ local_ptrs_reserved ce sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  alloca_inv s /\ fn_inst_ids_distinct func /\ local_ptrs_rel func ce ee.scopes s /\
  abi_malformed_destination func ce ee.scopes dstid d n s /\
  sa.cs_next_id <= dstid /\ sa.cs_next_var <= st.cs_next_var /\
  (!id. id IN sites ==> sa.cs_next_id <= id) /\
  (!id off len. id IN sites /\ FLOOKUP s.vs_allocas id = SOME (off,len) ==>
    ?inst q. MEM inst (fn_insts func) /\ inst.inst_id = id /\
      inst.inst_outputs = [q] /\ not_local_ptr ce ee.scopes q) /\
  abi_valid_allocated_frame sites d n s t /\
  abi_malformed_resource_post ctx func ce cx ee st.cs_next_var sites dstid s t ==>
  wb_frame ce es ee sa s0 t
Proof
  strip_tac >>
  `!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
    lookup_var x t = SOME w` by
    (rpt strip_tac >>
     `abi_decoder_operand_live st.cs_next_var (Var x)` by
       (simp[abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
        fs[not_fresh_at_def] >> metis_tac[LESS_EQ_TRANS]) >>
     fs[abi_malformed_resource_post_def] >>
     first_x_assum (qspecl_then [`Var x`, `w`] mp_tac) >>
     simp[eval_operand_def]) >>
  `!name lo sz. local_region ce es.scopes s0 name lo sz ==>
    mem_bytes_at lo sz t.vs_memory = mem_bytes_at lo sz s.vs_memory` by
    (rpt strip_tac >> irule return_allocated_local_frame >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`ce`, `d`, `dstid`, `func`, `n`, `name`, `ee.scopes`, `sites`] >> simp[] >>
     irule local_region_frame_fwd >> goal_assum (drule_at Any) >>
     simp[] >> qexists_tac `sa` >> fs[wb_frame_def]) >>
  simp[wb_frame_def] >> rpt conj_tac
  >- (fs[wb_frame_def] >> metis_tac[])
  >- (fs[wb_frame_def, abi_malformed_resource_post_def] >> metis_tac[])
  >- (rpt strip_tac >>
      `FLOOKUP s.vs_allocas aid = SOME (off,sz)` by
        (fs[wb_frame_def] >> metis_tac[]) >>
      `aid NOTIN sites /\ aid <> dstid` by
        (conj_tac >> strip_tac >> gvs[] >>
         qpat_x_assum `!id. id IN sites ==> _` drule >> decide_tac) >>
      `mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz s.vs_memory` by
        (fs[abi_malformed_resource_post_def] >>
         qpat_x_assum `!aid B cap L. _` irule >>
         qexistsl_tac [`aid`, `sz`] >> simp[]) >>
      fs[wb_frame_def] >> metis_tac[]) >>
  irule locals_kept_regions_tail >> goal_assum (drule_at Any) >>
  fs[wb_frame_def]
QED

Theorem return_allocated_immutable_frame:
  immutable_alloca_sep func ce cx ee s /\ ce.ce_is_ctor /\
  FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
  FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of
    NONE => FEMPTY | SOME imms => get_source_immutables ce.ce_module imms)
    name = SOME (tv,v) /\
  abi_malformed_destination func ce ee.scopes dstid d n s /\
  (!id b sz. id IN sites /\ FLOOKUP s.vs_allocas id = SOME (b,sz) ==>
    ?inst. MEM inst (fn_insts func) /\ inst.inst_id = id /\
      inst.inst_opcode = ALLOCA) /\
  abi_valid_allocated_frame sites d n s t ==>
  mem_bytes_at off (type_memory_size tv) t.vs_memory =
    mem_bytes_at off (type_memory_size tv) s.vs_memory
Proof
  strip_tac >>
  `off + type_memory_size tv <= s.vs_alloca_next /\
   (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
     FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
     regions_disjoint off (type_memory_size tv) b sz)` by
    (fs[immutable_alloca_sep_def] >> first_x_assum drule_all >>
     strip_tac >> metis_tac[]) >>
  `regions_disjoint d n off (type_memory_size tv)` by
    (gvs[abi_malformed_destination_def] >>
     qpat_x_assum `!inst b sz. _` drule_all >>
     simp[regions_disjoint_def] >> decide_tac) >>
  irule abi_valid_allocated_frame_slice >> goal_assum (drule_at Any) >>
  rpt gen_tac >> disch_tac >> conj_tac
  >- (fs[regions_disjoint_def] >> decide_tac) >> strip_tac >>
  fs[abi_malformed_site_range_def]
  >- (qpat_x_assum `!id b sz. _` drule >> disch_then drule >> strip_tac >>
      gvs[] >> qpat_x_assum `!inst b sz. _` drule_all >>
      simp[regions_disjoint_def] >> decide_tac) >>
  decide_tac
QED

Theorem return_allocated_ghost_frame:
  stmt_state_rel H0 ctx func ce cx es s /\
  ghost_inv_at D lo rb ce cx es G tn s /\
  local_ptrs_reserved ce st /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  fn_inst_ids_distinct func /\
  abi_malformed_destination func ce es.scopes dstid dest n s /\
  (!id off len. id IN sites /\ FLOOKUP s.vs_allocas id = SOME (off,len) ==>
    ?inst q. MEM inst (fn_insts func) /\ inst.inst_id = id /\
      inst.inst_outputs = [q] /\ not_local_ptr ce es.scopes q) /\
  abi_valid_allocated_frame sites dest n s t /\
  abi_malformed_resource_post ctx func ce cx es st.cs_next_var sites dstid s t /\
  (!x. abi_decoder_operand_live st.cs_next_var (Var x) ==>
    FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_immutables = s.vs_immutables /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  (!a. ~(dest <= a /\ a < dest+n) /\
    ~abi_malformed_site_range sites s t a 1 ==>
    (a IN tn'.t_mem <=> a IN tn.t_mem)) /\
  allocas_from lo t /\ lo <= t.vs_alloca_next
  ==>
  ghost_inv_at D lo rb ce cx es G' tn' t
Proof
  strip_tac >>
  `alloca_inv s /\ local_ptrs_rel func ce es.scopes s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `!x. not_fresh_at st x ==> abi_decoder_operand_live st.cs_next_var (Var x)` by
    simp[not_fresh_at_def, abi_decoder_operand_live_def, abi_decoder_older_vars_def] >>
  `!x w. not_fresh_at st x /\ lookup_var x s = SOME w ==>
     lookup_var x t = SOME w` by
    (rpt strip_tac >>
     `abi_decoder_operand_live st.cs_next_var (Var x)` by metis_tac[] >>
     qpat_assum `abi_malformed_resource_post _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [abi_malformed_resource_post_def]) >>
     qpat_assum `!op w. abi_decoder_operand_live _ op /\ _ ==> _`
       (qspecl_then [`Var x`, `w`] mp_tac) >>
     (impl_tac >- simp[eval_operand_def]) >>
     pure_rewrite_tac[eval_operand_def] >> disch_then ACCEPT_TAC) >>
  `!x sz. not_fresh_at st x /\ ptr_covers G tn x s sz ==>
     lookup_var x t = lookup_var x s /\ ptr_covers G' tn' x t sz` by
    (rpt strip_tac >> fs[ptr_covers_def] >> metis_tac[]) >>
  `!name b sz a. local_region ce es.scopes s name b sz /\ b <= a /\ a < b+sz ==>
     ~(dest <= a /\ a < dest+n) /\ ~abi_malformed_site_range sites s t a 1` by
    suspend "local_ranges" >>
  `!a. a < lo ==> ~(dest <= a /\ a < dest+n) /\
     ~abi_malformed_site_range sites s t a 1` by suspend "fixed_range" >>
  `!name entry p sz w.
     lookup_scopes name es.scopes = SOME entry /\
     FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) /\ lookup_var p s = SOME w ==>
     !mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
       val_in_memory entry.type entry.value (w2n w) mem` by
    suspend "robust_locals" >>
  `mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory` by
    (irule abi_valid_allocated_frame_slice >> goal_assum (drule_at Any) >>
     rpt gen_tac >> disch_tac >> first_x_assum irule >> decide_tac) >>
  `stor_taint_ok_at D tn' t` by
    fs[ghost_inv_at_def, stor_taint_ok_at_def] >>
  fs[ghost_inv_at_def] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at st p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
      `ptr_covers G tn p s sz` by metis_tac[] >>
      `lookup_var p t = lookup_var p s /\ ptr_covers G' tn' p t sz` by metis_tac[] >>
      conj_tac >- first_assum ACCEPT_TAC >> metis_tac[])
  >- (Cases_on `rb` >- simp[return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME pair) ce G' tn' t` >> PairCases_on `pair` >>
      gvs[return_buf_ptr_def, ptr_covers_def] >> metis_tac[])
  >- (rpt strip_tac >> metis_tac[])
  >> rpt strip_tac >> fs[local_ptrs_reserved_def] >> metis_tac[]
QED
Resume return_allocated_ghost_frame[local_ranges]:
  rpt gen_tac >> strip_tac >>
  `b + sz <= s.vs_alloca_next` by metis_tac[abi_caller_local_end] >>
  `regions_disjoint dest n b sz` by
    (gvs[abi_malformed_destination_def] >>
     drule_all local_ptrs_rel_alloca_disjoint >>
     simp[regions_disjoint_def] >> decide_tac) >>
  conj_tac >- (fs[regions_disjoint_def] >> decide_tac) >>
  strip_tac >> fs[abi_malformed_site_range_def]
  >- (qpat_assum `!id off len. id IN sites /\ _ ==> _`
        drule >> disch_then drule >> strip_tac >> gvs[] >>
      drule_all local_ptrs_rel_alloca_disjoint >>
      simp[regions_disjoint_def] >> decide_tac) >> decide_tac
QED
Resume return_allocated_ghost_frame[fixed_range]:
  gen_tac >> disch_tac >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `lo <= dest` by
    (fs[abi_malformed_destination_def, allocas_from_def] >>
     first_x_assum drule >> decide_tac) >>
  conj_tac >- decide_tac >> strip_tac >>
  fs[abi_malformed_site_range_def, allocas_from_def]
  >- (first_x_assum drule >> decide_tac) >> decide_tac
QED
Resume return_allocated_ghost_frame[robust_locals]:
  rpt gen_tac >> strip_tac >>
  `val_wf entry.type entry.value /\ type_memory_size entry.type <= sz` by
    (fs[local_ptrs_rel_def] >> metis_tac[]) >>
  `val_footprint entry.type entry.value <= sz` by
    metis_tac[val_footprint_le, LESS_EQ_TRANS] >>
  `local_region ce es.scopes s name (w2n w) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
     val_in_memory entry.type entry.value (w2n w) mem` by
    (fs[ghost_inv_at_def] >> metis_tac[]) >>
  mp_tac (Q.SPECL [`tn.t_mem`, `tn'.t_mem`, `s.vs_memory`, `t.vs_memory`,
    `{a | dest <= a /\ a < dest+n \/ abi_malformed_site_range sites s t a 1}`,
    `entry.type`, `entry.value`, `w2n (w:bytes32)`]
    robust_val_in_memory_exterior_frame) >>
  (impl_tac >-
    (simp_tac (srw_ss()) [GSPECIFICATION, DE_MORGAN_THM] >>
     rpt conj_tac
     >- first_assum ACCEPT_TAC
     >- (rpt strip_tac >>
         qpat_assum `!name b sz a. local_region ce es.scopes s name b sz /\ _ ==> _`
           (qspecl_then [`name`, `w2n (w:bytes32)`, `sz`, `i`] mp_tac) >>
         (impl_tac >-
           (rpt conj_tac >> FIRST [first_assum ACCEPT_TAC, decide_tac])) >> simp[])
     >- fs[abi_valid_allocated_frame_def]
     >- (qpat_assum `!a. ~(dest <= a /\ a < dest+n) /\ _ ==> (a IN tn'.t_mem <=> a IN tn.t_mem)`
           (ACCEPT_TAC o PURE_REWRITE_RULE [DE_MORGAN_THM]))
     >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC
QED
Finalise return_allocated_ghost_frame
