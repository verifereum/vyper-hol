(* Allocation-backed decode frames for caller-owned memory. *)
Theory extcallReturnFrameBridge
Ancestors
  abiValidAllocatedContract abiMalformedRecursiveInterface abiMalformedSiteFrame
  abiCallerLocalScratch abiDecoderReentry localPtrsProps exprSimProps loweringPosts
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
