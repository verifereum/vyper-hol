(* Destination ownership is the store's frame boundary. *)
Theory extcallReturnDefaultOwnership
Ancestors
  abiMalformedRecursiveInterface abiCallerAllocation localPtrsProps exprSimProps
  exprLoweringProps loweringPosts compileEnv loweringStateRelDefs venomState venomInst
  finite_map list arithmetic

Theorem return_default_destination_separation:
  stmt_state_rel ctx func ce cx ee s /\ fn_inst_ids_distinct func /\
  abi_malformed_destination func ce ee.scopes dstid d n s /\
  wb_frame ce es sa s0 s /\ local_ptrs_reserved ce sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\ sa.cs_next_id <= dstid ==>
  (!name lo sz. local_region ce ee.scopes s name lo sz ==>
     regions_disjoint d n lo sz) /\
  (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
     regions_disjoint d n lo sz) /\
  (!aid lo sz. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (lo,sz) ==>
     regions_disjoint d n lo sz) /\
  (ce.ce_is_ctor ==> !name itv iv off.
     FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of
       NONE => FEMPTY | SOME imms => get_source_immutables ce.ce_module imms)
       name = SOME (itv,iv) ==>
     regions_disjoint d n off (type_memory_size itv))
Proof
  strip_tac >>
  `alloca_inv s /\ local_ptrs_rel func ce ee.scopes s /\
   immutable_alloca_sep func ce cx ee s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `!name lo sz. local_region ce ee.scopes s name lo sz ==>
     regions_disjoint d n lo sz` by
    (rpt strip_tac >> gvs[abi_malformed_destination_def] >>
     drule_all local_ptrs_rel_alloca_disjoint >>
     simp[regions_disjoint_def] >> decide_tac) >>
  conj_tac >- gvs[] >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >> qexists_tac `name` >>
      irule local_region_frame_fwd >> goal_assum (drule_at Any) >>
      qexists_tac `sa` >> fs[wb_frame_def]) >>
  conj_tac
  >- (rpt strip_tac >> gvs[abi_malformed_destination_def] >>
      `aid <> inst.inst_id` by decide_tac >>
      drule_all abi_caller_allocation_separate >>
      simp[regions_disjoint_def] >> decide_tac) >>
  rpt strip_tac >>
  `!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
     FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
     regions_disjoint off (type_memory_size itv) b sz` by
    (fs[immutable_alloca_sep_def] >> first_x_assum drule_all >>
     strip_tac >> metis_tac[]) >>
  gvs[abi_malformed_destination_def] >>
  qpat_x_assum `!inst b sz. _` drule_all >>
  simp[regions_disjoint_def] >> decide_tac
QED
