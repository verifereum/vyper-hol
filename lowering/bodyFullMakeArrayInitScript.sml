(* One MakeArray allocation and its initial full-H element-loop packet. *)
Theory bodyFullMakeArrayInit
Ancestors
  bodyFullAllocaFresh bodyFullPreds bodyMemoryDefs exprSimProps
  abiBuiltinAllocation emitHelperProps exprLoweringProps vyperStorageFootprint
  venomState venomMemDefs

Theorem make_array_init_full:
  expr_body_pre cenv cx env
    (Builtin ann (MakeArray elem_opt bnd) args) es /\
  cap = type_memory_bytes cenv ann /\ cap < dimword (:256) /\
  storage_trace_domain cx st0 es.storage_trace /\
  compile_alloc_buffer cap sa = (ba,sm) /\
  fn_has_code sa sm func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
    not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?q w s1 G1 tn1.
    ba.buf_operand = Var q /\ ci_mono sa sm /\
    sa.cs_next_id < sm.cs_next_id /\ local_ptrs_reserved cenv sm /\
    not_fresh_at sm q /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s0,G0,tn0) [] (OK s1,G1,tn1)) /\
    s1 with <|vs_vars := s0.vs_vars; vs_allocas := s0.vs_allocas;
      vs_alloca_next := s0.vs_alloca_next; vs_inst_idx := s0.vs_inst_idx|> = s0 /\
    s1.vs_memory = s0.vs_memory /\
    alloca_history func s1 /\ allocas_from lo s1 /\
    s0.vs_alloca_next <= s1.vs_alloca_next /\
    lookup_var q s1 = SOME w /\ ptr_covers G1 tn1 q s1 cap /\
    FLOOKUP s1.vs_allocas sa.cs_next_id = SOME (w2n w,cap) /\
    w2n w + cap < dimword (:256) /\ w2n w + cap <= s1.vs_alloca_next /\
    (!aid e. FLOOKUP s0.vs_allocas aid = SOME e ==>
      FLOOKUP s1.vs_allocas aid = SOME e) /\
    (!aid b len. aid < sa.cs_next_id /\
      FLOOKUP s0.vs_allocas aid = SOME (b,len) ==>
      loweringStateRelDefs$regions_disjoint (w2n w) cap b len) /\
    (!name b len. local_region cenv es.scopes s1 name b len ==>
      loweringStateRelDefs$regions_disjoint (w2n w) cap b len) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x s1 = lookup_var x s0 /\
      FLOOKUP G1 x = FLOOKUP G0 x /\
      op_taint tn1 (Var x) = op_taint tn0 (Var x)) /\
    tn1.t_stor = tn0.t_stor /\ tn1.t_trans = tn0.t_trans /\
    tn1.t_imm = tn0.t_imm /\
    (!i. i IN tn1.t_mem <=>
      i IN tn0.t_mem \/ (s0.vs_alloca_next <= i /\ i < w2n w + cap)) /\
    wb_frame cenv es es sa s0 s1 /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
    return_buf_frame d cenv sm s1 /\ ~s1.vs_halted /\
    s1.vs_current_bb = sm.cs_current_bb /\
    s1.vs_inst_idx = LENGTH sm.cs_current_insts /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es s1 /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx es G1 tn1 s1)
Proof
  strip_tac >>
  `ci_mono sa sm` by
    metis_tac[ci_mono_compile_alloc_buffer, pairTheory.SND] >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace)
     es.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `storage_trace_horizon es.storage_trace` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `allocas_from lo s0 /\ lo <= s0.vs_alloca_next` by
    fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  drule_all (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``]
    alloc_buffer_origin_ptr_path) >>
  disch_then (qspecl_then [`tn0`, `explicit`, `PG`, `G0`]
    (qx_choosel_then [`q`,`w`,`s1`,`G1`,`tn1`] strip_assume_tac)) >>
  `s1.vs_memory = s0.vs_memory /\
   s1.vs_accounts = s0.vs_accounts /\
   s1.vs_transient = s0.vs_transient /\
   s1.vs_immutables = s0.vs_immutables /\
   s1.vs_call_ctx = s0.vs_call_ctx /\ ~s1.vs_halted` by
    (qpat_x_assum `s1 with <|vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _|> = s0` mp_tac >>
     simp[venom_state_component_equality]) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    fs[ci_mono_def] >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `sa.cs_next_id < sm.cs_next_id` by
    (drule abi_builtin_alloc_buffer_shape >> strip_tac >>
     drule emitted_insts_emit_op >> strip_tac >> decide_tac) >>
  `!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
     lookup_var x s1 = SOME v` by metis_tac[] >>
  `locals_kept cenv es es s0 s1` by metis_tac[locals_kept_mem] >>
  `wb_frame cenv es es sa s0 s1` by simp[loweringPostsTheory.wb_frame_def] >>
  `return_buf_frame d cenv sm s1` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[]) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es s1 /\
       storage_well_formed_on cx es (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx es G1 tn1 s1` by
    (qx_gen_tac `hh` >> strip_tac >>
     `stmt_state_rel hh ctx func cenv cx es s0 /\
      storage_well_formed_on cx es (FST hh) /\
      ghost_inv_at (DF hh) lo d cenv cx es G0 tn0 s0` by metis_tac[] >>
     simp[] >> irule (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``]
       alloc_buffer_ghost_inv_at) >>
     conj_tac >- simp[] >>
     qpat_assum `ghost_inv_at (DF hh) _ _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `local_ptrs_reserved cenv sa` (irule_at Any) >>
     qexistsl_tac [`func`, `w2n w + cap`, `ctx`, `hh`] >> simp[]) >>
  `alloca_next_valid s0` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ _ s0` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[stmt_state_rel_def, alloca_inv_def]) >>
  `!aid b n. FLOOKUP s0.vs_allocas aid = SOME (b,n) ==>
      b+n <= s0.vs_alloca_next` by fs[alloca_next_valid_def] >>
  `!name b n. local_region cenv es.scopes s0 name b n ==>
      b+n <= s0.vs_alloca_next` by metis_tac[body_local_region_frontier] >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1` by
    (irule alloc_buffer_ghost_kept_at >>
     qexistsl_tac [`G0`, `w2n w + cap`, `s0`, `tn0`] >>
     simp[bodyPtrDefsTheory.ghost_kept_at_def] >> metis_tac[]) >>
  qexistsl_tac [`q`,`w`,`s1`,`G1`,`tn1`] >> gvs[] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
