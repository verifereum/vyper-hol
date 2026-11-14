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
    metis_tac[exprLoweringPropsTheory.ci_mono_compile_alloc_buffer,pairTheory.SND] >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace)
     es.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  Q.UNDISCH_THEN `!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es s0 /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0`
    (fn th => assume_tac th >>
      mp_tac (Q.SPEC `storage_trace_horizon es.storage_trace` th)) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `allocas_from lo s0 /\ lo <= s0.vs_alloca_next` by
    fs[bodyPtrDefsTheory.ghost_inv_at_def] >>
  mp_tac (Q.INST [`G` |-> `G0`,`tn` |-> `tn0`,
      `explicit` |-> `explicit`,`PG` |-> `PG`,
      `n` |-> `cap`,
      `sa` |-> `sa`,`sb` |-> `sm`,`buf` |-> `ba`,`s` |-> `s0`,
      `H` |-> `storage_trace_horizon es.storage_trace`]
    (INST_TYPE [alpha |-> ``:256``,beta |-> ``:256``]
      alloc_buffer_origin_ptr_path)) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choosel_then [`q`,`w`,`s1`,`G1`,`tn1`] strip_assume_tac) >>
  `s1.vs_memory = s0.vs_memory /\
   s1.vs_accounts = s0.vs_accounts /\
   s1.vs_transient = s0.vs_transient /\
   s1.vs_immutables = s0.vs_immutables /\
   s1.vs_call_ctx = s0.vs_call_ctx /\ ~s1.vs_halted` by
    (Q.UNDISCH_TAC `s1 with <|vs_vars := s0.vs_vars;
       vs_allocas := s0.vs_allocas; vs_alloca_next := s0.vs_alloca_next;
       vs_inst_idx := s0.vs_inst_idx|> = s0` >>
     simp[venomStateTheory.venom_state_component_equality]) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
    fs[exprLoweringPropsTheory.ci_mono_def] >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `sa.cs_next_id < sm.cs_next_id` by
    (Q.UNDISCH_THEN `compile_alloc_buffer
       (cap) sa = (ba,sm)`
       (strip_assume_tac o MATCH_MP
         abiBuiltinAllocationTheory.abi_builtin_alloc_buffer_shape) >>
     Q.UNDISCH_THEN `emit_op ALLOCA
       [Lit (n2w (cap))] sa =
       (ba.buf_operand,sm)`
       (strip_assume_tac o MATCH_MP emitHelperPropsTheory.emitted_insts_emit_op) >>
     decide_tac) >>
  `!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
     lookup_var x s1 = SOME v` by metis_tac[] >>
  `locals_kept cenv es es s0 s1` by
    metis_tac[exprSimPropsTheory.locals_kept_mem] >>
  `wb_frame cenv es es sa s0 s1` by
    simp[loweringPostsTheory.wb_frame_def] >>
  `return_buf_frame d cenv sm s1` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[]) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es s1 /\
       storage_well_formed_on cx es (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx es G1 tn1 s1` by
    (qx_gen_tac `hh` >> strip_tac >>
     `stmt_state_rel hh ctx func cenv cx es s0 /\
      storage_well_formed_on cx es (FST hh) /\
      ghost_inv_at (DF hh) lo d cenv cx es G0 tn0 s0` by
       metis_tac[] >>
     simp[] >>
     mp_tac (Q.INST [`D` |->
         `DF (hh : (bool # 256 word # type_value) list # num list)`,
       `lo` |-> `lo`,`d` |-> `d`,
       `cenv` |-> `cenv`,`cx` |-> `cx`,`es` |-> `es`,
       `G` |-> `G0`,`tn` |-> `tn0`,`s` |-> `s0`,
       `G'` |-> `G1`,`tn'` |-> `tn1`,`t` |-> `s1`,`sa` |-> `sa`,
       `H` |-> `(hh : (bool # 256 word # type_value) list # num list)`,
       `ctx` |-> `ctx`,`func` |-> `func`,
       `e` |-> `w2n (w:256 word) + cap`]
       (INST_TYPE [alpha |-> ``:256``,beta |-> ``:256``]
         alloc_buffer_ghost_inv_at)) >>
     (impl_tac >- simp[]) >> simp[]) >>
  `alloca_next_valid s0` by
    (Q.UNDISCH_TAC `stmt_state_rel (storage_trace_horizon es.storage_trace)
       ctx func cenv cx es s0` >> POP_ASSUM_LIST (K all_tac) >>
     simp[exprLoweringPropsTheory.stmt_state_rel_def,
       venomMemDefsTheory.alloca_inv_def]) >>
  `!aid b n. FLOOKUP s0.vs_allocas aid = SOME (b,n) ==>
      b+n <= s0.vs_alloca_next` by
    fs[venomMemDefsTheory.alloca_next_valid_def] >>
  `!name b n. local_region cenv es.scopes s0 name b n ==>
      b+n <= s0.vs_alloca_next` by
    metis_tac[bodyMemoryDefsTheory.body_local_region_frontier] >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1` by
    (mp_tac (Q.INST [`lo` |-> `lo`,`cenv` |-> `cenv`,
       `es0` |-> `es`,`sk` |-> `sa`,`G0` |-> `G0`,`tn0` |-> `tn0`,
       `s0` |-> `s0`,`G` |-> `G0`,`tn` |-> `tn0`,`s` |-> `s0`,
       `G'` |-> `G1`,`tn'` |-> `tn1`,
       `e` |-> `w2n (w:256 word) + cap`]
       (INST_TYPE [alpha |-> ``:num # num``] alloc_buffer_ghost_kept_at)) >>
     (impl_tac >- (simp[bodyPtrDefsTheory.ghost_kept_at_def] >>
       rpt conj_tac >> metis_tac[])) >> simp[]) >>
  qexistsl_tac [`q`,`w`,`s1`,`G1`,`tn1`] >> gvs[] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

