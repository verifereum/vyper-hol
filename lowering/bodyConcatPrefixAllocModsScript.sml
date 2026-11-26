(* The linked Concat prefix through the data-address ADD and second allocation. *)
Theory bodyConcatPrefixAllocMods
Ancestors
  bodyMakeBufferInitMods bodyFullBuiltinConcatAdd bodyForRangeScalarFrameMods
  bodyFullAllocaFresh bodyFullPostsMods bodyFullShadowBodyInv
  bodyInvSplit bodyFullHashKeccakFixed exprSimAlloc exprSimFullBundleProps
  loweringHalt exprLoweringProps exprSimProps loweringPosts loweringStateRelDefs
  stateRelProj vyperStorageTrace vyperStorageFootprint bodyPtrDefs ptrDiscipline
  venomMemDefs venomExecSemantics venomState venomInst fragExec compileEnv
  finite_map context words

Theorem concat_prefix_alloc_mods:
  compile_alloc_buffer bsz sa = (buf,s1) /\
  compile_alloc_buffer bsz sha = (shbuf,sh1) /\ gas_shadow_state sa sha /\
  emit_op ADD [buf.buf_operand; Lit 32w] s1 = (data_operand,s2) /\
  compile_alloc_buffer 64 s2 = (ob,s3) /\
  compile_alloc_buffer 64 sh2 = (shob,sh3) /\ gas_shadow_state s2 sh2 /\
  fn_has_code sa s3 func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ 32 <= bsz /\ bsz < dimword (:256) /\
  stmt_state_rel (H0:(bool # bytes32 # type_value) list # num list)
    ctx func ce cx es s /\
  alloca_history func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  return_buf_frame d ce sa s /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  storage_trace_domain cx st0 es.storage_trace /\
  valid_horizon cx st0 H0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func ce cx es s /\
     immutable_frame_mods func ce cx es s /\
     storage_well_formed_on cx es (FST H) /\
     ghost_inv_at_mods (DF H) lo d ce cx es G0 tn0 s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t G tn bv dv ov B ow.
    buf.buf_operand = Var bv /\ data_operand = Var dv /\ ob.buf_operand = Var ov /\
    gas_shadow_state s3 sh3 /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G0,tn0) [] (OK t,G,tn)) /\
    t.vs_current_bb = s3.cs_current_bb /\
    t.vs_inst_idx = LENGTH s3.cs_current_insts /\ ~t.vs_halted /\
    alloca_history func t /\ allocas_from lo t /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    lookup_var bv t = SOME (n2w B) /\
    lookup_var dv t = SOME (n2w (B+32)) /\ lookup_var ov t = SOME ow /\
    ptr_covers G tn bv t bsz /\ ptr_covers G tn dv t (bsz-32) /\
    ptr_covers G tn ov t 64 /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (B,bsz) /\
    FLOOKUP t.vs_allocas (sa.cs_next_id+2) = SOME (w2n ow,64) /\
    lo <= B /\ lo <= w2n ow /\ B+bsz < dimword (:256) /\
    B+bsz <= t.vs_alloca_next /\ w2n ow+64 < dimword (:256) /\
    w2n ow+64 <= t.vs_alloca_next /\ regions_disjoint B bsz (w2n ow) 64 /\
    not_fresh_at s3 bv /\ not_fresh_at s3 dv /\ not_fresh_at s3 ov /\
    (!aid b n. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,n) ==>
      regions_disjoint B bsz b n /\ regions_disjoint (w2n ow) 64 b n) /\
    (!name b n. local_region ce es.scopes t name b n ==>
      regions_disjoint B bsz b n /\ regions_disjoint (w2n ow) 64 b n) /\
    t.vs_memory = s.vs_memory /\ ghost_kept_at lo ce es sa G0 tn0 s G tn /\
    return_buf_frame d ce s3 t /\
    local_ptrs_reserved ce s3 /\ ci_mono sa s3 /\
    FLOOKUP G bv = SOME (B,bsz) /\ FLOOKUP G ov = SOME (w2n ow,64) /\
    (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==>
      FLOOKUP t.vs_allocas aid = SOME e) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G x = FLOOKUP G0 x /\
      op_taint tn (Var x) = op_taint tn0 (Var x)) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func ce cx es t /\ immutable_frame_mods func ce cx es t /\
      storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx es G tn t)
Proof
  strip_tac >>
  `cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends s2 s3` by
    (rpt conj_tac
     >- metis_tac[compile_alloc_buffer_extends]
     >- metis_tac[exprSimAccountsTheory.emit_op_extends_next_var]
     >- metis_tac[compile_alloc_buffer_extends]) >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
   fn_has_code s2 s3 func` by
    (qpat_assum `fn_has_code sa s3 func` mp_tac >>
     metis_tac[fn_has_code_split, cs_extends_trans]) >>
  `sa.cs_next_var <= s1.cs_next_var` by
    (qpat_assum `compile_alloc_buffer _ sa = _`
       (mp_then Any strip_assume_tac compile_alloc_buffer_parts) >> simp[]) >>
  `s1.cs_next_var <= s2.cs_next_var` by
    (qpat_assum `emit_op ADD _ s1 = _`
       (mp_then Any strip_assume_tac exprSimAccountsTheory.emit_op_extends_next_var) >>
     first_assum ACCEPT_TAC) >>
  `local_ptrs_reserved ce s1` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  `local_ptrs_reserved ce s2` by
    (irule local_ptrs_reserved_next_var >> qexists `s1` >> simp[]) >>
  drule_all make_buffer_init_frame_mods >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`bv`,`B`,`t1`,`G1`,`tn1`]
      (map_every assume_tac o CONJUNCTS))) >>
  `lookup_var bv t1 = SOME (n2w B) /\ ptr_covers G1 tn1 bv t1 bsz` by
    (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `buf.buf_operand = Var bv` by first_assum ACCEPT_TAC >>
  `not_fresh_at s1 bv` by
    (qpat_assum `not_fresh_at s1 _` (fn th => first_assum ACCEPT_TAC)) >>
  `stmt_state_rel H0 ctx func ce cx es t1` by
    (qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _` (drule_then strip_assume_tac) >>
     first_assum ACCEPT_TAC) >>
  `t1.vs_current_bb = s1.cs_current_bb /\
   t1.vs_inst_idx = LENGTH s1.cs_current_insts` by
    (qpat_assum `expr_sim_full_endpoint func s1 s t1`
       (mp_then Any strip_assume_tac expr_sim_full_endpoint_fields) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `alloca_history func t1` by
    (qpat_assum `expr_sim_full_endpoint func s1 s t1`
       (mp_then Any strip_assume_tac expr_sim_full_endpoint_fields) >>
     first_assum ACCEPT_TAC) >>
  suspend "data_add"
QED

Resume concat_prefix_alloc_mods[data_add]:
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s1 x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s1 x)` by
    (conj_tac >> rpt gen_tac >> strip_tac >>
     irule freshWritesTheory.not_fresh_at_mono >> qexists `sa` >> simp[] >> metis_tac[]) >>
  `emit_op ADD [Var bv; Lit 32w] s1 = (data_operand,s2)` by
    (qpat_assum `buf.buf_operand = Var bv` (fn eq =>
       qpat_assum `emit_op ADD [buf.buf_operand; Lit 32w] s1 = _`
         (fn th => ACCEPT_TAC (PURE_REWRITE_RULE [eq] th)))) >>
  mp_tac (Q.INST [`sc` |-> `s1`, `sc'` |-> `s2`, `s` |-> `t1`,
    `cenv` |-> `ce`, `bw` |-> `n2w B`, `G` |-> `G1`, `tn` |-> `tn1`] concat_data_add_fresh_full) >>
  (impl_tac >- (rpt conj_tac >> simp[])) >>
  disch_then (qx_choosel_then [`dv`,`t2`,`G2`,`tn2`]
    (map_every assume_tac o CONJUNCTS)) >>
  `stmt_state_rel H0 ctx func ce cx es t2` by
    (first_assum irule >> first_assum ACCEPT_TAC) >>
  `allocas_from lo t2 /\ lo <= t2.vs_alloca_next` by
    (conj_tac
     >- qpat_assum `allocas_from lo t2` ACCEPT_TAC
     >- (qpat_assum `t2 with <|vs_vars := _; vs_inst_idx := _|> = t1`
           (strip_assume_tac o SIMP_RULE (srw_ss())
             [venomStateTheory.venom_state_component_equality]) >>
         qpat_assum `lo <= B` mp_tac >>
         qpat_assum `B + bsz <= t1.vs_alloca_next` mp_tac >>
         decide_tac)) >>
  `t2.vs_allocas = t1.vs_allocas /\ t2.vs_data_section = t1.vs_data_section /\
   t2.vs_memory = t1.vs_memory /\ t2.vs_alloca_next = t1.vs_alloca_next /\
   t2.vs_call_ctx = t1.vs_call_ctx /\ t2.vs_accounts = t1.vs_accounts /\
   t2.vs_transient = t1.vs_transient /\ t2.vs_immutables = t1.vs_immutables` by
    (qpat_assum `t2 with <|vs_vars := _; vs_inst_idx := _|> = t1`
       (strip_assume_tac o SIMP_RULE (srw_ss())
         [venomStateTheory.venom_state_component_equality]) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s2 x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s2 x)` by
    (conj_tac >> rpt gen_tac >> strip_tac >>
     irule freshWritesTheory.not_fresh_at_mono >> qexists `s1` >> simp[] >>
     metis_tac[]) >>
  `return_buf_frame d ce s2 t2` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`ce`,`t1`,`s1`] >> simp[] >> metis_tac[]) >>
  suspend "counter_allocation"
QED

Resume concat_prefix_alloc_mods[counter_allocation]:
  mp_tac (Q.INST [`cap` |-> `64`, `sa` |-> `s2`, `sha` |-> `sh2`,
    `sm` |-> `s3`, `shm` |-> `sh3`, `buf` |-> `ob`, `shbuf` |-> `shob`,
    `s` |-> `t2`, `G0` |-> `G2`, `tn0` |-> `tn2`] make_buffer_init_frame_mods) >>
  (impl_tac >-
    (rpt conj_tac >> simp[wordsTheory.dimword_def] >>
     (rpt gen_tac >> strip_tac >> conj_tac
         >- (qpat_assum `!H. valid_horizon _ _ _ _ ==> _`
               (drule_then strip_assume_tac) >>
             irule bodyForRangeScalarFrameModsTheory.immutable_frame_mods_exterior_frame >>
             qexistsl_tac [`es`,`t1`,`s1`] >> simp[] >>
             first_assum ACCEPT_TAC)
         >- (qpat_assum `!H. valid_horizon _ _ _ _ ==> _`
               (drule_then strip_assume_tac) >>
             irule bodyForRangeScalarFrameModsTheory.ghost_inv_at_mods_exterior_frame >>
             qexistsl_tac [`G1`,`es`,`t1`,`s1`,`tn1`] >> simp[] >>
             first_assum ACCEPT_TAC)))) >>
  disch_then (qx_choosel_then [`ov`,`ow`,`t`,`G`,`tn`]
    (map_every assume_tac o CONJUNCTS)) >>
  `not_fresh_at s2 bv` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists `s1` >> simp[] >>
     metis_tac[]) >>
  `lookup_var bv t = SOME (n2w B)` by
    (qpat_assum `!x. not_fresh_at s2 x ==> _` (qspec_then `bv` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
     qpat_assum `!x. not_fresh_at s1 x ==> _` (qspec_then `bv` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >> simp[] >>
     first_assum ACCEPT_TAC) >>
  `lookup_var dv t = SOME (n2w (B+32))` by
    (qpat_assum `!x. not_fresh_at s2 x ==> _` (qspec_then `dv` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >> simp[] >>
     first_assum ACCEPT_TAC) >>
  `!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G x = FLOOKUP G0 x /\
      op_taint tn (Var x) = op_taint tn0 (Var x)` by
    (rpt strip_tac >>
     `not_fresh_at s1 x` by
       (irule freshWritesTheory.not_fresh_at_mono >> qexists `sa` >> simp[] >> metis_tac[]) >>
     `not_fresh_at s2 x` by
       (irule freshWritesTheory.not_fresh_at_mono >> qexists `s1` >> simp[] >> metis_tac[]) >>
     qpat_assum `!x. not_fresh_at s2 x ==> _`
       (qspec_then `x` (drule_then strip_assume_tac)) >>
     qpat_assum `!x. not_fresh_at s1 x ==> _`
       (qspec_then `x` (drule_then strip_assume_tac)) >>
     qpat_assum `!x. not_fresh_at sa x ==> _`
       (qspec_then `x` (drule_then strip_assume_tac)) >>
     metis_tac[]) >>
  `!aid e. FLOOKUP s.vs_allocas aid = SOME e ==>
      FLOOKUP t.vs_allocas aid = SOME e` by
    (rpt strip_tac >>
     qpat_assum `!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> _`
       (qspec_then `aid` (qspec_then `e` (drule_then strip_assume_tac))) >>
     `FLOOKUP t2.vs_allocas aid = SOME e` by
       (qpat_assum `t2.vs_allocas = t1.vs_allocas` (fn eq =>
          qpat_assum `FLOOKUP t1.vs_allocas aid = SOME e` (fn h =>
            ACCEPT_TAC (PURE_REWRITE_RULE [GSYM eq] h)))) >>
     qpat_assum `!aid b. FLOOKUP t2.vs_allocas aid = SOME b ==> _`
       (qspec_then `aid` (qspec_then `e` (drule_then strip_assume_tac))) >>
     first_assum ACCEPT_TAC) >>
  suspend "endpoint"
QED

Resume concat_prefix_alloc_mods[endpoint]:
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G0,tn0) [] (OK t,G,tn)` by
    (gen_tac >> irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl [`G1`,`t1`,`tn1`] >>
     conj_tac >-
       (qpat_assum `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G0,tn0) [] _`
          (qspec_then `D` ACCEPT_TAC)) >>
     irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl [`G2`,`t2`,`tn2`] >>
     conj_tac >-
       (qpat_assum `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t1,G1,tn1) [] _`
          (qspec_then `D` ACCEPT_TAC)) >>
     qpat_assum `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t2,G2,tn2) [] _`
       (qspec_then `D` ACCEPT_TAC)) >>
  `t.vs_current_bb = s3.cs_current_bb /\
   t.vs_inst_idx = LENGTH s3.cs_current_insts` by
    (qpat_assum `expr_sim_full_endpoint func s3 t2 t`
       (mp_then Any strip_assume_tac expr_sim_full_endpoint_fields) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `alloca_history func t` by
    (qpat_assum `expr_sim_full_endpoint func s3 t2 t`
       (mp_then Any strip_assume_tac expr_sim_full_endpoint_fields) >>
     first_assum ACCEPT_TAC) >>
  `s.vs_alloca_next <= t1.vs_alloca_next` by
    (qpat_assum `expr_sim_full_endpoint func s1 s t1`
       (mp_then Any strip_assume_tac expr_sim_full_endpoint_fields) >>
     first_assum ACCEPT_TAC) >>
  `t2.vs_alloca_next <= t.vs_alloca_next` by
    (qpat_assum `expr_sim_full_endpoint func s3 t2 t`
       (mp_then Any strip_assume_tac expr_sim_full_endpoint_fields) >>
     first_assum ACCEPT_TAC) >>
  `ptr_covers G tn bv t bsz /\ ptr_covers G tn dv t (bsz-32)` by
    (conj_tac >> irule decoderGhostFramePtrTheory.ptr_covers_frame >>
     qexistsl [`G2`,`t2`,`tn2`] >> simp[]) >>
  `FLOOKUP t2.vs_allocas sa.cs_next_id = SOME (B,bsz)` by simp[] >>
  `FLOOKUP t.vs_allocas sa.cs_next_id = SOME (B,bsz)` by
    (qpat_assum `!aid e. FLOOKUP t2.vs_allocas aid = SOME e ==> _` irule >> simp[]) >>
  `s2.cs_next_id = sa.cs_next_id + 2` by
    (qpat_assum `compile_alloc_buffer bsz sa = _`
       (mp_then Any strip_assume_tac compile_alloc_buffer_parts) >>
     qpat_assum `emit_op ADD [buf.buf_operand; Lit 32w] s1 = _`
       (mp_then Any strip_assume_tac exprLoweringPropsTheory.emitted_insts_emit_op_local) >> simp[]) >>
  `regions_disjoint ow 64 B bsz` by
    (qpat_assum `!aid b n. aid < s2.cs_next_id /\ _ ==> _`
       (qspecl_then [`sa.cs_next_id`,`B`,`bsz`] mp_tac) >> simp[]) >>
  `regions_disjoint B bsz ow 64` by
    (qpat_assum `regions_disjoint ow 64 B bsz` mp_tac >>
     simp[NoAsms,loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
  `FLOOKUP t.vs_allocas (sa.cs_next_id+2) = SOME (ow,64)` by
    (qpat_assum `s2.cs_next_id = sa.cs_next_id + 2` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  `not_fresh_at s3 bv /\ not_fresh_at s3 dv` by
    (fs[ci_mono_def] >> conj_tac >>
     irule freshWritesTheory.not_fresh_at_mono >> qexists `s2` >> simp[]) >>
  suspend "separation"
QED

Resume concat_prefix_alloc_mods[separation]:
  `!aid b n. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,n) ==>
      regions_disjoint B bsz b n /\ regions_disjoint ow 64 b n` by
    (rpt gen_tac >> strip_tac >> conj_tac
     >- (qpat_assum `!aid b n. aid < sa.cs_next_id /\ _ ==> _`
           (qspecl_then [`aid`,`b`,`n`] mp_tac) >> simp[]) >>
     `FLOOKUP t2.vs_allocas aid = SOME (b,n)` by
       (qpat_assum `!aid e. FLOOKUP s.vs_allocas aid = SOME e ==> FLOOKUP t1.vs_allocas aid = SOME e`
          (qspecl_then [`aid`,`(b,n)`] mp_tac) >> simp[]) >>
     qpat_assum `!aid b n. aid < s2.cs_next_id /\ _ ==> _`
       (qspecl_then [`aid`,`b`,`n`] mp_tac) >> simp[]) >>
  `!name b n. local_region ce es.scopes t name b n ==>
      regions_disjoint B bsz b n /\ regions_disjoint ow 64 b n` by
    (rpt gen_tac >> strip_tac >> reverse conj_tac
     >- (qpat_assum `!name b n. local_region ce es.scopes t name b n ==> _`
          (drule_then ACCEPT_TAC)) >>
     `local_region ce es.scopes t name b n <=> local_region ce es.scopes t1 name b n` by
       (irule local_region_lookup_cong >> rpt strip_tac >>
        `not_fresh_at s1 p` by
          (qpat_assum `local_ptrs_reserved ce s1`
             (strip_assume_tac o REWRITE_RULE [local_ptrs_reserved_def]) >>
           qpat_assum `!n1 n2 p sz1 sz2. FLOOKUP ce.ce_vars n1 = SOME (PtrVar (Var p) sz1) ==> _`
             (qspecl_then [`name'`,`name'`,`p`,`sz`,`sz`] mp_tac) >> simp[]) >>
        `not_fresh_at s2 p` by
          (irule freshWritesTheory.not_fresh_at_mono >> qexists `s1` >> simp[]) >>
        simp[]) >>
     `local_region ce es.scopes t1 name b n` by
       (qpat_assum `local_region ce es.scopes t name b n <=> _`
          (fn eq => qpat_assum `local_region ce es.scopes t name b n`
            (ACCEPT_TAC o PURE_REWRITE_RULE [eq]))) >>
     qpat_assum `!name b n. local_region ce es.scopes t1 name b n ==> _`
       (drule_then ACCEPT_TAC)) >>
  suspend "parent_frame"
QED

Resume concat_prefix_alloc_mods[parent_frame]:
  `!i. i < s.vs_alloca_next /\ i IN tn.t_mem ==> i IN tn0.t_mem` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!i. i IN tn.t_mem <=> _` (qspec_then `i` mp_tac) >>
     qpat_assum `!i. i IN tn1.t_mem <=> _` (qspec_then `i` mp_tac) >>
     simp[] >> decide_tac) >>
  `ghost_kept_at lo ce es sa G0 tn0 s G tn` by
    (pure_rewrite_tac[ghost_kept_at_def] >> rpt conj_tac >> rpt gen_tac >> strip_tac
     >- (qpat_assum `!x. not_fresh_at sa x ==> lookup_var x t = _ /\ _`
           (drule_then strip_assume_tac) >> simp[])
     >- (qpat_assum `stmt_state_rel H0 ctx func ce cx es s`
           (mp_then Any mp_tac stmt_state_rel_local_ptrs_alloca) >>
         simp[NoAsms,alloca_inv_def,alloca_next_valid_def] >> strip_tac >>
         qpat_assum `!aid b n. FLOOKUP s.vs_allocas aid = SOME (b,n) ==> _`
           (drule_then assume_tac) >>
         qpat_assum `!i. i < s.vs_alloca_next /\ i IN tn.t_mem ==> _` irule >>
         conj_tac >- decide_tac >> first_assum ACCEPT_TAC) >>
     drule_all bodyMemoryDefsTheory.body_local_region_frontier >> strip_tac >>
     qpat_assum `!i. i < s.vs_alloca_next /\ i IN tn.t_mem ==> _` irule >>
     conj_tac >- decide_tac >> first_assum ACCEPT_TAC) >>
  `ci_mono sa s3` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `FLOOKUP G bv = SOME (B,bsz)` by
    (qpat_assum `!x. not_fresh_at s2 x ==> _` (qspec_then `bv` (drule_then strip_assume_tac)) >>
     qpat_assum `!x. not_fresh_at s1 x ==> _` (qspec_then `bv` (drule_then strip_assume_tac)) >> simp[]) >>
  `w2n (n2w ow : bytes32) = ow` by simp[] >>
  qexistsl [`t`,`G`,`tn`,`bv`,`dv`,`ov`,`B`,`n2w ow`] >>
  qpat_assum `w2n (n2w ow : bytes32) = ow` (fn eq => PURE_REWRITE_TAC [eq]) >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[])
QED

Finalise concat_prefix_alloc_mods
