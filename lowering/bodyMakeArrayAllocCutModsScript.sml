(* The paired ALLOCA landing is the pre-header MakeArray cut. *)
Theory bodyMakeArrayAllocCutMods
Ancestors
  bodyMakeBufferInitMods bodyMakeElementsContractMods bodyFullIfExpReach
  exprSimFullBundleProps wordArgsPtr vyperStorageFootprint

val _ = Parse.hide "base";
val array_init_contract = concl (GEN_ALL make_buffer_init_mods);

Theorem make_array_alloc_cut_from_init_mods:
  ^array_init_contract /\
  (compile_alloc_buffer cap sa = (buf,sm) /\
   compile_alloc_buffer cap sha = (shbuf,shm) /\ gas_shadow_state sa sha /\
   fn_has_code sa sm func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
   cap < dimword (:256) /\ storage_trace_domain cx st0 es.storage_trace /\
   (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func ce cx es s0 /\ immutable_frame_mods func ce cx es s0 /\
      storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx es G0 tn0 s0) /\
   (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
   return_buf_frame d ce sa s0 /\ alloca_history func s0 /\
   ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
   s0.vs_inst_idx = LENGTH sa.cs_current_insts) /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!fn i u. frag_reachable ctx func s0 fn i u ==> dalloca_fmp_headroom i u) ==>
  ?q base si Gi tni.
    buf.buf_operand = Var q /\ buf.buf_size = cap /\ shbuf = buf /\
    gas_shadow_state sm shm /\ ci_mono sa sm /\ local_ptrs_reserved ce sm /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s0,G0,tn0) [] (OK si,Gi,tni)) /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w cap)] [q]) (fn_insts func) /\
    FLOOKUP Gi q = SOME (base,cap) /\ allocas_from lo si /\
    (!aid b n. aid < sa.cs_next_id /\ FLOOKUP s0.vs_allocas aid = SOME (b,n) ==>
               loweringStateRelDefs$regions_disjoint base cap b n) /\
    (!i. i IN tni.t_mem <=> i IN tn0.t_mem \/ (s0.vs_alloca_next <= i /\ i < base + cap)) /\
    make_elements_cut_mods DF lo d ctx func ce cx st0 (sa,es,s0,G0,tn0)
      (sa.cs_next_id,base,cap,q) sm es si Gi tni /\
    si.vs_memory = s0.vs_memory /\
    (!name b n. local_region ce es.scopes si name b n <=> local_region ce es.scopes s0 name b n)
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "init")
     (CONJUNCTS_THEN2 (mk_asm "entry") strip_assume_tac)) >>
  asm_x "init" (fn init => asm "entry" (mp_tac o MATCH_MP (SPEC_ALL init))) >>
  disch_then (qx_choosel_then [`q`,`base`,`si`,`Gi`,`tni`] strip_assume_tac) >>
  asm_x "entry" strip_assume_tac >>
  `!fn i u. frag_reachable ctx func si fn i u ==> dalloca_fmp_headroom i u` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s0,G0,tn0) [] (OK si,Gi,tni)`
       (qspec_then `DF (storage_trace_horizon es.storage_trace)` assume_tac) >>
     rpt strip_tac >> drule_all_then ACCEPT_TAC gas_origin_ptr_path_dalloca_fmp_headroom) >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func ce cx es s0` by
    (qpat_assum `!H. valid_horizon cx st0 H _ ==> stmt_state_rel _ _ _ _ _ _ s0 /\ _`
       (qspec_then `storage_trace_horizon es.storage_trace` mp_tac) >>
     simp[GSYM storage_trace_domain_def]) >>
  `!n b k. local_region ce es.scopes s0 n b k <=> local_region ce es.scopes si n b k` by
    (irule (INST_TYPE [alpha |-> ``:256``] wb_frame_local_regions) >>
     qpat_assum `wb_frame ce es es sa s0 si` (irule_at Any) >>
     qpat_assum `stmt_state_rel _ ctx func ce cx es s0` (irule_at Any) >> simp[]) >>
  qexistsl [`q`,`base`,`si`,`Gi`,`tni`] >>
  qpat_x_assum `expr_sim_full_endpoint func sm s0 si`
    (strip_assume_tac o REWRITE_RULE [expr_sim_full_endpoint_def]) >>
  simp_tac (srw_ss()) [make_elements_cut_mods_def,make_elements_save_mods_def] >>
  rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >>
  once_rewrite_tac [EQ_SYM_EQ] >> first_assum ACCEPT_TAC
QED
