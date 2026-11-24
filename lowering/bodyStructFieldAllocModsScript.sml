(* Initialize the ordered-field prefix at the literal's actual ALLOCA. *)
Theory bodyStructFieldAllocMods
Ancestors
  bodyStructFieldCutsMods bodyFullAllocaFresh bodyFullShadowBodyInv
  bodyFullPostsMods bodyInvSplit
  bodyFullHashKeccakFixed bodyMemoryDefs exprSimAlloc exprSimFullBundleProps
  loweringHalt exprLoweringProps exprSimProps loweringPosts loweringStateRelDefs
  stateRelProj vyperStorageTrace vyperStorageFootprint vyperEvalScopesProgress
  bodyPtrDefs ptrDiscipline venomMemDefs venomExecSemantics venomState venomInst fragExec
  compileEnv context finite_map words

Theorem struct_alloc_ghost[local]:
  ghost_inv_at_mods D lo d ce cx es G tn s /\
  stmt_state_rel (H : (bool # bytes32 # type_value) list # num list) ctx func ce cx es s /\
  local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)) /\
  t with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
           vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|> = s /\
  allocas_from lo t /\ s.vs_alloca_next <= t.vs_alloca_next /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  (!i. i IN tn'.t_mem <=> i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < stop)) ==>
  ghost_inv_at_mods D lo d ce cx es G' tn' t
Proof
  strip_tac >>
  `ghost_inv_at D 0 d ce cx es G tn s /\ lo <= s.vs_alloca_next` by
    (fs[ghost_inv_at_mods_def, ghost_inv_at_def, allocas_from_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ghost_inv_at D 0 d ce cx es G' tn' t` by
    (irule (INST_TYPE [alpha |-> ``:256``] alloc_buffer_ghost_inv_at) >>
     conj_tac >- simp[allocas_from_def] >>
     qexistsl [`G`,`H`,`ctx`,`stop`,`func`,`s`,`sa`,`tn`] >> simp[]) >>
  `t.vs_memory = s.vs_memory` by
    (qpat_assum `t with <|vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _|> = s` (SUBST1_TAC o SYM) >> simp[]) >>
  `!i. i < lo /\ i IN tn'.t_mem ==> i IN tn.t_mem` by (simp[] >> decide_tac) >>
  fs[ghost_inv_at_mods_def, ghost_inv_at_def] >> rpt conj_tac
  >- metis_tac[]
  >- (rpt strip_tac >> `not_fresh_at sa x` by fs[local_ptrs_reserved_def] >>
      metis_tac[]) >>
  decide_tac
QED

Theorem struct_alloc_regions[local]:
  local_ptrs_reserved ce sa /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) ==>
  !ce' name b n. ce'.ce_vars = ce.ce_vars ==>
    (local_region ce' es.scopes t name b n <=> local_region ce' es.scopes s name b n)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  irule local_region_lookup_cong >> simp[] >> metis_tac[local_ptrs_reserved_def]
QED

Theorem struct_alloc_immutable[local]:
  immutable_frame_mods func ce cx es s /\
  t.vs_memory = s.vs_memory /\ t.vs_data_section = s.vs_data_section /\
  exec_alloca ins s (w:bytes32) = OK raw /\ t = raw with vs_inst_idx := idx /\
  (!ce' name b n. ce'.ce_vars = ce.ce_vars ==>
    (local_region ce' es.scopes t name b n <=> local_region ce' es.scopes s name b n)) ==>
  immutable_frame_mods func ce cx es t
Proof
  strip_tac >> fs[immutable_frame_mods_def] >> conj_tac
  >- (fs[immutables_rel_mods_def, immutables_rel_def] >> first_assum ACCEPT_TAC) >>
  fs[immutable_alloca_sep_mods_def] >> rpt gen_tac >> strip_tac >>
  `!id b n. local_region (ce with ce_module := src) es.scopes t id b n <=>
            local_region (ce with ce_module := src) es.scopes s id b n` by simp[] >>
  `!id b n. local_region (ce with ce_module := src) es.scopes raw id b n <=>
            local_region (ce with ce_module := src) es.scopes t id b n` by
    (qpat_assum `t = raw with vs_inst_idx := idx` SUBST1_TAC >>
     simp[local_region_def, lookup_var_def]) >>
  `immutable_alloca_sep func (ce with ce_module := src) cx es raw` by
    (irule immutable_alloca_sep_exec_alloca >> qexistsl [`ins`, `w`, `s`] >>
     simp[] >> rpt strip_tac >> qexists `id` >> fs[]) >>
  irule immutable_alloca_sep_fields >> qexistsl [`raw`, `es`] >>
  simp[] >> rpt gen_tac >> strip_tac >> qexists `id` >>
  qpat_assum `t = raw with vs_inst_idx := idx` (fn eq =>
    qpat_x_assum `local_region _ _ (raw with vs_inst_idx := idx) _ _ _`
      (assume_tac o PURE_REWRITE_RULE [GSYM eq])) >>
  metis_tac[]
QED

Theorem struct_field_alloc_prefix_mods:
  compile_alloc_buffer n sa = (buf,sm) /\ fn_has_code sa sm func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  n < dimword (:256) /\ storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es s /\
    immutable_frame_mods func ce cx es s /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at_mods (DF H) lo d ce cx es G0 tn0 s) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d ce sa s /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?root addr t G tn.
    buf.buf_operand = Var root /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G0,tn0) [] (OK t,G,tn)) /\
    return_buf_frame d ce sm t /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      struct_prefix_mods (ctx,func,ce,cx,lo,d,pure) (es,sa,s,G0,tn0)
        (root,addr,n,sa.cs_next_id) (H,DF H,es,sm,G,tn,t) [] 0)
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  drule_then assume_tac stmt_state_rel_allocas_below_fmp >>
  drule_all (INST_TYPE [beta |-> ``:256``] alloc_buffer_origin_ptr_path_with_raw_endpoint) >>
  disch_then (qspecl_then [`tn0`, `explicit`, `PG`, `G0`]
    (qx_choosel_then [`root`, `w`, `t`, `G`, `tn`, `raw`] strip_assume_tac)) >>
  `t.vs_memory = s.vs_memory /\ t.vs_data_section = s.vs_data_section /\ ~t.vs_halted` by
    (qpat_assum `~s.vs_halted` mp_tac >>
     qpat_assum `t with <|vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _|> = s` (SUBST1_TAC o SYM) >> simp[]) >>
  drule compile_alloc_buffer_insts >> strip_tac >>
  `root = STRING #"%" (toString sa.cs_next_var)` by metis_tac[operand_11] >>
  `emitted_insts sa sm = [mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [root]]` by
    simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND] >>
  `exec_alloca (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [root]) s (n2w n : bytes32) = OK raw` by
    (qpat_assum `emitted_insts sa sm = _` (fn eq =>
       qpat_assum `run_inst_seq _ _ = OK raw` (mp_tac o PURE_REWRITE_RULE [eq])) >>
     simp[NoAsms, run_inst_seq_def, step_inst_base_def, mk_inst_def] >>
     CASE_TAC >> simp[]) >>
  `!ce' name b n. ce'.ce_vars = ce.ce_vars ==>
    (local_region ce' es.scopes t name b n <=> local_region ce' es.scopes s name b n)` by
    (rpt gen_tac >> strip_tac >> irule struct_alloc_regions >>
     qpat_assum `local_ptrs_reserved ce sa` (irule_at Any) >>
     simp[] >> gen_tac >> strip_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> _` (drule_then strip_assume_tac) >> simp[]) >>
  `sa.cs_next_id < sm.cs_next_id /\ sa.cs_next_var <= sm.cs_next_var /\
   MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [root]) (fn_insts func)` by
    (drule_all buffer_alloc_code >> drule compile_alloc_buffer_parts >> simp[] >> strip_tac >> gvs[]) >>
  `return_buf_frame d ce sm t` by
    (drule return_buf_frame_frame >> disch_then irule >> simp[] >>
     rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `lo <= w2n w` by (fs[allocas_from_def] >> first_x_assum drule >> simp[]) >>
  `wb_frame ce es es sa s t` by
    (simp[wb_frame_def, locals_kept_def, popped_kept_def, scopes_progress_refl] >>
     rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `!name p k. local_region ce es.scopes s name p k ==> p+k <= s.vs_alloca_next` by
    (qpat_assum `stmt_state_rel (storage_trace_horizon _) _ _ _ _ _ s`
       (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) mp_tac body_local_region_frontier) >>
     disch_then (fn th => rpt gen_tac >> strip_tac >> drule th) >>
     decide_tac) >>
  `!aid p k. FLOOKUP s.vs_allocas aid = SOME (p,k) ==> p+k <= s.vs_alloca_next` by
    (qpat_assum `stmt_state_rel (storage_trace_horizon _) _ _ _ _ _ s`
       (mp_then Any mp_tac stmt_state_rel_local_ptrs_alloca) >>
     simp[alloca_inv_def, alloca_next_valid_def] >> strip_tac >>
     rpt gen_tac >> strip_tac >>
     qpat_assum `!aid p k. FLOOKUP s.vs_allocas aid = _ ==> _` drule >> decide_tac) >>
  `ghost_kept_at lo ce es sa G0 tn0 s G tn` by
    (irule alloc_buffer_ghost_kept_at >> qexistsl [`G0`, `w2n w+n`, `s`, `tn0`] >>
     simp[ghost_kept_at_def] >> rpt conj_tac >> rpt gen_tac >> strip_tac >>
     first_x_assum drule >> simp[]) >>
  `immutable_frame_mods func ce cx es t` by
    (irule struct_alloc_immutable >>
     qexistsl [`LENGTH sm.cs_current_insts`,
       `mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [root]`, `raw`, `s`, `n2w n`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `t = raw with vs_inst_idx := _` kall_tac >>
  qpat_x_assum `G = step_prov _ _ _ raw` kall_tac >>
  qpat_x_assum `tn = step_taint _ _ raw _` kall_tac >>
  qexistsl [`root`, `w2n w`, `t`, `G`, `tn`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon cx st0 H _ ==> stmt_state_rel _ _ _ _ _ _ s /\ _`
    (qspecl_then [`H`] mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `ghost_inv_at_mods (DF H) lo d ce cx es G tn t` by
    (irule struct_alloc_ghost >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`G0`, `H`, `ctx`, `func`, `s`, `sa`, `w2n w+n`, `tn0`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!name p k. local_region ce es.scopes s name p k ==> regions_disjoint (w2n w) n p k` by
    (rpt gen_tac >> strip_tac >>
     `local_region ce es.scopes t name p k` by simp[] >>
     qpat_assum `!name b len. local_region ce es.scopes t name b len ==> _`
       (drule_then ACCEPT_TAC)) >>
  `stmt_state_rel H ctx func ce cx es t` by
    (qpat_assum `!J. stmt_state_rel J ctx func ce cx es s ==> _` (drule_then ACCEPT_TAC)) >>
  qpat_x_assum `root = STRING _ _` kall_tac >>
  qpat_x_assum `buf.buf_operand = Var (STRING _ _)` kall_tac >>
  qpat_x_assum `sm.cs_current_insts = _` kall_tac >>
  irule struct_prefix_empty_intro >>
  asm_simp_tac bool_ss [expr_sim_full_endpoint_def, pure_frame_def, wordsTheory.n2w_w2n,
    GSYM loweringStateRelDefsTheory.regions_disjoint_def] >>
  rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC >>
  qx_gen_tac `old` >> rpt gen_tac >> strip_tac >>
  qpat_assum `!aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==> _`
    irule >> qexists `old` >> simp[]
QED
