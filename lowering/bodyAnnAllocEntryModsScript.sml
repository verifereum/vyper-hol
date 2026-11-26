(* The declaration's ALLOCA, before running the linked RHS or adding a
   source-scope binding. *)
Theory bodyAnnAllocEntryMods
Ancestors
  bodyFullPostsMods bodyFullAllocaFresh stmtSimDecl stmtSimProps stmtSimDefs
  stateRelProj venomMemDefs compileEnv bodyMemoryDefs loweringHalt exprSimAlloc
  vyperStorageFootprint
  stmtReasonMemory wordArgsPtr abiBuiltinAllocation emitHelperProps
  exprLoweringProps venomState finite_map bodyInvSplit loweringStateRelDefs
  bodyFullShadowBodyInv bodyPtrDefs loweringPosts ptrDiscipline vyperState

Theorem annalloc_new_site[local]:
  compile_alloc_buffer sz sa = (buf,a) /\ buf.buf_operand = Var p /\
  sz < dimword (:256) /\ run_inst_seq (emitted_insts sa a) s = OK raw /\
  t = raw with vs_inst_idx := k /\ FLOOKUP t.vs_allocas aid = SOME (b,n) ==>
  FLOOKUP s.vs_allocas aid = SOME (b,n) \/ s.vs_alloca_next <= b
Proof
  strip_tac >> drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[run_inst_seq_def, AllCaseEqs()] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[stmtReasonMemoryTheory.step_alloca_eq] >>
  Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id` >>
  gvs[AllCaseEqs(), update_var_def, FLOOKUP_UPDATE, wordsTheory.w2n_n2w] >>
  rpt strip_tac >> Cases_on `aid = sa.cs_next_id` >> gvs[FLOOKUP_UPDATE]
QED

Theorem annalloc_immutable[local]:
  immutable_frame_mods func old cx es s /\
  ce.ce_modules = old.ce_modules /\ ce.ce_module_vars = old.ce_module_vars /\
  ce.ce_module_var_type = old.ce_module_var_type /\ ce.ce_is_ctor = old.ce_is_ctor /\
  t.vs_memory = s.vs_memory /\ t.vs_data_section = s.vs_data_section /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  (!aid b sz. FLOOKUP t.vs_allocas aid = SOME (b,sz) ==>
    FLOOKUP s.vs_allocas aid = SOME (b,sz) \/ s.vs_alloca_next <= b) /\
  (!n b sz. local_region ce es.scopes t n b sz <=>
    local_region old es.scopes s n b sz) /\
  (!n b sz. local_region old es.scopes t n b sz <=>
    local_region old es.scopes s n b sz) ==>
  immutable_frame_mods func ce cx es t
Proof
  strip_tac >> fs[immutable_frame_mods_def, immutables_rel_mods_def,
                  immutable_alloca_sep_mods_def] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!src tops. _ ==> immutables_rel _ _ _ _ _ _`
        (drule_then assume_tac) >>
      fs[immutables_rel_def] >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  `!c s0 n b z. local_region (c with ce_module := src) es.scopes s0 n b z <=>
                   local_region c es.scopes s0 n b z` by simp[local_region_def] >>
  `immutable_alloca_sep func (old with ce_module := src) cx es t` by
    (irule immutable_alloca_sep_frame >> qexistsl_tac [`s`,`es`] >>
     simp[] >> metis_tac[]) >>
  irule immutable_alloca_sep_cenv_cong >>
  qexists_tac `old with ce_module := src` >> simp[] >> metis_tac[]
QED

(* Ordinary locals and return pointers can use the floor-zero transport.
   The real allocation floor and the linked low-section clause are retained
   separately; the counted path itself never changes floors. *)
Theorem annalloc_ghost[local]:
  ghost_inv_at_mods D lo d old cx es G tn s /\
  stmt_state_rel H ctx func old cx es s /\ local_ptrs_reserved old sa /\
  (!x sz. old.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ret_pc_ok old sa s /\ lookup_scopes id es.scopes = NONE /\
  (!n. n <> id ==> FLOOKUP ce.ce_vars n = FLOOKUP old.ce_vars n) /\
  ce.ce_modules = old.ce_modules /\ ce.ce_module_vars = old.ce_module_vars /\
  ce.ce_return_buf = old.ce_return_buf /\ ce.ce_return_pc = old.ce_return_pc /\
  ce.ce_imm_alloca = old.ce_imm_alloca /\
  (!x. not_fresh_at sa x ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP Ga x = FLOOKUP G x /\
    op_taint tna (Var x) = op_taint tn (Var x)) /\
  t with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
            vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|> = s /\
  allocas_from lo t /\ s.vs_alloca_next <= t.vs_alloca_next /\
  tna.t_stor = tn.t_stor /\ tna.t_trans = tn.t_trans /\ tna.t_imm = tn.t_imm /\
  (!i. i IN tna.t_mem <=> i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < stop)) ==>
  ghost_inv_at_mods D lo d ce cx es Ga tna t
Proof
  strip_tac >>
  `ghost_inv_at D 0 d old cx es G tn s /\ lo <= s.vs_alloca_next` by
    (fs[ghost_inv_at_mods_def, ghost_inv_at_def, allocas_from_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ghost_inv_at D 0 d old cx es Ga tna t` by
    (irule alloc_buffer_ghost_inv_at >> simp[allocas_from_def] >>
     qexistsl_tac [`G`,`H`,`ctx`,`stop`,`func`,`s`,`sa`,`tn`] >>
     simp[allocas_from_def] >> fs[ret_pc_ok_def] >> metis_tac[]) >>
  `t.vs_memory = s.vs_memory` by
    (qpat_assum `t with <|vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _|> = s` (SUBST1_TAC o SYM) >> simp[]) >>
  `!i. i < lo /\ i IN tna.t_mem ==> i IN tn.t_mem` by
    (rpt gen_tac >> simp[] >> decide_tac) >>
  fs[ghost_inv_at_mods_def, ghost_inv_at_def] >>
  rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> `name <> id` by (strip_tac >> gvs[]) >>
      qpat_assum `!n. n <> id ==> _` (drule_then assume_tac) >> fs[] >>
      qpat_assum `!n ent p sz. _ ==> ptr_covers Ga tna p t sz /\ _`
        (drule_all_then ACCEPT_TAC))
  >- (Cases_on `d` >> gvs[return_buf_ptr_def] >> PairCases_on `x` >>
      gvs[return_buf_ptr_def])
  >- (gen_tac >> disch_tac >>
      `i < lo /\ i IN tn.t_mem` by
        (pop_assum mp_tac >> Cases_on `i IN tn.t_mem` >> simp[] >> decide_tac) >>
      qpat_assum `!i. i < lo /\ i IN tn.t_mem ==> _` (drule_then assume_tac) >>
      fs[imm_section_dead_mods_def] >> first_assum ACCEPT_TAC)
  >- (rpt strip_tac >>
      `not_fresh_at sa x` by fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  decide_tac
QED

Theorem annalloc_live_locals[local]:
  lookup_scopes id es.scopes = NONE /\
  (!n. n <> id ==> FLOOKUP ce.ce_vars n = FLOOKUP old.ce_vars n) /\
  local_ptrs_reserved old sa /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) ==>
  (!n b sz. local_region old es.scopes t n b sz <=>
            local_region old es.scopes s n b sz) /\
  (!n b sz. local_region ce es.scopes t n b sz <=>
            local_region old es.scopes s n b sz)
Proof
  strip_tac >>
  `!n z. lookup_scopes n es.scopes = SOME z ==> n <> id` by
    (rpt strip_tac >> gvs[]) >>
  `!n z p sz. lookup_scopes n es.scopes = SOME z /\
    FLOOKUP old.ce_vars n = SOME (PtrVar (Var p) sz) ==>
    lookup_var p t = lookup_var p s` by
    (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `!n b sz. local_region old es.scopes t n b sz <=>
            local_region old es.scopes s n b sz` by
    (rpt gen_tac >> irule local_region_lookup_cong >> first_assum ACCEPT_TAC) >>
  simp[] >> rpt gen_tac >> simp[local_region_def] >> metis_tac[]
QED

Theorem annassign_alloc_entry_mods:
    declare_local old id typ sa = (ce,r) /\ old.ce_alloca_locals /\
    FLOOKUP old.ce_vars id = NONE /\ lookup_scopes id es.scopes = NONE /\
    sz = type_memory_bytes old typ /\ sz < dimword (:256) /\
    compile_alloc_buffer sz sa = (<|buf_operand := Var p; buf_size := sz|>,a) /\
    fn_has_code sa a func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved old sa /\ ret_pc_ok old sa s0 /\
    (!x cap. old.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
    return_buf_frame d old sa s0 /\ alloca_history func s0 /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
    storage_trace_domain cx st0 es.storage_trace /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func old cx es s0 /\
      immutable_frame_mods func old cx es s0 /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv_at_mods (DF H) lo d old cx es G0 tn0 s0) /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?w entry Ga tna.
      FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz) /\
      (!name. name <> id ==> FLOOKUP ce.ce_vars name = FLOOKUP old.ce_vars name) /\
      ce with <|ce_vars := old.ce_vars; ce_var_type := old.ce_var_type;
        ce_dynarray_capacity := old.ce_dynarray_capacity|> = old /\
      ce.ce_modules = old.ce_modules /\ ce.ce_is_ctor = old.ce_is_ctor /\
      ce.ce_return_buf = old.ce_return_buf /\
      ce.ce_return_pc = old.ce_return_pc /\ ce.ce_imm_alloca = old.ce_imm_alloca /\
      MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]) (fn_insts func) /\
      sa.cs_next_id <= a.cs_next_id /\ sa.cs_next_var <= a.cs_next_var /\
      not_fresh_at a p /\ local_ptrs_reserved ce a /\
      (!x. not_fresh_at sa x ==> not_fresh_at a x) /\
      (!x cap. ce.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at a x) /\
      (!x cap. ce.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at a x) /\
      ret_pc_ok ce a entry /\ return_buf_frame d ce a entry /\
      (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s0,G0,tn0) [] (OK entry,Ga,tna)) /\
      ~entry.vs_halted /\ entry.vs_current_bb = a.cs_current_bb /\
      entry.vs_inst_idx = LENGTH a.cs_current_insts /\
      entry with <|vs_vars := s0.vs_vars; vs_allocas := s0.vs_allocas;
        vs_alloca_next := s0.vs_alloca_next; vs_inst_idx := s0.vs_inst_idx|> = s0 /\
      entry.vs_gas_readings = s0.vs_gas_readings /\
      alloca_history func entry /\ s0.vs_alloca_next <= entry.vs_alloca_next /\
      lookup_var p entry = SOME w /\ ptr_covers Ga tna p entry sz /\
      FLOOKUP entry.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
      FLOOKUP Ga p = SOME (w2n w,sz) /\
      w2n w + sz < dimword (:256) /\ w2n w + sz <= entry.vs_alloca_next /\
      (!aid ent. FLOOKUP s0.vs_allocas aid = SOME ent ==>
        FLOOKUP entry.vs_allocas aid = SOME ent) /\
      (!x. not_fresh_at sa x ==>
        lookup_var x entry = lookup_var x s0 /\ FLOOKUP Ga x = FLOOKUP G0 x /\
        op_taint tna (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame old es sa s0 ce es entry /\
      ghost_kept_at lo old es sa G0 tn0 s0 Ga tna /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        stmt_state_rel H ctx func ce cx es entry /\
        immutable_frame_mods func ce cx es entry /\
        storage_well_formed_on cx es (FST H) /\
        ghost_inv_at_mods (DF H) lo d ce cx es Ga tna entry)
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> _` (drule_then strip_assume_tac) >>
  `allocas_from lo s0 /\ lo <= s0.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  drule_all (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``]
    alloc_buffer_origin_ptr_path_with_raw_endpoint) >>
  disch_then (qspecl_then [`tn0`,`explicit`,`PG`,`G0`]
    (qx_choosel_then [`p0`,`w`,`entry`,`Ga`,`tna`,`raw`] strip_assume_tac)) >>
  `p0 = p` by fs[] >> qpat_x_assum `p0 = p` SUBST_ALL_TAC >>
  `!aid base len. FLOOKUP entry.vs_allocas aid = SOME (base,len) ==>
    FLOOKUP s0.vs_allocas aid = SOME (base,len) \/ s0.vs_alloca_next <= base` by
    (rpt gen_tac >> disch_tac >> irule annalloc_new_site >>
     qexistsl_tac [`a`, `<|buf_operand := Var p; buf_size := sz|>`,
                   `LENGTH a.cs_current_insts`, `p`, `raw`, `sa`, `sz`, `entry`] >>
     simp[]) >>
  qpat_x_assum `entry = raw with vs_inst_idx := _` kall_tac >>
  qpat_x_assum `Ga = step_prov _ _ _ _` kall_tac >>
  qpat_x_assum `tna = step_taint _ _ _ _` kall_tac >>
  suspend "declared_frames"
QED

Resume annassign_alloc_entry_mods[declared_frames]:
  drule_all declare_local_ptr >> strip_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `p = STRING #"%" (toString sa.cs_next_var)` by fs[] >>
  `FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) sz)` by fs[] >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]) (fn_insts func)` by
    (drule_all buffer_alloc_code >> simp[]) >>
  `ce.ce_modules = old.ce_modules /\ ce.ce_module_vars = old.ce_module_vars /\
   ce.ce_module_var_type = old.ce_module_var_type /\ ce.ce_is_ctor = old.ce_is_ctor /\
   ce.ce_return_buf = old.ce_return_buf /\ ce.ce_return_pc = old.ce_return_pc /\
   ce.ce_imm_alloca = old.ce_imm_alloca` by
    (qpat_assum `ce with <|ce_vars := _; ce_var_type := _;
       ce_dynarray_capacity := _|> = old` mp_tac >>
     simp[compile_env_component_equality]) >>
  `entry.vs_memory = s0.vs_memory /\ entry.vs_data_section = s0.vs_data_section /\
   entry.vs_gas_readings = s0.vs_gas_readings /\ ~entry.vs_halted` by
    (qpat_assum `entry with <|vs_vars := _; vs_allocas := _;
      vs_alloca_next := _; vs_inst_idx := _|> = s0` mp_tac >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  `(!n b z. local_region old es.scopes entry n b z <=>
            local_region old es.scopes s0 n b z) /\
   (!n b z. local_region ce es.scopes entry n b z <=>
            local_region old es.scopes s0 n b z)` by
    (irule annalloc_live_locals >> conj_tac
     >- (qexists_tac `id` >> simp[] >> first_assum ACCEPT_TAC) >>
     qexists_tac `sa` >> simp[] >> metis_tac[]) >>
  `alloca_frame old es sa s0 ce es entry` by
    (simp[alloca_frame_def] >> rpt gen_tac >> strip_tac >> first_assum ACCEPT_TAC) >>
  `local_ptrs_reserved ce a` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `r` >>
     simp[] >> drule_all declare_local_reserved >> simp[]) >>
  `ret_pc_ok ce a entry` by
    (irule ret_pc_ok_frame >> qexistsl_tac [`old`,`s0`,`sa`] >>
     simp[] >> metis_tac[]) >>
  `return_buf_frame d ce a entry` by
    (irule return_buf_frame_frame >> qexistsl_tac [`old`,`s0`,`sa`] >>
     simp[] >> metis_tac[]) >>
  suspend "horizons"
QED

Resume annassign_alloc_entry_mods[horizons]:
  `!aid off len. FLOOKUP s0.vs_allocas aid = SOME (off,len) ==>
                  off + len <= s0.vs_alloca_next` by
    (drule stmt_state_rel_local_ptrs_alloca >> simp[alloca_inv_def,alloca_next_valid_def] >>
     strip_tac >> rpt gen_tac >> strip_tac >>
     qpat_assum `!aid base sz. FLOOKUP s0.vs_allocas aid = _ ==> _`
       (drule_then mp_tac) >> decide_tac) >>
  `!n b z. local_region old es.scopes s0 n b z ==> b + z <= s0.vs_alloca_next` by
    (rpt strip_tac >> drule_all body_local_region_frontier >> simp[]) >>
  `ghost_kept_at lo old es sa G0 tn0 s0 Ga tna` by
    (irule alloc_buffer_ghost_kept_at >>
     qexistsl_tac [`G0`,`w2n w + sz`,`s0`,`tn0`] >>
     simp[ghost_kept_at_refl] >> metis_tac[]) >>
  `immutable_frame_mods func ce cx es entry` by
    (irule annalloc_immutable >> qexistsl_tac [`old`,`s0`] >> simp[]) >>
  `!x cap. old.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at a x` by
    (qx_genl_tac [`x`,`cap`] >> disch_tac >>
     qpat_assum `ret_pc_ok ce a entry`
       (qspecl_then [`x`,`cap`] mp_tac o REWRITE_RULE [ret_pc_ok_def]) >> simp[]) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es entry /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at_mods (DF H) lo d ce cx es Ga tna entry` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ _ _ ==> _` (drule_then strip_assume_tac) >>
     `stmt_state_rel H ctx func old cx es entry` by
       (qpat_assum `!J. stmt_state_rel J _ _ _ _ _ s0 ==> stmt_state_rel J _ _ _ _ _ entry`
          (qspec_then `H` mp_tac) >> simp[]) >>
     conj_tac
     >- (irule stmt_state_rel_declare_local_entry >>
         goal_assum (drule_at (Pat `declare_local _ _ _ _ = _`)) >> simp[]) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     drule_all_then ACCEPT_TAC (INST_TYPE [alpha |-> ``:256``] annalloc_ghost)) >>
  qexistsl_tac [`w`,`entry`,`Ga`,`tna`] >> simp[]
QED

Finalise annassign_alloc_entry_mods
