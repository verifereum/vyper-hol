(* The actual range-slot ALLOCA and its linked frame. The same prefix is
   shared by the literal and the checked counter setup. *)
Theory bodyForRangeAllocMods
Ancestors
  bodyFullAllocaFresh bodyFullForRange bodyFullPostsMods bodyFullHashKeccakFixed
  bodyFullShared decoderAllocationBoundsPtr stateRelProj freshWrites
  robustCopyTransportPtr loweringHalt exprLoweringProps bodyPtrDefs
  bodyFullShadowBodyInv loweringStateRelDefs bodyInvSplit venomExecSemantics
  venomState venomInst fragExec ptrDiscipline bodyMemoryDefs stmtSimProps
  stmtSimDefs venomMemDefs vyperStorageTrace vyperStorageFootprint loweringPosts

Theorem range_alloc_ghost_mods[local]:
  ghost_inv_at_mods D lo d cenv cx es G tn s /\
  local_ptrs_rel func cenv es.scopes s /\ local_ptrs_reserved cenv st /\
  (!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at st x) /\
  (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at st x) /\
  (!x. not_fresh_at st x ==>
       lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
       op_taint tn' (Var x) = op_taint tn (Var x)) /\
  t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_immutables = s.vs_immutables /\ allocas_from lo t /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  (!i. i IN tn'.t_mem /\ i < s.vs_alloca_next ==> i IN tn.t_mem) ==>
  ghost_inv_at_mods D lo d cenv cx es G' tn' t
Proof
  strip_tac >>
  `!p sz. not_fresh_at st p /\ ptr_covers G tn p s sz ==>
          ptr_covers G' tn' p t sz` by (rw[ptr_covers_def] >> metis_tac[]) >>
  qpat_x_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[ghost_inv_at_mods_def] >> strip_tac >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at st p` by metis_tac[local_ptrs_reserved_def] >>
      first_x_assum (drule_all_then strip_assume_tac) >>
      conj_tac >- metis_tac[] >>
      rpt strip_tac >>
      `lookup_var p s = SOME w` by metis_tac[] >>
      `val_wf entry.type entry.value /\
       w2n w + val_footprint entry.type entry.value <= s.vs_alloca_next` by
        (qpat_x_assum `local_ptrs_rel _ _ _ _` mp_tac >>
         simp[local_ptrs_rel_def] >> strip_tac >>
         first_x_assum (drule_all_then strip_assume_tac) >> gvs[] >>
         drule exprSimPropsTheory.val_footprint_le >> strip_tac >> decide_tac) >>
      irule robust_val_in_memory_decreasing_taint_transport >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`s.vs_memory`, `t.vs_memory`,
                    `val_footprint entry.type entry.value`,
                    `w2n w`, `tn.t_mem`, `tn'.t_mem`] >>
      simp[] >> rpt strip_tac >>
      qpat_assum `!i. i IN tn'.t_mem /\ _ ==> _` irule >> simp[])
  >- (Cases_on `d` >> gvs[return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME rb)` >> PairCases_on `rb` >>
      gvs[return_buf_ptr_def] >> metis_tac[])
  >- metis_tac[]
  >- fs[stor_taint_ok_at_def]
  >- (rpt strip_tac >> `i < s.vs_alloca_next` by decide_tac >> metis_tac[])
  >- metis_tac[local_ptrs_reserved_imm_base]
  >- simp[] >> decide_tac
QED

Theorem range_alloc_local_regions[local]:
  local_ptrs_reserved cenv st /\ cenv'.ce_vars = cenv.ce_vars /\
  (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) ==>
  (local_region cenv' scopes t id b z <=> local_region cenv' scopes s id b z)
Proof
  strip_tac >> irule local_region_lookup_cong >> simp[] >>
  metis_tac[local_ptrs_reserved_def]
QED

Theorem range_alloc_immutable_mods[local]:
  immutable_frame_mods func cenv cx es s /\ local_ptrs_reserved cenv st /\
  (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
  exec_alloca ins s (n : bytes32) = OK r /\ t = r with vs_inst_idx := idx /\
  r.vs_memory = s.vs_memory /\ r.vs_data_section = s.vs_data_section ==>
  immutable_frame_mods func cenv cx es t
Proof
  strip_tac >> gvs[immutable_frame_mods_def] >> conj_tac
  >- (fs[immutables_rel_mods_def, immutables_rel_def] >> first_assum ACCEPT_TAC) >>
  fs[immutable_alloca_sep_mods_def] >> rpt strip_tac >>
  `!id b z. local_region (cenv with ce_module := src) es.scopes r id b z <=>
            local_region (cenv with ce_module := src) es.scopes s id b z` by
    (irule range_alloc_local_regions >>
     qpat_assum `local_ptrs_reserved cenv st` (irule_at Any) >>
     fs[lookup_var_def]) >>
  `immutable_alloca_sep func (cenv with ce_module := src) cx es r` by
    (irule immutable_alloca_sep_exec_alloca >>
     qexistsl_tac [`ins`, `n`, `s`] >> simp[] >> metis_tac[]) >>
  irule immutable_alloca_sep_fields >> qexistsl_tac [`r`, `es`] >> simp[] >>
  rpt strip_tac >> qexists_tac `id` >>
  pure_rewrite_tac[local_region_def, lookup_var_def] >> simp[] >>
  fs[local_region_def, lookup_var_def] >> metis_tac[local_ptrs_reserved_def]
QED

(* Return separation uses the return buffer's own lower bound, not lo. *)
Theorem range_alloc_return_sep[local]:
  return_buf_frame d cenv st s /\ return_buf_sep d cenv es s /\
  local_ptrs_reserved cenv st /\
  (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s) /\
  exec_alloca ins s (n : bytes32) = OK r /\ t = r with vs_inst_idx := idx ==>
  return_buf_sep d cenv es t
Proof
  strip_tac >> irule return_buf_sep_transport >> conj_tac
  >- (rpt strip_tac >>
      `allocas_from (w2n bw + capacity) s /\ w2n bw + capacity <= s.vs_alloca_next` by
        fs[bodySimFullTheory.return_buf_sep_def, return_buf_frame_def] >>
      `allocas_from (w2n bw + capacity) r` by
        (drule (REWRITE_RULE[GSYM AND_IMP_INTRO] exec_alloca_preserves_allocas_from) >>
         disch_then irule >> simp[]) >>
      qpat_assum `t = r with vs_inst_idx := _` SUBST1_TAC >>
      fs[allocas_from_def] >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`cenv`, `es`, `s`] >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> rename1 `local_region cenv es.scopes t id b cap ==> _` >>
  `local_region cenv es.scopes t id b cap <=> local_region cenv es.scopes s id b cap` by
    (irule range_alloc_local_regions >>
     qpat_assum `local_ptrs_reserved cenv st` (irule_at Any) >> simp[]) >>
  simp[]
QED

Theorem range_slot_alloc_path_mods:
  p = STRING #"%" (toString st.cs_next_var) /\
  lookup_block st.cs_current_bb func.fn_blocks =
    SOME <| bb_label := st.cs_current_bb;
            bb_instructions := st.cs_current_insts ++
              [mk_inst st.cs_next_id ALLOCA [Lit (n2w sz)] [p]] ++ tail |> /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv st /\ sz < dimword (:256) /\
  sa.cs_next_id <= st.cs_next_id /\ sa.cs_next_var <= st.cs_next_var /\
  (!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x) /\
  ret_pc_ok cenv sa s /\ return_buf_frame d cenv st s /\ return_buf_sep d cenv ea s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  storage_trace_domain cx st0 ea.storage_trace /\
  (!H. valid_horizon cx st0 H ea.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ea s /\
       immutable_frame_mods func cenv cx ea s /\
       storage_well_formed_on cx ea (FST H) /\
       ghost_inv_at_mods (DF H) lo d cenv cx ea GE tnE s) /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==> lookup_var x s = SOME v) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
  (!x. not_fresh_at sa x ==>
       FLOOKUP GE x = FLOOKUP G0 x /\ op_taint tnE (Var x) = op_taint tn0 (Var x)) /\
  alloca_frame cenv es sa s0 cenv ea s /\
  (!aid off z i. FLOOKUP s0.vs_allocas aid = SOME (off,z) /\ aid < sa.cs_next_id /\
     (!nm b z'. local_region cenv es.scopes s0 nm b z' ==>
                off + z <= b \/ b + z' <= off) /\
     off <= i /\ i < off + z /\ i IN tnE.t_mem ==> i IN tn0.t_mem) ==>
  ?w sA GA tnA.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,GE,tnE) [] (OK sA,GA,tnA)) /\
    sA.vs_current_bb = st.cs_current_bb /\ sA.vs_inst_idx = LENGTH st.cs_current_insts + 1 /\
    ~sA.vs_halted /\ sA.vs_memory = s.vs_memory /\
    ret_pc_ok cenv sa sA /\ return_buf_frame d cenv st sA /\ return_buf_sep d cenv ea sA /\
    (!H. valid_horizon cx st0 H ea.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ea sA /\
       immutable_frame_mods func cenv cx ea sA /\
       storage_well_formed_on cx ea (FST H) /\
       ghost_inv_at_mods (DF H) lo d cenv cx ea GA tnA sA) /\
    lookup_var p sA = SOME w /\ ptr_covers GA tnA p sA sz /\
    FLOOKUP sA.vs_allocas st.cs_next_id = SOME (w2n w,sz) /\
    FLOOKUP GA p = SOME (w2n w,sz) /\ lo <= w2n w /\
    w2n w + sz < dimword (:256) /\ w2n w + sz <= sA.vs_alloca_next /\
    (!aid b len. aid < st.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
                 regions_disjoint (w2n w) sz b len) /\
    (!name b len. local_region cenv ea.scopes sA name b len ==>
                  regions_disjoint (w2n w) sz b len) /\
    (!x. not_fresh_at st x ==>
         lookup_var x sA = lookup_var x s /\ FLOOKUP GA x = FLOOKUP GE x /\
         op_taint tnA (Var x) = op_taint tnE (Var x)) /\
    alloca_history func sA /\ (ctx_has_dalloca ctx ==> allocas_below_fmp sA) /\
    s0.vs_alloca_next <= sA.vs_alloca_next /\
    (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==> lookup_var x sA = SOME v) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP sA.vs_allocas aid = SOME b) /\
    (!x. not_fresh_at sa x ==>
         FLOOKUP GA x = FLOOKUP G0 x /\ op_taint tnA (Var x) = op_taint tn0 (Var x)) /\
    alloca_frame cenv es sa s0 cenv ea sA /\
    (!aid off z i. FLOOKUP s0.vs_allocas aid = SOME (off,z) /\ aid < sa.cs_next_id /\
       (!nm b z'. local_region cenv es.scopes s0 nm b z' ==>
                  off + z <= b \/ b + z' <= off) /\
       off <= i /\ i < off + z /\ i IN tnA.t_mem ==> i IN tn0.t_mem)
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ea.storage_trace) ea.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon cx st0 H ea.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  drule_then assume_tac stmt_state_rel_allocas_below_fmp >>
  Cases_on `compile_alloc_buffer sz st` >>
  rename1 `compile_alloc_buffer sz st = (buf,cut)` >>
  `fn_has_code st cut func` by
    (irule range_alloc_buffer_code >> qexistsl_tac [`buf`, `sz`, `tail`] >> simp[]) >>
  drule_then strip_assume_tac compile_alloc_buffer_insts >>
  drule_all (INST_TYPE [beta |-> alpha] alloc_buffer_origin_ptr_path_with_raw_endpoint) >>
  disch_then (qspecl_then [`tnE`, `explicit`, `PG`, `GE`]
    (qx_choosel_then [`q`, `w`, `sA`, `GA`, `tnA`, `r`] strip_assume_tac)) >>
  `q = p` by fs[] >> qpat_x_assum `q = p` SUBST_ALL_TAC >>
  `exec_alloca (mk_inst st.cs_next_id ALLOCA [Lit (n2w sz)] [p]) s (n2w sz : bytes32) = OK r` by
    (qpat_x_assum `run_inst_seq _ _ = OK r` mp_tac >>
     simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND,
          run_inst_seq_def, step_inst_base_def, mk_inst_def, AllCaseEqs()]) >>
  `sA.vs_memory = s.vs_memory /\ sA.vs_call_ctx = s.vs_call_ctx /\
   sA.vs_accounts = s.vs_accounts /\ sA.vs_transient = s.vs_transient /\
   sA.vs_immutables = s.vs_immutables /\ sA.vs_data_section = s.vs_data_section /\
   ~sA.vs_halted` by
    (qpat_assum `~s.vs_halted` mp_tac >>
     qpat_assum `(sA with <|vs_vars := _; vs_allocas := _;
                           vs_alloca_next := _; vs_inst_idx := _|>) = s`
       (SUBST1_TAC o SYM) >> simp[]) >>
  `r.vs_memory = s.vs_memory /\ r.vs_data_section = s.vs_data_section` by gvs[] >>
  `!i. i IN tnA.t_mem /\ i < s.vs_alloca_next ==> i IN tnE.t_mem` by
    (qpat_assum `!i. i IN tnA.t_mem <=> _` (fn th => rewrite_tac[th]) >>
     rpt strip_tac >> decide_tac) >>
  `!x. not_fresh_at sa x ==> not_fresh_at st x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `(!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at st x) /\
   (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at st x)` by
    fs[ret_pc_ok_def] >>
  `!H. valid_horizon cx st0 H ea.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ea sA /\
       immutable_frame_mods func cenv cx ea sA /\
       storage_well_formed_on cx ea (FST H) /\
       ghost_inv_at_mods (DF H) lo d cenv cx ea GA tnA sA` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon cx st0 H ea.storage_trace ==> stmt_state_rel _ _ _ _ _ _ s /\ _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
     conj_tac >- (qpat_assum `!H. stmt_state_rel H ctx func cenv cx ea s ==> _`
       irule >> first_assum ACCEPT_TAC) >>
     conj_tac >- (irule range_alloc_immutable_mods >>
       qpat_assum `exec_alloca _ s _ = OK r` (irule_at Any) >>
       qexistsl_tac [`st`, `LENGTH cut.cs_current_insts`] >>
       simp[] >> first_assum ACCEPT_TAC) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
     irule range_alloc_ghost_mods >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`GE`, `func`, `s`, `st`, `tnE`] >> simp[] >>
     rpt strip_tac >> decide_tac) >>
  `ret_pc_ok cenv sa sA /\ return_buf_frame d cenv st sA` by
    (conj_tac >- (drule ret_pc_ok_frame >> disch_then irule >> simp[]) >>
     drule return_buf_frame_frame >> disch_then irule >> simp[]) >>
  `return_buf_sep d cenv ea sA` by
    (irule range_alloc_return_sep >>
     qpat_assum `exec_alloca _ s _ = OK r` (irule_at Any) >>
     qpat_assum `sA = r with vs_inst_idx := _` (irule_at Any) >>
     qpat_assum `local_ptrs_reserved cenv st` (irule_at Any) >> simp[]) >>
  `alloca_frame cenv ea st s cenv ea sA` by
    (irule (INST_TYPE [alpha |-> ``:256``] alloca_frame_of_mem_frame) >>
     qpat_assum `stmt_state_rel (storage_trace_horizon _) _ _ _ _ _ s` (irule_at Any) >>
     simp[]) >>
  `alloca_frame cenv es sa s0 cenv ea sA` by
    (irule alloca_frame_trans >>
     qpat_assum `alloca_frame cenv ea st s cenv ea sA` (irule_at Any) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!aid off z. FLOOKUP s.vs_allocas aid = SOME (off,z) ==> off + z <= s.vs_alloca_next` by
    (drule stmt_state_rel_local_ptrs_alloca >>
     simp[alloca_inv_def, alloca_next_valid_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp sA` by
    (qpat_assum `!H. stmt_state_rel H ctx func cenv cx ea s ==> _`
       (drule_then assume_tac) >>
     qpat_assum `stmt_state_rel (storage_trace_horizon _) _ _ _ _ _ sA`
       (mp_then Any ACCEPT_TAC stmt_state_rel_allocas_below_fmp)) >>
  qpat_x_assum `sA = r with vs_inst_idx := _` kall_tac >>
  qpat_x_assum `GA = step_prov _ _ _ r` kall_tac >>
  qpat_x_assum `tnA = step_taint _ s r tnE` kall_tac >>
  qpat_x_assum `!i. i IN tnA.t_mem <=> _` kall_tac >>
  qexistsl_tac [`w`, `sA`, `GA`, `tnA`] >> rpt conj_tac >>
  TRY (first_assum ACCEPT_TAC) >> simp[] >>
  TRY (first_assum ACCEPT_TAC)
  >- (qpat_assum `allocas_from lo sA` (irule o REWRITE_RULE[allocas_from_def]) >>
      qexistsl_tac [`st.cs_next_id`, `sz`] >> first_assum ACCEPT_TAC)
  >> rpt gen_tac >> strip_tac >>
  `FLOOKUP s.vs_allocas aid = SOME (off,z)` by simp[] >>
  `off + z <= s.vs_alloca_next` by
    (qpat_assum `!aid off z. FLOOKUP s.vs_allocas aid = _ ==> _`
       (drule_then ACCEPT_TAC)) >>
  `i < s.vs_alloca_next` by decide_tac >>
  `i IN tnE.t_mem` by
    (qpat_assum `!i. i IN tnA.t_mem /\ _ ==> _` irule >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `!aid off z i. _ ==> i IN tn0.t_mem`
    (qspecl_then [`aid`, `off`, `z`, `i`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED
