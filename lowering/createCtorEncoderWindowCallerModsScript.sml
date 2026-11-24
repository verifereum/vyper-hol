Theory createCtorEncoderWindowCallerMods
Ancestors
  bodyFullExtCallDirectWindows bodyFullExtCallEncoderStmtFrame
  bodyFullShadowBodyInv bodyPtrBytestringBuiltinsWindowGhost exprSimProps
  abiDecodeStaticProps exprSimAbiEncodeFrameTransfer freshWrites pair
  abiEncoderWindowPhase abiEncoderWindowContract abiEncoderRegisteredEffect
  bodyFullAbiEncodeOriginFloor bodyFullPathHistory
  exprSimAbiEncodeExecFrame exprSimAbiEncodeSemantic
  allocationGrowth stateRelProj bodyPtrDefs loweringStateRelDefs loweringPosts
  fragGasOriginPtr fragGasOrigin fragGasMode
  ctorDeployMemoryRunMemEntryLiteralPath[qualified,ignore_grammar]
  compileEnv ptrDiscipline vyperContext vyperValue valueEncodingDefs venomState venomInst
  finite_map pred_set list alist words

(* Ghost transport uses only the protected local windows and low prefix.
   The linked immutable dead-byte predicate is carried at the same bytes. *)
Theorem encoder_ghost_window_mods[local]:
  ghost_inv_at_mods D lo d cenv cx es G tn s /\ local_ptrs_rel fn cenv es.scopes s /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
    lookup_var x s' = SOME w) /\
  (!x. not_fresh_at sa x ==> FLOOKUP HG x = FLOOKUP G x /\
    op_taint tm (Var x) = op_taint tn (Var x)) /\
  (!name b len. local_region cenv es.scopes s name b len ==>
    mem_bytes_at b len s'.vs_memory = mem_bytes_at b len s.vs_memory /\
    (!i. b <= i /\ i < b+len /\ i IN tm.t_mem ==> i IN tn.t_mem)) /\
  stor_taint_ok_at D tm s' /\
  mem_bytes_at 0 lo s'.vs_memory = mem_bytes_at 0 lo s.vs_memory /\
  (!i. i < lo /\ i IN tm.t_mem ==> i IN tn.t_mem) /\
  allocas_from lo s' /\ lo <= s'.vs_alloca_next ==>
  ghost_inv_at_mods D lo d cenv cx es HG tm s'
Proof
  strip_tac >>
  `!x sz. not_fresh_at sa x /\ ptr_covers G tn x s sz ==>
    ptr_covers HG tm x s' sz` by
    (rw[ptr_covers_def] >> metis_tac[]) >>
  fs[ghost_inv_at_mods_def] >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
      conj_tac >- metis_tac[] >>
      rpt gen_tac >> strip_tac >>
      `ptr_covers G tn p s sz` by metis_tac[] >>
      `?w0. lookup_var p s = SOME w0` by fs[ptr_covers_def] >>
      `lookup_var p s = SOME w` by metis_tac[] >>
      `val_wf entry.type entry.value /\ type_memory_size entry.type <= sz` by
        (fs[local_ptrs_rel_def] >> metis_tac[]) >>
      `val_footprint entry.type entry.value <= sz` by
        (drule val_footprint_le >> decide_tac) >>
      `local_region cenv es.scopes s name (w2n w) sz` by
        (simp[local_region_def] >> metis_tac[]) >>
      qpat_x_assum `!name b len. local_region _ _ _ _ _ _ ==> _` drule >> strip_tac >>
      `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
        val_in_memory entry.type entry.value (w2n w) m` by metis_tac[] >>
      drule_all robust_val_in_memory_window_transport >> simp[])
  >- (Cases_on `d` >> fs[return_buf_ptr_def] >>
      rename1 `return_buf_ptr (SOME bc)` >> PairCases_on `bc` >>
      fs[return_buf_ptr_def] >> metis_tac[]) >>
  metis_tac[local_ptrs_reserved_def]
QED

Theorem encoder_registered_pure_frame[local]:
  abi_encoder_registered_effect ids outs u v /\
  FLOOKUP u.vs_allocas owner = SOME (b,cap) /\
  EVERY (\(p,n). b <= p /\ p+n <= b+cap) outs /\
  (!id. id IN owner INSERT ids ==>
    ?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id = id /\ cut.cs_next_id <= id) /\
  (!name p n. local_region ce ee.scopes u name p n ==>
    mem_bytes_at p n v.vs_memory = mem_bytes_at p n u.vs_memory) ==>
  pure_frame ce func ee cut u v
Proof
  strip_tac >> rewrite_tac[pure_frame_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> disch_tac >>
  rename1 `mem_bytes_at off len v.vs_memory = _` >>
  `!id p n. id IN owner INSERT ids /\ FLOOKUP v.vs_allocas id = SOME (p,n) ==>
    off+len <= p \/ p+n <= off` by
    (rpt strip_tac >>
     qpat_assum `!id. id IN owner INSERT ids ==> _` (drule_then strip_assume_tac) >>
     qpat_assum `!inst p n. _ ==> loweringStateRelDefs$regions_disjoint off len p n`
       (qspecl_then [`inst`,`p`,`n`] mp_tac) >>
     asm_simp_tac (srw_ss()) [loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
  `FLOOKUP v.vs_allocas owner = SOME (b,cap)` by metis_tac[abi_encoder_registered_effect_allocated] >>
  `off+len <= b \/ b+cap <= off` by metis_tac[IN_INSERT] >>
  `EVERY (\(p,n). off+len <= p \/ p+n <= off) outs` by
    (qpat_assum `EVERY _ outs` mp_tac >>
     simp_tac (srw_ss()) [EVERY_MEM, FORALL_PROD] >> rpt strip_tac >>
     first_x_assum drule >> decide_tac) >>
  `!id p n. id IN ids /\ FLOOKUP v.vs_allocas id = SOME (p,n) ==>
    off+len <= p \/ p+n <= off` by metis_tac[IN_INSERT] >>
  irule mem_bytes_at_bytewise >> rpt strip_tac >>
  mp_tac (Q.INST [`s` |-> `u`,`t` |-> `v`,`lo` |-> `off`,`n` |-> `len`,
    `a` |-> `i`] abi_encode_registered_protected_byte) >>
  asm_rewrite_tac[]
QED

Theorem encoder_phase_frame_mods[local]:
  window_phase ctx func st en ids outs s t /\
  abi_encode_exec_frame func s t /\
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func ce cx ee s /\
  ghost_inv_at_mods D lo d ce cx ee G tn s /\
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn') /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ local_ptrs_reserved ce cut /\
  cut.cs_next_var <= st.cs_next_var /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at cut x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at cut x) /\
  (!x. not_fresh_at st x ==>
     FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  (!b n.
     ((b = 0 /\ n = lo) \/
      (?name. local_region ce ee.scopes s name b n) \/
      (?site. FLOOKUP s.vs_allocas site = SOME (b,n) /\ site < cut.cs_next_id)) ==>
     mem_bytes_at b n t.vs_memory = mem_bytes_at b n s.vs_memory /\
     (!i. b <= i /\ i < b+n /\ i IN tn'.t_mem ==> i IN tn.t_mem)) /\
  (ce.ce_is_ctor ==> !name tv v off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    mem_bytes_at off (type_memory_size tv) t.vs_memory =
    mem_bytes_at off (type_memory_size tv) s.vs_memory) ==>
  stmt_state_rel H ctx func ce cx ee t /\ ghost_inv_at_mods D lo d ce cx ee G' tn' t /\
  wb_frame ce ee ee cut s t /\ ghost_kept_at lo ce ee cut G tn s G' tn' /\
  alloca_history func t
Proof
  strip_tac >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  drule_then strip_assume_tac window_phase_resources >>
  drule_then assume_tac window_phase_effect >>
  drule_then assume_tac window_phase_labels >>
  `!i r. FLOOKUP s.vs_allocas i = SOME r ==> FLOOKUP t.vs_allocas i = SOME r` by
    metis_tac[abi_encoder_registered_effect_allocated] >>
  `allocation_growth s t` by
    (fs[allocation_growth_def, window_alloca_growth_def] >> metis_tac[]) >>
  `!x w. not_fresh_at cut x /\ lookup_var x s = SOME w ==> lookup_var x t = SOME w` by
    metis_tac[window_phase_vars, not_fresh_at_mono] >>
  `!x. not_fresh_at cut x ==>
    FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)` by
    metis_tac[not_fresh_at_mono] >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  drule_all abi_encode_origin_path_allocas_from >> strip_tac >>
  `stor_taint_ok_at D tn' t` by
    (qpat_assum `ghost_inv_at_mods D _ _ _ _ _ _ _ _`
       (mp_tac o cj 4 o REWRITE_RULE [ghost_inv_at_mods_def]) >>
     qpat_assum `abi_encode_exec_frame func s t`
       (strip_assume_tac o REWRITE_RULE [abi_encode_exec_frame_def, abi_encode_semantic_obs_fields]) >>
     qpat_assum `abi_encoder_registered_effect ids outs s t`
       (strip_assume_tac o REWRITE_RULE [abi_encoder_registered_effect_def]) >>
     simp[stor_taint_ok_at_def]) >>
  `gas_path_mem ctx func s 0 (OK t)` by
    (qpat_assum `gas_origin_ptr_path _ (s,G,tn) [] (OK t,G',tn')`
       (mp_tac o MATCH_MP gas_origin_ptr_path_projections) >>
     disch_then (mp_tac o MATCH_MP gas_origin_path_erase o cj 1) >>
     simp[gas_marked_path_def]) >>
  `!inst n b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
     inst.inst_operands = [Lit n] /\ FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) ==>
     sz = w2n n` by
    (drule_then assume_tac stmt_state_rel_alloca_size >>
     drule ctorDeployMemoryRunMemEntryLiteralPathTheory.ctor_path_literal_sizes >>
     disch_then (qspec_then `t` mp_tac) >> asm_rewrite_tac[]) >>
  `!name b n. local_region ce ee.scopes s name b n ==>
    mem_bytes_at b n t.vs_memory = mem_bytes_at b n s.vs_memory /\
    (!i. b <= i /\ i < b+n /\ i IN tn'.t_mem ==> i IN tn.t_mem)` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!b n. (b = 0 /\ _ \/ _) ==> _`
       (qspecl_then [`b`,`n`] mp_tac) >> metis_tac[]) >>
  `!aid b n. FLOOKUP s.vs_allocas aid = SOME (b,n) /\ aid < cut.cs_next_id ==>
    mem_bytes_at b n t.vs_memory = mem_bytes_at b n s.vs_memory /\
    (!i. b <= i /\ i < b+n /\ i IN tn'.t_mem ==> i IN tn.t_mem)` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!b n. (b = 0 /\ _ \/ _) ==> _`
       (qspecl_then [`b`,`n`] mp_tac) >> metis_tac[]) >>
  `mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory /\
    (!i. i < lo /\ i IN tn'.t_mem ==> i IN tn.t_mem)` by
    (qpat_assum `!b n. (b = 0 /\ _ \/ _) ==> _`
       (qspecl_then [`0`,`lo`] mp_tac) >> simp[]) >>
  conj_tac
  >- (match_mp_tac (Q.INST [`q` |-> `s`,`st` |-> `cut`,
        `ids` |-> `ids`,`outs` |-> `outs`] extcall_encoder_stmt_frame) >>
      asm_rewrite_tac[] >>
      rpt conj_tac >> rpt gen_tac >> strip_tac >> metis_tac[]) >>
  conj_tac
  >- (qpat_assum `ghost_inv_at_mods D lo d ce cx ee G tn s`
        (mp_then Any irule encoder_ghost_window_mods) >>
      qpat_assum `local_ptrs_rel func ce ee.scopes s` (irule_at Any) >>
      qpat_assum `local_ptrs_reserved ce cut` (irule_at Any) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (simp[wb_frame_def] >> conj_tac
      >- (rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
      irule locals_kept_regions >> rpt strip_tac >> first_x_assum drule >> simp[]) >>
  conj_tac
  >- (simp[ghost_kept_at_def] >> rpt conj_tac >> rpt strip_tac >>
      first_x_assum drule_all >> simp[]) >>
  metis_tac[body_full_path_alloca_history]
QED

Theorem ctor_encoder_window_caller_mods:
  window_phase ctx func st en ids outs s t /\
  abi_encode_exec_frame func s t /\
  fn_inst_ids_distinct func /\ alloca_history func s /\
  local_ptrs_reserved ce front /\ front.cs_next_var <= st.cs_next_var /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at front x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at front x) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
  (!x. not_fresh_at st x ==>
    FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  FLOOKUP s.vs_allocas shared = SOME (b,cap) /\ front.cs_next_id <= shared /\
  (!aid. aid IN ids ==> front.cs_next_id <= aid) /\
  EVERY (\(p,n). b <= p /\ p+n <= b+cap) outs /\
  (!aid. aid IN shared INSERT ids ==>
    ?inst x. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id = aid /\ inst.inst_outputs = [x] /\ not_local_ptr ce ee.scopes x) /\
  (!i. EVERY (\(p,n). i < p \/ p+n <= i) outs /\
    (!aid p n. aid IN ids /\ FLOOKUP t.vs_allocas aid = SOME (p,n) ==>
      i < p \/ p+n <= i) /\ i IN tn'.t_mem ==> i IN tn.t_mem) ==>
  pure_frame ce func ee front s t /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee t /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G' tn' t) /\
  wb_frame ce ee ee front s t /\ ghost_kept_at lo ce ee front G tn s G' tn' /\
  alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
  ~t.vs_halted /\ t.vs_current_bb = en.cs_current_bb /\
  t.vs_inst_idx = LENGTH en.cs_current_insts /\
  (!x. not_fresh_at st x ==>
    (!w. lookup_var x s = SOME w ==> lookup_var x t = SOME w) /\
    FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee t /\ ghost_inv_at_mods (DF H) lo d ce cx ee G' tn' t /\
    wb_frame ce ee ee front s t /\ ghost_kept_at lo ce ee front G tn s G' tn' /\
    alloca_history func t /\ pure_frame ce func ee front s t` by
    (qx_gen_tac `hz` >> disch_tac >>
     qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
       (qspec_then `hz` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     strip_tac >>
     `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
     qpat_assum `window_phase ctx func st en ids outs s t`
       (mp_then (Pos hd) (mp_tac o SPEC_ALL)
         (Q.INST [`p` |-> `b`,`cut` |-> `(front:compile_state).cs_next_id`,`H` |-> `hz`]
           extcall_direct_encode_windows)) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
     strip_tac >>
     `pure_frame ce func ee front s t` by
       (`abi_encoder_registered_effect ids outs s t` by metis_tac[window_phase_effect] >>
        mp_tac (Q.INST [`u` |-> `s`, `v` |-> `t`, `owner` |-> `shared`,
          `cut` |-> `front`] encoder_registered_pure_frame) >>
        impl_tac >-
          (asm_rewrite_tac[] >> conj_tac
           >- (gen_tac >> disch_tac >>
               qpat_assum `!aid. aid IN shared INSERT ids ==> _`
                 (drule_then strip_assume_tac) >>
               qexists_tac `inst` >> fs[IN_INSERT] >> metis_tac[]) >>
           metis_tac[]) >>
        disch_then ACCEPT_TAC) >>
     qpat_assum `stmt_state_rel hz ctx func ce cx ee s`
       (mp_then (Pos (el 3)) (mp_tac o SPEC_ALL)
         (Q.INST [`H` |-> `hz`,`cut` |-> `front`,
           `D` |-> `(DF:((bool # bytes32 # type_value) list # num list) -> dead) hz`]
           (SPEC_ALL encoder_phase_frame_mods))) >>
     impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> metis_tac[]) >>
     strip_tac >> asm_rewrite_tac[]) >>
  qpat_x_assum `?H. valid_horizon cx st0 H ee.storage_trace`
    (qx_choose_then `hz` assume_tac) >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H _ _ _ _ _ t /\ _`
    (qspec_then `hz` (drule_then strip_assume_tac)) >>
  drule_then strip_assume_tac window_phase_control >>
  drule_then strip_assume_tac window_phase_resources >>
  drule_then assume_tac window_alloca_growth_frontier >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H _ _ _ _ _ s /\ _`
        (drule_then strip_assume_tac) >>
      qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H _ _ _ _ _ t /\ _`
        (drule_then strip_assume_tac) >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >- (qpat_assum `window_alloca_growth s t`
        (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [window_alloca_growth_def])) >>
  metis_tac[window_phase_vars]
QED
