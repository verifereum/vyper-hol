(* Frame a supplied encoder phase, without changing its chosen endpoint. *)
Theory bodyAbiEncodeRegisteredFrameMods
Ancestors
  bodyFullExtCallDirectWindows bodyFullExtCallEncoderStmtFrame
  bodyFullPathHistory bodyMethodIdScratchFrameMods bodyFullAbiEncodeOriginFloor
  abiDecodeStaticProps
  bodyPtrBytestringBuiltinsWindowGhost bodyFullPostsMods bodyFullShadowBodyInv bodyInvSplit
  abiEncoderWindowPhase abiEncoderWindowContract abiEncoderRegisteredEffect
  exprSimAbiEncodeExecFrame exprSimAbiEncodeFrameTransfer exprLoweringProps
  ctorDeployMemoryRunMemEntryLiteralPath[qualified,ignore_grammar]
  fragGasOriginPtr fragGasOrigin fragGasMode allocationGrowth
  exprSimProps stateRelProj loweringSlice loweringStateRelDefs loweringPosts
  bodyPtrDefs compileEnv freshWrites ptrDiscipline valueEncodingDefs
  memoryReadProps venomState venomInst vyperContext
  finite_map pred_set list alist words arithmetic pair

Theorem registered_encoder_pure[local]:
  abi_encoder_registered_effect ids outs s t /\
  FLOOKUP s.vs_allocas owner = SOME (owner_base,cap) /\
  EVERY (\(p,n). owner_base <= p /\ p+n <= owner_base+cap) outs /\
  (!id. id IN owner INSERT ids ==>
    ?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      inst.inst_id = id /\ front.cs_next_id <= id) /\
  (!name p n. local_region ce ee.scopes s name p n ==>
    mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory) ==>
  pure_frame ce func ee front s t
Proof
  strip_tac >> rewrite_tac[pure_frame_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> disch_tac >>
  rename1 `mem_bytes_at off len t.vs_memory = _` >>
  `!id p n. id IN owner INSERT ids /\ FLOOKUP t.vs_allocas id = SOME (p,n) ==>
    off+len <= p \/ p+n <= off` by
    (rpt strip_tac >>
     qpat_assum `!id. id IN owner INSERT ids ==> _` (drule_then strip_assume_tac) >>
     qpat_assum `!inst p n. _ ==> loweringStateRelDefs$regions_disjoint off len p n`
       (qspecl_then [`inst`,`p`,`n`] mp_tac) >>
     asm_simp_tac (srw_ss()) [loweringStateRelDefsTheory.regions_disjoint_def]) >>
  `FLOOKUP t.vs_allocas owner = SOME (owner_base,cap)` by
    (irule abi_encoder_registered_effect_allocated >> qexistsl [`ids`,`outs`,`s`] >> simp[]) >>
  `off+len <= owner_base \/ owner_base+cap <= off` by metis_tac[IN_INSERT] >>
  `EVERY (\(p,n). off+len <= p \/ p+n <= off) outs` by
    (qpat_assum `EVERY _ outs` mp_tac >>
     simp_tac (srw_ss()) [EVERY_MEM, FORALL_PROD] >> rpt strip_tac >>
     first_x_assum drule >> decide_tac) >>
  `!id p n. id IN ids /\ FLOOKUP t.vs_allocas id = SOME (p,n) ==>
    off+len <= p \/ p+n <= off` by metis_tac[IN_INSERT] >>
  irule mem_bytes_at_bytewise >> rpt strip_tac >>
  irule abi_encode_registered_protected_byte >> qexistsl [`ids`,`off`,`len`,`outs`] >>
  asm_rewrite_tac[]
QED

(* Only existing bindings need to be preserved by the execution. Absence of
   arbitrary old variables is not part of the encoder's physical contract. *)
Theorem registered_encoder_linked_ghost[local]:
  ghost_inv_at_mods D lo d ce cx ee G tn s /\
  local_ptrs_rel func ce ee.scopes s /\ local_ptrs_reserved ce front /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at front x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at front x) /\
  (!x w. not_fresh_at front x /\ lookup_var x s = SOME w ==> lookup_var x t = SOME w) /\
  (!x. not_fresh_at front x ==> FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)) /\
  (!name p n. local_region ce ee.scopes s name p n ==>
    mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory /\
    (!i. p <= i /\ i < p+n /\ i IN tn'.t_mem ==> i IN tn.t_mem)) /\
  mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory /\
  (!i. i < lo /\ i IN tn'.t_mem ==> i IN tn.t_mem) /\
  stor_taint_ok_at D tn' t /\ allocas_from lo t /\ lo <= t.vs_alloca_next ==>
  ghost_inv_at_mods D lo d ce cx ee G' tn' t
Proof
  strip_tac >>
  drule_then assume_tac method_id_ghost_at_zero >>
  `ghost_inv_at D 0 d ce cx ee G' tn' t` by
    (irule ghost_inv_at_local_window_transport >>
     qpat_assum `ghost_inv_at D 0 d ce cx ee G tn s` (irule_at Any) >>
     qpat_assum `local_ptrs_rel func ce ee.scopes s` (irule_at Any) >>
     qpat_assum `local_ptrs_reserved ce front` (irule_at Any) >>
     asm_rewrite_tac[] >> simp[allocas_from_def, mem_bytes_at_def]) >>
  qpat_x_assum `ghost_inv_at D 0 _ _ _ _ _ _ t`
    (strip_assume_tac o REWRITE_RULE[ghost_inv_at_def]) >>
  qpat_x_assum `ghost_inv_at_mods D lo _ _ _ _ _ _ s`
    (strip_assume_tac o REWRITE_RULE[ghost_inv_at_mods_def]) >>
  rewrite_tac[ghost_inv_at_mods_def] >> rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac
  >- (rpt strip_tac >> asm_rewrite_tac[] >>
      qpat_assum `!i. i < lo /\ i IN tn.t_mem ==> _` irule >> simp[]) >>
  conj_tac
  >- (qx_gen_tac `x` >> strip_tac >>
      `not_fresh_at front x` by (irule local_ptrs_reserved_imm_base >> qexists_tac `ce` >> asm_rewrite_tac[]) >>
      qpat_assum `!x. not_fresh_at front x ==> _` (drule_then strip_assume_tac) >>
      qpat_assum `!x. lo <> 0 /\ ce.ce_imm_alloca = SOME (Var x) ==> _`
        (drule_all_then strip_assume_tac) >> asm_rewrite_tac[]) >>
  asm_rewrite_tac[]
QED

Theorem registered_encoder_immutable[local]:
  immutable_frame_mods func ce cx ee s /\
  (!name b n. local_region ce ee.scopes t name b n ==>
     local_region ce ee.scopes s name b n) /\
  t.vs_data_section = s.vs_data_section /\ LENGTH s.vs_memory <= LENGTH t.vs_memory /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  (!aid b n. FLOOKUP t.vs_allocas aid = SOME (b,n) ==>
     FLOOKUP s.vs_allocas aid = SOME (b,n) \/ s.vs_alloca_next <= b) /\
  pure_frame ce func ee front s t ==>
  immutable_frame_mods func ce cx ee t
Proof
  strip_tac >>
  `!src m id b n. local_region (ce with ce_module := src) ee.scopes m id b n =
                  local_region ce ee.scopes m id b n` by simp[local_region_def] >>
  `immutable_alloca_sep_mods func ce cx ee t` by
    (fs[immutable_frame_mods_def, immutable_alloca_sep_mods_def] >>
     rpt strip_tac >>
     irule immutable_alloca_sep_frame >> qexistsl [`s`,`ee`] >>
     asm_rewrite_tac[] >> conj_tac
     >- (rpt strip_tac >> disj1_tac >> qexists_tac `id` >>
         first_x_assum drule >> simp[]) >>
     first_assum drule >> simp[]) >>
  fs[immutable_frame_mods_def, immutables_rel_mods_def] >>
  rpt gen_tac >> disch_tac >>
  irule immutables_rel_mem_agree >> qexists_tac `s` >>
  asm_rewrite_tac[] >> reverse conj_tac
  >- (qpat_assum `!src tops. _ ==> immutables_rel _ _ _ _ _ s` (drule_then ACCEPT_TAC)) >>
  disch_tac >> rpt gen_tac >> strip_tac >> fs[pure_frame_def] >>
  qpat_assum `!off len. _` irule >>
  `immutable_alloca_sep func (ce with ce_module := src) cx ee t` by
    (fs[immutable_alloca_sep_mods_def] >> first_assum drule >> simp[]) >>
  fs[immutable_alloca_sep_def] >> metis_tac[]
QED

Theorem abi_encode_registered_phase_frame_mods:
  window_phase ctx func st en ids outs s t /\
  abi_encode_exec_frame func s t /\
  fn_inst_ids_distinct func /\ alloca_history func s /\
  local_ptrs_reserved ce front /\ front.cs_next_var <= st.cs_next_var /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at front x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at front x) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G tn s /\
    immutable_frame_mods func ce cx ee s) /\
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
    ghost_inv_at_mods (DF H) lo d ce cx ee G' tn' t /\
    immutable_frame_mods func ce cx ee t) /\
  wb_frame ce ee ee front s t /\ ghost_kept_at lo ce ee front G tn s G' tn' /\
  alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
  ~t.vs_halted /\ t.vs_current_bb = en.cs_current_bb /\
  t.vs_inst_idx = LENGTH en.cs_current_insts /\
  (!x. not_fresh_at st x ==>
    (!w. lookup_var x s = SOME w ==> lookup_var x t = SOME w) /\
    FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
  (!aid row. FLOOKUP s.vs_allocas aid = SOME row ==> FLOOKUP t.vs_allocas aid = SOME row)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_then strip_assume_tac window_phase_resources >>
  drule_then strip_assume_tac window_phase_control >>
  drule_then assume_tac window_phase_labels >>
  drule_then assume_tac window_phase_effect >>
  `!aid row. FLOOKUP s.vs_allocas aid = SOME row ==> FLOOKUP t.vs_allocas aid = SOME row` by
    (rpt strip_tac >> drule_all_then ACCEPT_TAC abi_encoder_registered_effect_allocated) >>
  qpat_x_assum `window_alloca_growth s t`
    (strip_assume_tac o REWRITE_RULE[window_alloca_growth_def]) >>
  `allocation_growth s t` by
    (rewrite_tac[allocation_growth_def] >> asm_rewrite_tac[] >>
     metis_tac[]) >>
  `!aid p n. FLOOKUP t.vs_allocas aid = SOME (p,n) ==>
    FLOOKUP s.vs_allocas aid = SOME (p,n) \/ s.vs_alloca_next <= p` by
    (rpt strip_tac >> Cases_on `FLOOKUP s.vs_allocas aid`
     >- (disj2_tac >>
         qpat_assum `!i b sz. FLOOKUP s.vs_allocas i = NONE /\ _ ==> _`
           (drule_all_then ACCEPT_TAC)) >>
     disj1_tac >>
     qpat_assum `!aid row. FLOOKUP s.vs_allocas aid = SOME row ==> _`
       (drule_then assume_tac) >> gvs[]) >>
  `!x. not_fresh_at front x ==> not_fresh_at st x` by metis_tac[not_fresh_at_mono] >>
  `!x w. not_fresh_at front x /\ lookup_var x s = SOME w ==> lookup_var x t = SOME w` by
    (rpt strip_tac >>
     `not_fresh_at st x` by (first_x_assum irule >> first_assum ACCEPT_TAC) >>
     drule_all_then ACCEPT_TAC window_phase_vars) >>
  `!x. not_fresh_at front x ==> FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!x. not_fresh_at front x ==> _` (drule_then assume_tac) >>
     qpat_assum `!x. not_fresh_at st x ==> FLOOKUP G' x = _ /\ _`
       (drule_then ACCEPT_TAC)) >>
  `t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
   t.vs_call_ctx = s.vs_call_ctx /\ t.vs_immutables = s.vs_immutables /\
   t.vs_data_section = s.vs_data_section /\ LENGTH s.vs_memory <= LENGTH t.vs_memory` by
    fs[abi_encoder_registered_effect_def, abi_encode_exec_frame_def] >>
  `gas_origin_ptr_path (DF (ARB:(bool # bytes32 # type_value) list # num list),lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK t,G',tn')` by simp[] >>
  `gas_path_mem ctx func s 0 (OK t)` by
    (drule_then strip_assume_tac gas_origin_ptr_path_projections >>
     drule_then mp_tac gas_origin_path_erase >> simp[gas_marked_path_def]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee t /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at_mods (DF H) lo d ce cx ee G' tn' t /\ immutable_frame_mods func ce cx ee t /\
    wb_frame ce ee ee front s t /\ ghost_kept_at lo ce ee front G tn s G' tn' /\
    alloca_history func t /\ pure_frame ce func ee front s t` by
    (qx_gen_tac `hz` >> disch_tac >>
     qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
       (drule_then strip_assume_tac) >>
     `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
     qpat_assum `window_phase ctx func st en ids outs s t`
       (mp_then (Pos hd) (mp_tac o SPEC_ALL)
         (Q.INST [`p` |-> `b`,`cut` |-> `(front:compile_state).cs_next_id`,`H` |-> `hz`]
           extcall_direct_encode_windows)) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> strip_tac >>
     drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
     `!name p n. local_region ce ee.scopes s name p n ==>
       mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory /\
       (!i. p <= i /\ i < p+n /\ i IN tn'.t_mem ==> i IN tn.t_mem)` by
       (rpt gen_tac >> disch_tac >>
        qpat_assum `!p n. p = 0 /\ _ \/ _ ==> _`
          (qspecl_then [`p`,`n`] mp_tac) >> metis_tac[]) >>
     `!aid p n. FLOOKUP s.vs_allocas aid = SOME (p,n) /\ aid < front.cs_next_id ==>
       mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory /\
       (!i. p <= i /\ i < p+n /\ i IN tn'.t_mem ==> i IN tn.t_mem)` by
       (rpt gen_tac >> disch_tac >>
        qpat_assum `!p n. p = 0 /\ _ \/ _ ==> _`
          (qspecl_then [`p`,`n`] mp_tac) >> metis_tac[]) >>
     `mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory /\
       (!i. i < lo /\ i IN tn'.t_mem ==> i IN tn.t_mem)` by
       (qpat_assum `!p n. p = 0 /\ _ \/ _ ==> _` (qspecl_then [`0`,`lo`] mp_tac) >> simp[]) >>
     `pure_frame ce func ee front s t` by
       (irule registered_encoder_pure >>
        qpat_assum `abi_encoder_registered_effect ids outs s t` (irule_at Any) >>
        qpat_assum `FLOOKUP s.vs_allocas shared = SOME (b,cap)` (irule_at Any) >>
        asm_rewrite_tac[] >> conj_tac
        >- (rpt strip_tac >>
            qpat_assum `!name p n. local_region ce _ s name p n ==> _ /\ _`
              (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
        gen_tac >> disch_tac >>
        qpat_assum `!aid. aid IN shared INSERT ids ==> _` (drule_then strip_assume_tac) >>
        qexists_tac `inst` >> fs[IN_INSERT] >> metis_tac[]) >>
     `!inst n p sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
       inst.inst_operands = [Lit n] /\ FLOOKUP t.vs_allocas inst.inst_id = SOME (p,sz) ==>
       sz = w2n n` by
       (drule_then assume_tac stmt_state_rel_alloca_size >>
        drule ctorDeployMemoryRunMemEntryLiteralPathTheory.ctor_path_literal_sizes >>
        disch_then (qspec_then `t` mp_tac) >> asm_rewrite_tac[]) >>
     `stmt_state_rel hz ctx func ce cx ee t` by
       (irule extcall_encoder_stmt_frame >>
        qpat_assum `abi_encoder_registered_effect ids outs s t` (irule_at Any) >>
        qexists_tac `front` >> asm_rewrite_tac[] >>
        rpt conj_tac >> rpt strip_tac >> metis_tac[]) >>
     `stor_taint_ok_at (DF hz) tn' t` by
       (qpat_assum `ghost_inv_at_mods (DF hz) lo _ _ _ _ _ _ _`
         (mp_tac o MATCH_MP (cj 4 (iffLR ghost_inv_at_mods_def))) >>
        simp[stor_taint_ok_at_def]) >>
     `allocas_from lo t /\ lo <= t.vs_alloca_next` by
       (drule_all_then ACCEPT_TAC abi_encode_origin_path_allocas_from) >>
     `ghost_inv_at_mods (DF hz) lo d ce cx ee G' tn' t` by
       (irule registered_encoder_linked_ghost >>
        qpat_assum `ghost_inv_at_mods (DF hz) lo d ce cx ee G tn s` (irule_at Any) >>
        qpat_assum `local_ptrs_rel func ce ee.scopes s` (irule_at Any) >>
        qpat_assum `local_ptrs_reserved ce front` (irule_at Any) >>
        asm_rewrite_tac[]) >>
     `immutable_frame_mods func ce cx ee t` by
       (irule registered_encoder_immutable >>
        qpat_assum `pure_frame ce func ee front s t` (irule_at Any) >>
        asm_rewrite_tac[] >> rpt strip_tac >>
        irule local_region_frame >>
        qpat_assum `local_ptrs_rel func ce ee.scopes s` (irule_at Any) >>
        qpat_assum `local_ptrs_reserved ce front` (irule_at Any) >>
        qpat_assum `local_region ce ee.scopes t _ _ _` (irule_at Any) >> simp[]) >>
     `wb_frame ce ee ee front s t` by
       (simp[wb_frame_def] >> conj_tac
        >- (rpt strip_tac >>
            qpat_assum `!aid p n. FLOOKUP s.vs_allocas aid = SOME (p,n) /\ _ ==> _ /\ _`
              (drule_all_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
        irule locals_kept_regions >> rpt strip_tac >>
        qpat_assum `!name p n. local_region ce _ s name p n ==> _ /\ _`
          (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
     `ghost_kept_at lo ce ee front G tn s G' tn'` by
       (rewrite_tac[ghost_kept_at_def] >> rpt conj_tac >> rpt strip_tac >>
        first_x_assum drule_all >> simp[]) >>
     `alloca_history func t` by drule_all_then ACCEPT_TAC body_full_path_alloca_history >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `?H. valid_horizon cx st0 H ee.storage_trace`
    (qx_choose_then `hz` assume_tac) >>
  qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H _ _ _ _ _ t /\ _`
    (drule_then strip_assume_tac) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >>
      qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> stmt_state_rel H _ _ _ _ _ t /\ _`
        (drule_then strip_assume_tac) >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >> conj_tac
  >- (gen_tac >> disch_tac >>
      qpat_assum `!x. not_fresh_at st x ==> FLOOKUP G' x = _ /\ _`
        (drule_then strip_assume_tac) >>
      asm_rewrite_tac[] >> rpt strip_tac >> drule_all_then ACCEPT_TAC window_phase_vars) >>
  first_assum ACCEPT_TAC
QED
