(* Caller resources at the ABI payload cursor, on the selected setup run. *)
Theory bodyAbiEncodeSetupFrameMods
Ancestors
  bodyFullAllocaFresh bodyMethodIdScratchFrameMods bodyIfExpTypedGhostMods
  bodyIfExpTypedImmFrameMods bodyPtrMakeArrayCopyStateFrame
  bodyFullHashKeccakFixed[qualified,ignore_grammar] bodyFullUnwrapRun
  bodyMemoryDefs exprSimHash exprSimCopy exprSimProps abiBuiltinAllocation
  exprSimStorageCopy loweringPosts typedMemoryCopy loweringStateRelDefs bodyFullPostsMods bodyFullShadowBodyInv
  bodyInvSplit stateRelProj bodyPtrDefs compileEnv exprLoweringProps freshWrites loweringSlice
  vyperStorageFootprint ptrDiscipline venomInst venomMemDefs venomState
  finite_map words pred_set

Theorem setup_alloc_rows[local]:
  FLOOKUP (abi_builtin_allocate_state aid cap t).vs_allocas j = SOME (b,n) ==>
  FLOOKUP t.vs_allocas j = SOME (b,n) \/ t.vs_alloca_next <= b
Proof
  Cases_on `FLOOKUP t.vs_allocas aid` >>
  simp[abi_builtin_allocate_state_def] >> strip_tac >>
  Cases_on `j = aid` >> gvs[FLOOKUP_UPDATE]
QED

Theorem setup_alloc_immutable[local]:
  immutable_frame_mods func ce cx ee t /\
  u.vs_memory = t.vs_memory /\ u.vs_data_section = t.vs_data_section /\
  t.vs_alloca_next <= u.vs_alloca_next /\
  u.vs_allocas = (abi_builtin_allocate_state aid cap t).vs_allocas /\
  local_ptrs_reserved ce st /\
  (!x. not_fresh_at st x ==> lookup_var x u = lookup_var x t) ==>
  immutable_frame_mods func ce cx ee u
Proof
  simp[immutable_frame_mods_def] >> strip_tac >> conj_tac
  >- (fs[immutables_rel_mods_def, immutables_rel_def] >> first_assum ACCEPT_TAC) >>
  fs[immutable_alloca_sep_mods_def] >> rpt gen_tac >> disch_tac >>
  irule immutable_alloca_sep_frame >> qexistsl_tac [`t`,`ee`] >> simp[] >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >> disj1_tac >>
      rename1 `local_region _ _ u name b n` >> qexists_tac `name` >>
      fs[local_region_def, local_ptrs_reserved_def] >> metis_tac[]) >>
  rpt gen_tac >> disch_tac >> drule_then ACCEPT_TAC setup_alloc_rows
QED

Theorem setup_alloc_ghost[local]:
  ghost_inv_at_mods D lo d ce cx ee G tn t /\
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func ce cx ee t /\
  local_ptrs_reserved ce st /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x. not_fresh_at st x ==> lookup_var x u = lookup_var x t /\
       FLOOKUP Gu x = FLOOKUP G x /\ op_taint tu (Var x) = op_taint tn (Var x)) /\
  u with <|vs_vars := t.vs_vars; vs_allocas := t.vs_allocas;
           vs_alloca_next := t.vs_alloca_next; vs_inst_idx := t.vs_inst_idx|> = t /\
  allocas_from lo u /\ t.vs_alloca_next <= u.vs_alloca_next /\
  tu.t_stor = tn.t_stor /\ tu.t_trans = tn.t_trans /\ tu.t_imm = tn.t_imm /\
  (!i. i IN tu.t_mem <=> i IN tn.t_mem \/ (t.vs_alloca_next <= i /\ i < stop)) ==>
  ghost_inv_at_mods D lo d ce cx ee Gu tu u
Proof
  strip_tac >>
  `ghost_inv_at D 0 d ce cx ee G tn t` by drule_then ACCEPT_TAC method_id_ghost_at_zero >>
  `ghost_inv_at D 0 d ce cx ee Gu tu u` by
    (irule (INST_TYPE [alpha |-> ``:256``] alloc_buffer_ghost_inv_at) >>
     conj_tac >- simp[allocas_from_def] >>
     qexistsl_tac [`G`,`H`,`ctx`,`stop`,`func`,`t`,`st`,`tn`] >> simp[]) >>
  `u.vs_memory = t.vs_memory` by
    (qpat_assum `u with <|vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _|> = t` (SUBST1_TAC o SYM) >> simp[]) >>
  `lo <= t.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `!i. i < lo /\ i IN tu.t_mem ==> i IN tn.t_mem` by (simp[] >> decide_tac) >>
  fs[ghost_inv_at_mods_def, ghost_inv_at_def] >> rpt conj_tac
  >- metis_tac[]
  >- (rpt strip_tac >> drule_all local_ptrs_reserved_imm_base >> metis_tac[]) >>
  decide_tac
QED

Theorem abi_encode_setup_frame_mods:
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_state_rel H ctx func ce cx ee t /\ immutable_frame_mods func ce cx ee t /\
     storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee G tn t) /\
  wb_frame ce es ee sa s0 t /\ ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
  (pure ==> pure_frame ce func es sa s0 t) /\ MAP FDOM ee.scopes = MAP FDOM es.scopes /\
  return_buf_frame d ce st t /\ local_ptrs_reserved ce sa /\ local_ptrs_reserved ce st /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st x) /\
  sa.cs_next_var <= st.cs_next_var /\ sa.cs_next_id <= st.cs_next_id /\
  st.cs_next_var <= allocated.cs_next_var /\ st.cs_next_var <= ready.cs_next_var /\
  (* Registration leaves the previous memory intact. *)
  u with <|vs_vars := t.vs_vars; vs_allocas := t.vs_allocas;
           vs_alloca_next := t.vs_alloca_next; vs_inst_idx := t.vs_inst_idx|> = t /\
  (!H:(bool # bytes32 # type_value) list # num list.
     stmt_state_rel H ctx func ce cx ee t ==> stmt_state_rel H ctx func ce cx ee u) /\
  alloca_history func pre /\ allocas_from lo pre /\ t.vs_alloca_next <= pre.vs_alloca_next /\
  FLOOKUP u.vs_allocas st.cs_next_id = SOME (p,N) /\
  MEM (mk_inst st.cs_next_id ALLOCA [Lit (n2w N)] [root]) (fn_insts func) /\
  u.vs_allocas = (abi_builtin_allocate_state st.cs_next_id N t).vs_allocas /\
  (!aid row. FLOOKUP t.vs_allocas aid = SOME row ==> FLOOKUP u.vs_allocas aid = SOME row) /\
  (!aid b n. aid < st.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,n) ==>
             regions_disjoint p N b n) /\
  (!name b n. local_region ce ee.scopes u name b n ==> regions_disjoint p N b n) /\
  (!x. not_fresh_at st x ==> lookup_var x u = lookup_var x t /\
       FLOOKUP Gu x = FLOOKUP G x /\ op_taint tu (Var x) = op_taint tn (Var x)) /\
  tu.t_stor = tn.t_stor /\ tu.t_trans = tn.t_trans /\ tu.t_imm = tn.t_imm /\
  (!i. i IN tu.t_mem <=> i IN tn.t_mem \/ (t.vs_alloca_next <= i /\ i < p+N)) /\
  (* The selector can write a full word, even when only four bytes are used. *)
  32+write_len <= N /\ typed_copy_state_frame allocated (p+32) write_len u pre /\
  tnpre.t_mem = tu.t_mem DIFF {i | p+32 <= i /\ i < p+32+write_len} /\
  tnpre.t_stor = tu.t_stor /\ tnpre.t_trans = tu.t_trans /\ tnpre.t_imm = tu.t_imm /\
  (!op. (!x. op = Var x ==> not_fresh_at allocated x) ==>
    op_taint tnpre op = op_taint tu op /\ op_prov Gpre op = op_prov Gu op) ==>
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_state_rel H ctx func ce cx ee pre /\ immutable_frame_mods func ce cx ee pre /\
     storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee Gpre tnpre pre) /\
  wb_frame ce es ee sa s0 pre /\ ghost_kept_at lo ce es sa G0 tn0 s0 Gpre tnpre /\
  (pure ==> pure_frame ce func es sa s0 pre) /\ return_buf_frame d ce ready pre /\
  alloca_history func pre /\ (ctx_has_dalloca ctx ==> allocas_below_fmp pre)
Proof
  strip_tac >>
  `u.vs_memory = t.vs_memory /\ u.vs_data_section = t.vs_data_section` by
    (qpat_assum `u with <|vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _|> = t` (SUBST1_TAC o SYM) >> simp[]) >>
  `typed_copy_state_frame allocated p N u pre` by
    (irule typed_copy_state_frame_subinterval >> qexistsl_tac [`p+32`,`write_len`] >> simp[]) >>
  `copy_static pre = copy_static u /\ pre.vs_allocas = u.vs_allocas /\
   pre.vs_alloca_next = u.vs_alloca_next /\ LENGTH u.vs_memory <= LENGTH pre.vs_memory /\
   (!a n. a+n <= p \/ p+N <= a ==>
      mem_bytes_at a n pre.vs_memory = mem_bytes_at a n u.vs_memory) /\
   (!x. not_fresh_at allocated x ==> lookup_var x pre = lookup_var x u)` by
     suspend "physical_fields" >>
  `allocas_from lo u` by
    (fs[allocas_from_def] >> first_assum ACCEPT_TAC) >>
  `t.vs_alloca_next <= u.vs_alloca_next` by fs[] >>
  `!x. not_fresh_at st x ==> not_fresh_at allocated x` by
    metis_tac[not_fresh_at_mono] >>
  `!x. not_fresh_at st x ==> lookup_var x pre = lookup_var x t` by
    (gen_tac >> disch_tac >> simp[]) >>
  `!x. not_fresh_at allocated x ==>
      FLOOKUP Gpre x = FLOOKUP Gu x /\ op_taint tnpre (Var x) = op_taint tu (Var x)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!op. _ ==> op_taint tnpre op = _ /\ _`
       (qspec_then `Var x` mp_tac) >>
     (impl_tac >- simp[]) >>
     disch_then (strip_assume_tac o SRULE[op_prov_def]) >> asm_rewrite_tac[]) >>
  `!name b n. local_region ce ee.scopes t name b n ==> regions_disjoint p N b n` by
    suspend "locals" >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_state_rel H ctx func ce cx ee pre /\ immutable_frame_mods func ce cx ee pre /\
     storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee Gpre tnpre pre` by
    suspend "horizons" >>
  `wb_frame ce es ee sa s0 pre /\ (pure ==> pure_frame ce func es sa s0 pre)` by
    suspend "caller_memory" >>
  `ghost_kept_at lo ce es sa G0 tn0 s0 Gpre tnpre` by suspend "caller_ghost" >>
  conj_tac >- first_assum ACCEPT_TAC >>
  asm_rewrite_tac[] >> conj_tac
  >- (irule return_buf_frame_frame >> qexistsl_tac [`ce`,`t`,`st`] >> simp[]) >>
  fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ pre /\ _`
     (drule_then strip_assume_tac) >>
  drule_then ACCEPT_TAC bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp
QED

Resume abi_encode_setup_frame_mods[physical_fields]:
  qpat_assum `typed_copy_state_frame allocated p N u pre`
    (strip_assume_tac o REWRITE_RULE[typed_copy_state_frame_def,typed_copy_frame_def]) >>
  conj_tac
  >- (qpat_assum `pre with <|vs_vars := _; vs_memory := _; vs_prev_bb := _;
      vs_current_bb := _; vs_inst_idx := _|> = u` (SUBST1_TAC o SYM) >> simp[copy_static_def]) >>
  qpat_assum `pre with <|vs_vars := _; vs_memory := _; vs_prev_bb := _;
      vs_current_bb := _; vs_inst_idx := _|> = u`
    (strip_assume_tac o SRULE[venom_state_component_equality]) >>
  asm_rewrite_tac[]
QED

Resume abi_encode_setup_frame_mods[locals]:
  rpt gen_tac >> disch_tac >> first_x_assum irule >>
  rename1 `local_region ce ee.scopes t name b n` >> qexists_tac `name` >>
  irule local_region_frame_fwd >> qexistsl_tac [`t`,`st`,`ee.scopes`] >> simp[]
QED

Resume abi_encode_setup_frame_mods[horizons]:
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  `stmt_state_rel H ctx func ce cx ee u` by
    (qpat_assum `!h. stmt_state_rel h _ _ _ _ _ t ==> _` (drule_then ACCEPT_TAC)) >>
  conj_tac
  >- (irule literal_copy_window_stmt_state_rel >>
      qexistsl_tac [`st.cs_next_id`,`p`,`N`,`root`,`st`,`allocated`,`u`] >>
      asm_rewrite_tac[]) >>
  `local_ptrs_reserved ce allocated` by (irule local_ptrs_reserved_next_var >> qexists_tac `st` >> simp[]) >>
  `immutable_frame_mods func ce cx ee u` by
    (irule setup_alloc_immutable >> qexistsl_tac [`st.cs_next_id`,`N`,`st`,`t`] >> simp[]) >>
  conj_tac
  >- (irule ifexp_typed_immutable_frame_mods >>
      qexistsl_tac [`p`,`mk_inst st.cs_next_id ALLOCA [Lit (n2w N)] [root]`,
                   `allocated`,`N`,`u`] >>
      qpat_x_assum `u.vs_allocas = (abi_builtin_allocate_state _ _ _).vs_allocas` kall_tac >>
      simp[mk_inst_def]) >>
  simp[] >>
  `ghost_inv_at_mods (DF H) lo d ce cx ee Gu tu u` by
    drule_all_then ACCEPT_TAC setup_alloc_ghost >>
  irule ifexp_typed_copy_ghost_mods >>
  qexistsl_tac [`Gu`,`p+32`,`func`,`allocated`,`write_len`,`u`,`tu`] >>
  simp[IN_DIFF] >> conj_tac
  >- (rpt gen_tac >> disch_tac >>
      qpat_assum `!name b n. local_region ce ee.scopes u name b n ==> _`
        (drule_then mp_tac) >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  conj_tac
  >- (`lo <= p` by
        (qpat_assum `allocas_from lo u` (mp_tac o REWRITE_RULE[allocas_from_def]) >>
         disch_then (drule_then ACCEPT_TAC)) >> decide_tac) >>
  drule_at (Pat `stmt_state_rel _ _ _ _ _ _ u`) stmt_state_rel_local_ptrs_alloca >> simp[]
QED

Resume abi_encode_setup_frame_mods[caller_memory]:
  qpat_x_assum `u.vs_allocas = (abi_builtin_allocate_state _ _ _).vs_allocas` kall_tac >>
  `!b n. regions_disjoint p N b n ==>
     mem_bytes_at b n pre.vs_memory = mem_bytes_at b n t.vs_memory` by
    (rpt gen_tac >> pure_rewrite_tac[loweringStateRelDefsTheory.regions_disjoint_def] >>
     strip_tac >>
     qpat_assum `!a n. a+n <= p \/ p+N <= a ==> _`
       (qspecl_then [`b`,`n`] mp_tac) >> simp[]) >>
  `!name b n. local_region ce ee.scopes t name b n ==>
     mem_bytes_at b n pre.vs_memory = mem_bytes_at b n t.vs_memory` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!name b n. local_region ce ee.scopes t name b n ==> _`
       (drule_then strip_assume_tac) >> simp[]) >>
  conj_tac
  >- (irule wb_frame_allocating_tail >> conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`t`,`ee.scopes`,`st`] >>
      conj_tac >- first_assum ACCEPT_TAC >> simp[] >>
      rpt gen_tac >> strip_tac >>
      qpat_assum `!b n. regions_disjoint p N b n ==> _` irule >>
      qpat_assum `!aid b n. _ /\ FLOOKUP t.vs_allocas aid = SOME (b,n) ==> _`
        (drule_all_then ACCEPT_TAC)) >>
  strip_tac >>
  `pure_frame ce func ee st t pre` by
    (irule pure_frame_fresh_alloca >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`p`,`st.cs_next_id`,`[Lit (n2w N)]`,`[root]`,`N`] >> simp[] >>
     rpt gen_tac >> disch_tac >>
     qpat_assum `!b n. regions_disjoint p N b n ==> _` irule >>
     fs[loweringStateRelDefsTheory.regions_disjoint_def, DISJ_COMM]) >>
  irule pure_frame_trans >> conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`ee`,`st`,`t`] >> fs[wb_frame_def]
QED

Resume abi_encode_setup_frame_mods[caller_ghost]:
  fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ t /\ _`
     (drule_then strip_assume_tac) >>
  `lo <= t.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `!x. not_fresh_at sa x ==> not_fresh_at st x` by metis_tac[not_fresh_at_mono] >>
  `!aid b n. FLOOKUP s0.vs_allocas aid = SOME (b,n) /\ aid < sa.cs_next_id ==>
      b+n <= t.vs_alloca_next` by
    (rpt gen_tac >> strip_tac >>
     `FLOOKUP t.vs_allocas aid = SOME (b,n)` by fs[wb_frame_def] >>
     drule stmt_state_rel_local_ptrs_alloca >>
     simp[alloca_inv_def,alloca_next_valid_def] >> strip_tac >>
     first_x_assum (drule_then ACCEPT_TAC)) >>
  `!name b n. local_region ce es.scopes s0 name b n ==> b+n <= t.vs_alloca_next` by
    (rpt gen_tac >> disch_tac >>
     `local_region ce ee.scopes t name b n` by
       (irule local_region_frame_fwd >> qexistsl_tac [`s0`,`sa`,`es.scopes`] >> fs[wb_frame_def]) >>
     drule_all_then ACCEPT_TAC body_local_region_frontier) >>
  `ghost_kept_at lo ce es sa G0 tn0 s0 Gu tu` by
    (irule alloc_buffer_ghost_kept_at >> qexistsl_tac [`G`,`p+N`,`t`,`tn`] >>
     simp[] >> conj_tac >> first_assum ACCEPT_TAC) >>
  irule ghost_kept_at_clean_suffix >> qexistsl_tac [`Gu`,`tu`] >>
  simp[SUBSET_DEF,IN_DIFF]
QED

Finalise abi_encode_setup_frame_mods
