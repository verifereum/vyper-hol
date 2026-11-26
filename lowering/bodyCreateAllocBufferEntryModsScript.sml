(* The empty-prefix cut of the registered Create initcode buffer. *)
Theory bodyCreateAllocBufferEntryMods
Ancestors
  bodyAbiTupleBufferStateMods bodyFullAllocaFresh bodyPtrIfExpAllocCompiler
  bodyFullHashKeccakFixed[qualified,ignore_grammar] bodyMethodIdScratchFrameMods
  abiBufferAllocationCode exprSimAlloc stmtReasonMemory
  bodyMemoryDefs exprSimCopy exprSimWordArgs wordArgsPtr stateRelProj
  bodyFullPostsMods bodyFullShadowBodyInv bodyInvSplit loweringStateRelDefs
  exprLoweringProps bodyPtrDefs ptrDiscipline valueEncodingDefs
  vyperStorageFootprint venomState venomMemDefs venomInst finite_map words

Theorem create_alloc_rows[local]:
  step_inst_base (mk_inst id ALLOCA [Lit (n2w cap)] [root]) s = OK raw /\
  FLOOKUP raw.vs_allocas aid = SOME (b,n) ==>
    FLOOKUP s.vs_allocas aid = SOME (b,n) \/ s.vs_alloca_next <= b
Proof
  simp[step_alloca_eq] >> Cases_on `FLOOKUP s.vs_allocas id` >>
  gvs[AllCaseEqs(), update_var_def] >> rpt strip_tac >>
  Cases_on `aid = id` >> gvs[FLOOKUP_UPDATE]
QED

Theorem create_alloc_immutable_frame[local]:
  immutable_frame_mods func ce cx ee s /\
  u.vs_memory = s.vs_memory /\ u.vs_data_section = s.vs_data_section /\
  s.vs_alloca_next <= u.vs_alloca_next /\
  (!aid b n. FLOOKUP u.vs_allocas aid = SOME (b,n) ==>
    FLOOKUP s.vs_allocas aid = SOME (b,n) \/ s.vs_alloca_next <= b) /\
  (!id b n. local_region ce ee.scopes u id b n <=> local_region ce ee.scopes s id b n) ==>
  immutable_frame_mods func ce cx ee u
Proof
  strip_tac >> fs[immutable_frame_mods_def] >> conj_tac
  >- (fs[immutables_rel_mods_def, immutables_rel_def] >> first_assum ACCEPT_TAC) >>
  fs[immutable_alloca_sep_mods_def] >> rpt gen_tac >> disch_tac >>
  irule immutable_alloca_sep_frame >> qexistsl [`s`,`ee`] >> simp[] >>
  rpt gen_tac >> disch_tac >> disj1_tac >> qexists `id` >>
  `!z. local_region (ce with ce_module := src) ee.scopes z id b sz =
       local_region ce ee.scopes z id b sz` by simp[local_region_def] >>
  metis_tac[]
QED

Theorem create_alloc_ghost_frame[local]:
  ghost_inv_at_mods D lo d ce cx ee G tn s /\
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func ce cx ee s /\
  local_ptrs_reserved ce se /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x. not_fresh_at se x ==> lookup_var x u = lookup_var x s /\
       FLOOKUP Gu x = FLOOKUP G x /\ op_taint tu (Var x) = op_taint tn (Var x)) /\
  u with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
           vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|> = s /\
  u.vs_memory = s.vs_memory /\ allocas_from lo u /\ s.vs_alloca_next <= u.vs_alloca_next /\
  tu.t_stor = tn.t_stor /\ tu.t_trans = tn.t_trans /\ tu.t_imm = tn.t_imm /\
  (!i. i IN tu.t_mem <=> i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < stop)) ==>
  ghost_inv_at_mods D lo d ce cx ee Gu tu u
Proof
  strip_tac >>
  `ghost_inv_at D 0 d ce cx ee G tn s` by drule_then ACCEPT_TAC method_id_ghost_at_zero >>
  `ghost_inv_at D 0 d ce cx ee Gu tu u` by
    (irule (INST_TYPE [alpha |-> ``:256``] alloc_buffer_ghost_inv_at) >>
     conj_tac >- simp[allocas_from_def] >>
     qexistsl [`G`,`H`,`ctx`,`stop`,`func`,`s`,`se`,`tn`] >> simp[]) >>
  `lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `!i. i < lo /\ i IN tu.t_mem ==> i IN tn.t_mem` by (simp[] >> decide_tac) >>
  fs[ghost_inv_at_mods_def, ghost_inv_at_def] >> rpt conj_tac
  >- metis_tac[]
  >- (rpt strip_tac >> drule_all local_ptrs_reserved_imm_base >> metis_tac[]) >>
  decide_tac
QED

Theorem create_alloc_buffer_entry_mods:
  compile_alloc_buffer cap se = (buf,a) /\ fn_has_code se a func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce se /\
  cap < dimword (:256) /\ storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func ce cx ee s /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee G tn s /\
    immutable_frame_mods func ce cx ee s) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at se x) /\
  return_buf_frame d ce se s /\ alloca_history func s /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = se.cs_current_bb /\
  s.vs_inst_idx = LENGTH se.cs_current_insts ==>
  ?root pbase inst u Gu tu.
    buf.buf_operand = Var root /\ MEM inst (fn_insts func) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_id = se.cs_next_id /\
    inst.inst_outputs = [root] /\ not_local_ptr ce ee.scopes root /\
    abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
      se.cs_next_id pbase cap root root 0 [] a u Gu tu /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tu)) /\
    allocas_from lo u /\ u.vs_memory = s.vs_memory /\ FLOOKUP Gu root = SOME (pbase,cap) /\
    pbase + cap < dimword (:256) /\ pbase + cap <= u.vs_alloca_next /\
    (!x. not_fresh_at se x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP Gu x = FLOOKUP G x /\ op_taint tu (Var x) = op_taint tn (Var x)) /\
    (!aid row. FLOOKUP s.vs_allocas aid = SOME row ==> FLOOKUP u.vs_allocas aid = SOME row) /\
    (!i. i IN tu.t_mem <=> i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < pbase+cap)) /\
    (!aid b n. aid < se.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,n) ==>
      regions_disjoint pbase cap b n) /\
    (!name b n. local_region ce ee.scopes u name b n ==> regions_disjoint pbase cap b n)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `storage_trace_domain _ _ _` (strip_assume_tac o REWRITE_RULE[storage_trace_domain_def]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  drule bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >> strip_tac >>
  drule_all (INST_TYPE [``:'b`` |-> ``:256``] alloc_buffer_origin_ptr_path_with_raw_endpoint) >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`]
    (qx_choosel_then [`root`,`w`,`u`,`Gu`,`tu`,`raw`]
      (map_every assume_tac o CONJUNCTS))) >>
  `not_local_ptr ce ee.scopes root` by
    (drule_at (Pat `compile_alloc_buffer _ _ = _`) (cj 1 compile_alloc_buffer_frame_separation) >>
     disch_then irule >> simp[] >> qexists `se` >> simp[]) >>
  `MEM (mk_inst se.cs_next_id ALLOCA [Lit (n2w cap)] [root]) (fn_insts func) /\
   step_inst_base (mk_inst se.cs_next_id ALLOCA [Lit (n2w cap)] [root]) s = OK raw /\
   se.cs_next_var <= a.cs_next_var /\ se.cs_next_id < a.cs_next_id` by
    (drule_then strip_assume_tac compile_alloc_buffer_code >>
     drule_all_then assume_tac buffer_alloc_code >>
     `root = STRING #"%" (toString se.cs_next_var)` by
       (qpat_assum `buf.buf_operand = Var root` mp_tac >>
        qpat_assum `buf.buf_operand = Var (STRING _ _)` SUBST1_TAC >> simp[]) >>
     conj_tac >- simp[] >>
     conj_tac >- (qpat_assum `run_inst_seq _ _ = OK raw` mp_tac >>
       qpat_assum `emitted_insts se a = _` (fn th => pure_rewrite_tac[th]) >>
       qpat_assum `root = STRING _ _` (fn th => pure_rewrite_tac[GSYM th]) >>
       Cases_on `step_inst_base (mk_inst se.cs_next_id ALLOCA [Lit (n2w cap)] [root]) s` >>
       simp[run_inst_seq_def]) >> simp[]) >>
  `~u.vs_halted /\ u.vs_memory = s.vs_memory /\ u.vs_accounts = s.vs_accounts /\
   u.vs_transient = s.vs_transient /\ u.vs_call_ctx = s.vs_call_ctx /\
   u.vs_immutables = s.vs_immutables /\ u.vs_data_section = s.vs_data_section` by
    (qpat_x_assum `u = _ with vs_inst_idx := _` kall_tac >>
     qpat_assum `u with <|vs_vars := _;vs_allocas := _;vs_alloca_next := _;vs_inst_idx := _|> = s`
       (strip_assume_tac o SRULE[venom_state_component_equality]) >> simp[]) >>
  `!name b n. local_region ce ee.scopes u name b n <=> local_region ce ee.scopes s name b n` by
    (rpt gen_tac >> irule copy_buffer_local_region_frame >> qexists `se` >> simp[]) >>
  `!aid b n. FLOOKUP u.vs_allocas aid = SOME (b,n) ==>
    FLOOKUP s.vs_allocas aid = SOME (b,n) \/ s.vs_alloca_next <= b` by
    (rpt gen_tac >> qpat_assum `u = _ with vs_inst_idx := _` SUBST1_TAC >>
     simp[] >> disch_tac >> drule_all_then ACCEPT_TAC create_alloc_rows) >>
  `abi_tuple_buffer_state_mods ctx func ce cx st0 ee DF lo d se s G tn
      se.cs_next_id (w2n w) cap root root 0 [] a u Gu tu` by suspend "state" >>
  qexistsl [`root`,`w2n w`,`mk_inst se.cs_next_id ALLOCA [Lit (n2w cap)] [root]`,`u`,`Gu`,`tu`] >>
  simp_tac (srw_ss()) [mk_inst_def] >>
  rpt conj_tac >> first_assum (ACCEPT_TAC o SRULE[mk_inst_def])
QED

Resume create_alloc_buffer_entry_mods[state]:
  qpat_x_assum `u = _ with vs_inst_idx := _` kall_tac >>
  qpat_x_assum `Gu = step_prov _ _ _ _` kall_tac >>
  qpat_x_assum `tu = step_taint _ _ _ _` kall_tac >>
  simp[abi_tuple_buffer_state_mods_def,eval_operand_def,read_memory_def] >>
  conj_tac >- suspend "horizons" >>
  conj_tac >- (drule return_buf_frame_frame >> disch_then irule >> simp[]) >>
  conj_tac >- (irule wb_frame_readonly_tail >> qexistsl [`se`,`s`] >> simp[wb_frame_refl]) >>
  `alloca_inv s` by drule_then ACCEPT_TAC (cj 2 stmt_state_rel_local_ptrs_alloca) >>
  `!aid b n. FLOOKUP s.vs_allocas aid = SOME (b,n) ==> b+n <= s.vs_alloca_next` by
    fs[alloca_inv_def,alloca_next_valid_def] >>
  `!name b n. local_region ce ee.scopes s name b n ==> b+n <= s.vs_alloca_next` by
    (rpt gen_tac >> disch_tac >> drule_all_then ACCEPT_TAC body_local_region_frontier) >>
  conj_tac
  >- (irule alloc_buffer_ghost_kept_at >> qexistsl [`G`,`w2n w+cap`,`s`,`tn`] >>
      simp[ghost_kept_at_refl] >> conj_tac >- first_assum ACCEPT_TAC >>
      rpt gen_tac >> strip_tac >> first_x_assum (drule_then ACCEPT_TAC)) >>
  rpt strip_tac >> gvs[] >> res_tac >> decide_tac
QED

Resume create_alloc_buffer_entry_mods[horizons]:
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  simp[] >> conj_tac
  >- (irule create_alloc_ghost_frame >> conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl [`G`,`H`,`ctx`,`func`,`s`,`se`,`w2n w+cap`,`tn`] >> simp[]) >>
  irule create_alloc_immutable_frame >> qexists `s` >> simp[]
QED

Finalise create_alloc_buffer_entry_mods
