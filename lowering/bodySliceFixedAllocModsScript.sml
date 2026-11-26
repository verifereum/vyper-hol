(* The fixed-byte Slice staging allocation, before its initializing store. *)
Theory bodySliceFixedAllocMods
Ancestors
  bodyFullAllocaFresh bodyFullPostsMods bodyFullShadowBodyInv bodyFullHashKeccakFixed
  abiBuiltinAllocation stmtReasonMemory loweringHalt ptrDiscipline venomMemDefs
  emitHelperProps fragExec fragGasOriginPtr venomExecSemantics context bodyMemoryDefs
  loweringStateRelDefs exprLoweringProps exprOperandVar vyperStorageFootprint
  bodyPtrDefs bodyInvSplit exprSimMemDefs vyperState venomState finite_map words exprSimAlloc

Theorem slice_alloc_new_sites[local]:
  compile_alloc_buffer 32 sa = (buf,sm) /\ buf.buf_operand = Var root /\
  run_inst_seq (emitted_insts sa sm) s = OK raw /\
  u = raw with vs_inst_idx := j /\ FLOOKUP u.vs_allocas aid = SOME (b,n) ==>
  FLOOKUP s.vs_allocas aid = SOME (b,n) \/ s.vs_alloca_next <= b
Proof
  strip_tac >> drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[run_inst_seq_def, AllCaseEqs()] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[step_alloca_eq] >> Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id` >>
  gvs[AllCaseEqs(), update_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> Cases_on `aid = sa.cs_next_id` >> gvs[FLOOKUP_UPDATE]
QED

Theorem slice_alloc_immutable[local]:
  immutable_frame_mods func ce cx es s /\
  u.vs_memory = s.vs_memory /\ u.vs_data_section = s.vs_data_section /\
  s.vs_alloca_next <= u.vs_alloca_next /\
  (!aid b n. FLOOKUP u.vs_allocas aid = SOME (b,n) ==>
      FLOOKUP s.vs_allocas aid = SOME (b,n) \/ s.vs_alloca_next <= b) /\
  (!id b n. local_region ce es.scopes u id b n <=> local_region ce es.scopes s id b n) ==>
  immutable_frame_mods func ce cx es u
Proof
  strip_tac >> fs[immutable_frame_mods_def] >> conj_tac
  >- (fs[immutables_rel_mods_def, immutables_rel_def] >> first_assum ACCEPT_TAC) >>
  fs[immutable_alloca_sep_mods_def] >> rpt gen_tac >> strip_tac >>
  irule immutable_alloca_sep_frame >> qexistsl_tac [`s`,`es`] >> simp[] >>
  rpt gen_tac >> disch_tac >> disj1_tac >> qexists_tac `id` >>
  `!z. local_region (ce with ce_module := src) es.scopes z id b sz =
       local_region ce es.scopes z id b sz` by simp[local_region_def] >>
  metis_tac[]
QED

Theorem slice_alloc_ghost[local]:
  ghost_inv_at_mods D lo d ce cx es G tn s /\
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func ce cx es s /\
  local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==>
    lookup_var x u = lookup_var x s /\ FLOOKUP Ga x = FLOOKUP G x /\
    op_taint ta (Var x) = op_taint tn (Var x)) /\
  u with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
           vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|> = s /\
  allocas_from lo u /\ s.vs_alloca_next <= u.vs_alloca_next /\
  ta.t_stor = tn.t_stor /\ ta.t_trans = tn.t_trans /\ ta.t_imm = tn.t_imm /\
  (!i. i IN ta.t_mem <=> i IN tn.t_mem \/ (s.vs_alloca_next <= i /\ i < stop)) ==>
  ghost_inv_at_mods D lo d ce cx es Ga ta u
Proof
  strip_tac >>
  `ghost_inv_at D 0 d ce cx es G tn s /\ lo <= s.vs_alloca_next` by
    (fs[ghost_inv_at_mods_def, ghost_inv_at_def, allocas_from_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `ghost_inv_at D 0 d ce cx es Ga ta u` by
    (irule (INST_TYPE [alpha |-> ``:256``] alloc_buffer_ghost_inv_at) >>
     conj_tac >- simp[allocas_from_def] >>
     qexistsl_tac [`G`,`H`,`ctx`,`stop`,`func`,`s`,`sa`,`tn`] >> simp[]) >>
  `u.vs_memory = s.vs_memory` by
    (qpat_assum `u with <|vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _|> = s` (SUBST1_TAC o SYM) >> simp[]) >>
  `!i. i < lo /\ i IN ta.t_mem ==> i IN tn.t_mem` by (simp[] >> decide_tac) >>
  fs[ghost_inv_at_mods_def, ghost_inv_at_def] >> rpt conj_tac
  >- metis_tac[]
  >- (rpt strip_tac >> `not_fresh_at sa x` by fs[local_ptrs_reserved_def] >>
      metis_tac[]) >>
  decide_tac
QED

Theorem slice_fixed_capture_alloc_mods:
  compile_alloc_buffer 32 sa = (buf,sm) /\ fn_has_code sa sm func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  alloca_history func s /\ return_buf_frame d ce sa s /\
  storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es s /\ immutable_frame_mods func ce cx es s /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx es G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?root p u Ga ta.
    buf.buf_operand = Var root /\ not_fresh_at sm root /\ local_ptrs_reserved ce sm /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [root]) (fn_insts func) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Ga,ta)) /\
    ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
    u.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func u /\
    lookup_var root u = SOME p /\ ptr_covers Ga ta root u 32 /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n p,32) /\
    FLOOKUP Ga root = SOME (w2n p,32) /\
    allocas_from lo u /\ lo <= w2n p /\ w2n p+32 < dimword (:256) /\
    w2n p+32 <= u.vs_alloca_next /\ s.vs_alloca_next <= u.vs_alloca_next /\
    u.vs_memory = s.vs_memory /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s /\
      FLOOKUP Ga x = FLOOKUP G x /\ op_taint ta (Var x) = op_taint tn (Var x)) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      regions_disjoint (w2n p) 32 b len) /\
    (!name b len. local_region ce es.scopes u name b len ==>
      regions_disjoint (w2n p) 32 b len) /\
    ta.t_stor = tn.t_stor /\ ta.t_trans = tn.t_trans /\ ta.t_imm = tn.t_imm /\
    (!i. i < s.vs_alloca_next ==> (i IN ta.t_mem <=> i IN tn.t_mem)) /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
    return_buf_frame d ce sm u /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func ce cx es u /\ immutable_frame_mods func ce cx es u /\
      storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx es Ga ta u)
Proof
  strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  `allocas_from lo s /\ lo <= s.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  drule_then assume_tac (SPEC_ALL stmt_state_rel_allocas_below_fmp) >>
  mp_tac (Q.INST [`n` |-> `32`, `sb` |-> `sm`, `cenv` |-> `ce`,
                  `H` |-> `storage_trace_horizon es.storage_trace`]
    (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``] alloc_buffer_origin_ptr_path_with_raw_endpoint)) >>
  impl_tac >- simp[dimword_def] >>
  disch_then (qx_choosel_then [`root`,`p`,`u`,`Ga`,`ta`,`raw`] strip_assume_tac) >>
  suspend "frame"
QED

Resume slice_fixed_capture_alloc_mods[frame]:
  drule_then strip_assume_tac compile_alloc_buffer_parts >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [root]) (fn_insts func)` by
    (`root = STRING #"%" (toString sa.cs_next_var)` by metis_tac[operand_11] >>
     gvs[] >> irule buffer_alloc_code >> goal_assum (drule_at Any) >> simp[]) >>
  `local_ptrs_reserved ce sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `lo <= w2n p` by
    (qpat_assum `allocas_from lo u` (mp_tac o REWRITE_RULE [allocas_from_def]) >>
     disch_then (qspecl_then [`sa.cs_next_id`,`w2n p`,`32`] mp_tac) >> simp[]) >>
  `u.vs_memory = s.vs_memory /\ u.vs_data_section = s.vs_data_section /\
   u.vs_halted = s.vs_halted` by
    (qpat_assum `u with <|vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _|> = s` (SUBST1_TAC o SYM) >> simp[]) >>
  `~u.vs_halted` by metis_tac[] >>
  `!i. i < s.vs_alloca_next ==> (i IN ta.t_mem <=> i IN tn.t_mem)` by simp[] >>
  `!aid b n. FLOOKUP u.vs_allocas aid = SOME (b,n) ==>
      FLOOKUP s.vs_allocas aid = SOME (b,n) \/ s.vs_alloca_next <= b` by
    (rpt gen_tac >> disch_tac >> drule_all_then ACCEPT_TAC slice_alloc_new_sites) >>
  `!id b n. local_region ce es.scopes u id b n <=> local_region ce es.scopes s id b n` by
    (rpt gen_tac >> irule local_region_lookup_cong >> fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `return_buf_frame d ce sm u` by
    (irule return_buf_frame_frame >> qexistsl_tac [`ce`,`s`,`sa`] >> simp[] >> metis_tac[]) >>
  suspend "finish"
QED

Resume slice_fixed_capture_alloc_mods[finish]:
  `immutable_frame_mods func ce cx es u` by
    (irule slice_alloc_immutable >> qexists_tac `s` >> simp[]) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func ce cx es u /\ immutable_frame_mods func ce cx es u /\
      storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx es Ga ta u` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ s /\ _`
       (drule_then strip_assume_tac) >>
     conj_tac >- (qpat_assum `!h:(bool # bytes32 # type_value) list # num list.
                      stmt_state_rel h _ _ _ _ _ s ==> stmt_state_rel h _ _ _ _ _ u`
                    irule >> first_assum ACCEPT_TAC) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     drule_all_then ACCEPT_TAC slice_alloc_ghost) >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
    (conj_tac >> rpt gen_tac >> disch_tac >> metis_tac[]) >>
  qexistsl_tac [`root`,`p`,`u`,`Ga`,`ta`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise slice_fixed_capture_alloc_mods
