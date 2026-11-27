(* RawCreate snapshot cut immediately after the allocation, before the copy. *)
Theory bodyCreateRawAllocMods
Ancestors
  bodyFullAllocaFresh bodyLocalSnapshotResourcesMods bodyFullPostsMods bodyFullShadowBodyInv
  bodyMemoryDefs bodyPtrDefs bodyFullHashKeccakFixed[qualified,ignore_grammar]
  actualAllocExec bufferAllocationExecution fragGasOriginPtr fragExec
  exprLowering exprLoweringProps stmtLoweringMono exprSimCopy exprSimOperands
  context contextCodegenRel compileEnv emitHelper emitHelperProps loweringHalt
  loweringShapeDefs loweringStateRelDefs typedMemoryCopy ptrDiscipline
  vyperStorageFootprint vyperValue venomInst venomState venomExecSemantics
  finite_map words arithmetic list

val residual = ``\ce vv cap buf m b func.
  ((vv_location vv = NONE \/ vv_location vv = SOME LocMemory) ==>
    ?len l size c.
      emit_op MLOAD [vv_operand vv] m = (len,l) /\
      emit_op ADD [len;Lit 32w] l = (size,c) /\
      compile_copy_memory_dynamic buf.buf_operand (vv_operand vv) size c = ((),b) /\
      ci_mono m l /\ ci_mono l c /\ ci_mono c b /\
      fn_has_code m l func /\ fn_has_code l c func /\ fn_has_code c b func) /\
  (!loc. vv_location vv = SOME loc /\ (loc = LocStorage \/ loc = LocTransient) ==>
    ?lab. compile_slot_to_memory (vv_operand vv) buf.buf_operand
            ((cap+31) DIV 32) loc m = (lab,b)) /\
  (vv_location vv = SOME LocCode ==>
    compile_imm_copy_to_memory ce.ce_is_ctor ce.ce_imm_alloca (vv_operand vv)
      buf.buf_operand ((type_memory_bytes ce (vv_type vv)+31) DIV 32) 0 m = ((),b))``;

Theorem snapshot_memory_residual[local]:
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) /\
  compile_create_snapshot ce vv ty a = (snap,b) /\
  compile_alloc_buffer (type_memory_bytes ce ty) a = (buf,m) /\
  fn_has_code a b func ==>
  snap = buf.buf_operand /\ ci_mono m b /\
  ?len l size c.
    emit_op MLOAD [vv_operand vv] m = (len,l) /\
    emit_op ADD [len;Lit 32w] l = (size,c) /\
    compile_copy_memory_dynamic buf.buf_operand (vv_operand vv) size c = ((),b) /\
    ci_mono m l /\ ci_mono l c /\ ci_mono c b /\
    fn_has_code m l func /\ fn_has_code l c func /\ fn_has_code c b func
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `emit_op MLOAD [vv_operand vv] m` >>
  rename1 `emit_op MLOAD _ _ = (len,l)` >>
  Cases_on `emit_op ADD [len;Lit 32w] l` >>
  rename1 `emit_op ADD _ _ = (cnt,sc)` >>
  Cases_on `compile_copy_memory_dynamic buf.buf_operand (vv_operand vv) cnt sc` >>
  `snap = buf.buf_operand /\
   compile_copy_memory_dynamic buf.buf_operand (vv_operand vv) cnt sc = ((),b)` by
    (qpat_x_assum `compile_create_snapshot _ _ _ _ = _` mp_tac >>
     Cases_on `vv_location vv = NONE` >>
     gvs[compile_create_snapshot_def,comp_bind_def,comp_ignore_bind_def,
         comp_return_def,oneTheory.one]) >>
  `ci_mono a m /\ ci_mono m l /\ ci_mono l sc /\ ci_mono sc b` by
    metis_tac[ci_mono_compile_alloc_buffer,ci_mono_emit_op,
              ci_mono_compile_copy_memory_dynamic,pairTheory.SND] >>
  `ci_mono l b` by metis_tac[ci_mono_trans] >>
  `ci_mono m b` by metis_tac[ci_mono_trans] >>
  `fn_has_code a m func /\ fn_has_code m b func` by
    (irule fn_has_code_split >> fs[ci_mono_def]) >>
  `fn_has_code m l func /\ fn_has_code l b func` by
    (irule fn_has_code_split >> fs[ci_mono_def]) >>
  `fn_has_code l sc func /\ fn_has_code sc b func` by
    (irule fn_has_code_split >> fs[ci_mono_def]) >>
  simp[] >> qexistsl_tac [`cnt`,`sc`] >> simp[]
QED

Theorem snapshot_compiler_cut[local]:
  compile_create_snapshot ce vv ty a = (snap,b) /\
  cap = type_memory_bytes ce ty /\ vv_location vv <> SOME LocCalldata /\
  fn_has_code a b func ==>
  ?buf m. compile_alloc_buffer cap a = (buf,m) /\ snap = buf.buf_operand /\
    ci_mono a m /\ ci_mono m b /\ fn_has_code a m func /\ fn_has_code m b func /\
    (^residual) ce vv cap buf m b func
Proof
  BETA_TAC >> strip_tac >>
  Cases_on `compile_alloc_buffer (type_memory_bytes ce ty) a` >>
  rename1 `compile_alloc_buffer _ a = (buf,m)` >>
  `ci_mono a m` by metis_tac[ci_mono_compile_alloc_buffer,pairTheory.SND] >>
  `snap = buf.buf_operand /\ ci_mono m b /\ (^residual) ce vv cap buf m b func` by
    suspend "layout" >>
  `fn_has_code a m func /\ fn_has_code m b func` by
    (irule fn_has_code_split >> fs[ci_mono_def]) >>
  qexistsl_tac [`buf`,`m`] >> gvs[] >> rpt conj_tac >> FIRST_ASSUM ACCEPT_TAC
QED

Resume snapshot_compiler_cut[layout]:
  BETA_TAC >> Cases_on `vv_location vv = NONE \/ vv_location vv = SOME LocMemory`
  >- (drule_all_then strip_assume_tac snapshot_memory_residual >>
      qpat_x_assum `vv_location vv = NONE \/ _` strip_assume_tac >> simp[]) >>
  Cases_on `vv_location vv` >> gvs[] >>
  rename1 `vv_location vv = SOME loc` >> Cases_on `loc` >> gvs[]
  >- (Cases_on `compile_slot_to_memory (vv_operand vv) buf.buf_operand
          ((type_memory_bytes ce ty+31) DIV 32) LocStorage m` >>
      gvs[compile_create_snapshot_def,comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
      metis_tac[cj 3 ci_mono_context_helpers,pairTheory.SND])
  >- (Cases_on `compile_slot_to_memory (vv_operand vv) buf.buf_operand
          ((type_memory_bytes ce ty+31) DIV 32) LocTransient m` >>
      gvs[compile_create_snapshot_def,comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
      metis_tac[cj 3 ci_mono_context_helpers,pairTheory.SND]) >>
  Cases_on `compile_imm_copy_to_memory ce.ce_is_ctor ce.ce_imm_alloca
    (vv_operand vv) buf.buf_operand ((type_memory_bytes ce (vv_type vv)+31) DIV 32) 0 m` >>
  gvs[compile_create_snapshot_def,comp_bind_def,comp_ignore_bind_def,comp_return_def,oneTheory.one] >>
  metis_tac[ci_mono_compile_imm_copy_to_memory,pairTheory.SND]
QED

Finalise snapshot_compiler_cut

Theorem snapshot_alloc_rows[local]:
  compile_alloc_buffer cap a = (buf,m) /\ cap < dimword (:256) /\
  run_inst_seq (emitted_insts a m) t = OK raw /\
  j = raw with vs_inst_idx := LENGTH m.cs_current_insts /\
  FLOOKUP j.vs_allocas a.cs_next_id = SOME (pbase,cap) /\
  pbase+cap <= j.vs_alloca_next ==>
  ((FLOOKUP t.vs_allocas a.cs_next_id = NONE /\ pbase = t.vs_alloca_next) \/
   (FLOOKUP t.vs_allocas a.cs_next_id = SOME (pbase,cap) /\
    j.vs_alloca_next = t.vs_alloca_next)) /\
  (!aid off sz. FLOOKUP j.vs_allocas aid = SOME (off,sz) ==>
    FLOOKUP t.vs_allocas aid = SOME (off,sz) \/ t.vs_alloca_next <= off)
Proof
  strip_tac >>
  drule bufferAllocationExecutionTheory.compile_alloc_buffer_execution >>
  disch_then (qspec_then `t` strip_assume_tac) >>
  qpat_x_assum `run_inst_seq _ _ = OK (update_var _ _ _)` mp_tac >>
  simp[] >> disch_then SUBST_ALL_TAC >>
  Cases_on `FLOOKUP t.vs_allocas a.cs_next_id` >>
  gvs[buffer_allocation_fields_def,FLOOKUP_UPDATE,update_var_def,w2n_n2w,LESS_MOD] >>
  rpt gen_tac >> Cases_on `aid = a.cs_next_id` >> simp[]
QED

Theorem raw_create_snapshot_alloc_mods:
  compile_create_snapshot ce vv (BaseT (BytesT (Dynamic k))) a = (snap,b) /\
  cap = type_memory_bytes ce (BaseT (BytesT (Dynamic k))) /\
  vv_location vv <> SOME LocCalldata /\ cap < dimword (:256) /\
  fn_has_code a b func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce a /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H : (bool # bytes32 # type_value) list # num list.
    valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee t /\ immutable_frame_mods func ce cx ee t /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee G tn t) /\
  return_buf_frame d ce a t /\ alloca_history func t /\
  ~t.vs_halted /\ t.vs_current_bb = a.cs_current_bb /\
  t.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?buf m site owner pbase j Gj tj.
    compile_alloc_buffer cap a = (buf,m) /\ snap = buf.buf_operand /\
    buf.buf_operand = Var owner /\ ci_mono a m /\ ci_mono m b /\
    fn_has_code a m func /\ fn_has_code m b func /\ (^residual) ce vv cap buf m b func /\
    site = mk_inst a.cs_next_id ALLOCA [Lit (n2w cap)] [owner] /\
    MEM site (fn_insts func) /\ site.inst_id = a.cs_next_id /\
    site.inst_opcode = ALLOCA /\ site.inst_outputs = [owner] /\
    not_local_ptr ce ee.scopes owner /\ not_fresh_at m owner /\ not_fresh_at b owner /\
    ((FLOOKUP t.vs_allocas a.cs_next_id = NONE /\ pbase = t.vs_alloca_next) \/
     FLOOKUP t.vs_allocas a.cs_next_id = SOME (pbase,cap)) /\
    FLOOKUP j.vs_allocas a.cs_next_id = SOME (pbase,cap) /\
    lookup_var owner j = SOME (n2w pbase) /\ eval_operand snap j = SOME (n2w pbase) /\
    FLOOKUP Gj owner = SOME (pbase,cap) /\ op_taint tj (Var owner) = {} /\
    ptr_covers Gj tj owner j cap /\ lo <= pbase /\ pbase+cap < dimword (:256) /\
    pbase+cap <= j.vs_alloca_next /\ t.vs_alloca_next <= j.vs_alloca_next /\
    allocas_from lo j /\ lo <= j.vs_alloca_next /\ alloca_history func j /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp j) /\ return_buf_frame d ce m j /\
    ~j.vs_halted /\ j.vs_current_bb = m.cs_current_bb /\ j.vs_inst_idx = LENGTH m.cs_current_insts /\
    j with <|vs_vars := t.vs_vars; vs_allocas := t.vs_allocas;
            vs_alloca_next := t.vs_alloca_next; vs_inst_idx := t.vs_inst_idx|> = t /\
    j.vs_memory = t.vs_memory /\ j.vs_data_section = t.vs_data_section /\
    j.vs_call_ctx = t.vs_call_ctx /\ j.vs_accounts = t.vs_accounts /\
    j.vs_transient = t.vs_transient /\ j.vs_immutables = t.vs_immutables /\
    j.vs_initial_fmp = t.vs_initial_fmp /\ j.vs_fmp = t.vs_fmp /\
    (!x. not_fresh_at a x ==> not_fresh_at m x /\ lookup_var x j = lookup_var x t /\
         FLOOKUP Gj x = FLOOKUP G x /\ op_taint tj (Var x) = op_taint tn (Var x)) /\
    (!aid ent. FLOOKUP t.vs_allocas aid = SOME ent ==> FLOOKUP j.vs_allocas aid = SOME ent) /\
    (!aid off sz. FLOOKUP j.vs_allocas aid = SOME (off,sz) ==>
         FLOOKUP t.vs_allocas aid = SOME (off,sz) \/ t.vs_alloca_next <= off) /\
    (!name off sz. local_region ce ee.scopes j name off sz <=> local_region ce ee.scopes t name off sz) /\
    (!name off sz. local_region ce ee.scopes j name off sz ==> regions_disjoint pbase cap off sz) /\
    (!aid off sz. aid < a.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (off,sz) ==>
         regions_disjoint pbase cap off sz) /\
    tj.t_stor = tn.t_stor /\ tj.t_trans = tn.t_trans /\ tj.t_imm = tn.t_imm /\
    (!i. i IN tj.t_mem <=> i IN tn.t_mem \/ (t.vs_alloca_next <= i /\ i < pbase+cap)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func ce cx ee j /\ immutable_frame_mods func ce cx ee j /\
      storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee Gj tj j /\
      gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK j,Gj,tj))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then (qx_choosel_then [`buf`,`m`] (map_every assume_tac o CONJUNCTS))
    snapshot_compiler_cut >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  drule_then strip_assume_tac bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  drule_all (INST_TYPE [beta |-> ``:256``] alloc_buffer_origin_ptr_path_with_raw_endpoint) >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`]
    (qx_choosel_then [`owner`,`w`,`j`,`Gj`,`tj`,`raw`] strip_assume_tac)) >>
  qabbrev_tac `pbase = w2n (w:bytes32)` >>
  qabbrev_tac `site = mk_inst a.cs_next_id ALLOCA [Lit (n2w cap)] [owner]` >>
  `MEM site (fn_insts func) /\ site.inst_id = a.cs_next_id /\ site.inst_opcode = ALLOCA /\
   site.inst_outputs = [owner] /\ not_local_ptr ce ee.scopes owner` by suspend "site" >>
  `j.vs_memory = t.vs_memory /\ j.vs_data_section = t.vs_data_section /\
   j.vs_call_ctx = t.vs_call_ctx /\ j.vs_accounts = t.vs_accounts /\
   j.vs_transient = t.vs_transient /\ j.vs_immutables = t.vs_immutables /\
   j.vs_initial_fmp = t.vs_initial_fmp /\ j.vs_fmp = t.vs_fmp /\ ~j.vs_halted` by
    (qpat_assum `j with <|vs_vars := _; vs_allocas := _; vs_alloca_next := _; vs_inst_idx := _|> = t`
       (mp_tac o AP_TERM ``\z. (z.vs_memory,z.vs_data_section,z.vs_call_ctx,z.vs_accounts,
         z.vs_transient,z.vs_immutables,z.vs_initial_fmp,z.vs_fmp,z.vs_halted)``) >>
     simp[NoAsms] >> fs[]) >>
  `!name off sz. local_region ce ee.scopes j name off sz <=> local_region ce ee.scopes t name off sz` by
    (rpt gen_tac >> irule copy_buffer_local_region_frame >> qexists `a` >> simp[]) >>
  `lo <= pbase` by
    (qpat_assum `allocas_from lo j` (mp_tac o REWRITE_RULE [allocas_from_def]) >>
     disch_then (drule_then ACCEPT_TAC)) >>
  drule_all_then (map_every assume_tac o CONJUNCTS) snapshot_alloc_rows >>
  suspend "land"
QED

Resume raw_create_snapshot_alloc_mods[site]:
  drule compile_alloc_buffer_parts >> strip_tac >>
  drule_all_then assume_tac actual_alloc_buffer_site >>
  `owner = STRING #"%" (toString a.cs_next_var)` by metis_tac[operand_11] >>
  gvs[Abbr `site`,mk_inst_def] >>
  irule fresh_not_local_ptr >> qexists `a` >> simp[]
QED

Resume raw_create_snapshot_alloc_mods[land]:
  `!i. ~(pbase <= i /\ i < pbase+cap) ==> (i IN tj.t_mem <=> i IN tn.t_mem)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!i. i IN tj.t_mem <=> _` (qspec_then `i` SUBST1_TAC) >>
     qpat_assum `(_ /\ pbase = _) \/ _` strip_assume_tac >> fs[] >> decide_tac) >>
  `return_buf_frame d ce m j /\ (ctx_has_dalloca ctx ==> allocas_below_fmp j)` by
    (conj_tac
     >- (irule return_buf_frame_frame >> qexistsl_tac [`ce`,`t`,`a`] >> fs[ci_mono_def]) >>
     `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func ce cx ee j` by simp[] >>
     qpat_assum `stmt_state_rel _ _ _ _ _ _ j`
       (mp_then Any ACCEPT_TAC bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func ce cx ee j /\ immutable_frame_mods func ce cx ee j /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d ce cx ee Gj tj j /\
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK j,Gj,tj)` by
    suspend "resources" >>
  suspend "finish"
QED

Resume raw_create_snapshot_alloc_mods[resources]:
  gen_tac >> disch_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ t /\ _`
    (drule_then strip_assume_tac) >>
  `typed_copy_frame pbase cap t.vs_memory j.vs_memory /\ lo <= j.vs_alloca_next` by
    (conj_tac >- simp[] >> decide_tac) >>
  `!name off sz. local_region ce ee.scopes t name off sz ==> regions_disjoint pbase cap off sz` by
    metis_tac[] >>
  `FLOOKUP j.vs_allocas site.inst_id = SOME (pbase,cap)` by
    (qpat_assum `site.inst_id = a.cs_next_id` SUBST1_TAC >> FIRST_ASSUM ACCEPT_TAC) >>
  drule_all_then strip_assume_tac local_snapshot_resources_mods >> simp[]
QED

Resume raw_create_snapshot_alloc_mods[finish]:
  `op_taint tj (Var owner) = {}` by fs[ptr_covers_def] >>
  `not_fresh_at b owner /\
   !x. not_fresh_at a x ==> not_fresh_at m x /\ lookup_var x j = lookup_var x t /\
       FLOOKUP Gj x = FLOOKUP G x /\ op_taint tj (Var x) = op_taint tn (Var x)` by
    (fs[ci_mono_def] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `lo <= j.vs_alloca_next` by decide_tac >>
  qexistsl_tac [`buf`,`m`,`site`,`owner`,`pbase`,`j`,`Gj`,`tj`] >>
  qpat_x_assum `j = raw with vs_inst_idx := _` kall_tac >>
  qpat_x_assum `Gj = step_prov _ _ _ _` kall_tac >>
  qpat_x_assum `tj = step_taint _ _ _ _` kall_tac >>
  `lookup_var owner j = SOME (n2w pbase)` by fs[Abbr `pbase`] >>
  `eval_operand snap j = SOME (n2w pbase)` by metis_tac[eval_operand_def] >>
  `site = mk_inst a.cs_next_id ALLOCA [Lit (n2w cap)] [owner]` by simp[Abbr `site`] >>
  rpt (FIRST_ASSUM ACCEPT_TAC ORELSE conj_tac) >>
  qpat_assum `(_ /\ pbase = _) \/ _` mp_tac >> tautLib.TAUT_TAC
QED

Finalise raw_create_snapshot_alloc_mods
