(* Full-capacity allocation landing for forcing non-memory values. *)
Theory bodyIntCallMaterializeLanding
Ancestors
  bodyIntCallProtectedAlloc bodyIntCallForceLanding placeMemoryStaging
  exprSimAlloc exprSimPrecompiles placeMemoryPrimitiveForward context emitHelperProps
  exprLoweringProps compileEnv venomState venomInst fragGasMode instIdxIndep
  finite_map list rich_list words intCallFrame emitHelper entrySinkExtraction
  immutableCopyExecution immutableConstructorRelation exprSimCopy
  abiDecoderArrayInitExec stmtReasonMemory valueCopy valueEncodingProps valueEncoding
  venomExecSemantics

(* Resource projections of the actual allocation run. *)
Theorem materialization_alloc_run_fields:
  compile_alloc_buffer sz sa = (buf,sm) /\
  run_inst_seq (emitted_insts sa sm) s = OK t /\ fresh_vars_wrt sa s /\
  sz < dimword (:256) ==>
  t.vs_data_section = s.vs_data_section /\
  t.vs_immutables = s.vs_immutables /\
  s.vs_alloca_next <= t.vs_alloca_next /\ fresh_vars_wrt sm t /\
  t.vs_allocas = (abiBuiltinAllocation$abi_builtin_allocate_state sa.cs_next_id sz s).vs_allocas
Proof
  simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def,
       comp_return_def, comp_ignore_bind_def, fresh_id_def, fresh_var_def,
       emit_def] >> strip_tac >>
  gvs[emitted_insts_def, DROP_LENGTH_APPEND, run_inst_seq_def,
      step_inst_base_def, mk_inst_def, exec_alloca_def, eval_operand_def] >>
  gvs[AllCaseEqs(), update_var_def, fresh_vars_wrt_def, FLOOKUP_UPDATE,
      abiBuiltinAllocationTheory.abi_builtin_allocate_state_def]
QED

Theorem materialization_alloc_landing:
  compile_alloc_buffer sz sa = (buf,sm) /\
  fn_has_code sa sm func /\ stmt_state_rel ctx func ce cx es s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\ fresh_vars_wrt sa s /\
  sz < dimword (:256) /\ allocas_above lo s /\
  (!q x. reserved q /\ q = Var x ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u w. gas_marked_path F ctx func s 0 (OK u) /\
    stmt_state_rel ctx func ce cx es u /\
    eval_operand buf.buf_operand u = SOME w /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
    lo <= w2n w /\ w2n w + sz < dimword (:256) /\
    allocas_above lo u /\ u.vs_memory = s.vs_memory /\
    u.vs_data_section = s.vs_data_section /\ u.vs_immutables = s.vs_immutables /\
    s.vs_alloca_next <= u.vs_alloca_next /\ fresh_vars_wrt sm u /\
    u.vs_allocas = (abiBuiltinAllocation$abi_builtin_allocate_state sa.cs_next_id sz s).vs_allocas /\
    (!q. reserved q ==> eval_operand q u = eval_operand q s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!name b len. local_region ce es.scopes u name b len ==>
       regions_disjoint (w2n w) sz b len) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sm p) /\
    ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
    u.vs_inst_idx = LENGTH sm.cs_current_insts
Proof
  strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  drule_all materialization_alloc_run_fields >> strip_tac >>
  `t.vs_labels = s.vs_labels` by (drule_all hash_alloc_buffer_labels >> simp[]) >>
  `allocas_above lo t` by (drule_all alloc_buffer_allocas_above >> simp[]) >>
  `lo <= w2n w` by (fs[allocas_above_def] >> metis_tac[]) >>
  `sm.cs_current_bb = sa.cs_current_bb /\
   sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sm) /\
   EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sm)` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> strip_tac >>
     gvs[fresh_id_def, fresh_var_def, emit_def, comp_bind_def,
         comp_ignore_bind_def, comp_return_def, emitted_insts_def,
         DROP_APPEND, mk_inst_def, is_terminator_def]) >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  `gas_marked_path F ctx func s 0
     (OK (t with vs_inst_idx := LENGTH sm.cs_current_insts))` by
    (irule straight_line_zero_gas_path >> simp[] >> metis_tac[]) >>
  drule gas_marked_path_exec >> strip_tac >>
  drule fragGasPathTheory.gas_path_normal >> strip_tac >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sm.cs_current_insts`, `w`] >>
  fs[stmt_state_rel_inst_idx, eval_op_inst_idx, fresh_vars_wrt_def, allocas_above_def,
       local_region_def, lookup_var_def] >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `q` >>
      gvs[eval_operand_def, lookup_var_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem immutable_materialization_snapshot:
  compile_imm_copy_to_memory ctor imm src dst n off sa = ((),sb) /\
  (ctor ==> imm = SOME region /\ eval_operand region s = SOME 0w /\
    regions_disjoint (a+off) (32*n) (b+off) (32*n)) /\
  eval_operand src s = SOME (n2w a) /\
  eval_operand dst s = SOME (n2w b) /\ fresh_vars_wrt sa s /\
  0 < n /\ a+off+32*n < dimword (:256) /\
  b+off+32*n < dimword (:256) ==>
  ?t. immutable_execution_frame sa s sb t /\
    t.vs_memory = (write_memory_with_expansion (b+off)
      (mem_bytes_at (a+off) (32*n)
        (if ctor then s.vs_memory else s.vs_data_section)) s).vs_memory /\
    t.vs_immutables = s.vs_immutables
Proof
  strip_tac >> Cases_on `ctor` >> gvs[]
  >- (drule compile_imm_copy_to_memory_execution >>
      disch_then (qspec_then `s` mp_tac) >> simp[] >> strip_tac >>
      ` (immutable_transfers F T (n2w a) (n2w b) n off s).vs_memory =
          (mcopy (b+off) (a+off) (32*n) s).vs_memory` by
        (irule immutable_memory_transfers_snapshot >> fs[regions_disjoint_def]) >>
      qexists_tac `s'` >> fs[mcopy_def, read_memory_def, GSYM mem_bytes_at_def]) >>
  drule immutable_compile_runtime_snapshot >>
  disch_then (qspecl_then [`a`, `s`, `b`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qexists_tac `s'` >> fs[GSYM mem_bytes_at_def]
QED

(* Project resource facts onto a supplied operational run, not a second
   normal-path endpoint (whose instruction index convention may differ). *)
Theorem immutable_materialization_run_frame:
  compile_imm_copy_to_memory ctor imm src dst n off sa = ((),sb) /\
  copy_old_operand sa src /\ copy_old_operand sa dst /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  (!region. ctor /\ imm = SOME region ==>
    eval_operand region s = SOME 0w /\ copy_old_operand sa region) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  copy_static t = copy_static s /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> Cases_on `ctor` >> gvs[]
  >- (drule copy_ctor_run >> disch_then (qspec_then `s` mp_tac) >>
      simp[] >> strip_tac >> gvs[copy_runtime_frame_def]) >>
  drule_all copy_runtime_run >> strip_tac >> gvs[copy_runtime_frame_def]
QED

(* The copy snapshot, value, allocation slot and frame belong to the same run.
   Protected slices need not already be backed by the concrete memory list. *)
Theorem immutable_materialization_copy_landing:
  compile_imm_copy_to_memory ctor imm src dst n off sa = ((),sb) /\
  (ctor ==> imm = SOME region /\ eval_operand region s = SOME 0w /\
    regions_disjoint (a+off) (32*n) (b+off) (32*n)) /\
  copy_old_operand sa src /\ copy_old_operand sa dst /\
  (ctor ==> copy_old_operand sa region) /\
  eval_operand src s = SOME (n2w a) /\
  eval_operand dst s = SOME (n2w b) /\ fresh_vars_wrt sa s /\
  0 < n /\ a + off + 32*n < dimword (:256) /\
  b + off + 32*n < dimword (:256) /\
  val_in_memory tv v (a+off)
    (if ctor then s.vs_memory else s.vs_data_section) /\ val_wf tv v /\
  type_memory_size tv = 32*n /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
  off + 32*n <= sz /\ b+sz < dimword (:256) /\ lo <= b /\
  allocas_above lo s /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    val_in_memory tv v (b+off) u.vs_memory /\
    FLOOKUP u.vs_allocas aid = SOME (b,sz) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    allocas_above lo u /\
    (!p k. regions_disjoint p k (b+off) (32*n) ==>
      mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!q w. eval_operand q s = SOME w ==> eval_operand q u = SOME w) /\
    (!q. copy_old_operand sa q ==> eval_operand q u = eval_operand q s) /\
    copy_static u = copy_static s /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    LENGTH s.vs_memory <= LENGTH u.vs_memory /\
    u.vs_data_section = s.vs_data_section /\ u.vs_immutables = s.vs_immutables /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!ce cx es inst. stmt_state_rel ctx func ce cx es s /\
      local_ptrs_reserved ce sa /\ MEM inst (fn_insts func) /\
      inst.inst_opcode = ALLOCA /\ inst.inst_id = aid /\
      (!name lb len. local_region ce es.scopes s name lb len ==>
        b+sz <= lb \/ lb+len <= b) ==>
      stmt_state_rel ctx func ce cx es u)
Proof
  strip_tac >>
  drule_all immutable_materialization_snapshot >> strip_tac >>
  `same_blocks sa sb /\ ?is. sb.cs_current_insts = sa.cs_current_insts ++ is /\
     EVERY (\i. MEM i.inst_opcode [ADD; ILOAD; DLOAD; MSTORE]) is` by
    (Cases_on `ctor` >> gvs[]
     >- (drule code_ctor_copy_insts >> strip_tac >> simp[] >>
         fs[EVERY_MEM] >> metis_tac[]) >>
     drule code_copy_insts >> strip_tac >> simp[] >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  `emitted_insts sa sb = is` by
    simp[emitted_insts_def, DROP_APPEND] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
      ~is_alloca_op i.inst_opcode) is /\
   EVERY (\i. i.inst_opcode <> GAS) is` by
    (fs[EVERY_MEM] >> rpt strip_tac >> res_tac >>
     gvs[is_terminator_def, is_alloca_op_def]) >>
  fs[immutable_execution_frame_def, immutable_operand_frame_def] >>
  `!reg. ctor /\ imm = SOME reg ==>
     eval_operand reg s = SOME 0w /\ copy_old_operand sa reg` by
    (rpt strip_tac >> gvs[]) >>
  `run_inst_seq (emitted_insts sa sb) s = OK t` by simp[] >>
  drule_all immutable_materialization_run_frame >> strip_tac >>
  drule exprSimStorageCopyTheory.copy_static_fields >> strip_tac >>
  drule_all abi_decoder_guard_sequence_fields >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) is` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  `gas_marked_path F ctx func s 0
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule straight_line_zero_gas_path >>
     simp[] >> qexistsl_tac [`is`, `sa`] >> fs[same_blocks_def]) >>
  `allocas_above lo (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (fs[allocas_above_def] >> metis_tac[]) >>
  `t.vs_current_bb = sb.cs_current_bb` by fs[same_blocks_def] >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  fs[eval_op_inst_idx] >>
  conj_tac
  >- (asm_rewrite_tac[GSYM mem_bytes_at_def] >>
      irule immutable_copy_memory_value >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> asm_rewrite_tac[GSYM mem_bytes_at_def] >>
      irule mem_bytes_at_write_disjoint >> fs[regions_disjoint_def, mem_bytes_at_def]) >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `q` >>
      gvs[copy_old_operand_def, eval_operand_def, lookup_var_def,
          exprSimStorageCopyTheory.copy_static_def]) >>
  fs[exprSimStorageCopyTheory.copy_static_def, lookup_var_def,
     immutableMemoryFrameTheory.immutable_write_memory_capacity] >>
  rpt strip_tac >> irule copy_buffer_state_rel_frame >>
  qexistsl_tac [`b`, `inst`, `s`, `sa`, `sz`] >>
  simp[exprSimStorageCopyTheory.copy_static_def, lookup_var_def,
       immutableMemoryFrameTheory.immutable_write_memory_capacity] >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >> asm_rewrite_tac[GSYM mem_bytes_at_def] >>
  irule mem_bytes_at_write_disjoint >>
  fs[regions_disjoint_def, mem_bytes_at_def] >> decide_tac
QED


(* Allocation and immutable copying are sequenced at their actual landings.
   Constructor separation is stated against the allocator's computed map. *)
Theorem immutable_alloc_materialization_landing:
  compile_alloc_buffer sz sa = (buf,sm) /\
  compile_imm_copy_to_memory ctor imm src buf.buf_operand n 0 sm = ((),sb) /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ fresh_vars_wrt sa s /\
  sz < dimword (:256) /\ 32*n <= sz /\ 0 < n /\ allocas_above lo s /\
  copy_old_operand sa src /\ eval_operand src s = SOME (n2w a) /\
  (ctor ==> imm = SOME region /\ eval_operand region s = SOME 0w /\
    copy_old_operand sa region /\
    (!b. FLOOKUP (abiBuiltinAllocation$abi_builtin_allocate_state sa.cs_next_id sz s).vs_allocas
       sa.cs_next_id = SOME (b,sz) ==> regions_disjoint a (32*n) b (32*n))) /\
  a+32*n < dimword (:256) /\ type_memory_size tv = 32*n /\ val_wf tv v /\
  val_in_memory tv v a (if ctor then s.vs_memory else s.vs_data_section) /\
  (!q x. reserved q /\ q = Var x ==> not_fresh_at sa x) /\
  (!p k. P p k ==> p+k <= lo) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u w. gas_marked_path F ctx func s 0 (OK u) /\
    stmt_state_rel ctx func ce cx es u /\
    eval_operand buf.buf_operand u = SOME w /\ val_in_memory tv v (w2n w) u.vs_memory /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
    lo <= w2n w /\ w2n w+sz < dimword (:256) /\ allocas_above lo u /\
    s.vs_alloca_next <= u.vs_alloca_next /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!p k. P p k ==> mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!q. reserved q ==> eval_operand q u = eval_operand q s) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `!q x. (reserved q \/ q = src \/ (ctor /\ q = region)) /\ q = Var x ==>
      not_fresh_at sa x` by (fs[copy_old_operand_def] >> metis_tac[]) >>
  mp_tac (Q.INST [`reserved` |-> `\q. reserved q \/ q = src \/ (ctor /\ q = region)`]
    (SPEC_ALL materialization_alloc_landing)) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  rename1 `gas_marked_path F ctx func s 0 (OK mid)` >>
  `!q. reserved q \/ q = src \/ (ctor /\ q = region) ==>
     eval_operand q mid = eval_operand q s` by simp[] >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (drule loweringHaltTheory.compile_alloc_buffer_parts >> simp[]) >>
  `local_ptrs_reserved ce sm` by (irule local_ptrs_reserved_next_var >> metis_tac[]) >>
  `copy_old_operand sm src /\ copy_old_operand sm buf.buf_operand /\
   (ctor ==> copy_old_operand sm region)` by
    (fs[copy_old_operand_def] >> gvs[not_fresh_at_def]) >>
  `eval_operand src mid = SOME (n2w a) /\
   eval_operand buf.buf_operand mid = SOME (n2w (w2n w))` by simp[] >>
  `(ctor ==> imm = SOME region /\ eval_operand region mid = SOME 0w /\
      regions_disjoint a (32*n) (w2n w) (32*n)) /\
    w2n w+32*n < dimword (:256) /\
    val_in_memory tv v a (if ctor then mid.vs_memory else mid.vs_data_section)` by
    (simp[] >> gvs[]) >>
  drule_all (SRULE [] (Q.INST [`s` |-> `mid`, `b` |-> `w2n w`, `off` |-> `0`]
    (SPEC_ALL immutable_materialization_copy_landing))) >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all buffer_alloc_code >> strip_tac >>
  `stmt_state_rel ctx func ce cx es u` by
    (qpat_x_assum `!ce cx es inst. _` irule >>
     conj_tac >- (fs[regions_disjoint_def] >> metis_tac[]) >>
     conj_tac >-
       (qexists_tac `mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
          [STRING #"%" (toString sa.cs_next_var)]` >> simp[mk_inst_def]) >>
     simp[]) >>
  `gas_marked_path F ctx func s 0 (OK u)` by
    (drule_all gas_marked_path_then >> simp[]) >>
  qexistsl_tac [`u`, `w`] >> simp[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >-
    (qx_gen_tac `addr` >> qx_gen_tac `len` >> strip_tac >>
     `regions_disjoint addr len (w2n w) (32*n)` by
       (simp[regions_disjoint_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
     metis_tac[]) >>
  qx_gen_tac `q` >> strip_tac >>
  `copy_old_operand sm q` by
    (simp[copy_old_operand_def] >> rpt strip_tac >>
     gvs[not_fresh_at_def] >> metis_tac[]) >>
  metis_tac[]
QED
