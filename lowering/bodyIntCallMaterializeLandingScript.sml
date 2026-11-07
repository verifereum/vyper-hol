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

Theorem materialization_alloc_landing:
  compile_alloc_buffer sz sa = (buf,sm) /\
  fn_has_code sa sm func /\ stmt_state_rel ctx func ce cx es s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
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
  fs[stmt_state_rel_inst_idx, eval_op_inst_idx, allocas_above_def,
       local_region_def, lookup_var_def] >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `q` >>
      gvs[eval_operand_def, lookup_var_def] >> metis_tac[]) >>
  metis_tac[]
QED

(* The copy snapshot, value, allocation slot and frame belong to the same run.
   Protected slices need not already be backed by the concrete memory list. *)
Theorem immutable_materialization_copy_landing:
  compile_imm_copy_to_memory ctor imm src dst n off sa = ((),sb) /\
  (ctor ==> imm = SOME region /\ eval_operand region s = SOME 0w /\
    regions_disjoint (a+off) (32*n) (b+off) (32*n)) /\
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
  (!p k. P p k ==> regions_disjoint p k (b+off) (32*n)) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    val_in_memory tv v (b+off) u.vs_memory /\
    FLOOKUP u.vs_allocas aid = SOME (b,sz) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    allocas_above lo u /\
    (!p k. P p k ==> mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!q w. eval_operand q s = SOME w ==> eval_operand q u = SOME w) /\
    u.vs_data_section = s.vs_data_section /\ u.vs_immutables = s.vs_immutables /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `?t. immutable_execution_frame sa s sb t /\
    t.vs_memory = (write_memory_with_expansion (b+off)
      (mem_bytes_at (a+off) (32*n)
        (if ctor then s.vs_memory else s.vs_data_section)) s).vs_memory /\
    t.vs_immutables = s.vs_immutables` by
    (Cases_on `ctor` >> gvs[]
     >- (drule compile_imm_copy_to_memory_execution >>
         disch_then (qspec_then `s` mp_tac) >> simp[] >> strip_tac >>
         ` (immutable_transfers F T (n2w a) (n2w b) n off s).vs_memory =
             (mcopy (b+off) (a+off) (32*n) s).vs_memory` by
           (irule immutable_memory_transfers_snapshot >> fs[regions_disjoint_def]) >>
         qexists_tac `s'` >> fs[mcopy_def, read_memory_def, GSYM mem_bytes_at_def]) >>
     drule immutable_compile_runtime_snapshot >>
     disch_then (qspecl_then [`a`, `s`, `b`] mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >>
     qexists_tac `s'` >> fs[GSYM mem_bytes_at_def]) >>
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
  rpt strip_tac >> asm_rewrite_tac[GSYM mem_bytes_at_def] >>
  irule mem_bytes_at_write_disjoint >> fs[regions_disjoint_def, mem_bytes_at_def]
QED
