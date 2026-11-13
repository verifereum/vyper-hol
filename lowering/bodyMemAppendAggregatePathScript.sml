(* Counted paths for aggregate storage Append. *)
Theory bodyMemAppendAggregatePath
Ancestors
  bodyMemAssignTopCopyPaths placeStoreCopyPath bodyMemAppendFacts
  exprLowering emitHelper emitHelperProps compileEnv
  fragGasMode fragGasPathMem fragExecMem venomState venomInst venomExecSemantics
  words list rich_list pair fragExec exprSimStorageCopy stmtSimAppendStorage
  stmtSimAppendStorageCompose
  loweringStateRelDefs stateFrame exprLoweringProps varsExt freshWrites
  appendStorageStageTransportPtr bodyDeclMemoryCounted instMemFrontier memSafeRun
  allocaFootprint fragGasSeqMem

Theorem append_sparse_header_load_mem[local]:
  emit_op MLOAD [arg] sa = (op,sb) /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand arg s = SOME w /\ w2n w + 32 <= s.vs_alloca_next ==>
  gas_path_mem ctx func s 0
    (OK ((update_var (STRING #"%" (toString sa.cs_next_var))
       (mload (w2n w) s) s) with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  `?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
     DROP s.vs_inst_idx bb.bb_instructions =
       [mk_inst sa.cs_next_id MLOAD [arg]
         [STRING #"%" (toString sa.cs_next_var)]] ++ rest` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
     simp[DROP_APPEND, DROP_LENGTH_TOO_LONG]) >>
  drule run_inst_seq_gas_path_mem >>
  disch_then (qspecl_then
    [`[mk_inst sa.cs_next_id MLOAD [arg]
        [STRING #"%" (toString sa.cs_next_var)]]`,
     `update_var (STRING #"%" (toString sa.cs_next_var)) (mload (w2n w) s) s`,
     `ctx`, `func`, `bb`] mp_tac) >>
  simp[is_terminator_def, run_inst_seq_mem_ok_def,
       run_inst_seq_def, below_frontier_MLOAD, step_MLOAD,
       mk_inst_def, IS_PREFIX_APPEND, venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_read1_def, eval_operand_def,
       venomStateTheory.eval_operands_def, arithmeticTheory.ADD1]
QED

Theorem append_sparse_slot_store_mem[local]:
  emit_void (if tr then TSTORE else SSTORE) [dst;src] sa = ((),sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand dst s = SOME dw /\ eval_operand src s = SOME w ==>
  gas_path_mem ctx func s 0
    (OK (((if tr then tstore else sstore) dw w s)
      with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_same_blocks >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by gvs[same_blocks_def] >>
  `?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
     DROP s.vs_inst_idx bb.bb_instructions =
       [mk_inst sa.cs_next_id (if tr then TSTORE else SSTORE) [dst;src] []] ++ rest` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
     simp[DROP_APPEND, DROP_LENGTH_TOO_LONG]) >>
  `run_inst_seq_mem_ok
     [mk_inst sa.cs_next_id (if tr then TSTORE else SSTORE) [dst;src] []] s` by
    (simp[run_inst_seq_mem_ok_def] >> conj_tac
     >- (irule below_frontier_no_ranges >> Cases_on `tr` >> simp[mk_inst_def]) >>
     Cases_on `tr` >> simp[inst_dload_in_section_def, mk_inst_def,
       venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_write2_def, venomStateTheory.eval_operands_def]) >>
  drule run_inst_seq_gas_path_mem >>
  disch_then (qspecl_then
    [`[mk_inst sa.cs_next_id (if tr then TSTORE else SSTORE) [dst;src] []]`,
     `(if tr then tstore else sstore) dw w s`, `ctx`, `func`, `bb`] mp_tac) >>
  Cases_on `tr` >>
  simp[is_terminator_def, run_inst_seq_def,
       mk_inst_def, IS_PREFIX_APPEND, venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_write2_def, venomStateTheory.eval_operands_def,
       arithmeticTheory.ADD1]
QED
Theorem append_sparse_word_path_mem[local]:
  emit_op MLOAD [src] sa = (loaded,sm) /\
  emit_void (if tr then TSTORE else SSTORE) [dst;loaded] sm = ((),sb) /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand dst s = SOME k /\ eval_operand src s = SOME sw /\
  w2n sw + 32 <= s.vs_alloca_next ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    store_copy_normalize s t = (if tr then tstore else sstore) k (mload (w2n sw) s) s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_labels = s.vs_labels /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_alloca_next = s.vs_alloca_next /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule_all append_sparse_header_load_mem >>
  disch_then (qspec_then `ctx` assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_mem ctx func s 0 (OK u)` >>
  `loaded = Var (STRING #"%" (toString sa.cs_next_var)) /\
   sm.cs_current_bb = sa.cs_current_bb /\
   LENGTH sm.cs_current_insts = SUC (LENGTH sa.cs_current_insts)` by
    gvs[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  `!x. not_fresh_at sa x ==> x <> STRING #"%" (toString sa.cs_next_var)` by
    (rpt strip_tac >> gvs[not_fresh_at_def]) >>
  `eval_operand dst u = SOME k /\
   eval_operand loaded u = SOME (mload (w2n sw) s)` by
    (Cases_on `dst` >> gvs[Abbr `u`, eval_operand_def, lookup_var_def,
       update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]) >>
  `~u.vs_halted /\ ~u.vs_call_ctx.cc_static /\
   u.vs_current_bb = sm.cs_current_bb /\
   u.vs_inst_idx = LENGTH sm.cs_current_insts` by simp[Abbr `u`, update_var_def] >>
  drule_all append_sparse_slot_store_mem >>
  disch_then (qspec_then `ctx` assume_tac) >>
  qexists_tac `((if tr then tstore else sstore) k (mload (w2n sw) s) u)
    with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  conj_tac
  >- (simp[gas_marked_path_def] >>
      metis_tac[fragGasPathMemTheory.gas_path_mem_then, arithmeticTheory.ADD_CLAUSES]) >>
  `sb.cs_current_bb = sm.cs_current_bb` by
    metis_tac[emit_void_same_blocks, same_blocks_def] >>
  Cases_on `tr` >>
  simp[Abbr `u`, stmtSimStoreCopyTheory.store_copy_normalize_def, sstore_def, tstore_def,
       update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
       venom_state_component_equality] >> metis_tac[]
QED


Theorem append_sparse_bulk_path_mem[local]:
  (if tr then compile_memory_to_transient else compile_memory_to_storage)
    src dst n sa = (result,sb) /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_call_ctx.cc_static /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  n < dimword (:256) /\ w2n sw + 32*n < dimword (:256) /\
  w2n sw + 32*n <= s.vs_alloca_next ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    store_copy_normalize s t =
      FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
        (mload (w2n sw + 32*j) s) q) s (COUNT_LIST n) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_labels = s.vs_labels /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_alloca_next = s.vs_alloca_next /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `compile_word_copy_loop src dst n LocMemory
     (if tr then LocTransient else LocStorage) F sa = (result,sb)` by
    (Cases_on `tr` >> gvs[contextTheory.compile_memory_to_transient_def,
                          contextTheory.compile_memory_to_storage_def]) >>
  drule_at (Pat `compile_word_copy_loop _ _ _ _ _ _ _ = _`)
    topcopy_compile_loop_path >>
  disch_then (qspecl_then [`ctx`, `func`, `s`, `sw`, `dw`] mp_tac) >>
  simp[] >>
  (impl_tac >- (Cases_on `tr` >> simp[] >> metis_tac[])) >> strip_tac >>
  qexists_tac `t` >> simp[] >>
  drule place_store_copy_frame_observations >> strip_tac >>
  drule topcopy_frame_frontier >> strip_tac >> simp[] >>
  gvs[stmtSimStoreCopyTheory.store_copy_frame_def,
      stmtSimStoreCopyTheory.store_copy_prefix_def] >>
  irule listTheory.FOLDL_CONG >> simp[MEM_COUNT_LIST] >> rpt strip_tac >>
  `32*x + w2n sw < dimword (:256)` by (simp[dimword_def] >> decide_tac) >>
  `sw + n2w x * 32w = n2w (32*x + w2n sw)` by
    (pure_rewrite_tac[GSYM word_add_n2w, GSYM word_mul_n2w, n2w_w2n] >>
     wordsLib.WORD_DECIDE_TAC) >>
  Cases_on `tr` >> simp[w2n_n2w, arithmeticTheory.LESS_MOD] >> gvs[]
QED

Theorem append_sparse_static_checked[local]:
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv.
      evaluate_type tenv fty = SOME tv ==> sz = type_memory_size tv) fields) /\
  ~is_abi_dynamic cenv.ce_struct_fields ty /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\
  compile_store_slots cenv src slot ty tr sa = ((),sb) /\
  (!x. src = Var x \/ slot = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand slot s = SOME dw /\
  val_in_memory tv v (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size tv < dimword (:256) /\
  w2n sw + type_memory_size tv <= s.vs_alloca_next /\
  w2n dw + type_slot_size tv <= dimword (:256) /\
  encode_value tv v = SOME writes /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_call_ctx.cc_static ==>
  ?t ks. gas_marked_path T ctx func s 0 (OK t) /\
    store_copy_normalize s t =
      FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
        (mload (w2n sw + 32*j) s) q) s ks /\
    (!j. MEM j ks <=> MEM j (MAP FST writes)) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_labels = s.vs_labels /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_alloca_next = s.vs_alloca_next /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `type_memory_bytes cenv ty = type_memory_size tv` by
    (irule typedMemoryCopyTheory.typed_copy_memory_size >> metis_tac[]) >>
  `~vyper_is_dynamic tenv ty` by
    (drule_all abiTypeBoundPropsTheory.abi_props_vyper_typed >> simp[]) >>
  `!j. MEM j (MAP FST writes) <=> j < type_slot_size tv` by
    (gen_tac >> eq_tac
     >- metis_tac[CONJUNCT1 vyperEncodeDecodeTheory.encode_writes_bounded] >>
     strip_tac >> irule vyperStorageCoverageTheory.encode_value_live_written >>
     metis_tac[]) >>
  `type_memory_bytes cenv ty DIV 32 = type_slot_size tv` by
    simp[valueEncodingPropsTheory.type_memory_size_slots] >>
  qpat_x_assum `compile_store_slots _ _ _ _ _ _ = _` mp_tac >>
  simp[Once contextTheory.compile_store_slots_def, comp_bind_def, comp_return_def] >>
  Cases_on `type_slot_size tv = 1`
  >- (simp[comp_bind_def] >> pairarg_tac >> strip_tac >> gvs[] >>
      rename1 `emit_op MLOAD [src] sa = (loaded,sm)` >>
      `ci_mono sa sm /\ ci_mono sm sb` by
        metis_tac[typedMemoryCopyTheory.typed_copy_emit_op_mono,
                  ci_mono_emit_void, pairTheory.SND] >>
      `fn_has_code sa sm func /\ fn_has_code sm sb func` by
        (gvs[ci_mono_def] >> metis_tac[fragExecTheory.fn_has_code_split]) >>
      `!x. slot = Var x ==> not_fresh_at sa x` by metis_tac[] >>
      `w2n sw + 32 <= s.vs_alloca_next` by
        gvs[valueEncodingPropsTheory.type_memory_size_slots] >>
      drule_all append_sparse_word_path_mem >>
      disch_then (qspec_then `ctx` strip_assume_tac) >>
      qexistsl_tac [`t`, `[0]`] >> simp[]) >>
  simp[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  `type_slot_size tv < dimword (:256) /\
   w2n sw + 32 * type_slot_size tv < dimword (:256) /\
   w2n sw + 32 * type_slot_size tv <= s.vs_alloca_next` by
    (fs[valueEncodingPropsTheory.type_memory_size_slots] >> decide_tac) >>
  drule_all append_sparse_bulk_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexistsl_tac [`t`, `COUNT_LIST (type_slot_size tv)`] >> simp[MEM_COUNT_LIST]
QED

Theorem append_sparse_bytes_count_mem_ok[local]:
  compile_bytestring_word_count src sa = (out,sb) /\
  eval_operand src s = SOME sw /\ w2n sw + 32 <= s.vs_alloca_next ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >>
  gvs[contextTheory.compile_bytestring_word_count_def, emit_op_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_id_def, fresh_var_def, emit_def] >>
  simp[emitted_insts_def, DROP_APPEND, arithmeticTheory.SUB_PLUS] >>
  simp[Once run_inst_seq_mem_ok_def, below_frontier_MLOAD, step_MLOAD] >>
  `!id ops outs u. inst_mem_below_frontier (mk_inst id ADD ops outs) u /\
     inst_mem_below_frontier (mk_inst id SHR ops outs) u` by
    (rpt strip_tac >> irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  Cases_on `step_inst_base (mk_inst sa.cs_next_id MLOAD [src]
    [STRING #"%" (toString sa.cs_next_var)]) s` >> simp[] >>
  simp[Once run_inst_seq_mem_ok_def] >>
  rename1 `step_inst_base _ s1` >>
  Cases_on `step_inst_base
    (mk_inst (sa.cs_next_id + 1) ADD
      [Var (STRING #"%" (toString sa.cs_next_var)); Lit 63w]
      [STRING #"%" (toString (sa.cs_next_var + 1))]) s1` >>
  simp[run_inst_seq_mem_ok_def] >>
  rename1 `step_inst_base _ s2` >>
  Cases_on `step_inst_base
    (mk_inst (sa.cs_next_id + 2) SHR
      [Lit 5w; Var (STRING #"%" (toString (sa.cs_next_var + 1)))]
      [STRING #"%" (toString (sa.cs_next_var + 2))]) s2` >> simp[]
QED

Theorem append_sparse_bytes_count_checked[local]:
  compile_bytestring_word_count src sa = (out,sb) /\
  fn_has_code sa sb func /\ eval_operand src s = SOME sw /\
  mload (w2n sw) s = n2w len /\ len + 63 < dimword (:256) /\
  w2n sw + 32 <= s.vs_alloca_next /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    eval_operand out t = SOME (n2w (1 + vfmConstants$word_size len)) /\
    (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  drule_all bytestringCopyExecutionTheory.bytestring_word_count_run >> strip_tac >>
  drule bytestringCopyExecutionTheory.bytestring_word_count_shape >> strip_tac >>
  drule_all append_sparse_bytes_count_mem_ok >> strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[fn_has_code_def, same_blocks_def, IS_PREFIX_APPEND] >>
     qexists_tac `l` >> simp[DROP_APPEND, arithmeticTheory.SUB_PLUS]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
   EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  drule_all topcopy_seq_path >>
  disch_then (qspec_then `ctx` assume_tac) >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  fs[same_blocks_def, eval_operand_def, lookup_var_def] >>
  fs[venom_state_component_equality] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem append_sparse_runtime_header_checked[local]:
  !ctx func bb sa loc b k sbase i n s cv tv id exit loop_body cop.
    store_copy_frame sa loc b k sbase i s /\
    eval_operand (Var cv) s = SOME (n2w i) /\
    eval_operand cop s = SOME (n2w n) /\
    cv <> tv /\ (!x. not_fresh_at sa x ==> x <> tv) /\
    i <= n /\ n < dimword (:256) /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx =
      SOME (mk_inst id EQ [Var cv;cop] [tv]) /\
    get_instruction bb (SUC s.vs_inst_idx) =
      SOME (mk_inst (id+1) JNZ [Var tv;Label exit;Label loop_body] []) ==>
    ?t. gas_marked_path T ctx func s 0 (OK t) /\
      store_copy_frame sa loc b k sbase i t /\
      eval_operand (Var cv) t = SOME (n2w i) /\
      t.vs_current_bb = (if i = n then exit else loop_body) /\
      t.vs_inst_idx = 0 /\ ~t.vs_halted
Proof
  rpt gen_tac >> strip_tac >>
  `((n2w i:bytes32) = n2w n) = (i = n)` by
    (`i < dimword (:256)` by decide_tac >> simp[n2w_11, arithmeticTheory.LESS_MOD]) >>
  qabbrev_tac `u = update_var tv (bool_to_word (i = n)) s` >>
  qabbrev_tac `r = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  `step_inst_base (mk_inst id EQ [Var cv;cop] [tv]) s = OK u` by
    (simp[Abbr `u`] >>
     qpat_assum `(n2w i = n2w n) = (i = n)`
       (fn th => once_rewrite_tac [GSYM th]) >>
     irule step_EQ >> simp[]) >>
  `gas_path_mem_edge ctx func s 0 (OK r)` by
    (drule_at (Pat `step_inst_base _ _ = _`) straight_line_mem_edge >>
     disch_then (qspecl_then [`func`, `ctx`, `bb`] mp_tac) >>
     simp[mk_inst_def, is_terminator_def, Abbr `r`,
          memSafeRunTheory.inst_dload_in_section_def] >>
     disch_then irule >>
     irule instMemFrontierTheory.below_frontier_no_ranges >> simp[mk_inst_def]) >>
  `gas_marked_path T ctx func s 0 (OK r)` by
    (simp[gas_marked_path_def] >>
     drule (cj 2 gas_path_mem_rules) >>
     disch_then (qspec_then `0` mp_tac) >> simp[] >>
     disch_then irule >> irule (cj 1 gas_path_mem_rules) >>
     simp[Abbr `r`, Abbr `u`, update_var_def]) >>
  `eval_operand (Var tv) r = SOME (bool_to_word (i = n)) /\
   r.vs_current_bb = s.vs_current_bb /\ r.vs_inst_idx = SUC s.vs_inst_idx /\
   ~r.vs_halted` by
    simp[Abbr `r`, Abbr `u`, eval_operand_def, lookup_var_update_var,
         update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  `step_inst_base (mk_inst (id+1) JNZ [Var tv;Label exit;Label loop_body] []) r =
    OK (jump_to (if i = n then exit else loop_body) r)` by
    (simp[stepInstBaseLib.simp_opcode_clause ``JNZ``, mk_inst_def] >>
     Cases_on `i = n` >> gvs[bool_to_word_def]) >>
  `gas_marked_path T ctx func r 0
    (OK (jump_to (if i = n then exit else loop_body) r))` by
    (irule topcopy_jump_path >> simp[] >>
     qexistsl_tac [`bb`, `mk_inst (id+1) JNZ [Var tv;Label exit;Label loop_body] []`] >>
     simp[mk_inst_def]) >>
  qexists_tac `jump_to (if i = n then exit else loop_body) r` >>
  conj_tac
  >- (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_marked_path_then)) >>
      qexists_tac `r` >> simp[]) >>
  `store_copy_frame sa loc b k sbase i u` by
    (simp[Abbr `u`] >> irule topcopy_frame_update >> metis_tac[]) >>
  simp[Abbr `r`, Abbr `u`, jump_to_def, eval_operand_def,
       lookup_var_update_var, update_var_def] >>
  gvs[eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem append_sparse_runtime_loop_checked[local]:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_word_copy_loop_op src dst cop LocMemory loc F sa = (u,sb) /\
  fn_has_code sa sb func /\ n < dimword (:256) /\
  w2n b + 32*n <= s0.vs_alloca_next /\
  (!x. src = Var x \/ dst = Var x \/ cop = Var x ==> not_fresh_at sa x) /\
  eval_operand src s0 = SOME b /\ eval_operand dst s0 = SOME k /\
  eval_operand cop s0 = SOME (n2w n) /\
  ~s0.vs_call_ctx.cc_static /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s0 0 (OK t) /\
      store_copy_frame sa loc b k s0 n t /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  drule_all place_store_runtime_copy_code >> strip_tac >>
  map_every (fn q => qpat_x_assum q kall_tac)
    [`compile_word_copy_loop_op _ _ _ _ _ _ _ = _`, `fn_has_code _ _ _`] >>
  `!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  `!j s. j <= n /\ store_copy_frame sa loc b k s0 j s /\
     eval_operand (Var cv) s = SOME (n2w j) /\ ~s.vs_halted /\
     s.vs_current_bb = hdr /\ s.vs_inst_idx = 0 ==>
     ?t. gas_marked_path T ctx func s 0 (OK t) /\
       store_copy_frame sa loc b k s0 j t /\
       eval_operand (Var cv) t = SOME (n2w j) /\ ~t.vs_halted /\
       t.vs_current_bb = (if j=n then exit else body_lbl) /\ t.vs_inst_idx = 0` by
    (suspend "header") >>
  `!j s. j < n /\ store_copy_frame sa loc b k s0 j s /\
     eval_operand (Var cv) s = SOME (n2w j) /\ ~s.vs_halted /\
     s.vs_current_bb = body_lbl /\ s.vs_inst_idx = 0 ==>
     ?t. gas_marked_path T ctx func s 0 (OK t) /\
       store_copy_frame sa loc b k s0 (SUC j) t /\
       eval_operand (Var cv) t = SOME (n2w (SUC j)) /\ ~t.vs_halted /\
       t.vs_current_bb = hdr /\ t.vs_inst_idx = 0` by
    (suspend "body") >>
  suspend "entry"
QED

Resume append_sparse_runtime_loop_checked[header]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `isPREFIX [mk_inst _ ASSIGN _ _; _] _` kall_tac >>
  qpat_x_assum `isPREFIX (mk_inst _ MUL _ _ :: _) _` kall_tac >>
  `cv <> tv /\ (!x. not_fresh_at sa x ==> x <> tv)` by
    (fs[ALL_DISTINCT] >> metis_tac[]) >>
  `eval_operand cop s = SOME (n2w n)` by
    (irule topcopy_frame_operand >> metis_tac[]) >>
  `isPREFIX [mk_inst idh EQ [Var cv;cop] [tv];
      mk_inst (idh+1) JNZ [Var tv;Label exit;Label body_lbl] []]
      (DROP 0 bbh.bb_instructions)` by simp[Excl "isPREFIX"] >>
  drule fragGasSeqAbortTheory.instruction_prefix_cursor >> strip_tac >>
  qpat_x_assum `isPREFIX [_] (DROP _ _)`
    (strip_assume_tac o MATCH_MP fragGasSeqAbortTheory.instruction_prefix_cursor) >>
  `get_instruction bbh s.vs_inst_idx = SOME (mk_inst idh EQ [Var cv;cop] [tv]) /\
   get_instruction bbh (SUC s.vs_inst_idx) =
     SOME (mk_inst (idh+1) JNZ [Var tv;Label exit;Label body_lbl] [])` by fs[] >>
  `lookup_block s.vs_current_bb func.fn_blocks = SOME bbh` by simp[] >>
  drule_all append_sparse_runtime_header_checked >>
  disch_then (qspec_then `ctx` mp_tac) >> metis_tac[]
QED

Resume append_sparse_runtime_loop_checked[body]:
  qpat_x_assum `!j s. j <= n /\ _ ==> _` kall_tac >>
  qpat_x_assum `isPREFIX [mk_inst _ ASSIGN _ _; _] _` kall_tac >>
  qpat_x_assum `isPREFIX [mk_inst _ EQ _ _; _] _` kall_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `isPREFIX (mk_inst _ MUL _ _ :: _) _`
    (strip_assume_tac o MATCH_MP
      (SRULE [Excl "isPREFIX"]
        (Q.INST [`k` |-> `0`] fragGasSeqAbortTheory.instruction_prefix_cursor))) >>
  ntac 7 (qpat_x_assum `isPREFIX (_::_) (DROP _ _)`
    (strip_assume_tac o MATCH_MP fragGasSeqAbortTheory.instruction_prefix_cursor)) >>
  fs[arithmeticTheory.ADD1] >>
  `?r. gas_marked_path T ctx func s 0 (OK r) /\
       store_copy_frame sa loc b k s0 (SUC j) r /\
       eval_operand (Var cv) r = SOME (n2w (SUC j)) /\
       r.vs_current_bb = s.vs_current_bb /\
       r.vs_inst_idx = s.vs_inst_idx+7 /\ ~r.vs_halted` by
    (`w2n b + 32*(j+1) <= s0.vs_alloca_next` by decide_tac >>
     irule topcopy_body_path >> simp[] >>
     qexistsl_tac [`dst`, `dv`, `idb`, `mv`, `nv`, `src`, `sv`, `vv`] >>
     simp[] >> fs[ALL_DISTINCT] >> metis_tac[]) >>
  `gas_marked_path T ctx func r 0 (OK (jump_to hdr r))` by
    (irule topcopy_jump_path >>
     simp[mk_inst_def, stepInstBaseLib.simp_opcode_clause ``JMP``]) >>
  qexists_tac `jump_to hdr r` >>
  (conj_tac
   >- (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_marked_path_then)) >>
       qexists_tac `r` >> simp[])) >>
  gvs[jump_to_def, eval_operand_def, lookup_var_def, arithmeticTheory.ADD1]
QED

Resume append_sparse_runtime_loop_checked[entry]:
  qpat_x_assum `isPREFIX (mk_inst _ MUL _ _ :: _) _` kall_tac >>
  qpat_x_assum `isPREFIX [mk_inst _ EQ _ _; _] _` kall_tac >>
  `!x. not_fresh_at sa x ==> x <> cv` by (fs[] >> metis_tac[]) >>
  `~not_fresh_at sa cv` by metis_tac[] >>
  qpat_x_assum `isPREFIX [mk_inst _ ASSIGN _ _; _] _`
    (strip_assume_tac o MATCH_MP fragGasSeqAbortTheory.instruction_prefix_cursor) >>
  qpat_x_assum `isPREFIX [_] (DROP _ _)`
    (strip_assume_tac o MATCH_MP fragGasSeqAbortTheory.instruction_prefix_cursor) >>
  `?r. gas_marked_path T ctx func s0 0 (OK r) /\
       store_copy_frame sa loc b k s0 0 r /\
       eval_operand (Var cv) r = SOME 0w /\
       r.vs_current_bb = s0.vs_current_bb /\
       r.vs_inst_idx = SUC s0.vs_inst_idx /\ ~r.vs_halted` by
    (irule topcopy_init_path >> simp[] >> qexists_tac `id0` >> simp[]) >>
  `gas_marked_path T ctx func r 0 (OK (jump_to hdr r))` by
    (fs[arithmeticTheory.ADD1] >> irule topcopy_jump_path >>
     simp[mk_inst_def, stepInstBaseLib.simp_opcode_clause ``JMP``]) >>
  `?t. gas_marked_path T ctx func (jump_to hdr r) 0 (OK t) /\
       store_copy_frame sa loc b k s0 n t /\ ~t.vs_halted /\
       t.vs_current_bb = exit /\ t.vs_inst_idx = 0` by
    (irule topcopy_loop_induction >>
     conj_tac >- simp[jump_to_def] >>
     conj_tac >- simp[jump_to_def] >>
     qexistsl_tac [`cv`, `hdr`, `0`, `body_lbl`, `n`] >>
     simp[] >> gvs[jump_to_def, eval_operand_def, lookup_var_def]) >>
  qexists_tac `t` >> simp[] >>
  irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_marked_path_then)) >>
  qexists_tac `r` >> simp[] >>
  irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_marked_path_then)) >>
  qexists_tac `jump_to hdr r` >> simp[]
QED

Finalise append_sparse_runtime_loop_checked

Theorem append_sparse_runtime_bulk_path_mem[local]:
  compile_word_copy_loop_op src dst cop LocMemory
    (if tr then LocTransient else LocStorage) F sa = (result,sb) /\
  fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_call_ctx.cc_static /\
  (!x. src = Var x \/ dst = Var x \/ cop = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  eval_operand cop s = SOME (n2w n) /\
  n < dimword (:256) /\ w2n sw + 32*n < dimword (:256) /\
  w2n sw + 32*n <= s.vs_alloca_next ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    store_copy_normalize s t =
      FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
        (mload (w2n sw + 32*j) s) q) s (COUNT_LIST n) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_labels = s.vs_labels /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_alloca_next = s.vs_alloca_next /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  drule_at (Pat `compile_word_copy_loop_op _ _ _ _ _ _ _ = _`)
    append_sparse_runtime_loop_checked >>
  disch_then (qspecl_then [`s`, `n`, `dw`, `func`, `ctx`, `sw`] mp_tac) >>
  simp[] >>
  (impl_tac >- (Cases_on `tr` >> simp[] >> metis_tac[])) >> strip_tac >>
  qexists_tac `t` >> simp[] >>
  drule place_store_copy_frame_observations >> strip_tac >>
  drule topcopy_frame_frontier >> strip_tac >> simp[] >>
  gvs[stmtSimStoreCopyTheory.store_copy_frame_def,
      stmtSimStoreCopyTheory.store_copy_prefix_def] >>
  irule listTheory.FOLDL_CONG >> simp[MEM_COUNT_LIST] >> rpt strip_tac >>
  `32*x + w2n sw < dimword (:256)` by (simp[dimword_def] >> decide_tac) >>
  `sw + n2w x * 32w = n2w (32*x + w2n sw)` by
    (pure_rewrite_tac[GSYM word_add_n2w, GSYM word_mul_n2w, n2w_w2n] >>
     wordsLib.WORD_DECIDE_TAC) >>
  Cases_on `tr` >> simp[w2n_n2w, arithmeticTheory.LESS_MOD] >> gvs[]
QED

Theorem append_sparse_bytes_footprint[local]:
  (tv = BaseTV (BytesT (Dynamic cap)) \/ tv = BaseTV (StringT cap)) /\
  value_has_type tv v /\ val_in_memory tv v off mem /\
  off + type_memory_size tv < dimword (:256) /\
  encode_value tv v = SOME writes ==>
  ?len. mem_word_at off mem = n2w len /\
    (!j. MEM j (MAP FST writes) <=> j < 1 + vfmConstants$word_size len) /\
    32 * (1 + vfmConstants$word_size len) <= type_memory_size tv /\
    len + 63 < dimword (:256) /\
    1 + vfmConstants$word_size len < dimword (:256)
Proof
  strip_tac >> Cases_on `v` >>
  gvs[vyperTypingTheory.value_has_type_def, valueEncodingDefsTheory.val_in_memory_def,
      valueEncodingTheory.type_memory_size_def, vyperStorageTheory.encode_value_def] >>
  drule vyperEncodeDecodeTheory.encode_dyn_bytes_slots_keys >> strip_tac >>
  gvs[] >> rename1 `mem_word_at off mem = n2w len` >>
  qexists_tac `len` >> simp[] >>
  fs[vfmConstantsTheory.word_size_def] >>
  qspec_then `len + 31` mp_tac (SRULE [] (Q.SPEC `32` arithmeticTheory.DIVISION)) >>
  qspec_then `cap + 31` mp_tac (SRULE [] (Q.SPEC `32` arithmeticTheory.DIVISION)) >>
  simp[] >> rpt strip_tac >> rpt conj_tac >>
  fs[wordsTheory.dimword_def] >> intLib.ARITH_TAC
QED

Theorem append_sparse_bytes_checked[local]:
  is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\
  compile_store_slots cenv src slot ty tr sa = ((),sb) /\
  (!x. src = Var x \/ slot = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand slot s = SOME dw /\
  val_in_memory tv v (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size tv < dimword (:256) /\
  w2n sw + type_memory_size tv <= s.vs_alloca_next /\
  w2n dw + type_slot_size tv <= dimword (:256) /\
  encode_value tv v = SOME writes /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_call_ctx.cc_static ==>
  ?t ks. gas_marked_path T ctx func s 0 (OK t) /\
    store_copy_normalize s t =
      FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
        (mload (w2n sw + 32*j) s) q) s ks /\
    (!j. MEM j ks <=> MEM j (MAP FST writes)) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_labels = s.vs_labels /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_alloca_next = s.vs_alloca_next /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `?cap. tv = BaseTV (BytesT (Dynamic cap)) \/ tv = BaseTV (StringT cap)` by
    (Cases_on `ty` >> gvs[is_bytestring_type_def, vyperValueTheory.evaluate_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[is_bytestring_type_def, vyperValueTheory.evaluate_type_def] >>
     rename1 `BytesT bound` >> Cases_on `bound` >>
     gvs[is_bytestring_type_def, vyperValueTheory.evaluate_type_def]) >>
  drule_at (Pat `val_in_memory _ _ _ _`) append_sparse_bytes_footprint >>
  disch_then (qspecl_then [`writes`, `cap`] mp_tac) >>
  simp[] >> strip_tac >>
  `is_abi_dynamic cenv.ce_struct_fields ty` by
    (qpat_x_assum `is_bytestring_type ty` mp_tac >>
     Cases_on `ty` >> simp[is_bytestring_type_def, is_abi_dynamic_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     simp[is_bytestring_type_def, is_abi_dynamic_def] >>
     rename1 `BytesT bound` >> Cases_on `bound` >>
     simp[is_bytestring_type_def, is_abi_dynamic_def]) >>
  qpat_x_assum `compile_store_slots _ _ _ _ _ _ = _` mp_tac >>
  simp[Once contextTheory.compile_store_slots_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `compile_bytestring_word_count src sa = (cnt,sm)` >>
  fs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >>
  `ci_mono sa sm /\ (!x. cnt = Var x ==> not_fresh_at sm x)` by
    (qpat_x_assum `compile_bytestring_word_count _ _ = _` mp_tac >>
     simp[contextTheory.compile_bytestring_word_count_def, comp_bind_def] >>
     pairarg_tac >> pairarg_tac >> strip_tac >> gvs[] >>
     pairarg_tac >> gvs[] >>
     imp_res_tac typedMemoryCopyTheory.typed_copy_emit_op_mono >>
     conj_tac
     >- (fs[ci_mono_def] >> metis_tac[cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS]) >>
     metis_tac[typedMemoryCopyTheory.typed_copy_emit_op_fresh]) >>
  rename1 `compile_word_copy_loop_op _ _ _ _ _ _ sm = (res,sb)` >>
  `ci_mono sm sb` by
    metis_tac[ci_mono_compile_word_copy_loop_op, pairTheory.SND] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (fs[ci_mono_def] >> metis_tac[fragExecTheory.fn_has_code_split]) >>
  `mload (w2n sw) s = n2w len` by metis_tac[GSYM valueEncodingPropsTheory.mem_word_at_eq_mload] >>
  `w2n sw + 32 <= s.vs_alloca_next` by decide_tac >>
  `len + 63 < dimword (:256)` by fs[dimword_def] >>
  drule_all append_sparse_bytes_count_checked >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `eval_operand cnt u = SOME _` >>
  `u.vs_labels = s.vs_labels` by gvs[venom_state_component_equality] >>
  `eval_operand src u = SOME sw /\ eval_operand slot u = SOME dw` by
    (Cases_on `src` >> Cases_on `slot` >>
     gvs[eval_operand_def] >> metis_tac[]) >>
  `!x. src = Var x \/ slot = Var x \/ cnt = Var x ==> not_fresh_at sm x` by
    metis_tac[exprOperandVarTheory.compiler_ci_mono_not_fresh] >>
  `u.vs_memory = s.vs_memory /\ u.vs_alloca_next = s.vs_alloca_next /\
   u.vs_call_ctx = s.vs_call_ctx` by
    gvs[venom_state_component_equality] >>
  `1 + vfmConstants$word_size len < dimword (:256) /\
   w2n sw + 32 * (1 + vfmConstants$word_size len) < dimword (:256) /\
   w2n sw + 32 * (1 + vfmConstants$word_size len) <= u.vs_alloca_next` by
    (fs[dimword_def] >> decide_tac) >>
  `~u.vs_call_ctx.cc_static` by simp[] >>
  drule_all append_sparse_runtime_bulk_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexistsl_tac [`t`, `COUNT_LIST (1 + vfmConstants$word_size len)`] >>
  (conj_tac
   >- (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_marked_path_then)) >>
       qexists_tac `u` >> simp[])) >>
  (reverse conj_tac
   >- (simp[MEM_COUNT_LIST] >>
       qpat_x_assum `store_copy_normalize _ _ = _` kall_tac >>
       fs[venom_state_component_equality] >> rpt strip_tac >>
       `not_fresh_at sm x` by
         metis_tac[exprOperandVarTheory.compiler_ci_mono_not_fresh] >>
       metis_tac[])) >>
  `!ks q. store_copy_normalize s
     (FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
                      (mload (w2n sw + 32*j) u) q) q ks) =
     FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
                      (mload (w2n sw + 32*j) u) q)
       (store_copy_normalize s q) ks` by
    (Induct >> pure_rewrite_tac[listTheory.FOLDL] >> rpt gen_tac
     >- simp[] >>
     asm_rewrite_tac[] >>
     AP_THM_TAC >> AP_TERM_TAC >>
     Cases_on `tr` >> simp[stmtSimStoreCopyTheory.store_copy_normalize_def, sstore_def, tstore_def]) >>
  `store_copy_normalize s u = s` by
    (qpat_x_assum `u with <|vs_vars := _; vs_inst_idx := _|> = s` mp_tac >>
     simp[NoAsms, stmtSimStoreCopyTheory.store_copy_normalize_def] >>
     disch_then (fn th => once_rewrite_tac[GSYM th]) >>
     simp[NoAsms, venom_state_component_equality]) >>
  `store_copy_normalize s t = store_copy_normalize s (store_copy_normalize u t)` by
    simp[NoAsms, stmtSimStoreCopyTheory.store_copy_normalize_def] >>
  pop_assum SUBST1_TAC >> asm_rewrite_tac[] >>
  `!j. mload (w2n sw + 32*j) u = mload (32*j + w2n sw) s` by
    metis_tac[GSYM valueEncodingPropsTheory.mem_word_at_eq_mload, arithmeticTheory.ADD_COMM] >>
  asm_rewrite_tac[]
QED

Theorem append_sparse_offset_checked[local]:
  compile_with_byte_offset ptr0 off sa = (op,sb) /\
  eval_operand ptr0 s = SOME w /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    eval_operand op t = SOME (w + n2w off) /\
    t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|> = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> Cases_on `off = 0`
  >- (gvs[contextTheory.compile_with_byte_offset_def, comp_return_def] >>
      qexists_tac `s` >> simp[gas_marked_path_def, gas_path_mem_rules,
        venom_state_component_equality]) >>
  drule_all typedMemoryCopyTheory.typed_copy_offset_run_seq >> strip_tac >>
  `EVERY (\i. i.inst_opcode = ADD) (emitted_insts sa sb)` by
    (qpat_x_assum `compile_with_byte_offset _ _ _ = _` mp_tac >>
     simp[contextTheory.compile_with_byte_offset_def] >>
     strip_tac >> drule emitted_insts_emit_op >> simp[mk_inst_def]) >>
  `EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    fs[EVERY_MEM] >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule run_inst_seq_mem_ok_every >> fs[EVERY_MEM] >> rpt strip_tac >>
     simp[inst_dload_in_section_def] >>
     irule below_frontier_no_ranges >> simp[]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (fs[fn_has_code_def, same_blocks_def, IS_PREFIX_APPEND] >>
     qexists_tac `l` >> simp[DROP_APPEND, arithmeticTheory.SUB_PLUS]) >>
  drule_all topcopy_seq_path >>
  disch_then (qspec_then `ctx` assume_tac) >>
  qexists_tac `(update_var (STRING #"%" (toString sa.cs_next_var)) (w + n2w off) s)
    with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  fs[same_blocks_def, eval_operand_def, lookup_var_def, update_var_def,
     finite_mapTheory.FLOOKUP_UPDATE] >>
  `LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts + LENGTH (emitted_insts sa sb)` by simp[] >>
  conj_tac
  >- (qpat_x_assum `gas_marked_path _ _ _ _ _ _` mp_tac >>
      simp[arithmeticTheory.ADD_COMM]) >>
  simp[venom_state_component_equality] >> rpt strip_tac >>
  `x <> STRING #"%" (toString sa.cs_next_var)` by
    (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >> simp[]
QED

Theorem append_sparse_lit_offset_checked[local]:
  !ptr0 off sa op sb s w func ctx.
  compile_lit_byte_offset ptr0 off sa = (op,sb) /\
  eval_operand ptr0 s = SOME w /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    eval_operand op t = SOME (w + n2w off) /\
    t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|> = s /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> Cases_on `off = 0`
  >- (simp[contextTheory.compile_lit_byte_offset_def, comp_return_def] >>
      rpt strip_tac >> gvs[] >> qexists_tac `s` >>
      simp[gas_marked_path_def, gas_path_mem_rules, venom_state_component_equality]) >>
  Cases_on `ptr0`
  >- (simp[contextTheory.compile_lit_byte_offset_def, comp_return_def, eval_operand_def] >>
      rpt strip_tac >> gvs[] >> qexists_tac `s` >>
      simp[gas_marked_path_def, gas_path_mem_rules, eval_operand_def,
           venom_state_component_equality]) >>
  simp[contextTheory.compile_lit_byte_offset_def] >> strip_tac >>
  rename1 `emit_op ADD [arg; Lit (n2w off)] sa = (op,sb)` >>
  `compile_with_byte_offset arg off sa = (op,sb)` by
    simp[contextTheory.compile_with_byte_offset_def] >>
  drule_all append_sparse_offset_checked >>
  disch_then (qspec_then `ctx` mp_tac) >> simp[]
QED

Theorem append_sparse_lit_offset_fresh[local]:
  !ptr0 off sa op sb.
  compile_lit_byte_offset ptr0 off sa = (op,sb) /\
  (!x. ptr0 = Var x ==> not_fresh_at sa x) ==>
  !x. op = Var x ==> not_fresh_at sb x
Proof
  rpt gen_tac >> Cases_on `off = 0`
  >- (simp[contextTheory.compile_lit_byte_offset_def, comp_return_def] >> metis_tac[]) >>
  Cases_on `ptr0`
  >- (simp[contextTheory.compile_lit_byte_offset_def, comp_return_def] >> rpt strip_tac >> gvs[]) >>
  simp[contextTheory.compile_lit_byte_offset_def] >> rpt strip_tac >>
  drule typedMemoryCopyTheory.typed_copy_emit_op_fresh >> simp[]
QED

(* Source-level notation only: no new HOL constant or definition. *)
val append_sparse_entry = ``\cenv ctx ty tv v.
 !src slot tr sa sb func s sw dw writes.
 compile_store_slots cenv src slot ty tr sa = ((),sb) /\
 (!x. src = Var x \/ slot = Var x ==> not_fresh_at sa x) /\
 eval_operand src s = SOME sw /\ eval_operand slot s = SOME dw /\
 val_in_memory tv v (w2n sw) s.vs_memory /\
 w2n sw + type_memory_size tv < dimword (:256) /\
 w2n sw + type_memory_size tv <= s.vs_alloca_next /\
 w2n dw + type_slot_size tv <= dimword (:256) /\
 encode_value tv v = SOME writes /\ fn_has_code sa sb func /\
 fn_inst_ids_distinct func /\ ~s.vs_halted /\
 s.vs_current_bb = sa.cs_current_bb /\
 s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_call_ctx.cc_static ==>
 ?t ks. gas_marked_path T ctx func s 0 (OK t) /\
 store_copy_normalize s t =
   FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
     (mload (w2n sw + 32*j) s) q) s ks /\
 (!j. MEM j ks <=> MEM j (MAP FST writes)) /\
 (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
 t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
 t.vs_labels = s.vs_labels /\ t.vs_call_ctx = s.vs_call_ctx /\
 t.vs_alloca_next = s.vs_alloca_next /\ ~t.vs_halted /\
 t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts``;

Theorem append_sparse_entry_run[local]:
 (^append_sparse_entry) cenv ctx ty tv v ==>
 !src slot tr sa sb func s sw dw writes.
 compile_store_slots cenv src slot ty tr sa = ((),sb) /\
 (!x. src = Var x \/ slot = Var x ==> not_fresh_at sa x) /\
 eval_operand src s = SOME sw /\ eval_operand slot s = SOME dw /\
 val_in_memory tv v (w2n sw) s.vs_memory /\
 w2n sw + type_memory_size tv < dimword (:256) /\
 w2n sw + type_memory_size tv <= s.vs_alloca_next /\
 w2n dw + type_slot_size tv <= dimword (:256) /\
 encode_value tv v = SOME writes /\ fn_has_code sa sb func /\
 fn_inst_ids_distinct func /\ ~s.vs_halted /\
 s.vs_current_bb = sa.cs_current_bb /\
 s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_call_ctx.cc_static ==>
 ?t ks. gas_marked_path T ctx func s 0 (OK t) /\
 store_copy_normalize s t =
   FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
     (mload (w2n sw + 32*j) s) q) s ks /\
 (!j. MEM j ks <=> MEM j (MAP FST writes)) /\
 (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
 t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
 t.vs_labels = s.vs_labels /\ t.vs_call_ctx = s.vs_call_ctx /\
 t.vs_alloca_next = s.vs_alloca_next /\ ~t.vs_halted /\
 t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
 simp[]
QED

Theorem append_sparse_normalize_fold[local]:
 !ks a. store_copy_normalize s
   (FOLDL (\q j. (if tr then tstore else sstore) (key j) (value j) q) a (ks:num list)) =
 FOLDL (\q j. (if tr then tstore else sstore) (key j) (value j) q)
   (store_copy_normalize s a) ks
Proof
 Induct >> pure_rewrite_tac[listTheory.FOLDL] >> rpt gen_tac
 >- simp[] >>
 asm_rewrite_tac[] >> AP_THM_TAC >> AP_TERM_TAC >>
 Cases_on `tr` >> simp[stmtSimStoreCopyTheory.store_copy_normalize_def, sstore_def, tstore_def]
QED

Theorem append_sparse_normalize_pure[local]:
 u with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|> = s ==>
 store_copy_normalize s u = s
Proof
 strip_tac >> simp[NoAsms, stmtSimStoreCopyTheory.store_copy_normalize_def] >>
 first_x_assum (fn th => once_rewrite_tac[GSYM th]) >>
 simp[NoAsms, venom_state_component_equality]
QED

Theorem append_sparse_member_offset_checked[local]:
 (^append_sparse_entry) cenv ctx ty tv v ==>
 compile_lit_byte_offset src mo sa = (ms,a) /\
 compile_lit_byte_offset slot so a = (ds,b) /\
 compile_store_slots cenv ms ds ty tr b = ((),sc) /\
 encode_value tv v = SOME writes /\
 (!x. src = Var x \/ slot = Var x ==> not_fresh_at sa x) /\
 eval_operand src s = SOME sw /\ eval_operand slot s = SOME dw /\
 val_in_memory tv v (w2n sw + mo) s.vs_memory /\
 w2n sw + mo + type_memory_size tv < dimword (:256) /\
 w2n sw + mo + type_memory_size tv <= s.vs_alloca_next /\
 w2n dw + so + type_slot_size tv <= dimword (:256) /\
 fn_has_code sa sc func /\ fn_inst_ids_distinct func /\
 ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
 s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_call_ctx.cc_static ==>
 ?t ks. gas_marked_path T ctx func s 0 (OK t) /\
 store_copy_normalize s t =
   FOLDL (\q j. (if tr then tstore else sstore) ((dw + n2w so) + n2w j)
     (mload (w2n sw + mo + 32*j) s) q) s ks /\
 (!j. MEM j ks <=> MEM j (MAP FST writes)) /\
 (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
 t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
 t.vs_labels = s.vs_labels /\ t.vs_call_ctx = s.vs_call_ctx /\
 t.vs_alloca_next = s.vs_alloca_next /\ ~t.vs_halted /\
 t.vs_current_bb = sc.cs_current_bb /\ t.vs_inst_idx = LENGTH sc.cs_current_insts
Proof
 ntac 2 strip_tac >>
 `ci_mono sa a /\ ci_mono a b /\ ci_mono b sc` by
   metis_tac[exprLoweringPropsTheory.ci_mono_compile_lit_byte_offset,
     cj 1 stmtLoweringMonoTheory.ci_mono_compile_store_slots, pairTheory.SND] >>
 `fn_has_code sa a func /\ fn_has_code a b func /\ fn_has_code b sc func` by
   (fs[ci_mono_def] >> metis_tac[fn_has_code_split, cs_extends_trans]) >>
 `(!x. slot = Var x ==> not_fresh_at a x) /\
  (!x. ms = Var x ==> not_fresh_at a x) /\
  (!x. ms = Var x \/ ds = Var x ==> not_fresh_at b x)` by
   metis_tac[append_sparse_lit_offset_fresh,
             typedMemoryCopyTheory.typed_copy_operand_fresh_mono] >>
 qpat_assum `compile_lit_byte_offset src _ _ = _` mp_tac >>
 disch_then (mp_then Any mp_tac append_sparse_lit_offset_checked) >>
 disch_then (qspecl_then [`s`, `sw`, `func`, `ctx`] mp_tac) >>
 simp[] >> disch_then (qx_choose_then `q1` strip_assume_tac) >>
 `q1.vs_labels = s.vs_labels /\ q1.vs_memory = s.vs_memory /\
  q1.vs_allocas = s.vs_allocas /\ q1.vs_call_ctx = s.vs_call_ctx /\
  q1.vs_alloca_next = s.vs_alloca_next` by
   (qpat_x_assum `q1 with <|vs_vars := _; vs_inst_idx := _|> = s` mp_tac >>
    simp[NoAsms, venom_state_component_equality]) >>
 `eval_operand slot q1 = SOME dw` by
   (Cases_on `slot` >> fs[eval_operand_def] >> metis_tac[]) >>
 qpat_assum `compile_lit_byte_offset slot _ _ = _` mp_tac >>
 disch_then (mp_then Any mp_tac append_sparse_lit_offset_checked) >>
 disch_then (qspecl_then [`q1`, `dw`, `func`, `ctx`] mp_tac) >>
 simp[] >> disch_then (qx_choose_then `q2` strip_assume_tac) >>
 `q2.vs_labels = q1.vs_labels /\ q2.vs_memory = q1.vs_memory /\
  q2.vs_allocas = q1.vs_allocas /\ q2.vs_call_ctx = q1.vs_call_ctx /\
  q2.vs_alloca_next = q1.vs_alloca_next` by
   (qpat_x_assum `q2 with <|vs_vars := _; vs_inst_idx := _|> = q1` mp_tac >>
    simp[NoAsms, venom_state_component_equality]) >>
 `eval_operand ms q2 = SOME (sw + n2w mo)` by
   (Cases_on `ms` >> fs[eval_operand_def] >> metis_tac[]) >>
 `w2n (sw + n2w mo) = w2n sw + mo` by
   (irule typedMemoryCopyTheory.typed_copy_offset_nonwrap >> decide_tac) >>
 `w2n (dw + n2w so) + type_slot_size tv <= dimword (:256)` by
   (simp[wordsTheory.word_add_def, wordsTheory.w2n_n2w] >>
    mp_tac (Q.INST [`x` |-> `so + w2n (dw:bytes32)`, `y` |-> `dimword (:256)`]
      arithmeticTheory.MOD_LESS_EQ) >>
    qpat_x_assum `w2n dw + so + _ <= _` mp_tac >> simp[] >> decide_tac) >>
 drule append_sparse_entry_run >>
 disch_then (drule_at (Pat `compile_store_slots _ _ _ _ _ _ = _`)) >>
 disch_then (qspecl_then [`func`, `q2`, `sw + n2w mo`, `dw + n2w so`, `writes`] mp_tac) >>
 (impl_tac >- asm_rewrite_tac[]) >>
 disch_then (qx_choose_then `t` (qx_choose_then `ks` strip_assume_tac)) >>
 `gas_marked_path T ctx func s 0 (OK t)` by
   metis_tac[gas_marked_path_then, arithmeticTheory.ADD_CLAUSES] >>
 `!x. not_fresh_at sa x ==> not_fresh_at a x /\ not_fresh_at b x` by
   metis_tac[exprOperandVarTheory.compiler_ci_mono_not_fresh] >>
 `store_copy_normalize s q1 = s` by
   (irule append_sparse_normalize_pure >> asm_rewrite_tac[]) >>
 `store_copy_normalize q1 q2 = q1` by
   (irule append_sparse_normalize_pure >> asm_rewrite_tac[]) >>
 `store_copy_normalize s q2 = s` by
   (qpat_x_assum `store_copy_normalize q1 q2 = q1`
      (mp_tac o AP_TERM ``store_copy_normalize s``) >>
    simp[stmtSimStoreCopyTheory.store_copy_normalize_def]) >>
 qexistsl_tac [`t`, `ks`] >> asm_rewrite_tac[] >>
 reverse conj_tac
 >- metis_tac[] >>
 `store_copy_normalize s t = store_copy_normalize s (store_copy_normalize q2 t)` by
   simp[NoAsms, stmtSimStoreCopyTheory.store_copy_normalize_def] >>
 pop_assum SUBST1_TAC >> asm_rewrite_tac[append_sparse_normalize_fold] >>
 simp[NoAsms, mload_def] >> asm_rewrite_tac[] >>
 simp[append_sparse_normalize_fold]
QED

Theorem append_sparse_fold_compose[local]:
 u.vs_memory = s.vs_memory /\
 store_copy_normalize s u =
   FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
     (mload (w2n sw + 32*j) s) q) s hs /\
 store_copy_normalize u t =
   FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
     (mload (w2n sw + 32*j) u) q) u ts ==>
 store_copy_normalize s t =
   FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
     (mload (w2n sw + 32*j) s) q) s (hs ++ ts)
Proof
 strip_tac >>
 qpat_x_assum `store_copy_normalize u t = _`
   (mp_tac o AP_TERM ``store_copy_normalize s``) >>
 simp[append_sparse_normalize_fold, FOLDL_APPEND, mload_def] >>
 simp[stmtSimStoreCopyTheory.store_copy_normalize_def]
QED

Theorem append_sparse_members_checked[local]:
 !members tvs vs cenv ctx mo so src slot tr sa sb func s sw dw.
 compile_store_slots_members cenv src slot members mo so tr sa = ((),sb) /\
 LIST_REL (\(ty,sz) (tv,v). sz = type_memory_size tv /\
   (^append_sparse_entry) cenv ctx ty tv v /\ IS_SOME (encode_value tv v))
   members (ZIP (tvs,vs)) /\
 LENGTH vs = LENGTH tvs /\ mo = 32 * so /\
 tuple_in_memory vs tvs (w2n sw + mo) s.vs_memory /\
 (!x. src = Var x \/ slot = Var x ==> not_fresh_at sa x) /\
 eval_operand src s = SOME sw /\ eval_operand slot s = SOME dw /\
 w2n sw + mo + type_memory_size_list tvs < dimword (:256) /\
 w2n sw + mo + type_memory_size_list tvs <= s.vs_alloca_next /\
 w2n dw + so + type_slot_size_list tvs <= dimword (:256) /\
 fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
 ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
 s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_call_ctx.cc_static ==>
 ?t ks. gas_marked_path T ctx func s 0 (OK t) /\
 store_copy_normalize s t =
   FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
     (mload (w2n sw + 32*j) s) q) s ks /\
 (!k. MEM k ks <=> ?i writes j. i < LENGTH tvs /\
    encode_value (EL i tvs) (EL i vs) = SOME writes /\
    MEM j (MAP FST writes) /\ k = so + tuple_prefix_slot_size i tvs + j) /\
 (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
 t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
 t.vs_labels = s.vs_labels /\ t.vs_call_ctx = s.vs_call_ctx /\
 t.vs_alloca_next = s.vs_alloca_next /\ ~t.vs_halted /\
 t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
 qabbrev_tac `E = ^append_sparse_entry` >>
 Induct_on `members`
 >- (rpt gen_tac >>
     simp[Once contextTheory.compile_store_slots_def, comp_return_def] >> strip_tac >>
     `tvs = [] /\ vs = []` by (Cases_on `tvs` >> Cases_on `vs` >> gvs[]) >>
     gvs[] >> qexistsl_tac [`s`, `[]`] >>
     simp[gas_marked_path_def, gas_path_mem_rules,
          stmtSimStoreCopyTheory.store_copy_normalize_def, venom_state_component_equality]) >>
 qx_gen_tac `hdmem` >> PairCases_on `hdmem` >>
 Cases_on `tvs` >> Cases_on `vs` >> simp[] >>
 rpt gen_tac >> strip_tac >>
 qpat_x_assum `compile_store_slots_members _ _ _ _ _ _ _ _ = _` mp_tac >>
 simp[Once contextTheory.compile_store_slots_def, comp_bind_def, comp_ignore_bind_def] >>
 strip_tac >>
 rename1 `E cenv ctx ty tv v` >> rename1 `ZIP (tvs,vs)` >>
 Cases_on `compile_lit_byte_offset src (32 * so) sa` >>
 rename1 `compile_lit_byte_offset src (32 * so) sa = (ms,a)` >>
 Cases_on `compile_lit_byte_offset slot so a` >>
 rename1 `compile_lit_byte_offset slot so a = (ds,b)` >>
 Cases_on `compile_store_slots cenv ms ds ty tr b` >>
 rename1 `compile_store_slots cenv ms ds ty tr b = (unit,sc)` >>
 Cases_on `unit` >> gvs[] >>
 `ci_mono sa a /\ ci_mono a b /\ ci_mono b sc /\ ci_mono sc sb` by
   metis_tac[exprLoweringPropsTheory.ci_mono_compile_lit_byte_offset,
     cj 1 stmtLoweringMonoTheory.ci_mono_compile_store_slots,
     cj 2 stmtLoweringMonoTheory.ci_mono_compile_store_slots, pairTheory.SND] >>
 `fn_has_code sa sc func /\ fn_has_code sc sb func` by
   (fs[ci_mono_def] >> metis_tac[fn_has_code_split, cs_extends_trans]) >>
 qpat_x_assum `tuple_in_memory _ _ _ _` mp_tac >>
 simp[Once valueEncodingDefsTheory.val_in_memory_def] >> strip_tac >>
 `?writes. encode_value tv v = SOME writes` by metis_tac[optionTheory.IS_SOME_EXISTS] >>
 `w2n sw + 32*so + type_memory_size tv < dimword (:256) /\
  w2n sw + 32*so + type_memory_size tv <= s.vs_alloca_next /\
  w2n dw + so + type_slot_size tv <= dimword (:256)` by
   (fs[valueEncodingTheory.type_memory_size_def, vyperValueTheory.type_slot_size_def] >> decide_tac) >>
 `val_in_memory tv v (w2n sw + 32*so) s.vs_memory` by metis_tac[arithmeticTheory.ADD_COMM] >>
 `(^append_sparse_entry) cenv ctx ty tv v` by
   (qpat_x_assum `E cenv ctx ty tv v` mp_tac >>
    simp[]) >>
 drule append_sparse_member_offset_checked >>
 disch_then (drule_at (Pat `compile_store_slots _ _ _ _ _ _ = _`)) >>
 disch_then (drule_at (Pat `compile_lit_byte_offset _ _ _ = _`)) >>
 disch_then (drule_at (Pat `compile_lit_byte_offset _ _ _ = _`)) >>
 disch_then (drule_at (Pat `eval_operand src s = SOME sw`)) >>
 disch_then (qspecl_then [`writes`, `sw`, `func`] mp_tac) >>
 (impl_tac >- asm_rewrite_tac[]) >>
 disch_then (qx_choose_then `u` (qx_choose_then `hs` strip_assume_tac)) >>
 `eval_operand src u = SOME sw /\ eval_operand slot u = SOME dw` by
   (qpat_assum `eval_operand src s = SOME sw` mp_tac >>
    qpat_assum `eval_operand slot s = SOME dw` mp_tac >>
    qpat_assum `!x. not_fresh_at sa x ==> lookup_var x u = _` mp_tac >>
    qpat_assum `!x. src = Var x \/ slot = Var x ==> _` mp_tac >>
    qpat_assum `u.vs_labels = s.vs_labels` mp_tac >>
    rpt (pop_assum kall_tac) >> rpt strip_tac >>
    Cases_on `src` >> Cases_on `slot` >> gvs[eval_operand_def] >> metis_tac[]) >>
 `!x. src = Var x \/ slot = Var x ==> not_fresh_at sc x` by
   metis_tac[exprOperandVarTheory.compiler_ci_mono_not_fresh] >>
 `compile_store_slots_members cenv src slot members
    (32 * (so + type_slot_size tv)) (so + type_slot_size tv) tr sc = ((),sb)` by
   (qpat_assum `compile_store_slots_members _ _ _ _ _ _ _ _ = _` mp_tac >>
    simp[NoAsms, valueEncodingPropsTheory.type_memory_size_slots,
         arithmeticTheory.LEFT_ADD_DISTRIB]) >>
 qpat_x_assum `!tvs vs cenv ctx so src slot tr sa sb func s sw dw. _`
   (drule_at (Pat `compile_store_slots_members _ _ _ _ _ _ _ _ = _`)) >>
 disch_then (drule_at (Pat `LIST_REL _ _ _`)) >>
 disch_then (qspecl_then [`func`, `u`, `sw`, `dw`] mp_tac) >>
 (impl_tac >-
   (qpat_x_assum `Abbrev (E = _)` kall_tac >>
    qpat_x_assum `E cenv ctx ty tv v` kall_tac >>
    qpat_x_assum `(^append_sparse_entry) cenv ctx ty tv v` kall_tac >>
    asm_rewrite_tac[] >>
    qpat_assum `tuple_in_memory vs tvs _ _` mp_tac >>
    qpat_assum `32 * so + (type_memory_size_list (tv::tvs) + w2n sw) < _` mp_tac >>
    qpat_assum `32 * so + (type_memory_size_list (tv::tvs) + w2n sw) <= _` mp_tac >>
    qpat_assum `so + (type_slot_size_list (tv::tvs) + w2n dw) <= _` mp_tac >>
    rpt (pop_assum kall_tac) >>
    pure_rewrite_tac[valueEncodingPropsTheory.type_memory_size_slots] >>
    pure_rewrite_tac[vyperValueTheory.type_slot_size_def] >>
    pure_rewrite_tac[arithmeticTheory.LEFT_ADD_DISTRIB, GSYM arithmeticTheory.ADD_ASSOC] >>
    simp[])) >>
 disch_then (qx_choose_then `t` (qx_choose_then `ts` strip_assume_tac)) >>
 qpat_x_assum `Abbrev (E = _)` kall_tac >>
 qpat_x_assum `E cenv ctx ty tv v` kall_tac >>
 qpat_x_assum `(^append_sparse_entry) cenv ctx ty tv v` kall_tac >>
 `store_copy_normalize s u =
   FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
     (mload (w2n sw + 32*j) s) q) s (MAP ((+) so) hs)` by
   (qpat_x_assum `store_copy_normalize s u = _` mp_tac >>
    pure_rewrite_tac[FOLDL_MAP] >> BETA_TAC >>
    pure_rewrite_tac[GSYM wordsTheory.word_add_n2w,
      arithmeticTheory.LEFT_ADD_DISTRIB, arithmeticTheory.ADD_ASSOC,
      GSYM wordsTheory.WORD_ADD_ASSOC] >> simp[NoAsms]) >>
 `store_copy_normalize s t =
   FOLDL (\q j. (if tr then tstore else sstore) (dw + n2w j)
     (mload (w2n sw + 32*j) s) q) s (MAP ((+) so) hs ++ ts)` by
   (irule append_sparse_fold_compose >> qexists_tac `u` >> simp[] >>
    qpat_x_assum `store_copy_normalize u t = _` mp_tac >>
    simp[NoAsms, arithmeticTheory.ADD_COMM]) >>
 `gas_marked_path T ctx func s 0 (OK t)` by
   metis_tac[gas_marked_path_then, arithmeticTheory.ADD_CLAUSES] >>
 qexistsl_tac [`t`, `MAP ((+) so) hs ++ ts`] >> simp[] >>
 reverse conj_tac
 >- (fs[ci_mono_def, not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
 qpat_x_assum `!k. MEM k ts <=> _` mp_tac >>
 qpat_x_assum `!j. MEM j hs <=> _` mp_tac >>
 qpat_x_assum `encode_value tv v = SOME writes` mp_tac >>
 rpt (pop_assum kall_tac) >> rpt strip_tac >>
 simp[MEM_MAP] >>
 CONV_TAC (RHS_CONV (HO_REWR_CONV arithmeticTheory.EXISTS_NUM)) >>
 simp[vyperStateTheory.tuple_prefix_slot_size_def] >>
 AP_THM_TAC >> AP_TERM_TAC >>
 rpt (pop_assum kall_tac) >>
 metis_tac[arithmeticTheory.ADD_COMM]

QED

Theorem append_storage_aggregate_address_run:
  emit_op ADD [bop; Lit 1w] st3 = (dop,st4) /\
  emit_op MUL [lop; Lit (n2w n)] st4 = (off,st5) /\
  emit_op ADD [dop; off] st5 = (pop,st6) /\
  eval_operand bop ss = SOME slot /\ eval_operand lop ss = SOME len /\
  fresh_vars_wrt st3 ss ==>
  ?t. run_inst_seq (emitted_insts st3 st6) ss = OK t /\
    eval_operand pop t = SOME (slot + 1w + len * n2w n) /\
    same_blocks st3 st6 /\ fresh_vars_wrt st6 t /\
    state_frame t = state_frame ss /\
    (!op w. eval_operand op ss = SOME w ==> eval_operand op t = SOME w)
Proof
  strip_tac >>
  `eval_operand (Lit 1w) ss = SOME 1w` by simp[eval_operand_def] >>
  drule_all emit_op_ADD_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st3 st4) ss = OK ss4` >>
  `eval_operand lop ss4 = SOME len /\
   eval_operand (Lit (n2w n)) ss4 = SOME (n2w n)` by
    (simp[eval_operand_def] >> metis_tac[]) >>
  drule_all emit_op_MUL_correct >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st4 st5) ss4 = OK ss5` >>
  `eval_operand dop ss5 = SOME (slot + 1w)` by metis_tac[] >>
  drule_all emit_op_ADD_correct >> strip_tac >>
  imp_res_tac inst_extends_emit_op >>
  `inst_extends st3 st5` by metis_tac[inst_extends_trans] >>
  `run_inst_seq (emitted_insts st3 st5) ss = OK ss5` by
    (irule run_inst_seq_compose_ok >>
     qexistsl_tac [`ss4`, `st4`] >> simp[]) >>
  `run_inst_seq (emitted_insts st3 st6) ss = OK ss'` by
    (irule run_inst_seq_compose_ok >>
     qexistsl_tac [`ss5`, `st5`] >> simp[]) >>
  `state_frame ss' = state_frame ss` by
    (irule append_storage_seq_frame >>
     qexists_tac `emitted_insts st3 st6` >> simp[] >>
     `emitted_insts st3 st6 = emitted_insts st3 st4 ++
       emitted_insts st4 st5 ++ emitted_insts st5 st6` by
       metis_tac[inst_extends_trans, inst_extends_def, emitted_insts_append] >>
     imp_res_tac emitted_insts_emit_op >>
     simp[EVERY_APPEND, mk_inst_def]) >>
  gvs[same_blocks_def] >> metis_tac[]
QED

Theorem append_storage_aggregate_prefix_run:
  emit_op (if tr then TLOAD else SLOAD) [bop] sa = (lop,s1) /\
  emit_op LT [lop; Lit (n2w cap)] s1 = (valid,s2) /\
  emit_void ASSERT [valid] s2 = ((),s3) /\
  emit_op ADD [bop; Lit 1w] s3 = (dop,s4) /\
  emit_op MUL [lop; Lit (n2w n)] s4 = (off,s5) /\
  emit_op ADD [dop; off] s5 = (dst,s6) /\
  eval_operand bop s = SOME slot /\ fresh_vars_wrt sa s /\
  cap < dimword (:256) /\
  len = w2n (if tr then tload slot s else sload slot s) /\ len < cap ==>
  ?t. run_inst_seq (emitted_insts sa s6) s = OK t /\
    eval_operand dst t = SOME (slot + 1w + n2w len * n2w n) /\
    eval_operand lop t = SOME (n2w len) /\
    same_blocks sa s6 /\ fresh_vars_wrt s6 t /\
    state_frame t = state_frame s /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w)
Proof
  strip_tac >>
  `w2n (if tr then tload slot s else sload slot s) < cap` by metis_tac[] >>
  drule_all append_storage_guard_run >> strip_tac >>
  qpat_x_assum `if _ then _ else _` mp_tac >>
  asm_rewrite_tac [] >> strip_tac >>
  `eval_operand bop ss' = SOME slot` by metis_tac[] >>
  drule_all append_storage_aggregate_address_run >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `inst_extends sa s3 /\ inst_extends s3 s6` by
    metis_tac[inst_extends_trans] >>
  `run_inst_seq (emitted_insts sa s6) s = OK t` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`ss'`, `s3`] >> simp[]) >>
  qexists_tac `t` >> gvs[same_blocks_def] >> metis_tac[n2w_w2n]
QED

Theorem append_storage_aggregate_prefix_layout:
  emit_op (if tr then TLOAD else SLOAD) [bop] sa = (lop,s1) /\
  emit_op LT [lop; Lit (n2w cap)] s1 = (valid,s2) /\
  emit_void ASSERT [valid] s2 = ((),s3) /\
  emit_op ADD [bop; Lit 1w] s3 = (dop,s4) /\
  emit_op MUL [lop; Lit (n2w n)] s4 = (off,s5) /\
  emit_op ADD [dop; off] s5 = (dst,s6) ==>
  same_blocks sa s6 /\ inst_extends sa s6 /\
  (!x. not_fresh_at sa x ==> not_fresh_at s6 x) /\
  (!x. dst = Var x \/ lop = Var x ==> not_fresh_at s6 x) /\
  EVERY (\i. MEM i.inst_opcode [SLOAD; TLOAD; LT; ASSERT; ADD; MUL])
    (emitted_insts sa s6)
Proof
  simp[emit_op_def, emit_void_def, fresh_id_def, fresh_var_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, emit_def] >>
  strip_tac >> gvs[] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[same_blocks_def, inst_extends_def, emitted_insts_def,
       DROP_LENGTH_APPEND, mk_inst_def, Excl "isPREFIX"] >>
  Cases_on `tr` >> simp[not_fresh_at_def, Excl "isPREFIX"] >>
  rpt strip_tac >> gvs[fresh_var_distinct] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]
QED

Theorem append_storage_aggregate_prefix_run_unpruned:
  emit_op (if tr then TLOAD else SLOAD) [bop] sa = (lop,s1) /\
  emit_op LT [lop; Lit (n2w cap)] s1 = (valid,s2) /\
  emit_void ASSERT [valid] s2 = ((),s3) /\
  emit_op ADD [bop; Lit 1w] s3 = (dop,s4) /\
  emit_op MUL [lop; Lit (n2w n)] s4 = (off,s5) /\
  emit_op ADD [dop; off] s5 = (dst,s6) /\
  (!x. bop = Var x ==> not_fresh_at sa x) /\
  eval_operand bop s = SOME slot /\ cap < dimword (:256) /\
  len = w2n (if tr then tload slot s else sload slot s) /\ len < cap ==>
  ?u. run_inst_seq (emitted_insts sa s6) s = OK u /\
    eval_operand dst u = SOME (slot + 1w + n2w len * n2w n) /\
    eval_operand lop u = SOME (n2w len) /\ state_frame u = state_frame s /\
    (!x a. not_fresh_at sa x /\ lookup_var x s = SOME a ==> lookup_var x u = SOME a)
Proof
  strip_tac >> drule_all append_storage_aggregate_prefix_layout >> strip_tac >>
  `fresh_vars_wrt sa (drop_fresh sa s)` by simp[fresh_vars_wrt_drop_fresh] >>
  `eval_operand bop (drop_fresh sa s) = SOME slot` by simp[eval_operand_drop_fresh] >>
  `len = w2n (if tr then tload slot (drop_fresh sa s)
             else sload slot (drop_fresh sa s))` by
    simp[drop_fresh_def, tload_def, sload_def,
         contract_transient_def, contract_storage_def] >>
  drule_all append_storage_aggregate_prefix_run >> strip_tac >>
  `vars_ext_result (run_inst_seq (emitted_insts sa s6) (drop_fresh sa s))
     (run_inst_seq (emitted_insts sa s6) s)` by
    (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh] >>
     fs[EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `!i. MEM i (emitted_insts sa s6) ==> i.inst_opcode = SLOAD \/ _` drule >>
     disch_then strip_assume_tac >>
     gvs[is_terminator_def, is_ext_call_op_def]) >>
  `?u. run_inst_seq (emitted_insts sa s6) s = OK u /\ vars_ext t u` by
    (qpat_x_assum `vars_ext_result _ _` mp_tac >> asm_rewrite_tac [] >>
     Cases_on `run_inst_seq (emitted_insts sa s6) s` >> simp[vars_ext_result_def]) >>
  qexists_tac `u` >> asm_rewrite_tac [] >>
  conj_tac >- metis_tac[vars_ext_eval_operand] >>
  conj_tac >- metis_tac[vars_ext_eval_operand] >>
  conj_tac
  >- (`state_frame u = state_frame t` by
        (qpat_x_assum `vars_ext t u` mp_tac >>
         simp_tac bool_ss [vars_ext_def] >> strip_tac >>
         qpat_x_assum `u = _` (fn th => once_rewrite_tac [th]) >>
         rewrite_tac [state_frame_vars]) >>
      gvs[drop_fresh_def, state_frame_vars]) >>
  rpt strip_tac >>
  `eval_operand (Var x) (drop_fresh sa s) = SOME a` by
    simp[eval_operand_def, lookup_var_drop_fresh] >>
  `eval_operand (Var x) t = SOME a` by metis_tac[] >>
  `eval_operand (Var x) u = SOME a` by metis_tac[vars_ext_eval_operand] >>
  fs[eval_operand_def]
QED

Theorem append_storage_aggregate_prefix_path:
  emit_op (if tr then TLOAD else SLOAD) [bop] sa = (lop,s1) /\
  emit_op LT [lop; Lit (n2w cap)] s1 = (valid,s2) /\
  emit_void ASSERT [valid] s2 = ((),s3) /\
  emit_op ADD [bop; Lit 1w] s3 = (dop,s4) /\
  emit_op MUL [lop; Lit (n2w n)] s4 = (off,s5) /\
  emit_op ADD [dop; off] s5 = (dst,s6) /\
  (!x. bop = Var x ==> not_fresh_at sa x) /\
  eval_operand bop s = SOME slot /\ cap < dimword (:256) /\
  len = w2n (if tr then tload slot s else sload slot s) /\ len < cap /\
  fn_has_code sa s6 func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    eval_operand dst t = SOME (slot + 1w + n2w len * n2w n) /\
    eval_operand lop t = SOME (n2w len) /\
    state_frame t = state_frame (s with vs_inst_idx := LENGTH s6.cs_current_insts) /\
    (!x a. not_fresh_at sa x /\ lookup_var x s = SOME a ==> lookup_var x t = SOME a) /\
    t.vs_current_bb = s6.cs_current_bb /\
    t.vs_inst_idx = LENGTH s6.cs_current_insts /\ ~t.vs_halted
Proof
  strip_tac >> drule_all append_storage_aggregate_prefix_layout >> strip_tac >>
  drule_all append_storage_aggregate_prefix_run_unpruned >> strip_tac >>
  `s6.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa s6` by
    fs[inst_extends_def, emitted_insts_def, IS_PREFIX_APPEND] >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
              ~is_terminator i.inst_opcode) (emitted_insts sa s6)` by
    (fs[EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `!i. MEM i (emitted_insts sa s6) ==> i.inst_opcode = SLOAD \/ _` drule >>
     disch_then strip_assume_tac >> gvs[is_terminator_def]) >>
  `run_inst_seq_mem_ok (emitted_insts sa s6) s` by
    (irule run_inst_seq_mem_ok_every >> fs[EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `!i. MEM i (emitted_insts sa s6) ==> i.inst_opcode = SLOAD \/ _` drule >>
     disch_then strip_assume_tac >>
     simp[below_frontier_no_ranges, inst_dload_in_section_def]) >>
  `gas_path_mem ctx func s 0 (OK (u with vs_inst_idx := LENGTH s6.cs_current_insts))` by
    (irule body_decl_zero_gas_path >> simp[] >> qexists_tac `sa` >> simp[]) >>
  qexists_tac `u with vs_inst_idx := LENGTH s6.cs_current_insts` >>
  gvs[gas_marked_path_def, same_blocks_def, state_frame_def,
      eval_operand_def, lookup_var_def]
QED

Theorem append_storage_aggregate_code_bounds:
  emit_op (if tr then TLOAD else SLOAD) [bop] sa = (lop,s1) /\
  emit_op LT [lop; Lit (n2w cap)] s1 = (valid,s2) /\
  emit_void ASSERT [valid] s2 = ((),s3) /\
  emit_op ADD [bop; Lit 1w] s3 = (dop,s4) /\
  emit_op MUL [lop; Lit (n2w n)] s4 = (off,s5) /\
  emit_op ADD [dop; off] s5 = (dst,s6) /\
  compile_word_copy_loop vop dst n LocMemory
    (if tr then LocTransient else LocStorage) F s6 = (u,s7) /\
  emit_op ADD [lop; Lit 1w] s7 = (fresh,s8) /\
  emit_void (if tr then TSTORE else SSTORE) [bop;fresh] s8 = ((),sf) /\
  fn_has_code sa sf func ==>
  fn_has_code sa s6 func /\ fn_has_code s6 s7 func /\
  fn_has_code s7 sf func /\
  (!x. not_fresh_at sa x ==> not_fresh_at s6 x) /\
  (!x. dst = Var x \/ lop = Var x ==> not_fresh_at s6 x) /\
  (!x. not_fresh_at s6 x ==> not_fresh_at s7 x)
Proof
  strip_tac >> drule_all append_storage_aggregate_prefix_layout >> strip_tac >>
  `cs_extends sa s6` by
    (fs[same_blocks_def, inst_extends_def] >>
     simp[cs_extends_def] >> qexists_tac `[]` >> simp[IS_PREFIX_APPEND]) >>
  `ci_mono s6 s7` by metis_tac[ci_mono_compile_word_copy_loop, SND] >>
  `ci_mono s7 s8` by metis_tac[ci_mono_emit_op, SND] >>
  `ci_mono s8 sf` by metis_tac[ci_mono_emit_void, SND] >>
  `cs_extends s6 s7 /\ cs_extends s7 sf` by
    metis_tac[ci_mono_def, cs_extends_trans] >>
  `cs_extends sa s7` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa s7 func /\ fn_has_code s7 sf func` by
    metis_tac[fn_has_code_split] >>
  simp[] >> conj_tac >- metis_tac[fn_has_code_split] >>
  conj_tac >- metis_tac[fn_has_code_split] >>
  conj_tac >- asm_rewrite_tac [] >>
  fs[ci_mono_def] >> simp[not_fresh_at_def] >> rpt strip_tac >>
  qpat_x_assum `!n. s6.cs_next_var <= n ==> _` irule >> decide_tac
QED

Theorem append_storage_aggregate_header_run:
  emit_op ADD [lop; Lit 1w] sa = (fresh,s1) /\
  emit_void (if tr then TSTORE else SSTORE) [bop;fresh] s1 = ((),sb) /\
  (!x. bop = Var x ==> not_fresh_at sa x) /\
  eval_operand bop s = SOME slot /\ eval_operand lop s = SOME len /\
  ~s.vs_call_ctx.cc_static ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    state_frame t = state_frame
      (if tr then tstore slot (len+1w) s else sstore slot (len+1w) s) /\
    (!x a. not_fresh_at sa x /\ lookup_var x s = SOME a ==> lookup_var x t = SOME a) /\
    same_blocks sa sb /\ inst_extends sa sb /\
    EVERY (\i. MEM i.inst_opcode [ADD;SSTORE;TSTORE]) (emitted_insts sa sb)
Proof
  strip_tac >>
  `!x. not_fresh_at sa x ==> x <> STRING #"%" (toString sa.cs_next_var)` by
    simp[not_fresh_at_def] >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
  `inst_extends sa sb` by metis_tac[inst_extends_trans] >>
  `emitted_insts sa sb = emitted_insts sa s1 ++ emitted_insts s1 sb` by
    metis_tac[emitted_insts_append, inst_extends_def] >>
  `same_blocks sa sb` by
    (imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
     fs[same_blocks_def]) >>
  qmatch_asmsub_abbrev_tac `fresh = Var v` >>
  `!x. not_fresh_at sa x ==> x <> v` by metis_tac[Abbr `v`] >>
  `eval_operand bop (update_var v (len+1w) s) = SOME slot` by
    (Cases_on `bop` >> gvs[eval_operand_def, lookup_var_update_var] >> metis_tac[]) >>
  `step_inst_base (mk_inst sa.cs_next_id ADD [lop;Lit 1w] [v]) s =
    OK (update_var v (len+1w) s)` by
    (irule step_ADD >> simp[eval_operand_def]) >>
  qexists_tac `if tr then tstore slot (len+1w) (update_var v (len+1w) s)
              else sstore slot (len+1w) (update_var v (len+1w) s)` >>
  conj_tac
  >- (asm_rewrite_tac [] >> pure_rewrite_tac [APPEND] >>
      rewrite_tac[run_inst_seq_def] >>
      asm_rewrite_tac [] >> Cases_on `tr` >>
      simp[stepInstBaseLib.simp_opcode_clause ``SSTORE``,
           stepInstBaseLib.simp_opcode_clause ``TSTORE``, mk_inst_def,
           exec_write2_def, eval_operand_update_var] >>
      gvs[update_var_def]) >>
  Cases_on `tr` >>
  simp[state_frame_def, tstore_def, sstore_def, update_var_def, mk_inst_def,
       lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem append_storage_aggregate_header_path:
  emit_op ADD [lop; Lit 1w] sa = (fresh,s1) /\
  emit_void (if tr then TSTORE else SSTORE) [bop;fresh] s1 = ((),sb) /\
  (!x. bop = Var x ==> not_fresh_at sa x) /\
  eval_operand bop s = SOME slot /\ eval_operand lop s = SOME len /\
  ~s.vs_call_ctx.cc_static /\ fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    state_frame t = state_frame
      ((if tr then tstore slot (len+1w) s else sstore slot (len+1w) s)
       with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    (!x a. not_fresh_at sa x /\ lookup_var x s = SOME a ==> lookup_var x t = SOME a) /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ~t.vs_halted
Proof
  strip_tac >> drule_all append_storage_aggregate_header_run >> strip_tac >>
  `sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    fs[inst_extends_def] >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
              ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (qpat_x_assum `EVERY (\i. MEM i.inst_opcode _) _` mp_tac >>
     pure_rewrite_tac [EVERY_MEM] >> strip_tac >> gen_tac >> strip_tac >>
     first_x_assum drule >> simp[] >> strip_tac >> simp[is_terminator_def]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule run_inst_seq_mem_ok_every >> fs[EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `!i. MEM i (emitted_insts sa sb) ==> i.inst_opcode = ADD \/ _` drule >>
     simp[] >> strip_tac >>
     gvs[below_frontier_no_ranges, inst_dload_in_section_def]) >>
  `gas_path_mem ctx func s 0 (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule body_decl_zero_gas_path >> simp[] >> qexists_tac `sa` >> simp[]) >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  Cases_on `tr` >>
  gvs[gas_marked_path_def, same_blocks_def, state_frame_def,
      sstore_def, tstore_def, lookup_var_def]
QED

Theorem append_storage_aggregate_success_path:
  compile_dynarray_append cenv bop vop 1 n dt vt cap F
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sa = ((),sf) /\
  (!x. bop = Var x \/ vop = Var x ==> not_fresh_at sa x) /\
  eval_operand bop s = SOME slot /\ eval_operand vop s = SOME b /\
  cap < dimword (:256) /\ n < dimword (:256) /\
  w2n b + 32*n <= s.vs_alloca_next /\
  len = w2n (if tr then tload slot s else sload slot s) /\ len < cap /\
  fn_has_code sa sf func /\ ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
    store_copy_normalize s t =
      (if tr then tstore else sstore) slot (n2w len+1w)
        (store_copy_prefix (if tr then LocTransient else LocStorage)
          b (slot+1w+n2w len*n2w n) s n) /\
    (!x a. not_fresh_at sa x /\ lookup_var x s = SOME a ==> lookup_var x t = SOME a) /\
    t.vs_current_bb = sf.cs_current_bb /\ t.vs_inst_idx = LENGTH sf.cs_current_insts /\
    ~t.vs_halted
Proof
  strip_tac >> drule (iffLR append_storage_copy_suffix_parts) >>
  disch_then (qx_choosel_then
    [`len'`, `valid`, `data`, `offset`, `dst`, `fresh`, `u`,
     `s1`, `s2`, `s3`, `s4`, `s5`, `s6`, `s7`, `s8`] strip_assume_tac) >>
  drule_all append_storage_aggregate_code_bounds >> strip_tac >>
  `!x. bop = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  drule_all append_storage_aggregate_prefix_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `gas_marked_path T ctx func s 0 (OK r)` >>
  `r.vs_alloca_next = s.vs_alloca_next /\ r.vs_call_ctx = s.vs_call_ctx` by
    fs[state_frame_def] >>
  `eval_operand bop r = SOME slot /\ eval_operand vop r = SOME b` by
    (Cases_on `bop` >> Cases_on `vop` >>
     gvs[eval_operand_def, state_frame_def] >> metis_tac[]) >>
  `!x. vop = Var x \/ dst = Var x ==> not_fresh_at s6 x` by metis_tac[] >>
  `?q. gas_marked_path T ctx func r 0 (OK q) /\
    store_copy_frame s6 (if tr then LocTransient else LocStorage)
      b (slot+1w+n2w len*n2w n) r n q /\ ~q.vs_halted /\
    q.vs_current_bb = s7.cs_current_bb /\ q.vs_inst_idx = LENGTH s7.cs_current_insts` by
    (irule topcopy_compile_loop_path >> simp[] >>
     reverse conj_tac >- (Cases_on `tr` >> simp[]) >>
     qexistsl_tac [`dst`, `vop`, `u`] >> asm_rewrite_tac [] >> simp[]) >>
  `eval_operand bop q = SOME slot /\ eval_operand len' q = SOME (n2w len)` by
    (conj_tac >> irule topcopy_frame_operand >> metis_tac[]) >>
  `!x. bop = Var x ==> not_fresh_at s7 x` by metis_tac[] >>
  `~q.vs_call_ctx.cc_static` by metis_tac[topcopy_frame_call_ctx] >>
  drule_all append_storage_aggregate_header_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  suspend "post"
QED

Resume append_storage_aggregate_success_path[post]:
  qexists_tac `t` >> conj_tac
  >- (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_marked_path_then)) >>
      qexists_tac `r` >> simp[] >>
      irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_marked_path_then)) >>
      qexists_tac `q` >> simp[]) >>
  reverse conj_tac
  >- (simp[] >> rpt strip_tac >>
      qpat_x_assum `store_copy_frame _ _ _ _ _ _ _` mp_tac >>
      simp[stmtSimStoreCopyTheory.store_copy_frame_def] >> metis_tac[]) >>
  suspend "normalize"
QED

Resume append_storage_aggregate_success_path[normalize]:
  `r.vs_memory = s.vs_memory /\ store_copy_normalize s r = s` by
    (qpat_x_assum `state_frame r = _` mp_tac >>
     simp[state_frame_def, stmtSimStoreCopyTheory.store_copy_normalize_def] >>
     rpt strip_tac >> simp[venom_state_component_equality]) >>
  `!i. store_copy_normalize s
       (store_copy_prefix (if tr then LocTransient else LocStorage)
          b (slot+1w+n2w len*n2w n) r i) =
       store_copy_prefix (if tr then LocTransient else LocStorage)
          b (slot+1w+n2w len*n2w n) s i` by
    (Cases_on `tr` >> simp[] >> Induct >>
     simp[topcopy_prefix_suc,
       SRULE [] (Q.INST [`loc` |-> `LocStorage`] topcopy_normalize_store),
       SRULE [] (Q.INST [`loc` |-> `LocTransient`] topcopy_normalize_store),
       mload_def]) >>
  `store_copy_normalize s q =
    store_copy_prefix (if tr then LocTransient else LocStorage)
      b (slot+1w+n2w len*n2w n) s n` by
    (qpat_x_assum `store_copy_frame _ _ _ _ _ _ _` mp_tac >>
     simp[stmtSimStoreCopyTheory.store_copy_frame_def] >> strip_tac >>
     qpat_x_assum `store_copy_normalize r q = _`
       (mp_tac o Q.AP_TERM `store_copy_normalize s`) >>
     first_x_assum (qspec_then `n` mp_tac) >>
     simp[stmtSimStoreCopyTheory.store_copy_normalize_def] >>
     metis_tac[]) >>
  qpat_x_assum `state_frame t = _`
    (mp_tac o Q.AP_TERM `store_copy_normalize s`) >>
  simp[state_frame_def, stmtSimStoreCopyTheory.store_copy_normalize_def] >>
  strip_tac >> asm_rewrite_tac [] >>
  Cases_on `tr` >>
  qpat_x_assum `store_copy_normalize s q = _` mp_tac >>
  simp[stmtSimStoreCopyTheory.store_copy_normalize_def, venom_state_component_equality,
       sstore_def, tstore_def] >> rpt strip_tac >> simp[]
QED

Finalise append_storage_aggregate_success_path


Theorem append_storage_aggregate_abort_path:
  compile_dynarray_append cenv bop vop 1 n dt vt cap F
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sa = ((),sf) /\
  (!x. bop = Var x ==> not_fresh_at sa x) /\
  eval_operand bop s = SOME slot /\ cap < dimword (:256) /\
  cap <= w2n (if tr then tload slot s else sload slot s) /\
  fn_has_code sa sf func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?a t. gas_marked_path T ctx func s 0 (Abort a t)
Proof
  strip_tac >> drule (iffLR append_storage_copy_suffix_parts) >>
  disch_then (qx_choosel_then
    [`len'`, `valid`, `data`, `offset`, `dst`, `fresh`, `u`,
     `s1`, `s2`, `s3`, `s4`, `s5`, `s6`, `s7`, `s8`] strip_assume_tac) >>
  drule_all append_storage_aggregate_code_bounds >> strip_tac >>
  drule_all append_storage_aggregate_prefix_layout >> strip_tac >>
  `fresh_vars_wrt sa (drop_fresh sa s)` by simp[fresh_vars_wrt_drop_fresh] >>
  `eval_operand bop (drop_fresh sa s) = SOME slot` by simp[eval_operand_drop_fresh] >>
  drule_all append_storage_guard_run >> strip_tac >>
  `~(w2n (if tr then tload slot (drop_fresh sa s)
           else sload slot (drop_fresh sa s)) < cap)` by
    (simp[drop_fresh_def, tload_def, sload_def, contract_transient_def, contract_storage_def] >>
     qpat_x_assum `cap <= _` mp_tac >>
     simp[tload_def, sload_def, contract_transient_def, contract_storage_def]) >>
  qpat_x_assum `if _ then _ else _` mp_tac >> asm_rewrite_tac [] >> strip_tac >>
  suspend "abort_run"
QED

Resume append_storage_aggregate_abort_path[abort_run]:
  `inst_extends sa s3 /\ inst_extends s3 s6` by
    (imp_res_tac inst_extends_emit_op >> imp_res_tac inst_extends_emit_void >>
     metis_tac[inst_extends_trans]) >>
  `run_inst_seq (emitted_insts sa s6) (drop_fresh sa s) =
    Abort Revert_abort (revert_state (set_returndata [] ss'))` by
    (`emitted_insts sa s6 = emitted_insts sa s3 ++ emitted_insts s3 s6` by
       metis_tac[emitted_insts_append, inst_extends_def] >>
     asm_rewrite_tac [] >>
     irule EQ_TRANS >> qexists_tac `run_inst_seq (emitted_insts sa s3) (drop_fresh sa s)` >>
     conj_tac >- (irule run_inst_seq_append_err >> simp[]) >> simp[]) >>
  `vars_ext_result (run_inst_seq (emitted_insts sa s6) (drop_fresh sa s))
     (run_inst_seq (emitted_insts sa s6) s)` by
    (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh] >>
     fs[EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `!i. MEM i (emitted_insts sa s6) ==> i.inst_opcode = SLOAD \/ _` drule >>
     disch_then strip_assume_tac >> gvs[is_terminator_def, is_ext_call_op_def]) >>
  `?a t. run_inst_seq (emitted_insts sa s6) s = Abort a t` by
    (qpat_x_assum `vars_ext_result _ _` mp_tac >> asm_rewrite_tac [] >>
     Cases_on `run_inst_seq (emitted_insts sa s6) s` >> simp[vars_ext_result_def]) >>
  suspend "path"
QED

Resume append_storage_aggregate_abort_path[path]:
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
              ~is_terminator i.inst_opcode) (emitted_insts sa s6)` by
    (qpat_x_assum `EVERY _ _` mp_tac >> rewrite_tac[EVERY_MEM] >>
     strip_tac >> rpt strip_tac >> first_x_assum drule >>
     simp[] >> strip_tac >> simp[is_terminator_def]) >>
  `run_inst_seq_mem_ok (emitted_insts sa s6) s` by
    (irule run_inst_seq_mem_ok_every >> fs[EVERY_MEM] >> rpt strip_tac >>
     qpat_x_assum `!i. MEM i (emitted_insts sa s6) ==> i.inst_opcode = SLOAD \/ _` drule >>
     simp[] >> strip_tac >> gvs[below_frontier_no_ranges, inst_dload_in_section_def]) >>
  `?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
     DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa s6 ++ rest` by
    (gvs[fn_has_code_def, same_blocks_def, inst_extends_def, IS_PREFIX_APPEND,
         emitted_insts_def] >> simp[DROP_APPEND, DROP_LENGTH_TOO_LONG]) >>
  `isPREFIX (emitted_insts sa s6) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[IS_PREFIX_APPEND] >>
  drule_all bodyUnopFragMemoryTheory.run_inst_seq_abort_zero_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >> metis_tac[]
QED

Finalise append_storage_aggregate_abort_path


Theorem append_storage_aggregate_suffix_mem:
  compile_dynarray_append cenv bop vop 1 n dt vt cap F
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sa = ((),sf) /\
  (!x. bop = Var x \/ vop = Var x ==> not_fresh_at sa x) /\
  eval_operand bop s = SOME slot /\ cap < dimword (:256) /\
  fn_has_code sa sf func /\ ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  (cap <= w2n (if tr then tload slot s else sload slot s) ==>
    ?a t. gas_marked_path T ctx func s 0 (Abort a t)) /\
  (!b len. eval_operand vop s = SOME b /\ n < dimword (:256) /\
    w2n b + 32*n <= s.vs_alloca_next /\
    len = w2n (if tr then tload slot s else sload slot s) /\ len < cap ==>
    ?t. gas_marked_path T ctx func s 0 (OK t) /\
      store_copy_normalize s t =
        (if tr then tstore else sstore) slot (n2w len+1w)
          (store_copy_prefix (if tr then LocTransient else LocStorage)
            b (slot+1w+n2w len*n2w n) s n) /\
      (!x a. not_fresh_at sa x /\ lookup_var x s = SOME a ==> lookup_var x t = SOME a) /\
      t.vs_current_bb = sf.cs_current_bb /\ t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      ~t.vs_halted /\ t.vs_memory = s.vs_memory /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next)
Proof
  strip_tac >> conj_tac
  >- (strip_tac >>
      `!x. bop = Var x ==> not_fresh_at sa x` by metis_tac[] >>
      drule_all append_storage_aggregate_abort_path >>
      disch_then (qspec_then `ctx` mp_tac) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  drule_all append_storage_aggregate_success_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists_tac `t` >> asm_rewrite_tac [] >>
  `!i. (store_copy_prefix (if tr then LocTransient else LocStorage)
           b (slot+1w+n2w len*n2w n) s i).vs_memory = s.vs_memory /\
         (store_copy_prefix (if tr then LocTransient else LocStorage)
           b (slot+1w+n2w len*n2w n) s i).vs_allocas = s.vs_allocas /\
         (store_copy_prefix (if tr then LocTransient else LocStorage)
           b (slot+1w+n2w len*n2w n) s i).vs_alloca_next = s.vs_alloca_next` by
    (Cases_on `tr` >> Induct >> gvs[topcopy_prefix_suc, sstore_def, tstore_def]) >>
  qpat_x_assum `store_copy_normalize s t = _`
    (mp_tac o Q.AP_TERM `\q. (q.vs_memory,q.vs_allocas,q.vs_alloca_next)`) >>
  Cases_on `tr` >>
  gvs[stmtSimStoreCopyTheory.store_copy_normalize_def, sstore_def, tstore_def]
QED
