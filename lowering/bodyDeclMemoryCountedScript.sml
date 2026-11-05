(* Counted straight-line paths for declaration memory operations. *)
Theory bodyDeclMemoryCounted
Ancestors
  bodyDeclMemoryCore fragGasSeqMem fragGasPathMem
  loweringPosts exprSimProps stmtSimProps exprSimHypsDefs
  bodyNameMemoryFacts bodyCopyMemory bodyMemoryDefs stmtSimDeclMem
  localPtrsProps stmtSimDeclStore stmtSimDecl valueCopy valueCopyBytes
  exprOperandVar freshWrites valueTypingMemoryProps vyperTyping
  exprSimDefs stmtSimDefs venomState valueEncoding valueEncodingProofs
  intCallResult compileEnv exprLoweringProps loweringSlice exprLowering
  exprSimBufferStore words venomExecSemantics stmtLowering context
  fragExec fragExecMem allocaHistoryFragment list rich_list emitHelper
  emitHelperProps venomInst exprSimLiteralBuffer exprSimAlloc exprSimBuffer
  finite_map bodySimDeclCases allocLimits bodySim exprSimHyps
  vyperTypeSystem vyperTypeInvariants memoryLocalRhsProps
  supportedStmtTraverse supportedExprTraverse vyperTypeCallGraph
  vyperTypeCallStackSoundness vyperInterpreter vyperState

Theorem body_decl_zero_gas_path:
  fn_has_code sa sb func /\ same_blocks sa sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  gas_path_mem ctx func s 0
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  `(?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest) /\
    s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND, same_blocks_def] >>
     simp[DROP_APPEND, DROP_LENGTH_TOO_LONG]) >>
  `isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[IS_PREFIX_APPEND] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  `FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (simp[FILTER_EQ_NIL, EVERY_MEM] >> fs[EVERY_MEM]) >>
  drule_all run_inst_seq_gas_path_mem >> simp[]
QED

Theorem annassign_setup_body_gas_path_mem:
  declare_local ce id ty sa = (c,st) /\ ce.ce_alloca_locals /\
  lookup_scopes id es.scopes = NONE /\
  (!l. FLOOKUP ce.ce_vars id = SOME l ==> ?q sz. l = PtrVar q sz) /\
  p = STRING #"%" (toString sa.cs_next_var) /\
  emit_inst ALLOCA [Lit (n2w (type_memory_bytes ce ty))] [p] st = ((),sA) /\
  type_memory_bytes ce ty < dimword (:256) /\
  fn_has_code sa sA func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ stmt_state_rel ctx func ce cx es s /\
  alloca_history func s /\ return_buf_frame d ce sa s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
    ~t.vs_halted /\ t.vs_current_bb = sA.cs_current_bb /\
    t.vs_inst_idx = LENGTH sA.cs_current_insts /\
    stmt_state_rel ctx func c cx es t /\ alloca_history func t /\
    return_buf_frame d c sA t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    local_ptrs_reserved c sA /\ not_fresh_at sA p /\
    FLOOKUP c.ce_vars id = SOME (PtrVar (Var p) (type_memory_bytes ce ty)) /\
    not_local_ptr c es.scopes p /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
    ?w. lookup_var p t = SOME w /\
      FLOOKUP t.vs_allocas st.cs_next_id = SOME (w2n w,type_memory_bytes ce ty) /\
      w2n w + type_memory_bytes ce ty <= t.vs_alloca_next
Proof
  strip_tac >> drule_all annassign_setup_shape >> strip_tac >>
  `stmt_state_rel ctx func c cx es s` by metis_tac[stmt_state_rel_declare_local_entry] >>
  qabbrev_tac `A = mk_inst st.cs_next_id ALLOCA
    [Lit (n2w (type_memory_bytes ce ty))] [p]` >>
  `A.inst_opcode = ALLOCA /\ A.inst_operands = [Lit (n2w (type_memory_bytes ce ty))] /\
   A.inst_outputs = [p] /\ A.inst_id = st.cs_next_id` by simp[Abbr `A`, mk_inst_def] >>
  drule_all body_decl_alloca_run >> strip_tac >>
  `sa.cs_next_var <= sA.cs_next_var` by (drule emit_inst_extends >> gvs[]) >>
  `return_buf_frame d c sA t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`ce`, `s`, `sa`] >> simp[]) >>
  `emitted_insts sa sA = [A] /\ same_blocks sa sA /\
   sA.cs_current_insts = sa.cs_current_insts ++ [A]` by
    (drule emit_inst_extends >> strip_tac >>
     gvs[emitted_insts_def, same_blocks_def, Abbr `A`, DROP_LENGTH_APPEND]) >>
  `run_inst_seq (emitted_insts sa sA) s = OK t` by
    (gvs[mk_inst_def] >> simp[run_inst_seq_def, step_inst_base_def]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sA) s` by
    (simp[run_inst_seq_mem_ok_last] >>
     irule instMemFrontierTheory.below_frontier_no_ranges >> simp[Abbr `A`, mk_inst_def]) >>
  `gas_path_mem ctx func s 0 (OK (t with vs_inst_idx := LENGTH sA.cs_current_insts))` by
    (irule body_decl_zero_gas_path >> simp[] >> qexists_tac `sa` >> simp[is_terminator_def]) >>
  `alloca_history func (t with vs_inst_idx := LENGTH sA.cs_current_insts)` by
    (irule body_store_memory_history >> simp[same_blocks_def, is_terminator_def] >>
     qexistsl_tac [`s`, `sa`] >> simp[is_terminator_def] >> fs[stmt_state_rel_def, same_blocks_def]) >>
  `t.vs_halted = s.vs_halted /\ t.vs_current_bb = s.vs_current_bb` by
    (qpat_x_assum `exec_alloca A s _ = OK t` mp_tac >>
     simp[exec_alloca_def, AllCaseEqs()] >> rpt strip_tac >>
     gvs[update_var_def]) >>
  qexists_tac `t with vs_inst_idx := LENGTH sA.cs_current_insts` >>
  gvs[stmt_state_rel_inst_idx, same_blocks_def] >>
  conj_tac
  >- (Cases_on `d` >- fs[return_buf_frame_def] >>
      rename1 `return_buf_frame (SOME pair)` >> PairCases_on `pair` >>
      fs[return_buf_frame_def, lookup_var_def]) >>
  fs[lookup_var_def] >> rpt strip_tac >>
  first_x_assum irule >> strip_tac >> gvs[]
QED

Theorem body_decl_cursor_path:
  !sa sb s t ctx func.
    fn_has_code sa sb func /\ same_blocks sa sb /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
      ~is_terminator i.inst_opcode) (emitted_insts sa sb) /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    run_inst_seq_mem_ok (emitted_insts sa sb) s /\
    run_inst_seq (emitted_insts sa sb) s = OK t ==>
    gas_path_mem ctx func s 0
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb
Proof
  rpt gen_tac >> strip_tac >>
  `gas_path_mem ctx func s 0
     (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule body_decl_zero_gas_path >> simp[] >> qexists_tac `sa` >> simp[]) >>
  drule gas_path_mem_exec >> strip_tac >> gvs[exit_result_def] >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
     isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND, same_blocks_def] >>
     simp[DROP_APPEND, DROP_LENGTH_TOO_LONG]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  qspecl_then [`emitted_insts sa sb`, `s`, `0`, `ctx`, `bb`] mp_tac
    exec_block_run_inst_seq >>
  simp[] >> gvs[same_blocks_def]
QED

Theorem compile_copy_memory_no_gas:
  compile_copy_memory dst src n sa = ((),sb) ==>
  EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  Cases_on `n` >> simp[compile_copy_memory_def, comp_return_def] >>
  strip_tac >- gvs[emitted_insts_def] >>
  drule emitted_insts_emit_void >> simp[mk_inst_def]
QED

Theorem compile_store_memory_same_no_gas:
  compile_store_memory cenv src dst ty ty sa = ((),sb) /\ ~is_word_type ty ==>
  EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)
Proof
  rw[compile_store_memory_def]
  >- (gvs[compile_store_bytestring_def, compile_bytestring_copy_len_def,
          emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
          comp_return_def, fresh_id_def, fresh_var_def, emit_def, LET_THM] >>
      simp[emitted_insts_def, mk_inst_def] >>
      rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]) >>
  metis_tac[compile_copy_memory_no_gas]
QED

Theorem body_scratch_prefix_no_gas:
  compile_alloc_buffer n sa = (buf,sm) /\
  compile_copy_memory buf.buf_operand src n sm = ((),sn) ==>
  EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sn)
Proof
  rpt strip_tac >> drule_all body_scratch_prefix_shape >> strip_tac >>
  drule abiBuiltinAllocationTheory.abi_builtin_alloc_buffer_shape >> strip_tac >>
  asm_simp_tac (srw_ss()) [EVERY_APPEND] >> conj_tac
  >- (drule emitted_insts_emit_op >> simp[mk_inst_def]) >>
  metis_tac[compile_copy_memory_no_gas]
QED

Theorem annassign_memory_store_body_path:
  !ctx func cenv cx es s id p sz w inst v tyv sc rest a src ty sa sb sw d.
    compile_store_memory cenv src (Var p) ty ty sa = ((), sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\ not_fresh_at sa p /\
    eval_operand src s = SOME sw /\ lookup_var p s = SOME w /\
    ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tyv /\
    value_has_type tyv v /\ val_wf tyv v /\
    val_in_memory tyv v (w2n sw) s.vs_memory /\
    type_memory_bytes cenv ty = type_memory_size tyv /\
    type_memory_size tyv <= sz /\ type_memory_size tyv + 64 < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr cenv es.scopes p /\ MEM inst (fn_insts func) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
    local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\
    w2n sw + val_store_size tyv v <= s.vs_alloca_next /\
    w2n w + type_memory_size tyv <= s.vs_alloca_next /\
    alloca_history func s /\ return_buf_frame d cenv sa s /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_path_mem ctx func s 0 (OK t) /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      stmt_state_rel ctx func cenv cx
        (es with scopes :=
          (sc |+ (id, <|assignable := a; type := tyv; value := v; popped := []|>)) :: rest) t /\
      alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
      return_buf_frame d cenv sb t /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b)
Proof
  rpt gen_tac >> strip_tac >>
  `eval_operand (Var p) s = SOME w` by simp[eval_operand_def] >>
  drule compile_store_memory_run_size_bound_with_capacity >>
  disch_then (qspecl_then [`s`, `get_tenv cx`, `tyv`, `v`, `sw`, `w`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `stmt_state_rel ctx func cenv cx
     (es with scopes :=
       (sc |+ (id, <|assignable := a; type := tyv; value := v; popped := []|>)) :: rest) t` by
    (irule body_stmt_state_rel_declare_store_frame >> simp[] >>
     qexistsl_tac [`inst`, `s`, `sa`, `w`] >> gs[] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
     simp[venom_state_component_equality] >> metis_tac[]) >>
  `return_buf_frame d cenv sb t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`, `s`, `sa`] >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule body_typed_store_memory_mem_ok >>
     goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
     qexistsl_tac [`w`, `get_tenv cx`, `tyv`, `v`, `sw`] >>
     simp[] >> metis_tac[]) >>
  `EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb)` by
    metis_tac[compile_store_memory_same_no_gas] >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by fs[EVERY_MEM] >>
  `gas_path_mem ctx func s 0
     (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
   ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb` by
    (irule body_decl_cursor_path >> simp[] >> qexists_tac `sa` >> simp[]) >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule body_store_memory_history >> simp[] >>
     qexistsl_tac [`s`, `sa`] >> simp[]) >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[stmt_state_rel_inst_idx] >>
  conj_tac
  >- (Cases_on `d` >- fs[return_buf_frame_def] >>
      rename1 `return_buf_frame (SOME pair)` >> PairCases_on `pair` >>
      fs[return_buf_frame_def, lookup_var_def]) >>
  fs[lookup_var_def]
QED

Theorem compile_scratch_prefix_body_path:
  !ctx func ce cx es s sa sm sn buf src n sw tv v d.
    compile_alloc_buffer n sa = (buf,sm) /\
    compile_copy_memory buf.buf_operand src n sm = ((),sn) /\
    fn_has_code sa sn func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved ce sa /\ stmt_state_rel ctx func ce cx es s /\
    alloca_history func s /\ return_buf_frame d ce sa s /\
    (!x. src = Var x ==> not_fresh_at sa x) /\
    eval_operand src s = SOME sw /\ n < dimword (:256) /\
    w2n sw + n <= s.vs_alloca_next /\
    val_in_memory tv v (w2n sw) s.vs_memory /\ val_wf tv v /\
    val_footprint tv v <= n /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_path_mem ctx func s 0 (OK t) /\ ~t.vs_halted /\
      t.vs_current_bb = sn.cs_current_bb /\
      t.vs_inst_idx = LENGTH sn.cs_current_insts /\
      stmt_state_rel ctx func ce cx es t /\ alloca_history func t /\
      return_buf_frame d ce sn t /\ s.vs_alloca_next <= t.vs_alloca_next /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
               FLOOKUP t.vs_allocas aid = SOME b) /\
      val_wf tv v /\ ?w. eval_operand buf.buf_operand t = SOME w /\
        val_in_memory tv v (w2n w) t.vs_memory /\
        w2n w + n <= t.vs_alloca_next
Proof
  rpt gen_tac >> strip_tac >>
  drule_all body_scratch_prefix_shape >> strip_tac >>
  `fn_has_code sa sm func` by metis_tac[fn_has_code_split] >>
  drule_all body_scratch_prefix_run >> strip_tac >>
  `run_inst_seq (emitted_insts sa sn) s = OK t` by
    (asm_rewrite_tac[] >>
     qpat_x_assum `run_inst_seq (emitted_insts sa sm) s = OK a`
       (mp_tac o MATCH_MP run_inst_seq_append) >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sn) s` by
    (asm_rewrite_tac[] >> irule run_inst_seq_mem_ok_append >> simp[] >>
     rpt strip_tac >> gvs[]) >>
  `return_buf_frame d ce sn t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`ce`, `s`, `sa`] >> simp[]) >>
  `EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sn)` by
    metis_tac[body_scratch_prefix_no_gas] >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) (emitted_insts sa sn)` by fs[EVERY_MEM] >>
  `gas_path_mem ctx func s 0
     (OK (t with vs_inst_idx := LENGTH sn.cs_current_insts)) /\
   ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb` by
    (irule body_decl_cursor_path >> simp[] >> qexists_tac `sa` >> simp[]) >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `alloca_history func (t with vs_inst_idx := LENGTH sn.cs_current_insts)` by
    (irule body_store_memory_history >> simp[] >>
     qexistsl_tac [`s`, `sa`] >> simp[]) >>
  qexists_tac `t with vs_inst_idx := LENGTH sn.cs_current_insts` >>
  simp[stmt_state_rel_inst_idx] >>
  conj_tac
  >- (Cases_on `d` >- fs[return_buf_frame_def] >>
      rename1 `return_buf_frame (SOME pair)` >> PairCases_on `pair` >>
      fs[return_buf_frame_def, lookup_var_def]) >>
  fs[lookup_var_def] >>
  Cases_on `buf.buf_operand` >> gvs[eval_operand_def, lookup_var_def]
QED

Theorem annassign_memory_assign_body_path:
  !ctx func cenv cx es s id p sz w inst v tyv sc rest a src ty sa sb sw d info bytes.
    compile_assign_value cenv (Var p) LocMemory src F (SOME LocMemory)
      ty ty info bytes sa = ((), sb) /\
    (!x. src = Var x ==> not_fresh_at sa x) /\ not_fresh_at sa p /\
    eval_operand src s = SOME sw /\ lookup_var p s = SOME w /\
    ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tyv /\
    value_has_type tyv v /\ val_wf tyv v /\
    val_in_memory tyv v (w2n sw) s.vs_memory /\
    type_memory_bytes cenv ty = type_memory_size tyv /\
    type_memory_size tyv <= sz /\ type_memory_size tyv + 64 < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr cenv es.scopes p /\ MEM inst (fn_insts func) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
    local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\
    w2n sw + type_memory_size tyv <= s.vs_alloca_next /\
    w2n w + type_memory_size tyv <= s.vs_alloca_next /\
    alloca_history func s /\ return_buf_frame d cenv sa s /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_path_mem ctx func s 0 (OK t) /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      stmt_state_rel ctx func cenv cx
        (es with scopes :=
          (sc |+ (id, <|assignable := a; type := tyv; value := v; popped := []|>)) :: rest) t /\
      alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
      return_buf_frame d cenv sb t /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b)
Proof
  rpt gen_tac >> strip_tac >> drule_all assign_memory_body_code >> strip_tac >>
  `cs_extends sa sn` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sn func` by metis_tac[fn_has_code_split] >>
  `val_footprint tyv v <= type_memory_bytes cenv ty` by
    (drule val_footprint_le >> simp[]) >>
  `type_memory_bytes cenv ty < dimword (:256)` by decide_tac >>
  `w2n sw + type_memory_bytes cenv ty <= s.vs_alloca_next` by simp[] >>
  drule_all compile_scratch_prefix_body_path >> strip_tac >>
  `sa.cs_next_var <= sn.cs_next_var` by
    (drule_all body_scratch_prefix_shape >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sn x` by
    metis_tac[not_fresh_at_mono] >>
  `local_ptrs_reserved cenv sn` by
    (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `!x. buf.buf_operand = Var x ==> not_fresh_at sn x` by
    (drule body_scratch_alloc_operand >> strip_tac >>
     drule abiBuiltinAllocationTheory.abi_builtin_alloc_buffer_shape >> strip_tac >>
     drule buffer_copy_memory_shape >> strip_tac >>
     qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, fresh_var_def, fresh_id_def, emit_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def] >> strip_tac >> gvs[not_fresh_at_def]) >>
  `lookup_var p t = SOME w /\
   FLOOKUP t.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
   w2n w + type_memory_size tyv <= t.vs_alloca_next` by
    (simp[] >> decide_tac) >>
  `w2n w' + type_memory_size tyv <= t.vs_alloca_next` by decide_tac >>
  `w2n w' + val_store_size tyv v <= t.vs_alloca_next` by
    (`val_store_size tyv v <= type_memory_size tyv` by
       metis_tac[val_store_size_le] >> decide_tac) >>
  `not_fresh_at sn p` by simp[] >>
  drule_all annassign_memory_store_body_path >>
  disch_then (qspec_then `a` (qx_choose_then `t2` strip_assume_tac)) >>
  qexists_tac `t2` >>
  `gas_path_mem ctx func s (0 + 0) (OK t2)` by
    (irule gas_path_mem_then >> qexists_tac `t` >> simp[]) >>
  fs[] >> rpt strip_tac >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem annassign_name_rhs_body_path:
  !ctx func cenv cx env source_id es s id p sz w inst v tyv sc rest a src ty sa sm sb d info bytes.
    lower_value compile_expr cenv ty (Name ty source_id) sa = (src,sm) /\
    expr_sim_pre cenv cx env (Name ty source_id) es /\
    (do result <- eval_expr cx (Name ty source_id); read_result cx result od) es = (INL v,es) /\
    compile_assign_value cenv (Var p) LocMemory src F (SOME LocMemory)
      ty ty info bytes sm = ((), sb) /\
    not_fresh_at sa p /\ lookup_var p s = SOME w /\
    ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tyv /\
    type_memory_bytes cenv ty = type_memory_size tyv /\
    type_memory_size tyv <= sz /\ type_memory_size tyv + 64 < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    not_local_ptr cenv es.scopes p /\ MEM inst (fn_insts func) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w, sz) /\
    local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\
    w2n w + type_memory_size tyv <= s.vs_alloca_next /\
    alloca_history func s /\ return_buf_frame d cenv sa s /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_path_mem ctx func s 0 (OK t) /\ ~t.vs_halted /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      stmt_state_rel ctx func cenv cx
        (es with scopes :=
          (sc |+ (id, <|assignable := a; type := tyv; value := v; popped := []|>)) :: rest) t /\
      alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
      return_buf_frame d cenv sb t /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all bodyNameMemoryFactsTheory.body_name_source_region >> strip_tac >>
  drule_then (qspecl_then [`cx`, `ty`] assume_tac) eval_name_word >> gvs[] >>
  gvs[lower_value_def, compile_expr_def, compile_name_vv_def,
      comp_bind_def, comp_return_def, unwrap_value_def,
      contextTheory.mk_ptr_def, vyperASTTheory.expr_type_def] >>
  irule annassign_memory_assign_body_path >> simp[] >>
  goal_assum (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  simp[eval_operand_def] >>
  qexists_tac `inst` >> simp[] >>
  fs[local_ptrs_reserved_def] >> metis_tac[]
QED
