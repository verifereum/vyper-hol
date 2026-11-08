(* Immutable-copy landing with arbitrary prior register bindings. *)
Theory bodyIntCallWindowCode
Ancestors
  bodyIntCallWindowLanding bodyIntCallWindowCopy bodyIntCallForcingCode
  bodyIntCallForcingCodeRun exprSimCopy exprSimStorageCopy
  immutableCopyExecution immutableConstructorRelation valueEncodingProps
  valueEncoding valueCopy venomExecSemantics context intCallFrame
  fragGasMode entrySinkExtraction abiDecoderArrayInitExec stmtReasonMemory
  finite_map list rich_list words placeMemoryStaging venomState compileEnv
  fragExec emitHelperProps exprLoweringProps venomInst instIdxIndep
  placeMemoryPrimitiveForward vyperInterpreter vyperState loweringHalt
  exprSimAlloc bodyIntCallLiteralLanding exprSimProps
  loweringPosts exprLowering exprSimFieldLayout

Theorem optional_immutable_copy_landing:
  compile_imm_copy_to_memory ctor imm src dst n off sa = ((),sb) /\
  copy_old_operand sa src /\ copy_old_operand sa dst /\
  eval_operand src s = SOME (n2w a) /\ eval_operand dst s = SOME (n2w b) /\
  (!region. ctor /\ imm = SOME region ==>
     eval_operand region s = SOME 0w /\ copy_old_operand sa region) /\
  a+off+32*n < dimword (:256) /\ b+off+32*n < dimword (:256) /\
  (ctor ==> regions_disjoint (a+off) (32*n) (b+off) (32*n)) /\
  val_in_memory tv v (a+off) (if ctor then s.vs_memory else s.vs_data_section) /\
  val_wf tv v /\ type_memory_size tv = 32*n /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    val_in_memory tv v (b+off) u.vs_memory /\
    copy_static u = copy_static s /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (!q. copy_old_operand sa q ==> eval_operand q u = eval_operand q s) /\
    LENGTH s.vs_memory <= LENGTH u.vs_memory /\
    (!p k. regions_disjoint p k (b+off) (32*n) ==>
      mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  drule_all bodyIntCallWindowCopyTheory.optional_immutable_copy_run >> strip_tac >>
  drule_all materialization_snapshot_memory >> strip_tac >>
  `same_blocks sa sb /\ ?is. sb.cs_current_insts = sa.cs_current_insts ++ is /\
     EVERY (\i. MEM i.inst_opcode [ADD; ILOAD; DLOAD; MSTORE]) is` by
    (Cases_on `ctor` >> gvs[]
     >- (drule code_ctor_copy_insts >> strip_tac >> simp[] >>
         fs[EVERY_MEM] >> metis_tac[]) >>
     drule code_copy_insts >> strip_tac >> simp[] >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  `emitted_insts sa sb = is` by simp[emitted_insts_def, DROP_APPEND] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) is /\
   EVERY (\i. i.inst_opcode <> GAS) is` by
    (fs[EVERY_MEM] >> rpt strip_tac >> res_tac >> gvs[is_terminator_def]) >>
  fs[copy_runtime_frame_def] >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  `gas_marked_path F ctx func s 0
     (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule straight_line_zero_gas_path >> simp[] >>
     qexistsl_tac [`is`, `sa`] >> fs[same_blocks_def]) >>
  `t.vs_current_bb = sb.cs_current_bb` by fs[same_blocks_def] >>
  drule copy_static_fields >> strip_tac >>
  qpat_x_assum `t.vs_memory = _` kall_tac >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  fs[copy_static_def, lookup_var_def, eval_op_inst_idx] >>
  rpt strip_tac >> Cases_on `q` >>
  gvs[copy_old_operand_def, eval_operand_def, lookup_var_def]
QED

Theorem immutable_value_copy_landing:
  compile_imm_copy_to_memory ce.ce_is_ctor ce.ce_imm_alloca src dst
    (type_slot_size tv) 0 sa = ((),sb) /\
  immutable_holds ce cx ty (Value v) aw es s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sa /\
  copy_old_operand sa src /\ copy_old_operand sa dst /\
  eval_operand src s = SOME aw /\ eval_operand dst s = SOME w /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w,type_memory_size tv) /\
  w2n w + type_memory_size tv < dimword (:256) /\
  (!name b len. local_region ce es.scopes s name b len ==>
    regions_disjoint (w2n w) (type_memory_size tv) b len) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    stmt_state_rel ctx func ce cx es u /\
    val_in_memory tv v (w2n w) u.vs_memory /\ val_wf tv v /\
    copy_static u = copy_static s /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (!q. copy_old_operand sa q ==> eval_operand q u = eval_operand q s) /\
    (!p k. regions_disjoint p k (w2n w) (type_memory_size tv) ==>
      mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `val_wf tv v /\ w2n aw + type_memory_size tv < dimword (:256)` by
    (drule_all immutable_holds_bounds >> simp[]) >>
  `val_in_memory tv v (w2n aw)
    (if ce.ce_is_ctor then s.vs_memory else s.vs_data_section)` by
    (Cases_on `ce.ce_is_ctor` >> fs[]
     >- metis_tac[exprSimCopyTheory.immutable_holds_memory] >>
     drule_all immutable_holds_data >> simp[read_result_def, return_def]) >>
  `(ce.ce_is_ctor ==> regions_disjoint (w2n aw) (type_memory_size tv)
       (w2n w) (type_memory_size tv))` by
    (strip_tac >> drule_all immutable_holds_alloca_disjoint >> simp[]) >>
  `!region. ce.ce_is_ctor /\ ce.ce_imm_alloca = SOME region ==>
    eval_operand region s = SOME 0w /\ copy_old_operand sa region` by
    (gen_tac >> strip_tac >> conj_tac
     >- fs[stmt_state_rel_def, immutable_base_zero_def] >>
     fs[copy_old_operand_def] >> rpt strip_tac >>
     metis_tac[local_ptrs_reserved_imm_base]) >>
  drule (SRULE [] (Q.INST
    [`a` |-> `w2n (aw:bytes32)`, `b` |-> `w2n (w:bytes32)`, `off` |-> `0`]
    (SPEC_ALL optional_immutable_copy_landing))) >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (qspecl_then [`w`, `ctx`] mp_tac) >>
  (impl_tac >- fs[type_memory_size_slots]) >> strip_tac >>
  `stmt_state_rel ctx func ce cx es u` by
    (irule copy_buffer_state_rel_frame >>
     qexistsl_tac [`w2n w`, `inst`, `s`, `sa`, `type_memory_size tv`] >>
     fs[type_memory_size_slots, regions_disjoint_def] >> metis_tac[]) >>
  qexists_tac `u` >> fs[type_memory_size_slots]
QED

Theorem immutable_value_alloc_window_landing:
  compile_alloc_buffer (type_memory_size tv) sa = (buf,sm) /\
  compile_imm_copy_to_memory ce.ce_is_ctor ce.ce_imm_alloca src buf.buf_operand
    (type_slot_size tv) 0 sm = ((),sb) /\
  immutable_holds ce cx ty (Value v) aw es s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  fn_inst_ids_distinct func /\ stmt_state_rel ctx func ce cx es s /\
  local_ptrs_reserved ce sa /\ type_memory_size tv < dimword (:256) /\
  allocas_above lo s /\ copy_old_operand sa src /\ eval_operand src s = SOME aw /\
  (!q x. reserved q /\ q = Var x ==> not_fresh_at sa x) /\
  (!p k. P p k ==> p+k <= lo) /\
  (!p k. Win p k ==> ?aid b len. aid < sa.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (b,len) /\ b <= p /\ p+k <= b+len) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u w. gas_marked_path F ctx func s 0 (OK u) /\
    stmt_state_rel ctx func ce cx es u /\
    eval_operand buf.buf_operand u = SOME w /\ val_wf tv v /\
    val_in_memory tv v (w2n w) u.vs_memory /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,type_memory_size tv) /\
    lo <= w2n w /\ w2n w+type_memory_size tv < dimword (:256) /\
    allocas_above lo u /\ s.vs_alloca_next <= u.vs_alloca_next /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!p k. P p k ==> mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!p k. Win p k ==> mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!q. reserved q ==> eval_operand q u = eval_operand q s) /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (!name b len. local_region ce es.scopes s name b len ==>
      regions_disjoint (w2n w) (type_memory_size tv) b len) /\
    (!p k. regions_disjoint p k (w2n w) (type_memory_size tv) ==>
      mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  mp_tac (Q.INST [`sz` |-> `type_memory_size tv`,
    `reserved` |-> `\q. reserved q \/ q = src`]
    (SPEC_ALL bodyIntCallWindowLandingTheory.materialization_alloc_window_landing)) >>
  (impl_tac >- (simp[] >> fs[copy_old_operand_def] >> metis_tac[])) >> strip_tac >>
  rename1 `gas_marked_path F ctx func s 0 (OK mid)` >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (drule loweringHaltTheory.compile_alloc_buffer_parts >> simp[]) >>
  `local_ptrs_reserved ce sm` by (irule local_ptrs_reserved_next_var >> metis_tac[]) >>
  `copy_old_operand sm src /\ copy_old_operand sm buf.buf_operand` by
    (fs[copy_old_operand_def] >> rpt strip_tac >>
     gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `immutable_holds ce cx ty (Value v) aw es mid /\ eval_operand src mid = SOME aw` by
    (conj_tac >- (drule immutable_holds_memory_cong >> simp[]) >> metis_tac[]) >>
  drule_all buffer_alloc_code >> strip_tac >>
  `?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
     FLOOKUP mid.vs_allocas inst.inst_id = SOME (w2n w,type_memory_size tv)` by
    (qexists_tac `mk_inst sa.cs_next_id ALLOCA [Lit (n2w (type_memory_size tv))]
       [STRING #"%" (toString sa.cs_next_var)]` >> fs[mk_inst_def]) >>
  drule_all immutable_value_copy_landing >> strip_tac >>
  drule copy_static_fields >> strip_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `!q. reserved q ==> eval_operand q u = eval_operand q s` by
    (rpt strip_tac >> `copy_old_operand sm q` by
      (fs[copy_old_operand_def] >> metis_tac[]) >> metis_tac[]) >>
  `!p k. P p k ==> regions_disjoint p k (w2n w) (type_memory_size tv)` by
    (rpt strip_tac >> qpat_x_assum `!p k. P p k ==> _` drule >>
     simp[regions_disjoint_def]) >>
  `gas_marked_path F ctx func s 0 (OK u)` by
    (drule_all gas_marked_path_then >> simp[]) >>
  qexistsl_tac [`u`, `w`] >> fs[allocas_above_def] >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >>
  `local_region ce es.scopes mid name b len` by
    (mp_tac (Q.INST [`st` |-> `sa`, `t` |-> `mid`, `cenv` |-> `ce`,
       `scopes` |-> `es.scopes`, `sz` |-> `len`]
       (SPEC_ALL copy_buffer_local_region_frame)) >> simp[]) >>
  metis_tac[]
QED

Theorem protected_code_value_window_forcing:
  unwrap_value ce (LocatedValue ty p) sa = (op,sb) /\ p.ptr_location = LocCode /\
  vv_holds ce cx ty (Value v) (LocatedValue ty p) es s /\
  ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  type_memory_bytes ce ty = type_memory_size tv /\ type_memory_size tv < 2**64 /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sa /\
  allocas_above lo s /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sa x) /\
  (!q x. reserved q /\ q = Var x ==> not_fresh_at sa x) /\
  (!p k. P p k ==> p+k <= lo) /\
  (!p k. Win p k ==> ?aid b len. aid < sa.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (b,len) /\ b <= p /\ p+k <= b+len) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u w. gas_marked_path F ctx func s 0 (OK u) /\
    expr_val_rel cx ty v op u /\ stmt_state_rel ctx func ce cx es u /\
    eval_operand op u = SOME w /\ val_wf tv v /\
    val_in_memory tv v (w2n w) u.vs_memory /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,type_memory_size tv) /\
    lo <= w2n w /\ w2n w + type_memory_size tv < dimword (:256) /\
    allocas_above lo u /\ s.vs_alloca_next <= u.vs_alloca_next /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!p k. P p k ==> mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!p k. Win p k ==> mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!q. reserved q ==> eval_operand q u = eval_operand q s) /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (!name b sz. local_region ce scopes u name b sz <=> local_region ce scopes s name b sz) /\
    (!name b sz. local_region ce es.scopes s name b sz ==>
      regions_disjoint (w2n w) (type_memory_size tv) b sz) /\
    locals_kept ce es s u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `?aw. eval_operand p.ptr_operand s = SOME aw /\
    immutable_holds ce cx ty (Value v) aw es s` by
    (Cases_on `p.ptr_location` >> gvs[vv_holds_def]) >>
  `?buf sm. compile_alloc_buffer (type_memory_size tv) sa = (buf,sm) /\
    compile_imm_copy_to_memory ce.ce_is_ctor ce.ce_imm_alloca p.ptr_operand
      buf.buf_operand (type_slot_size tv) 0 sm = ((),sb) /\ op = buf.buf_operand` by
    (fs[unwrap_value_def, compile_ensure_in_memory_def, slot_count_of_memory_size,
        comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     pairarg_tac >> fs[] >> pairarg_tac >> fs[]) >>
  `cs_extends sa sm` by metis_tac[compile_alloc_buffer_extends] >>
  `same_blocks sm sb /\ ?code. sb.cs_current_insts = sm.cs_current_insts ++ code` by
    (Cases_on `ce.ce_is_ctor` >> fs[] >>
     metis_tac[code_ctor_copy_insts, code_copy_insts]) >>
  `cs_extends sm sb` by
    (fs[same_blocks_def, cs_extends_def] >> qexists_tac `[]` >> simp[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_split] >>
  `type_memory_size tv < dimword (:256)` by (fs[dimword_def] >> decide_tac) >>
  `copy_old_operand sa p.ptr_operand` by fs[copy_old_operand_def] >>
  mp_tac (Q.INST [`src` |-> `p.ptr_operand`]
    (SPEC_ALL immutable_value_alloc_window_landing)) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `!name b sz. local_region ce scopes u name b sz <=> local_region ce scopes s name b sz` by
    (irule copy_buffer_local_region_frame >> qexists_tac `sa` >> simp[]) >>
  `locals_kept ce es s u` by
    (rw[locals_kept_def] >>
     `regions_disjoint off len (w2n w) (type_memory_size tv)` by
       (qpat_x_assum `!name b len. local_region _ _ _ _ _ _ ==> _` drule >>
        simp[regions_disjoint_def] >> decide_tac) >> metis_tac[]) >>
  qexistsl_tac [`u`, `w`] >> simp[expr_val_rel_def] >> gvs[]
QED
