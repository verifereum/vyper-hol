(* Typed normalization interfaces for conditional-arm memory consumers. *)
Theory bodyIfExpTypedMemory
Ancestors
  typedNormalizeEntryBoundary typedStoreEndpoint typedStorePathsMem exprSimMemUnwrap
  externalNormalizePremises externalReturnNormalizeRun exprSimIfExp
  context compileEnv venomExecSemantics venomInst emitHelper fragExec
  fragGasMemoryLength exprSimCopy ifExpPhysicalSourceAllocation
  bodyIfExpNormalizationSuffix exprSimTypedAlloc freshWrites
  exprLoweringProps

(* Recover the semantic frame at the same operational endpoint as the copy. *)
Theorem ifexp_normalization_state_rel[local]:
  gas_path_mem ctx func s n (OK t) /\
  (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
    vs_current_bb := bb; vs_inst_idx := k; vs_prev_bb := prev|>) = s /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sa /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
  (!name lb len. local_region ce es.scopes s name lb len ==>
    b + sz <= lb \/ lb + len <= b) /\
  (!off len. off + len <= b \/ b + sz <= off ==>
    mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory) ==>
  stmt_state_rel ctx func ce cx es t
Proof
  strip_tac >>
  `copy_static t = copy_static s` by
    (qpat_x_assum `_ = s` mp_tac >>
     simp[venomStateTheory.venom_state_component_equality,
          exprSimStorageCopyTheory.copy_static_def]) >>
  drule gas_path_mem_memory_length >> strip_tac >>
  irule copy_buffer_state_rel_frame >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  qexists_tac `sa` >> simp[arithmeticTheory.ADD_COMM] >> gvs[]
QED

(* Safe allocation and physical typed normalization, retaining the expression
   frame needed by destination-indexed post reconstruction. *)
Theorem ifexp_typed_allocate_path_mem[local]:
  compile_alloc_buffer (type_memory_size dtv) sa = (buf,sm) /\
  compile_store_memory_typed ce buf.buf_operand dty src sty sm = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  type_widens_to (get_tenv cx) sty dty /\
  ~is_word_type sty /\ ~is_bytestring_type sty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  0 < type_memory_size stv /\ type_memory_size dtv < dimword (:256) /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  (emitted_blocks sm sb <> [] ==>
    ?bb. lookup_block sb.cs_current_bb func.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0) /\
  stmt_state_rel ctx func ce cx es s /\
  expr_val_at ce cx sty origin sa es v src s /\
  eval_operand src s = SOME sw /\
  w2n sw + type_memory_size stv <= s.vs_alloca_next /\
  val_in_memory stv v (w2n sw) s.vs_memory /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?ngas t w. gas_path_mem ctx func s ngas (OK t) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    stmt_state_rel ctx func ce cx es t /\
    eval_operand buf.buf_operand t = SOME w /\
    val_in_memory dtv v (w2n w) t.vs_memory /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,type_memory_size dtv) /\
    w2n w + type_memory_size dtv <= t.vs_alloca_next /\
    sa.cs_next_id < sb.cs_next_id /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!off len. off + len <= w2n w \/ w2n w + type_memory_size dtv <= off ==>
      mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory) /\
    (!aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
      regions_disjoint (w2n w) (type_memory_size dtv) b len) /\
    (!name b len. local_region ce es.scopes s name b len ==>
      regions_disjoint (w2n w) (type_memory_size dtv) b len)
Proof
  strip_tac >>
  `ci_mono sa sm /\ ci_mono sm sb` by
    (conj_tac
     >- (qspecl_then [`type_memory_size dtv`, `sa`] mp_tac
           ci_mono_compile_alloc_buffer >> simp[]) >>
     drule typed_return_store_mono >> simp[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split]) >>
  drule_all ifexp_allocate_physical_source >> strip_tac >>
  `local_ptrs_reserved ce sm /\
   (!x. buf.buf_operand = Var x \/ src = Var x ==> not_fresh_at sm x)` by
    (fs[ci_mono_def] >> metis_tac[local_ptrs_reserved_next_var, not_fresh_at_mono]) >>
  drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`) typed_store_path_mem >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
  disch_then (qspecl_then [`get_tenv cx`, `func`, `dtv`, `ctx`] mp_tac) >>
  (impl_tac >- (simp[] >> fs[regions_disjoint_def, DISJ_COMM] >> metis_tac[])) >>
  strip_tac >>
  suspend "frame"
QED
Resume ifexp_typed_allocate_path_mem[frame]:
  drule typedStoreAllocationFrameTheory.typed_store_frame_allocations >> strip_tac >>
  drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  `stmt_state_rel ctx func ce cx es t` by
    (irule ifexp_normalization_state_rel >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`w2n w`, `sm.cs_current_bb`,
       `LENGTH sm.cs_current_insts`, `u.vs_prev_bb`, `type_memory_size dtv`] >>
     simp[mk_inst_def] >>
     conj_tac >- (fs[regions_disjoint_def] >> metis_tac[]) >>
     conj_tac >- (gvs[] >> rpt strip_tac >> first_x_assum irule >> decide_tac) >>
     gvs[]) >>
  suspend "finish"
QED
Resume ifexp_typed_allocate_path_mem[finish]:
  `gas_path_mem ctx func s ngas (OK t)` by
    metis_tac[fragGasPathMemTheory.gas_path_mem_then, arithmeticTheory.ADD] >>
  `sa.cs_next_id < sb.cs_next_id /\ sa.cs_next_var <= sm.cs_next_var` by
    (fs[ci_mono_def] >> decide_tac) >>
  `eval_operand buf.buf_operand t = SOME w` by
    (gvs[venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  `!name b len. local_region ce es.scopes s name b len ==>
    regions_disjoint (w2n w) (type_memory_size dtv) b len` by
    (qspecl_then [`ce`, `sa`, `s`, `u`] mp_tac copy_buffer_local_region_frame >>
     simp[] >> metis_tac[]) >>
  qexistsl_tac [`ngas`, `t`, `w`] >> simp[] >>
  conj_tac >- (rpt strip_tac >>
    `not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >> metis_tac[]) >>
  conj_tac >- (gvs[] >> rpt strip_tac >>
    qpat_x_assum `!p k. _ ==> mem_bytes_at _ _ _ = _` irule >> decide_tac) >>
  rpt strip_tac >>
  qpat_x_assum `!aid b len. _ /\ _ ==> regions_disjoint _ _ _ _`
    (qspecl_then [`aid`, `b`, `len`] mp_tac) >> simp[] >> metis_tac[]
QED
Finalise ifexp_typed_allocate_path_mem[local]
