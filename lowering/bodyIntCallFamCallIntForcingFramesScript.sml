(* Same-endpoint byte frames retained from the materialization landings. *)
Theory bodyIntCallFamCallIntForcingFrames
Ancestors
  bodyIntCallWindowCode bodyIntCallWindowStorage bodyIntCallWindowLanding
  bodyIntCallWindowCopy bodyIntCallForcingCode bodyIntCallForcingCodeRun
  exprSimCopy exprSimStorageCopy immutableCopyExecution
  immutableConstructorRelation valueEncodingProps valueEncoding valueCopy
  venomExecSemantics context intCallFrame fragGasMode entrySinkExtraction
  abiDecoderArrayInitExec stmtReasonMemory finite_map list rich_list words
  placeMemoryStaging venomState compileEnv fragExec emitHelperProps
  exprLoweringProps venomInst instIdxIndep placeMemoryPrimitiveForward
  vyperInterpreter vyperState loweringHalt exprSimAlloc bodyIntCallLiteralLanding
  exprSimProps loweringPosts exprLowering exprSimFieldLayout

Theorem intcall_code_forcing_frames:
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
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!p k. regions_disjoint p k (w2n w) (type_memory_size tv) ==>
      mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!name b sz. local_region ce es.scopes s name b sz ==>
      mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz s.vs_memory)
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
  `!name b sz. local_region ce es.scopes s name b sz ==>
     mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz s.vs_memory` by
    (rpt strip_tac >>
     `regions_disjoint b sz (w2n w) (type_memory_size tv)` by
       (qpat_x_assum `!name b len. local_region _ _ _ _ _ _ ==> regions_disjoint _ _ _ _` drule >>
        simp[regions_disjoint_def] >> decide_tac) >> metis_tac[]) >>
  `locals_kept ce es s u` by
    (rw[locals_kept_def] >>
     `regions_disjoint off len (w2n w) (type_memory_size tv)` by
       (qpat_x_assum `!name b len. local_region _ _ _ _ _ _ ==> regions_disjoint _ _ _ _` drule >>
        simp[regions_disjoint_def] >> decide_tac) >> metis_tac[]) >>
  qexistsl_tac [`u`, `w`] >> simp[expr_val_rel_def] >> gvs[] >> metis_tac[]
QED

Theorem intcall_storage_forcing_frames:
  unwrap_value ce (LocatedValue ty p) sa = (op,sb) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
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
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!p k. regions_disjoint p k (w2n w) (type_memory_size tv) ==>
      mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!name b sz. local_region ce es.scopes s name b sz ==>
      mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz s.vs_memory)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?a. eval_operand p.ptr_operand s = SOME a /\
    storage_holds cx (p.ptr_location = LocTransient) ty (Value v) a es s` by
    (Cases_on `p.ptr_location` >> fs[vv_holds_def]) >>
  `?buf sm result.
    compile_alloc_buffer (type_memory_size tv) sa = (buf,sm) /\
    (if type_slot_size tv = 1 then
       do value <- emit_op (if p.ptr_location = LocStorage then SLOAD else TLOAD) [p.ptr_operand];
          emit_void MSTORE [buf.buf_operand; value] od
     else do compile_word_copy_loop p.ptr_operand buf.buf_operand (type_slot_size tv)
               p.ptr_location LocMemory F; return () od) sm = (result,sb) /\
    op = buf.buf_operand` by
    (drule ensure_storage_memory_layout >>
     disch_then (qspecl_then [`p.ptr_operand`, `type_memory_size tv`, `type_slot_size tv`,
       `ce.ce_is_ctor`, `ce.ce_imm_alloca`] assume_tac) >>
     fs[unwrap_value_def, slot_count_of_memory_size, comp_bind_def,
        comp_ignore_bind_def, comp_return_def] >> fs[comp_bind_def,
          comp_ignore_bind_def, comp_return_def] >>
     pairarg_tac >> fs[] >> pairarg_tac >> fs[] >> metis_tac[]) >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    metis_tac[compile_alloc_buffer_extends, storage_copy_suffix_extends] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by metis_tac[fn_has_code_split] >>
  `type_slot_size tv < 2**256 /\ type_memory_size tv < dimword (:256)` by
    (fs[type_memory_size_slots, dimword_def] >> decide_tac) >>
  `copy_old_operand sa p.ptr_operand` by fs[copy_old_operand_def] >>
  mp_tac (Q.INST [`sz` |-> `type_memory_size tv`, `n` |-> `type_slot_size tv`,
    `src` |-> `p.ptr_operand`, `loc` |-> `p.ptr_location`]
    (SPEC_ALL storage_alloc_window_landing)) >>
  (impl_tac >- simp[type_memory_size_slots]) >> strip_tac >>
  `!name b sz. local_region ce scopes u name b sz <=> local_region ce scopes s name b sz` by
    (irule copy_buffer_local_region_frame >> qexists_tac `sa` >> simp[]) >>
  `!name b sz. local_region ce es.scopes s name b sz ==>
     mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz s.vs_memory` by
    (rpt strip_tac >>
     `regions_disjoint b sz (w2n w) (type_memory_size tv)` by
       (qpat_x_assum `!name b len. local_region _ _ _ _ _ _ ==> regions_disjoint _ _ _ _` drule >>
        simp[regions_disjoint_def] >> decide_tac) >> metis_tac[]) >>
  `locals_kept ce es s u` by
    (rw[locals_kept_def] >>
     `regions_disjoint off len (w2n w) (type_memory_size tv)` by
       (qpat_x_assum `!name b len. local_region _ _ _ _ _ _ ==> regions_disjoint _ _ _ _` drule >>
        simp[regions_disjoint_def] >> decide_tac) >> metis_tac[]) >>
  qexistsl_tac [`u`, `w`] >> simp[expr_val_rel_def] >> gvs[] >> metis_tac[]
QED
