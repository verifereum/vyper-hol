(* Storage materialization at a fresh-free allocation endpoint. *)
Theory bodyIntCallWindowStorage
Ancestors
  bodyIntCallWindowLanding bodyIntCallStorageLanding bodyIntCallWindowCode
  exprSimCopy exprSimStorageCopy valueCopy valueEncoding valueEncodingProps
  compileEnv loweringStateRelDefs context venomState words finite_map intCallFrame fragGasMode
  loweringHalt venomInst exprLoweringProps emitHelperProps loweringPosts exprSimAlloc
  exprLowering exprSimFieldLayout fragExec bodyIntCallForcingReadOnly exprSimProps

Theorem storage_value_copy_landing:
  (loc = LocStorage \/ loc = LocTransient) /\
  (if n = 1 then
     do value <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
        emit_void MSTORE [dst; value] od
   else do compile_word_copy_loop src dst n loc LocMemory F; return () od)
    sa = (result,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved ce sa /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME (n2w b) /\
  n = type_slot_size tv /\ n < 2**256 /\ b+sz < 2**256 /\ 32*n <= sz /\
  stmt_state_rel ctx func ce cx es s /\
  storage_holds cx (loc = LocTransient) ty (Value v) a es s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\ allocas_above lo s /\
  (!name lb len. local_region ce es.scopes s name lb len ==>
    regions_disjoint b sz lb len) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    stmt_state_rel ctx func ce cx es u /\
    val_wf tv v /\ val_in_memory tv v b u.vs_memory /\
    val_footprint tv v <= type_memory_size tv /\
    copy_static u = copy_static s /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (!q. copy_old_operand sa q ==> eval_operand q u = eval_operand q s) /\
    (!p k. regions_disjoint p k b sz ==>
      mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `b+32*n < 2**256` by decide_tac >>
  mp_tac (Q.INST [`aid` |-> `inst.inst_id`,
    `P` |-> `\p k. regions_disjoint p k b sz`,
    `reserved` |-> `copy_old_operand sa`]
    (SPEC_ALL protected_storage_suffix_landing)) >>
  (impl_tac >- (simp[copy_old_operand_def, regions_disjoint_def] >>
     rpt strip_tac >> fs[] >> decide_tac)) >> strip_tac >>
  `stmt_state_rel ctx func ce cx es u` by
    (irule copy_buffer_state_rel_frame >>
     qexistsl_tac [`b`, `inst`, `s`, `sa`, `sz`] >> simp[] >>
     fs[regions_disjoint_def] >> metis_tac[]) >>
  qexists_tac `u` >> simp[]
QED

Theorem storage_alloc_window_landing:
  compile_alloc_buffer sz sa = (buf,sm) /\
  (if n = 1 then
     do value <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
        emit_void MSTORE [buf.buf_operand; value] od
   else do compile_word_copy_loop src buf.buf_operand n loc LocMemory F; return () od)
    sm = (result,sb) /\
  (loc = LocStorage \/ loc = LocTransient) /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  sz < dimword (:256) /\ 32*n <= sz /\ n = type_slot_size tv /\ n < 2**256 /\
  allocas_above lo s /\ copy_old_operand sa src /\ eval_operand src s = SOME a /\
  storage_holds cx (loc = LocTransient) ty (Value v) a es s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
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
    val_footprint tv v <= type_memory_size tv /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
    lo <= w2n w /\ w2n w+sz < dimword (:256) /\ allocas_above lo u /\
    s.vs_alloca_next <= u.vs_alloca_next /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!p k. P p k ==> mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!p k. Win p k ==> mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!q. reserved q ==> eval_operand q u = eval_operand q s) /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (!name b len. local_region ce es.scopes s name b len ==>
      regions_disjoint (w2n w) sz b len) /\
    (!p k. regions_disjoint p k (w2n w) sz ==>
      mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`reserved` |-> `\q. reserved q \/ q = src`]
    (SPEC_ALL bodyIntCallWindowLandingTheory.materialization_alloc_window_landing)) >>
  (impl_tac >- (simp[] >> fs[copy_old_operand_def] >> metis_tac[])) >> strip_tac >>
  rename1 `gas_marked_path F ctx func s 0 (OK mid)` >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (drule loweringHaltTheory.compile_alloc_buffer_parts >> simp[]) >>
  `local_ptrs_reserved ce sm` by (irule local_ptrs_reserved_next_var >> metis_tac[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `!x. src = Var x \/ buf.buf_operand = Var x ==> not_fresh_at sm x` by
    (rpt strip_tac >> fs[copy_old_operand_def] >> metis_tac[]) >>
  `storage_holds cx (loc = LocTransient) ty (Value v) a es mid` by
    gvs[storage_holds_def, contract_storage_def, contract_transient_def] >>
  `eval_operand src mid = SOME a /\
   eval_operand buf.buf_operand mid = SOME (n2w (w2n w))` by simp[] >>
  drule_all buffer_alloc_code >> strip_tac >>
  `?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
     FLOOKUP mid.vs_allocas inst.inst_id = SOME (w2n w,sz)` by
    (qexists_tac `mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
       [STRING #"%" (toString sa.cs_next_var)]` >> fs[mk_inst_def]) >>
  `w2n w + sz < 2**256` by fs[dimword_def] >>
  drule_all storage_value_copy_landing >> strip_tac >>
  drule copy_static_fields >> strip_tac >>
  `!q. reserved q ==> eval_operand q u = eval_operand q s` by
    (rpt strip_tac >> `copy_old_operand sm q` by
      (fs[copy_old_operand_def] >> metis_tac[]) >> metis_tac[]) >>
  `!p k. P p k ==> regions_disjoint p k (w2n w) sz` by
    (rpt strip_tac >> qpat_x_assum `!p k. P p k ==> _` drule >>
     simp[regions_disjoint_def]) >>
  `gas_marked_path F ctx func s 0 (OK u)` by
    (drule_all gas_marked_path_then >> simp[]) >>
  `eval_operand buf.buf_operand u = SOME w` by
    (qpat_x_assum `!q. copy_old_operand sm q ==> _`
      (qspec_then `buf.buf_operand` mp_tac) >> gvs[copy_old_operand_def]) >>
  qexistsl_tac [`u`, `w`] >> gnvs[allocas_above_def] >>
  conj_tac >- metis_tac[] >> rpt strip_tac >>
  `local_region ce es.scopes mid name b len` by
    (mp_tac (Q.INST [`st` |-> `sa`, `t` |-> `mid`, `cenv` |-> `ce`,
       `scopes` |-> `es.scopes`, `sz` |-> `len`]
       (SPEC_ALL copy_buffer_local_region_frame)) >> simp[]) >> metis_tac[]
QED

Theorem protected_storage_value_window_forcing:
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
    u.vs_inst_idx = LENGTH sb.cs_current_insts
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
  `locals_kept ce es s u` by
    (rw[locals_kept_def] >>
     `regions_disjoint off len (w2n w) (type_memory_size tv)` by
       (qpat_x_assum `!name b len. local_region _ _ _ _ _ _ ==> _` drule >>
        simp[regions_disjoint_def] >> decide_tac) >> metis_tac[]) >>
  qexistsl_tac [`u`, `w`] >> simp[expr_val_rel_def] >> gvs[]
QED

Theorem protected_word_value_frame_forcing:
  unwrap_value ce (LocatedValue ann p) sa = (op,sb) /\
  vv_holds ce cx ty (Value v) (LocatedValue ann p) es s /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME stv /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sa /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!q x. reserved q /\ q = Var x ==> not_fresh_at sa x) ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    expr_val_rel cx ty v op u /\ stmt_state_rel ctx func ce cx es u /\
    u = s with <|vs_vars := u.vs_vars; vs_inst_idx := LENGTH sb.cs_current_insts|> /\
    (!q. reserved q ==> eval_operand q u = eval_operand q s) /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (!name b sz. local_region ce scopes u name b sz <=> local_region ce scopes s name b sz) /\
    locals_kept ce es s u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  mp_tac (Q.INST
    [`reserved` |-> `\q. reserved q \/ ?x. q = Var x /\ not_fresh_at sa x`]
    (SPEC_ALL protected_word_value_forcing)) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s` by
    (rpt strip_tac >> qpat_x_assum `!q. _ ==> eval_operand q u = _`
      (qspec_then `Var x` mp_tac) >> simp[eval_operand_def]) >>
  `u.vs_memory = s.vs_memory` by
    (qpat_x_assum `u = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `locals_kept ce es s u` by (irule locals_kept_mem >> simp[]) >>
  qexists_tac `u` >> simp[]
QED
