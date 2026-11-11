(* Earlier-site windows are disjoint from the materialization destination. *)
Theory bodyIntCallAllocatedForcing
Ancestors
  bodyIntCallMaterializeLanding bodyIntCallForcingCode bodyIntCallStorageLanding
  bodyIntCallLiteralLanding exprSimPrecompiles exprLoweringProps compileEnv loweringStateRelDefs
  exprSimStorageCopy context venomState words finite_map intCallFrame
  fragGasMode exprSimCopy exprSimProps exprSimAlloc venomInst loweringPosts
  exprLowering exprSimFieldLayout emitHelperProps loweringHalt fragExec valueEncoding valueEncodingProps
  bodyIntCallForcingReadOnly exprSimAggregateChildren valueCopyBytes
Libs
  pairLib

Theorem earlier_allocated_window_disjoint:
  stmt_state_rel ctx func ce cx es u /\
  FLOOKUP u.vs_allocas site = SOME (dst,sz) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP u.vs_allocas aid = SOME entry) /\
  (!p k. Win p k ==> ?aid b len. aid < site /\
    FLOOKUP s.vs_allocas aid = SOME (b,len) /\ b <= p /\ p+k <= b+len) ==>
  !p k. Win p k ==> regions_disjoint p k dst sz
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  `FLOOKUP u.vs_allocas aid = SOME (b,len)` by metis_tac[] >>
  `aid <> site` by decide_tac >>
  `regions_disjoint b len dst sz` by
    (irule state_allocations_disjoint >> metis_tac[]) >>
  fs[regions_disjoint_def] >> decide_tac
QED

Theorem materialization_alloc_window_landing:
  compile_alloc_buffer sz sa = (buf,sm) /\
  fn_has_code sa sm func /\ stmt_state_rel ctx func ce cx es s /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\ fresh_vars_wrt sa s /\
  sz < dimword (:256) /\ allocas_above lo s /\
  (!q x. reserved q /\ q = Var x ==> not_fresh_at sa x) /\
  (!p k. Win p k ==> ?aid b len. aid < sa.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (b,len) /\ b <= p /\ p+k <= b+len) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u w. gas_marked_path F ctx func s 0 (OK u) /\
    stmt_state_rel ctx func ce cx es u /\
    eval_operand buf.buf_operand u = SOME w /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
    lo <= w2n w /\ w2n w + sz < dimword (:256) /\
    allocas_above lo u /\ u.vs_memory = s.vs_memory /\
    u.vs_data_section = s.vs_data_section /\ u.vs_immutables = s.vs_immutables /\
    u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
    u.vs_call_ctx = s.vs_call_ctx /\
    s.vs_alloca_next <= u.vs_alloca_next /\ fresh_vars_wrt sm u /\
    (!q. reserved q ==> eval_operand q u = eval_operand q s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!name b len. local_region ce es.scopes u name b len ==>
       regions_disjoint (w2n w) sz b len) /\
    (!p k. Win p k ==> regions_disjoint p k (w2n w) sz) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sm p) /\
    ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
    u.vs_inst_idx = LENGTH sm.cs_current_insts
Proof
  strip_tac >> drule_all materialization_alloc_landing >> strip_tac >>
  `!p k. Win p k ==> regions_disjoint p k (w2n w) sz` by
    (mp_tac (Q.INST [`u` |-> `u`, `s` |-> `s`,
       `site` |-> `sa.cs_next_id`, `dst` |-> `w2n (w:bytes32)`]
       (SPEC_ALL earlier_allocated_window_disjoint)) >> simp[]) >>
  qexistsl_tac [`u`, `w`] >> simp[] >> metis_tac[]
QED

Theorem immutable_value_alloc_window_landing:
  compile_alloc_buffer (type_memory_size tv) sa = (buf,sm) /\
  compile_imm_copy_to_memory ce.ce_is_ctor ce.ce_imm_alloca src buf.buf_operand
    (type_slot_size tv) 0 sm = ((),sb) /\
  immutable_holds ce cx ty (Value v) aw es s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  fn_inst_ids_distinct func /\ stmt_state_rel ctx func ce cx es s /\
  local_ptrs_reserved ce sa /\ fresh_vars_wrt sa s /\
  type_memory_size tv < dimword (:256) /\ allocas_above lo s /\
  copy_old_operand sa src /\ eval_operand src s = SOME aw /\
  (!q x. reserved q /\ q = Var x ==> not_fresh_at sa x) /\
  (!p k. P p k ==> p+k <= lo) /\
  (!p k. Win p k ==> ?aid b len. aid < sa.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (b,len) /\ b <= p /\ p+k <= b+len) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u w. gas_marked_path F ctx func s 0 (OK u) /\
    stmt_state_rel ctx func ce cx es u /\
    eval_operand buf.buf_operand u = SOME w /\
    val_in_memory tv v (w2n w) u.vs_memory /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,type_memory_size tv) /\
    lo <= w2n w /\ w2n w+type_memory_size tv < dimword (:256) /\
    allocas_above lo u /\ s.vs_alloca_next <= u.vs_alloca_next /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!p k. P p k ==> mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!p k. Win p k ==> mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!q. reserved q ==> eval_operand q u = eval_operand q s) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `!q x. (reserved q \/ q = src) /\ q = Var x ==> not_fresh_at sa x` by
    (fs[copy_old_operand_def] >> metis_tac[]) >>
  mp_tac (Q.INST [`sz` |-> `type_memory_size tv`,
    `reserved` |-> `\q. reserved q \/ q = src`]
    (SPEC_ALL materialization_alloc_window_landing)) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
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
  `gas_marked_path F ctx func s 0 (OK u)` by
    (drule_all gas_marked_path_then >> simp[]) >>
  `!q. reserved q ==> eval_operand q u = eval_operand q s` by
    (rpt strip_tac >>
     `copy_old_operand sm q` by
       (fs[copy_old_operand_def] >> rpt strip_tac >>
        gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
     metis_tac[]) >>
  `!p k. P p k ==> regions_disjoint p k (w2n w) (type_memory_size tv)` by
    (rpt strip_tac >> qpat_x_assum `!p k. P p k ==> _` drule >>
     simp[regions_disjoint_def]) >>
  qexistsl_tac [`u`, `w`] >> fs[allocas_above_def] >> metis_tac[]
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
  local_ptrs_reserved ce sa /\ fresh_vars_wrt sa s /\
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
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!q x. (reserved q \/ q = src) /\ q = Var x ==> not_fresh_at sa x` by
    (fs[copy_old_operand_def] >> metis_tac[]) >>
  mp_tac (Q.INST [`reserved` |-> `\q. reserved q \/ q = src`]
    (SPEC_ALL materialization_alloc_window_landing)) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  rename1 `gas_marked_path F ctx func s 0 (OK mid)` >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (drule loweringHaltTheory.compile_alloc_buffer_parts >> simp[]) >>
  `local_ptrs_reserved ce sm` by (irule local_ptrs_reserved_next_var >> metis_tac[]) >>
  `!x. src = Var x \/ buf.buf_operand = Var x ==> not_fresh_at sm x` by
    (rpt strip_tac >> fs[copy_old_operand_def] >>
     gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `storage_holds cx (loc = LocTransient) ty (Value v) a es mid` by
    gvs[storage_holds_def, contract_storage_def, contract_transient_def] >>
  `eval_operand src mid = SOME a /\
   eval_operand buf.buf_operand mid = SOME (n2w (w2n w)) /\
   w2n w+32*n < 2**256` by (fs[dimword_def] >> metis_tac[]) >>
  `!q x. (reserved q \/ q = buf.buf_operand) /\ q = Var x ==>
     not_fresh_at sm x` by
    (rpt strip_tac >> gvs[not_fresh_at_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  mp_tac (Q.INST [`s` |-> `mid`, `sa` |-> `sm`, `b` |-> `w2n (w:bytes32)`,
      `dst` |-> `buf.buf_operand`, `aid` |-> `sa.cs_next_id`,
      `P` |-> `\p k. regions_disjoint p k (w2n (w:bytes32)) (32*n)`,
      `reserved` |-> `\q. reserved q \/ q = buf.buf_operand`]
    (SPEC_ALL protected_storage_suffix_landing)) >>
  (impl_tac >- (simp[] >> gvs[] >> metis_tac[])) >> strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  `stmt_state_rel ctx func ce cx es u` by
    (irule copy_buffer_state_rel_frame >>
     qexistsl_tac [`w2n w`,
       `mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
          [STRING #"%" (toString sa.cs_next_var)]`, `mid`, `sm`, `sz`] >>
     simp[mk_inst_def] >> gvs[regions_disjoint_def] >>
     rpt strip_tac >>
     qpat_assum `!nm b len. local_region ce es.scopes mid nm b len ==> _`
       (qspecl_then [`name`, `lb`, `len`] mp_tac) >>
     simp[] >> decide_tac) >>
  `gas_marked_path F ctx func s 0 (OK u)` by
    (drule_all gas_marked_path_then >> simp[]) >>
  `!p k. P p k \/ Win p k ==> regions_disjoint p k (w2n w) (32*n)` by
    (rpt gen_tac >> strip_tac
     >- (qpat_x_assum `!p k. P p k ==> _` drule >>
         simp[regions_disjoint_def]) >>
     qpat_x_assum `!p k. Win p k ==> regions_disjoint _ _ _ _` drule >>
     simp[regions_disjoint_def] >> decide_tac) >>
  qexistsl_tac [`u`, `w`] >> simp[] >> metis_tac[]
QED

Theorem protected_code_value_window_forcing:
  unwrap_value ce (LocatedValue ty p) sa = (op,sb) /\ p.ptr_location = LocCode /\
  vv_holds ce cx ty (Value v) (LocatedValue ty p) es s /\
  ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  type_memory_bytes ce ty = type_memory_size tv /\ type_memory_size tv < 2**64 /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sa /\
  fresh_vars_wrt sa s /\ allocas_above lo s /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sa x) /\
  (!q x. reserved q /\ q = Var x ==> not_fresh_at sa x) /\
  (!p k. P p k ==> p+k <= lo) /\
  (!p k. Win p k ==> ?aid b len. aid < sa.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (b,len) /\ b <= p /\ p+k <= b+len) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u w. gas_marked_path F ctx func s 0 (OK u) /\
    expr_val_rel cx ty v op u /\ stmt_state_rel ctx func ce cx es u /\
    eval_operand op u = SOME w /\ val_in_memory tv v (w2n w) u.vs_memory /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,type_memory_size tv) /\
    lo <= w2n w /\ w2n w + type_memory_size tv < dimword (:256) /\
    allocas_above lo u /\ s.vs_alloca_next <= u.vs_alloca_next /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!p k. P p k ==> mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!p k. Win p k ==> mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!q. reserved q ==> eval_operand q u = eval_operand q s) /\
    (!name b sz. local_region ce scopes u name b sz <=> local_region ce scopes s name b sz) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `?aw. eval_operand p.ptr_operand s = SOME aw /\
    immutable_holds ce cx ty (Value v) aw es s` by (Cases_on `p.ptr_location` >> gvs[vv_holds_def]) >>
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
  `type_memory_size tv < dimword (:256)` by
    (fs[dimword_def] >> decide_tac) >>
  `copy_old_operand sa p.ptr_operand` by fs[copy_old_operand_def] >>
  mp_tac (Q.INST [`src` |-> `p.ptr_operand`,
    `reserved` |-> `\q. reserved q \/ ?x. q = Var x /\ not_fresh_at sa x`]
    (SPEC_ALL immutable_value_alloc_window_landing)) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  `!name b sz. local_region ce scopes u name b sz <=> local_region ce scopes s name b sz` by
    (irule local_region_reserved_operands >>
     qexists_tac `\q. reserved q \/ ?x. q = Var x /\ not_fresh_at sa x` >>
     simp[] >> fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  qexistsl_tac [`u`, `w`] >> simp[expr_val_rel_def]
QED

Theorem protected_storage_value_window_forcing:
  unwrap_value ce (LocatedValue ty p) sa = (op,sb) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  vv_holds ce cx ty (Value v) (LocatedValue ty p) es s /\
  ~is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  type_memory_bytes ce ty = type_memory_size tv /\ type_memory_size tv < 2**64 /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sa /\
  fresh_vars_wrt sa s /\ allocas_above lo s /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sa x) /\
  (!q x. reserved q /\ q = Var x ==> not_fresh_at sa x) /\
  (!p k. P p k ==> p+k <= lo) /\
  (!p k. Win p k ==> ?aid b len. aid < sa.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (b,len) /\ b <= p /\ p+k <= b+len) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u w. gas_marked_path F ctx func s 0 (OK u) /\
    expr_val_rel cx ty v op u /\ stmt_state_rel ctx func ce cx es u /\
    eval_operand op u = SOME w /\ val_in_memory tv v (w2n w) u.vs_memory /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,type_memory_size tv) /\
    lo <= w2n w /\ w2n w + type_memory_size tv < dimword (:256) /\
    allocas_above lo u /\ s.vs_alloca_next <= u.vs_alloca_next /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!p k. P p k ==> mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!p k. Win p k ==> mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!q. reserved q ==> eval_operand q u = eval_operand q s) /\
    (!name b sz. local_region ce scopes u name b sz <=> local_region ce scopes s name b sz) /\
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
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_split] >>
  `type_slot_size tv < 2**256 /\ type_memory_size tv < dimword (:256)` by
    (fs[type_memory_size_slots, dimword_def] >> decide_tac) >>
  `copy_old_operand sa p.ptr_operand` by fs[copy_old_operand_def] >>
  mp_tac (Q.INST [`sz` |-> `type_memory_size tv`, `n` |-> `type_slot_size tv`,
    `src` |-> `p.ptr_operand`, `loc` |-> `p.ptr_location`,
    `reserved` |-> `\q. reserved q \/ ?x. q = Var x /\ not_fresh_at sa x`]
    (SPEC_ALL storage_alloc_window_landing)) >>
  (impl_tac >- (simp[type_memory_size_slots] >> metis_tac[])) >> strip_tac >>
  `!name b sz. local_region ce scopes u name b sz <=> local_region ce scopes s name b sz` by
    (irule local_region_reserved_operands >>
     qexists_tac `\q. reserved q \/ ?x. q = Var x /\ not_fresh_at sa x` >>
     simp[] >> fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  qexistsl_tac [`u`, `w`] >> simp[expr_val_rel_def]
QED

Theorem protected_value_window_forcing:
  unwrap_value ce vv sa = (op,sb) /\ vv_holds ce cx ty r vv es s /\
  read_result cx r es = (INL v,es) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  type_memory_bytes ce ty = type_memory_size tv /\ type_memory_size tv < 2**64 /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sa /\
  fresh_vars_wrt sa s /\ allocas_above lo s /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\
  (!q x. reserved q /\ q = Var x ==> not_fresh_at sa x) /\
  (!p k. P p k ==> p+k <= lo) /\
  (!p k. Win p k ==> ?aid b len. aid < sa.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (b,len) /\ b <= p /\ p+k <= b+len) /\
  (~is_word_type ty /\ ~is_bytestring_type ty /\
    (case vv of StackValue _ _ => T | LocatedValue _ p => p.ptr_location = LocMemory) ==>
    ?w a k. eval_operand (vv_operand vv) s = SOME w /\
      a <= w2n w /\ w2n w + type_memory_size tv <= a+k /\ a+k < dimword (:256) /\
      (lo <= a \/ ?b z. staged b z /\ b <= a /\ a+k <= b+z)) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    expr_val_rel cx ty v op u /\ stmt_state_rel ctx func ce cx es u /\
    allocas_above lo u /\ s.vs_alloca_next <= u.vs_alloca_next /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!p k. P p k ==> mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!p k. Win p k ==> mem_bytes_at p k u.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!q. reserved q ==> eval_operand q u = eval_operand q s) /\
    (!name b sz. local_region ce scopes u name b sz <=> local_region ce scopes s name b sz) /\
    (~is_word_type ty /\ ~is_bytestring_type ty ==>
      ?w a k. eval_operand op u = SOME w /\ a <= w2n w /\
        w2n w + type_memory_size tv <= a+k /\ a+k < dimword (:256) /\
        (lo <= a \/ ?b z. staged b z /\ b <= a /\ a+k <= b+z)) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  drule_all vv_holds_materialise >> strip_tac >>
  Cases_on `vv`
  >- (drule (SRULE [] protected_identity_value_forcing) >>
      disch_then drule >> simp[] >> strip_tac >>
      qexists_tac `s` >> fs[] >> metis_tac[]) >>
  rename1 `LocatedValue ann p` >>
  Cases_on `is_word_type ty`
  >- (drule_all protected_word_value_forcing >>
      disch_then (qspec_then `scopes` strip_assume_tac) >>
      `u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
       u.vs_alloca_next = s.vs_alloca_next` by
        (rpt conj_tac >> qpat_assum `u = _` (fn th => simp[Once th])) >>
      qexists_tac `u` >> fs[allocas_above_def] >> metis_tac[]) >>
  Cases_on `p.ptr_location = LocMemory`
  >- (drule protected_identity_value_forcing >> disch_then drule >>
      simp[] >> strip_tac >> qexists_tac `s` >> fs[] >> metis_tac[]) >>
  `ann = ty` by fs[vv_holds_def] >> gvs[] >>
  `p.ptr_location <> LocCalldata` by
    (Cases_on `p.ptr_location` >> fs[vv_holds_def]) >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sa x` by fs[vv_operand_def] >>
  Cases_on `p.ptr_location = LocCode`
  >- (mp_tac (Q.INST [`reserved` |-> `reserved`, `Win` |-> `Win`, `P` |-> `P`,
          `scopes` |-> `scopes`, `tv` |-> `tv`, `ty` |-> `ann`]
          (SPEC_ALL protected_code_value_window_forcing)) >>
      (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
      qexists_tac `u` >> simp[] >> rpt strip_tac >>
      qexistsl_tac [`w2n w`, `type_memory_size tv`] >> simp[]) >>
  `(p.ptr_location = LocStorage \/ p.ptr_location = LocTransient)` by
    (Cases_on `p.ptr_location` >> fs[]) >>
  mp_tac (Q.INST [`reserved` |-> `reserved`, `Win` |-> `Win`, `P` |-> `P`,
      `scopes` |-> `scopes`, `tv` |-> `tv`, `ty` |-> `ann`]
      (SPEC_ALL protected_storage_value_window_forcing)) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  qexists_tac `u` >> simp[] >> rpt strip_tac >>
  qexistsl_tac [`w2n w`, `type_memory_size tv`] >> simp[]
QED
