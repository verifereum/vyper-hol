(* Semantic immutable forcing uses separation at the actual allocation landing. *)
Theory bodyIntCallForcingCode
Ancestors
  bodyIntCallForcingCodeRun bodyIntCallLiteralLanding bodyIntCallMaterializeLanding
  exprSimCopy exprSimStorageCopy exprSimProps exprLoweringProps loweringPosts
  context compileEnv valueEncodingProps valueEncoding intCallFrame exprSimAlloc
  loweringHalt fragGasPath fragGasMode
  venomState venomInst finite_map list words vyperInterpreter vyperState

Theorem immutable_value_copy_landing:
  compile_imm_copy_to_memory ce.ce_is_ctor ce.ce_imm_alloca src dst
    (type_slot_size tv) 0 sa = ((),sb) /\
  immutable_holds ce cx ty (Value v) aw es s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sa /\
  fresh_vars_wrt sa s /\ copy_old_operand sa src /\ copy_old_operand sa dst /\
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
    val_in_memory tv v (w2n w) u.vs_memory /\
    copy_static u = copy_static s /\
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

Theorem immutable_value_alloc_landing:
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
    (!q. reserved q ==> eval_operand q u = eval_operand q s) /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `!q x. (reserved q \/ q = src) /\ q = Var x ==> not_fresh_at sa x` by
    (fs[copy_old_operand_def] >> metis_tac[]) >>
  mp_tac (Q.INST [`sz` |-> `type_memory_size tv`,
    `reserved` |-> `\q. reserved q \/ q = src`]
    (SPEC_ALL materialization_alloc_landing)) >>
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
  qexistsl_tac [`u`, `w`] >> fs[allocas_above_def] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  qx_gen_tac `addr` >> qx_gen_tac `len` >> strip_tac >>
  `addr + len <= lo` by (qpat_x_assum `!p k. P p k ==> _` drule >> simp[]) >>
  `regions_disjoint addr len (w2n w) (type_memory_size tv)` by
    (simp[regions_disjoint_def] >> decide_tac) >> metis_tac[]
QED
