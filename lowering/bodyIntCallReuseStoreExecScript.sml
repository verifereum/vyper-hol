(* Allocation and staging store at an actual, possibly reused base. *)
Theory bodyIntCallReuseStoreExec
Ancestors
  bodyIntCallReuseAllocation bodyIntCallReuseUnwrap bodyIntCallStageStore
  exprSimCopy exprSimStorageCopy exprLoweringProps loweringPosts
  loweringHalt compileEnv context venomState venomInst finite_map words freshWrites

Theorem intcall_reuse_alloc_store:
  compile_alloc_buffer (MAX 32 (type_memory_bytes ce ty)) sm = (buf,si) /\
  compile_store_memory ce op buf.buf_operand ty ty si = ((),sn) /\
  fn_has_code sm si func /\ fn_has_code si sn func /\
  MAX 32 (type_memory_bytes ce ty) < dimword (:256) /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sm /\ intcall_held_args ce cx a sm es s H /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!x. op = Var x ==> not_fresh_at sm x) /\
  eval_operand op s = SOME sw /\ evaluate_type tenv ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce ty = type_memory_size tv /\
  (if is_word_type ty then sw = typed_val_to_w256 tv v
   else val_in_memory tv v (w2n sw) s.vs_memory) ==>
  ?t inst b. gas_marked_path F ctx func s 0 (OK t) /\
    ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
    t.vs_inst_idx = LENGTH sn.cs_current_insts /\
    stmt_state_rel ctx func ce cx es t /\
    intcall_held_args ce cx a sn es t H /\ wb_frame ce es sm s t /\
    eval_operand buf.buf_operand t = SOME (n2w b) /\
    val_in_memory tv v b t.vs_memory /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = sm.cs_next_id /\
    FLOOKUP t.vs_allocas sm.cs_next_id = SOME (b,MAX 32 (type_memory_bytes ce ty)) /\
    (!y. not_fresh_at sm y ==> lookup_var y t = lookup_var y s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP t.vs_allocas aid = SOME entry) /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory /\
    (!off len. off+len <= b \/ b+MAX 32 (type_memory_bytes ce ty) <= off ==>
      mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory) /\
    (!aid lb sz. FLOOKUP s.vs_allocas aid = SOME (lb,sz) /\ aid < sm.cs_next_id ==>
      regions_disjoint b (MAX 32 (type_memory_bytes ce ty)) lb sz) /\
    (!name lb sz. local_region ce es.scopes s name lb sz ==>
      regions_disjoint b (MAX 32 (type_memory_bytes ce ty)) lb sz) /\
    type_memory_size tv <= MAX 32 (type_memory_bytes ce ty)
Proof
  strip_tac >> drule_all intcall_reuse_allocation >> strip_tac >>
  `sm.cs_next_var <= si.cs_next_var` by
    (drule compile_alloc_buffer_parts >> simp[]) >>
  `u.vs_memory = s.vs_memory /\ u.vs_labels = s.vs_labels /\
   contract_storage u = contract_storage s /\ contract_transient u = contract_transient s` by
    (qpat_x_assum `u with <|vs_vars := _; vs_allocas := _;
      vs_alloca_next := _; vs_inst_idx := _|> = s` mp_tac >>
     simp[venom_state_component_equality,contract_storage_def,contract_transient_def]) >>
  `eval_operand op u = SOME sw` by
    (Cases_on `op` >> fs[eval_operand_def]) >>
  `(!x. op = Var x ==> not_fresh_at si x) /\
   (!x. buf.buf_operand = Var x ==> not_fresh_at si x)` by
    (gvs[] >> metis_tac[not_fresh_at_mono]) >>
  `if is_word_type ty then sw = typed_val_to_w256 tv v
   else val_in_memory tv v (w2n sw) u.vs_memory` by simp[] >>
  drule_all intcall_stage_store_forward >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `w2n (n2w b :256 word) = b` by simp[] >>
  `copy_static t = copy_static u` by suspend "static" >>
  `stmt_state_rel ctx func ce cx es t /\ wb_frame ce es sm s t /\
   intcall_held_args ce cx a sn es t H` by suspend "frame" >>
  qexistsl_tac [`t`,`mk_inst sm.cs_next_id ALLOCA
    [Lit (n2w (MAX 32 (type_memory_bytes ce ty)))] [x]`,`b`] >>
  simp[mk_inst_def] >> suspend "finish"
QED
Resume intcall_reuse_alloc_store[static]:
  qpat_x_assum `t with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|> = u` mp_tac >>
  simp[venom_state_component_equality,copy_static_def]
QED
Resume intcall_reuse_alloc_store[frame]:
  `si.cs_next_var <= sn.cs_next_var /\ si.cs_next_id <= sn.cs_next_id` by
    (mp_tac (Q.SPECL [`ce`,`op`,`buf.buf_operand`,`ty`,`ty`,`si`]
      ci_mono_compile_store_memory) >> simp[ci_mono_def]) >>
  `local_ptrs_rel func ce es.scopes s` by fs[stmt_state_rel_def,state_rel_def] >>
  `!n lb sz. local_region ce es.scopes s n lb sz <=>
      local_region ce es.scopes u n lb sz` by
    metis_tac[copy_buffer_local_region_frame] >>
  irule intcall_reuse_copy_frame >> simp[] >>
  qexistsl_tac [`b`,`mk_inst sm.cs_next_id ALLOCA
    [Lit (n2w (MAX 32 (type_memory_bytes ce ty)))] [x]`,
    `MAX 32 (type_memory_bytes ce ty)`,`si`,`u`] >>
  simp[mk_inst_def] >>
  conj_tac >- metis_tac[regions_disjoint_def] >>
  conj_tac >- metis_tac[regions_disjoint_def] >>
  conj_tac >- metis_tac[regions_disjoint_def] >>
  gvs[] >> metis_tac[arithmeticTheory.ADD_SYM]
QED
Resume intcall_reuse_alloc_store[finish]:
  conj_tac >- metis_tac[fragGasModeTheory.gas_marked_path_then,arithmeticTheory.ADD_0] >>
  conj_tac >- (qpat_x_assum `eval_operand buf.buf_operand u = _` mp_tac >>
    simp[eval_operand_def]) >>
  gvs[] >>
  conj_tac >- metis_tac[not_fresh_at_mono] >>
  conj_tac >- metis_tac[arithmeticTheory.ADD_SYM] >>
  conj_tac >- metis_tac[] >>
  metis_tac[copy_buffer_local_region_frame]
QED
Finalise intcall_reuse_alloc_store
