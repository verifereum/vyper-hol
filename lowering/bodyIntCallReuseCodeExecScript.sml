(* Immutable unwrap at an actual, possibly reused, allocation base. *)
Theory bodyIntCallReuseCodeExec
Ancestors
  bodyIntCallReuseAllocation bodyIntCallReuseUnwrap bodyIntCallHeldImmutableCopy
  bodyIntCallHeldArgs bodyIntCallStorageTyped bodyIntCallStageUnwrapRead exprSimCopy exprSimStorageCopy exprLoweringProps
  loweringPosts loweringHalt compileEnv context venomState venomInst
  finite_map words freshWrites

Theorem intcall_reuse_unwrap_code:
  unwrap_value ce (LocatedValue sty p) sa = (op,sn) /\
  p.ptr_location = LocCode /\
  ~is_word_type sty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  type_memory_bytes ce sty < dimword(:256) /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  fn_has_code sa sn func /\ local_ptrs_reserved ce sa /\
  expr_sim_inv ce cx env es /\ fn_directly_calls ctx func.fn_name name /\
  MEM func ctx.ctx_functions /\
  intcall_held_args ce cx a sa es s ((ty,raw,LocatedValue sty p)::H) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?v w z. gas_marked_path F ctx func s 0 (OK z) /\
    read_result cx raw es = (INL v,es) /\ eval_operand op z = SOME w /\
    value_has_type tv v /\ val_wf tv v /\
    (if is_word_type ty then w = typed_val_to_w256 tv v
     else val_in_memory tv v (w2n w) z.vs_memory) /\
    stmt_state_rel ctx func ce cx es z /\
    intcall_held_args ce cx a sn es z H /\ wb_frame ce es sa s z /\
    ~z.vs_halted /\ z.vs_current_bb = sn.cs_current_bb /\
    z.vs_inst_idx = LENGTH sn.cs_current_insts /\
    (!x q. not_fresh_at sa x /\ lookup_var x s = SOME q ==> lookup_var x z = SOME q) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP z.vs_allocas aid = SOME entry)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `MEM (ty,raw,LocatedValue sty p) ((ty,raw,LocatedValue sty p)::H)` by simp[] >>
  drule_all intcall_held_args_member >> strip_tac >>
  `p.ptr_location <> LocMemory` by simp[] >>
  drule_all held_nonmemory_layout >> strip_tac >>
  drule_all immutable_held_read_value >> strip_tac >>
  drule_all immutable_unwrap_layout >> strip_tac >>
  drule_all intcall_reuse_allocation >> strip_tac >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sa x` by gvs[vv_operand_def] >>
  `u.vs_memory = s.vs_memory /\ u.vs_labels = s.vs_labels /\
   contract_storage u = contract_storage s /\
   contract_transient u = contract_transient s` by
    (qpat_x_assum `u with <|vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _|> = s` mp_tac >>
     simp[venom_state_component_equality, contract_storage_def,
          contract_transient_def]) >>
  `eval_operand p.ptr_operand u = SOME a'` by
    (Cases_on `p.ptr_operand` >> fs[eval_operand_def]) >>
  `immutable_holds ce cx ty (Value v) a' es u` by suspend "holds" >>
  `ce.ce_is_ctor ==> regions_disjoint (w2n a') (type_memory_size tv)
       b (type_memory_size tv)` by suspend "sep" >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (drule compile_alloc_buffer_parts >> simp[]) >>
  `copy_old_operand sm p.ptr_operand /\ copy_old_operand sm buf.buf_operand` by
    (Cases_on `p.ptr_operand` >>
     gvs[copy_old_operand_def, eval_operand_def] >> metis_tac[not_fresh_at_mono]) >>
  qpat_x_assum `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> disch_tac >>
  drule_at (Pat `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _`) immutable_typed_copy_path >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ u`)) >>
  disch_then (drule_at (Pat `immutable_holds _ _ _ _ _ _ u`)) >>
  disch_then (qspec_then `n2w b` mp_tac) >>
  (impl_tac >- gvs[w2n_n2w, dimword_def]) >> strip_tac >>
  `sa.cs_next_id <= sn.cs_next_id /\ sa.cs_next_var <= sn.cs_next_var` by
    (mp_tac (Q.SPECL [`ce`,`LocatedValue sty p`,`sa`] ci_mono_unwrap_value) >>
     simp[ci_mono_def]) >>
  `stmt_state_rel ctx func ce cx es z /\ wb_frame ce es sa s z /\
   intcall_held_args ce cx a sn es z H` by suspend "frame" >>
  `gas_marked_path F ctx func s 0 (OK z)` by
    metis_tac[fragGasModeTheory.gas_marked_path_then,arithmeticTheory.ADD_0] >>
  drule copy_static_fields >> strip_tac >>
  `value_has_type tv v` by metis_tac[] >>
  qexistsl_tac [`v`,`n2w b`,`z`] >>
  gvs[w2n_n2w, dimword_def] >> rpt strip_tac >> metis_tac[not_fresh_at_mono]
QED

Resume intcall_reuse_unwrap_code[holds]:
  metis_tac[exprSimPropsTheory.immutable_holds_memory_cong]
QED
Resume intcall_reuse_unwrap_code[sep]:
  strip_tac >>
  drule_at (Pat `MEM _ (fn_insts _)`) immutable_holds_alloca_disjoint >>
  simp[mk_inst_def] >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ u`)) >>
  disch_then (drule_at (Pat `immutable_holds _ _ _ _ _ _ u`)) >>
  gvs[]
QED
Resume intcall_reuse_unwrap_code[frame]:
  `local_ptrs_rel func ce es.scopes s` by fs[stmt_state_rel_def, state_rel_def] >>
  `intcall_held_args ce cx a sa es s H` by fs[intcall_held_args_def] >>
  `!n lb sz. local_region ce es.scopes s n lb sz <=>
      local_region ce es.scopes u n lb sz` by
    metis_tac[exprSimCopyTheory.copy_buffer_local_region_frame] >>
  irule intcall_reuse_copy_frame >> simp[] >>
  qexistsl_tac [`b`,
    `mk_inst sa.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes ce sty))] [x]`,
    `type_memory_bytes ce sty`,`sm`,`u`] >>
  simp[mk_inst_def] >>
  conj_tac >- metis_tac[regions_disjoint_def] >>
  conj_tac >- metis_tac[regions_disjoint_def] >>
  conj_tac >- metis_tac[regions_disjoint_def] >>
  gvs[w2n_n2w, dimword_def] >>
  metis_tac[arithmeticTheory.ADD_SYM]
QED
Finalise intcall_reuse_unwrap_code
