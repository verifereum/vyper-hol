(* Storage unwrap at an actual, possibly reused, allocation base. *)
Theory bodyIntCallReuseStorageExec
Ancestors
  bodyIntCallReuseAllocation bodyIntCallReuseUnwrap bodyIntCallStorageTyped
  bodyIntCallHeldArgs exprSimMemUnwrap exprSimStorageCopy exprLoweringProps
  loweringPosts loweringHalt compileEnv context venomState venomInst
  finite_map words freshWrites

Theorem intcall_reuse_unwrap_storage:
  unwrap_value ce (LocatedValue sty p) sa = (op,sn) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
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
  `p.ptr_location <> LocMemory` by gvs[] >>
  drule_all held_nonmemory_layout >> strip_tac >>
  drule storage_held_read_value >> simp[] >> strip_tac >>
  drule_all exprSimMemUnwrapTheory.storage_unwrap_layout_facts >> strip_tac >>
  drule_all intcall_reuse_allocation >> strip_tac >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sa x` by
    gvs[vv_operand_def] >>
  `u.vs_memory = s.vs_memory /\ u.vs_labels = s.vs_labels /\
   contract_storage u = contract_storage s /\
   contract_transient u = contract_transient s` by
    (qpat_x_assum `u with <|vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _|> = s` mp_tac >>
     simp[venom_state_component_equality, contract_storage_def,
          contract_transient_def]) >>
  `eval_operand p.ptr_operand u = SOME a'` by
    (Cases_on `p.ptr_operand` >> fs[eval_operand_def]) >>
  `storage_holds cx (p.ptr_location = LocTransient) ty (Value v) a' es u` by
    (qpat_x_assum `storage_holds _ _ _ _ _ _ s` mp_tac >>
     gvs[venom_state_component_equality, storage_holds_def,
         contract_storage_def, contract_transient_def]) >>
  `!y. p.ptr_operand = Var y \/ buf.buf_operand = Var y ==>
       not_fresh_at mid y` by
    (rpt strip_tac >> gvs[] >> metis_tac[not_fresh_at_mono]) >>
  qpat_x_assum `(if _ then _ else _) mid = _` mp_tac >>
  asm_rewrite_tac[] >> disch_tac >>
  drule_at (Pat `(if _ then _ else _) _ = _`) storage_copy_suffix_owned_path >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ u`)) >>
  disch_then (drule_at (Pat `storage_holds _ _ _ _ _ _ u`)) >>
  (impl_tac >- (gvs[dimword_def] >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
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
  gvs[w2n_n2w, dimword_def] >>
  rpt strip_tac >> metis_tac[not_fresh_at_mono]
QED

Resume intcall_reuse_unwrap_storage[frame]:
  `local_ptrs_rel func ce es.scopes s` by fs[stmt_state_rel_def, state_rel_def] >>
  `intcall_held_args ce cx a sa es s H` by
    fs[intcall_held_args_def] >>
  `!n lb sz. local_region ce es.scopes s n lb sz <=>
      local_region ce es.scopes u n lb sz` by
    metis_tac[exprSimCopyTheory.copy_buffer_local_region_frame] >>
  irule intcall_reuse_copy_frame >> simp[] >>
  qexistsl_tac [`b`,
    `mk_inst sa.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes ce sty))] [x]`,
    `type_memory_bytes ce sty`,`mid`,`u`] >>
  simp[mk_inst_def] >>
  conj_tac >- metis_tac[regions_disjoint_def] >>
  conj_tac >- metis_tac[regions_disjoint_def] >>
  conj_tac >- metis_tac[regions_disjoint_def] >>
  rpt gen_tac >> strip_tac >>
  `mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory` by
    (irule copy_prefix_bytes >>
     metis_tac[arithmeticTheory.ADD_SYM]) >> simp[]
QED

Finalise intcall_reuse_unwrap_storage
