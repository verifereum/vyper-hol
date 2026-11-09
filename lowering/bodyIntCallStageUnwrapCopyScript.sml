(* State transfer at the actual allocating unwrap endpoint. *)
Theory bodyIntCallStageUnwrapCopy
Ancestors
  bodyIntCallStageUnwrapRead bodyIntCallStorageTyped bodyIntCallHeldImmutableCopy
  bodyIntCallStageAllocation exprSimCopy venomState exprLoweringProps
  compileEnv context finite_map loweringHalt

Theorem intcall_allocation_state_frame:
  compile_alloc_buffer nb sa = (buf,sm) /\ fn_has_code sa sm func /\
  nb < dimword(:256) /\ sa.cs_next_id NOTIN FDOM s.vs_allocas /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  u.vs_allocas = s.vs_allocas |+ (sa.cs_next_id,(s.vs_alloca_next,nb)) /\
  u.vs_alloca_next = s.vs_alloca_next + nb /\
  (u with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
    vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|>) = s /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) ==>
  stmt_state_rel ctx func ce cx es u
Proof
  strip_tac >> drule compile_alloc_buffer_parts >> strip_tac >>
  qabbrev_tac `q = (update_var (STRING #"%" (toString sa.cs_next_var)) (n2w s.vs_alloca_next)
    (s with <|vs_allocas := s.vs_allocas |+
       (sa.cs_next_id,(s.vs_alloca_next,nb));
      vs_alloca_next := s.vs_alloca_next + nb|>)) with
    vs_inst_idx := LENGTH sm.cs_current_insts` >>
  `stmt_state_rel ctx func ce cx es q` by
    (irule (cj 1 bodyIntCallStorageAllocateTheory.fresh_buffer_allocation_state_rel) >>
     metis_tac[]) >>
  irule intcall_readonly_state_frame >> qexistsl_tac [`q`,`sa`] >>
  simp[] >>
  gvs[Abbr `q`, update_var_def, venom_state_component_equality] >>
  rpt strip_tac >> gvs[lookup_var_def,FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem intcall_allocation_copy_state_frame:
  compile_alloc_buffer nb sa = (buf,sm) /\ fn_has_code sa sm func /\
  nb < dimword(:256) /\ sa.cs_next_id NOTIN FDOM s.vs_allocas /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\
  u.vs_allocas = s.vs_allocas |+ (sa.cs_next_id,(s.vs_alloca_next,nb)) /\
  u.vs_alloca_next = s.vs_alloca_next + nb /\
  (u with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
    vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|>) = s /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  copy_static z = copy_static u /\ LENGTH u.vs_memory <= LENGTH z.vs_memory /\
  (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x u) /\
  (!off len. off+len <= s.vs_alloca_next \/ s.vs_alloca_next+nb <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory) ==>
  stmt_state_rel ctx func ce cx es z
Proof
  strip_tac >>
  `stmt_state_rel ctx func ce cx es u` by
    (irule intcall_allocation_state_frame >> metis_tac[]) >>
  drule_all exprSimAggregateChildrenTheory.buffer_alloc_provenance >> strip_tac >>
  drule_all actualAllocExecTheory.actual_alloc_buffer_site >> disch_tac >>
  `!name lb len. local_region ce es.scopes u name lb len ==>
     s.vs_alloca_next+nb <= lb \/ lb+len <= s.vs_alloca_next` by
    (rpt strip_tac >>
     `local_region ce es.scopes s name lb len` by
       (qspecl_then [`ce`,`sa`,`s`,`u`] mp_tac copy_buffer_local_region_frame >>
        (impl_tac >- simp[]) >>
        disch_then (qspecl_then [`es.scopes`,`name`,`lb`,`len`] mp_tac) >>
        metis_tac[]) >>
     disj2_tac >> irule bodyMemoryDefsTheory.body_local_region_frontier >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  irule copy_buffer_state_rel_frame >>
  qexistsl_tac [`s.vs_alloca_next`,
    `mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)]
       [STRING #"%" (toString sa.cs_next_var)]`, `u`,`sm`,`nb`] >>
  simp[venomInstTheory.mk_inst_def,FLOOKUP_UPDATE] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem intcall_unwrap_copy_frame:
  compile_alloc_buffer nb sa = (buf,sm) /\ fn_has_code sa sm func /\
  nb < dimword(:256) /\ sa.cs_next_id NOTIN FDOM s.vs_allocas /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ intcall_held_args ce cx a sa es s H /\
  sa.cs_next_id < sn.cs_next_id /\ sa.cs_next_var <= sn.cs_next_var /\
  u.vs_allocas = s.vs_allocas |+ (sa.cs_next_id,(s.vs_alloca_next,nb)) /\
  u.vs_alloca_next = s.vs_alloca_next+nb /\
  (u with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
    vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|>) = s /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  copy_static z = copy_static u /\ LENGTH u.vs_memory <= LENGTH z.vs_memory /\
  (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x u) /\
  (!off len. off+len <= s.vs_alloca_next \/ s.vs_alloca_next+nb <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory) ==>
  stmt_state_rel ctx func ce cx es z /\
  intcall_held_args ce cx a sn es z H /\ wb_frame ce es sa s z /\
  (!x q. not_fresh_at sa x /\ lookup_var x s = SOME q ==> lookup_var x z = SOME q) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP z.vs_allocas aid = SOME entry) /\
  (!aid. sn.cs_next_id <= aid /\ aid NOTIN FDOM s.vs_allocas ==>
    aid NOTIN FDOM z.vs_allocas)
Proof
  strip_tac >>
  `stmt_state_rel ctx func ce cx es z` by
    (irule intcall_allocation_copy_state_frame >> metis_tac[]) >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `u.vs_memory = s.vs_memory /\ z.vs_allocas = u.vs_allocas /\
   z.vs_labels = s.vs_labels /\ contract_storage z = contract_storage s /\
   contract_transient z = contract_transient s` by
    (drule exprSimStorageCopyTheory.copy_static_fields >> strip_tac >>
     gvs[venom_state_component_equality,contract_storage_def,contract_transient_def]) >>
  `wb_frame ce es sa s z /\ intcall_held_args ce cx a sn es z H` by
    (irule bodyIntCallHeldByteFrameTheory.intcall_held_allocation_bytes_frame >>
     goal_assum (drule_at (Pat `intcall_held_args _ _ _ _ _ _ _`)) >>
     simp[] >> reverse conj_tac >- metis_tac[] >>
     qexistsl_tac [`sa.cs_next_id`,`nb`,`sm`,`u`] >> gvs[] >> metis_tac[]) >>
  simp[]
  >- (rpt strip_tac >> gvs[FLOOKUP_UPDATE,FLOOKUP_DEF] >> metis_tac[]) >>
  rpt strip_tac >>
  gvs[FDOM_FUPDATE] >> decide_tac
QED

Theorem intcall_stage_unwrap_storage:
  unwrap_value ce (LocatedValue sty p) sa = (op,sn) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  ~is_word_type sty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  type_memory_bytes ce sty < dimword(:256) /\
  sa.cs_next_id NOTIN FDOM s.vs_allocas /\
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
      FLOOKUP z.vs_allocas aid = SOME entry) /\
    (!aid. sn.cs_next_id <= aid /\ aid NOTIN FDOM s.vs_allocas ==>
      aid NOTIN FDOM z.vs_allocas)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `MEM (ty,raw,LocatedValue sty p) ((ty,raw,LocatedValue sty p)::H)` by simp[] >>
  drule_all bodyIntCallHeldArgsTheory.intcall_held_args_member >> strip_tac >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sa x` by gvs[vv_operand_def] >>
  `alloca_room ctx func s` by gvs[stmt_state_rel_def] >>
  `p.ptr_location <> LocMemory` by gvs[] >>
  drule_all held_nonmemory_layout >> strip_tac >>
  drule (Q.INST [`margin` |-> `0`]
    bodyIntCallStorageReadTheory.storage_unwrap_site_reserve) >>
  disch_then (drule_at (Pat `alloca_room _ _ _`)) >> simp[] >>
  disch_then (qspec_then `name` mp_tac) >> simp[] >> strip_tac >>
  drule_all storage_typed_unwrap_path >> strip_tac >>
  qpat_x_assum `sty = ty` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [GSYM th]) >> SUBST_ALL_TAC (GSYM th)) >>
  qpat_x_assum `b = s.vs_alloca_next` SUBST_ALL_TAC >>
  `mid = sm /\ buf = buf'` by metis_tac[pairTheory.PAIR_EQ] >>
  qpat_x_assum `mid = sm` SUBST_ALL_TAC >>
  qpat_x_assum `buf = buf'` SUBST_ALL_TAC >>
  `sa.cs_next_id < sn.cs_next_id /\ sa.cs_next_var <= sn.cs_next_var` by
    suspend "mono" >>
  `stmt_state_rel ctx func ce cx es z /\ intcall_held_args ce cx a sn es z H /\
   wb_frame ce es sa s z /\
   (!x q. not_fresh_at sa x /\ lookup_var x s = SOME q ==> lookup_var x z = SOME q) /\
   (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> FLOOKUP z.vs_allocas aid = SOME entry) /\
   (!aid. sn.cs_next_id <= aid /\ aid NOTIN FDOM s.vs_allocas ==> aid NOTIN FDOM z.vs_allocas)` by
    suspend "frame" >>
  gvs[loweringPostsTheory.expr_val_rel_def] >>
  qexistsl_tac [`w`,`z`] >> simp[] >> metis_tac[]
QED

Resume intcall_stage_unwrap_storage[mono]:
  markerLib.RESUME_TAC >>
  `ci_mono sm sn` by
    (irule storage_copy_suffix_ci_mono >> goal_assum (drule_at Any) >> simp[]) >>
  mp_tac (Q.SPECL [`ce`,`LocatedValue sty p`,`sa`] ci_mono_unwrap_value) >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  gvs[ci_mono_def] >> decide_tac
QED

Resume intcall_stage_unwrap_storage[frame]:
  markerLib.RESUME_TAC >>
  irule intcall_unwrap_copy_frame >>
  simp[] >> reverse conj_tac
  >- gvs[bodyIntCallHeldArgsTheory.intcall_held_args_def] >>
  qexistsl_tac [`buf'`,`type_memory_bytes ce sty`,`sm`,`u`] >> simp[] >>
  reverse conj_tac >- gvs[] >>
  rpt strip_tac >>
  drule exprSimStorageCopyTheory.copy_prefix_bytes >>
  disch_then (qspecl_then [`off`,`len`] mp_tac) >>
  simp[] >> decide_tac
QED
Finalise intcall_stage_unwrap_storage

Theorem intcall_stage_unwrap_code:
  unwrap_value ce (LocatedValue sty p) sa = (op,sn) /\
  p.ptr_location = LocCode /\
  ~is_word_type sty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  type_memory_bytes ce sty < dimword(:256) /\
  sa.cs_next_id NOTIN FDOM s.vs_allocas /\
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
      FLOOKUP z.vs_allocas aid = SOME entry) /\
    (!aid. sn.cs_next_id <= aid /\ aid NOTIN FDOM s.vs_allocas ==>
      aid NOTIN FDOM z.vs_allocas)
Proof
  strip_tac >>
  `MEM (ty,raw,LocatedValue sty p) ((ty,raw,LocatedValue sty p)::H)` by simp[] >>
  drule_all bodyIntCallHeldArgsTheory.intcall_held_args_member >> strip_tac >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sa x` by gvs[vv_operand_def] >>
  `alloca_room ctx func s` by gvs[stmt_state_rel_def] >>
  `p.ptr_location <> LocMemory` by simp[] >>
  drule_all held_nonmemory_layout >> strip_tac >>
  drule_all immutable_typed_unwrap_path >> strip_tac >>
  drule_all immutable_unwrap_layout >> strip_tac >>
  `sa.cs_next_id < sn.cs_next_id /\ sa.cs_next_var <= sn.cs_next_var` by
    suspend "mono" >>
  `stmt_state_rel ctx func ce cx es z /\ intcall_held_args ce cx a sn es z H /\
   wb_frame ce es sa s z /\
   (!x q. not_fresh_at sa x /\ lookup_var x s = SOME q ==> lookup_var x z = SOME q) /\
   (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> FLOOKUP z.vs_allocas aid = SOME entry) /\
   (!aid. sn.cs_next_id <= aid /\ aid NOTIN FDOM s.vs_allocas ==> aid NOTIN FDOM z.vs_allocas)` by
    suspend "frame" >>
  gvs[loweringPostsTheory.expr_val_rel_def] >>
  qexistsl_tac [`w`,`z`] >> simp[] >> metis_tac[]
QED

Resume intcall_stage_unwrap_code[mono]:
  `ci_mono sm' sn` by
    metis_tac[ci_mono_compile_imm_copy_to_memory,pairTheory.SND] >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  gvs[ci_mono_def] >> decide_tac
QED
Resume intcall_stage_unwrap_code[frame]:
  `sm' = sm /\ buf' = buf` by metis_tac[pairTheory.PAIR_EQ] >>
  qpat_x_assum `sm' = sm` SUBST_ALL_TAC >>
  irule intcall_unwrap_copy_frame >> simp[] >> reverse conj_tac
  >- gvs[bodyIntCallHeldArgsTheory.intcall_held_args_def] >>
  qexistsl_tac [`buf`,`type_memory_bytes ce sty`,`sm`,`u`] >>
  simp[] >> reverse conj_tac >- gvs[] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED
Finalise intcall_stage_unwrap_code
