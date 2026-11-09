(* Counted immutable copies at the held argument endpoint. *)
Theory bodyIntCallHeldImmutableCopy
Ancestors
  bodyIntCallHeldByteFrame bodyIntCallStorageAllocate bodyIntCallStorageTyped loweringPosts
  exprSimCopy exprSimStorageCopy exprSimMemUnwrap entrySinkExtraction fragGasSeq fragGasPath fragGasMode fragExec exprLoweringProps
  venomState venomExecSemantics venomInst compileEnv context list rich_list finite_map words

Theorem immutable_copy_run_marked:
  copy_runtime_frame sa s sb z /\ fn_has_code sa sb func /\
  EVERY (\i. MEM i.inst_opcode [ADD; ILOAD; DLOAD; MSTORE])
    (emitted_insts sa sb) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_marked_path F ctx func s 0
    (OK (z with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  z.vs_halted = s.vs_halted /\ z.vs_current_bb = s.vs_current_bb
Proof
  strip_tac >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    (gvs[copy_runtime_frame_def, same_blocks_def, fn_has_code_def, IS_PREFIX_APPEND] >>
     simp[DROP_APPEND]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb) /\
   FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (gvs[EVERY_MEM, FILTER_EQ_NIL] >> rpt strip_tac >>
     res_tac >> gvs[is_terminator_def]) >>
  `run_inst_seq (emitted_insts sa sb) s = OK z` by
    gvs[copy_runtime_frame_def] >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  drule_all tuple_run_inst_seq_gas_path >>
  gvs[copy_runtime_frame_def, gas_marked_path_def]
QED

Theorem immutable_copy_counted_run:
  compile_imm_copy_to_memory ctor imm src dst n off sa = ((),sb) /\
  copy_old_operand sa src /\ copy_old_operand sa dst /\
  eval_operand src s = SOME a /\ eval_operand dst s = SOME b /\
  (ctor ==> !region. imm = SOME region ==>
    eval_operand region s = SOME 0w /\ copy_old_operand sa region) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?z. copy_runtime_frame sa s sb z /\
    z.vs_memory = (immutable_transfers F ctor a b n off s).vs_memory /\
    gas_marked_path F ctx func s 0
      (OK (z with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    z.vs_halted = s.vs_halted /\ z.vs_current_bb = s.vs_current_bb
Proof
  strip_tac >>
  `?z. copy_runtime_frame sa s sb z /\
    z.vs_memory = (immutable_transfers F ctor a b n off s).vs_memory` by
    (Cases_on `ctor` >> fs[]
     >- (drule_all copy_ctor_run >> simp[]) >>
     drule_all copy_runtime_run >> simp[]) >>
  `EVERY (\i. MEM i.inst_opcode [ADD; ILOAD; DLOAD; MSTORE])
     (emitted_insts sa sb)` by
    (Cases_on `ctor` >> fs[]
     >- (drule code_ctor_copy_insts >> strip_tac >>
         gvs[emitted_insts_def, DROP_LENGTH_APPEND, EVERY_MEM] >> metis_tac[]) >>
     drule code_copy_insts >> strip_tac >>
     gvs[emitted_insts_def, DROP_LENGTH_APPEND, EVERY_MEM] >> metis_tac[]) >>
  drule_all immutable_copy_run_marked >> strip_tac >>
  qexists_tac `z` >> simp[]
QED

Theorem immutable_copy_owned_contents:
  stmt_state_rel ctx func ce cx es u /\
  immutable_holds ce cx ty (Value v) a es u /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  w2n w + type_memory_size tv < dimword (:256) /\
  (ce.ce_is_ctor ==> regions_disjoint (w2n a) (type_memory_size tv)
      (w2n w) (type_memory_size tv)) /\
  z.vs_memory = (immutable_transfers F ce.ce_is_ctor a w
    (type_slot_size tv) 0 u).vs_memory ==>
  val_wf tv v /\ val_in_memory tv v (w2n w) z.vs_memory /\
  val_footprint tv v <= type_memory_size tv /\
  LENGTH u.vs_memory <= LENGTH z.vs_memory /\
  (!off len. off+len <= w2n w \/ w2n w+type_memory_size tv <= off ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory)
Proof
  strip_tac >> Cases_on `ce.ce_is_ctor`
  >- (irule copy_ctor_contents >> asm_rewrite_tac[] >> metis_tac[]) >>
  `w2n a + type_memory_size tv < dimword (:256)` by
    metis_tac[immutable_holds_bounds] >>
  qpat_x_assum `z.vs_memory = _` mp_tac >> asm_rewrite_tac[] >> disch_tac >>
  drule_all copy_runtime_contents >> strip_tac >>
  drule_all runtime_code_copy_memory_frame >> strip_tac >>
  asm_rewrite_tac[]
QED

Theorem immutable_typed_copy_path:
  compile_imm_copy_to_memory ce.ce_is_ctor ce.ce_imm_alloca src dst
    (type_slot_size tv) 0 sa = ((),sb) /\
  copy_old_operand sa src /\ copy_old_operand sa dst /\
  eval_operand src u = SOME a /\ eval_operand dst u = SOME w /\
  stmt_state_rel ctx func ce cx es u /\ local_ptrs_reserved ce sa /\
  immutable_holds ce cx ty (Value v) a es u /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  w2n w + type_memory_size tv < dimword (:256) /\
  (ce.ce_is_ctor ==> regions_disjoint (w2n a) (type_memory_size tv)
      (w2n w) (type_memory_size tv)) /\
  fn_has_code sa sb func /\ ~u.vs_halted /\
  u.vs_current_bb = sa.cs_current_bb /\
  u.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?z. gas_marked_path F ctx func u 0 (OK z) /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    val_wf tv v /\ val_in_memory tv v (w2n w) z.vs_memory /\
    val_footprint tv v <= type_memory_size tv /\
    LENGTH u.vs_memory <= LENGTH z.vs_memory /\
    (!off len. off+len <= w2n w \/ w2n w+type_memory_size tv <= off ==>
      mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory) /\
    copy_static z = copy_static u /\
    (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x u) /\
    eval_operand dst z = SOME w
Proof
  strip_tac >>
  `(ce.ce_is_ctor ==> !region. ce.ce_imm_alloca = SOME region ==>
     eval_operand region u = SOME 0w /\ copy_old_operand sa region)` by
    (gvs[stmt_state_rel_def, immutable_base_zero_def, local_ptrs_reserved_def,
         copy_old_operand_def] >> metis_tac[]) >>
  drule_all immutable_copy_counted_run >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all immutable_copy_owned_contents >> strip_tac >>
  qexists_tac `z with vs_inst_idx := LENGTH sb.cs_current_insts` >> simp[] >>
  `~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb` by
    (gvs[copy_runtime_frame_def, same_blocks_def] >>
     metis_tac[copy_static_fields]) >>
  gvs[copy_runtime_frame_def] >> asm_rewrite_tac[] >>
  conj_tac >- gvs[copy_static_def] >>
  simp[lookup_var_def] >> asm_rewrite_tac[] >>
  Cases_on `dst` >> gvs[copy_old_operand_def, eval_operand_def, lookup_var_def] >>
  drule copy_static_fields >> simp[]
QED

Theorem immutable_unwrap_layout:
  unwrap_value ce (LocatedValue sty p) sa = (op,sb) /\
  p.ptr_location = LocCode /\ ~is_word_type sty /\
  fn_has_code sa sb func ==>
  ?buf sm. compile_alloc_buffer (type_memory_bytes ce sty) sa = (buf,sm) /\
    op = buf.buf_operand /\
    compile_imm_copy_to_memory ce.ce_is_ctor ce.ce_imm_alloca p.ptr_operand
      buf.buf_operand ((type_memory_bytes ce sty + 31) DIV 32) 0 sm = ((),sb) /\
    fn_has_code sa sm func /\ fn_has_code sm sb func
Proof
  strip_tac >>
  gvs[exprLoweringTheory.unwrap_value_def, compile_ensure_in_memory_def, comp_bind_def,
      comp_return_def, comp_ignore_bind_def] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `compile_alloc_buffer _ sa = (buf,sm)` >>
  rename1 `fn_has_code sa sb func` >>
  `cs_extends sa sm` by metis_tac[loweringHaltTheory.compile_alloc_buffer_extends] >>
  `cs_extends sm sb` by
    (Cases_on `ce.ce_is_ctor` >> fs[] >>
     imp_res_tac code_ctor_copy_insts >> imp_res_tac code_copy_insts >>
     gvs[same_blocks_def] >> irule cs_extends_same_block >> simp[]) >>
  metis_tac[fn_has_code_split]
QED

Theorem immutable_typed_allocation_path:
  compile_alloc_buffer nb sa = (buf,sm) /\ fn_has_code sa sm func /\
  nb < dimword(:256) /\ sa.cs_next_id NOTIN FDOM s.vs_allocas /\
  alloca_room ctx func s /\ fn_directly_calls ctx func.fn_name name /\
  MEM func ctx.ctx_functions /\ type_memory_size tv = nb /\
  (!x. src = Var x ==> not_fresh_at sa x) /\ eval_operand src s = SOME a /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ immutable_holds ce cx ty (Value v) a es s ==>
  ?u b. gas_marked_path F ctx func s 0 (OK u) /\ b = s.vs_alloca_next /\
    eval_operand buf.buf_operand u = SOME (n2w b) /\
    eval_operand src u = SOME a /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (b,nb) /\
    b + type_memory_size tv < dimword(:256) /\
    ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
    u.vs_inst_idx = LENGTH sm.cs_current_insts /\
    stmt_state_rel ctx func ce cx es u /\
    immutable_holds ce cx ty (Value v) a es u /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    u.vs_allocas = s.vs_allocas |+ (sa.cs_next_id,(b,nb)) /\
    u.vs_alloca_next = b+nb /\ u.vs_memory = s.vs_memory /\
    (u with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
      vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|>) = s
Proof
  strip_tac >>
  `s.vs_alloca_next + nb < dimword(:256)` by
    (drule (Q.INST [`margin` |-> `0`]
       bodyIntCallConsumerProbeTheory.alloc_buffer_own_site_reserve) >> simp[] >> metis_tac[]) >>
  drule_all fresh_buffer_allocation_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all fresh_buffer_allocation_state_rel >> strip_tac >>
  `u.vs_memory = s.vs_memory` by simp[update_var_def] >>
  `immutable_holds ce cx ty (Value v) a es u` by
    metis_tac[exprSimPropsTheory.immutable_holds_memory_cong] >>
  qexistsl_tac [`u`, `s.vs_alloca_next`] >> simp[] >>
  `!y. src = Var y ==> y <> x` by metis_tac[] >>
  qpat_x_assum `u = _` SUBST_ALL_TAC >>
  simp[update_var_def, lookup_var_def, eval_operand_def,
       venom_state_component_equality, FLOOKUP_UPDATE] >>
  Cases_on `src` >> gvs[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem immutable_held_read_value:
  vv_holds ce cx ty raw (LocatedValue sty p) es s /\
  p.ptr_location = LocCode ==>
  ?a v. eval_operand p.ptr_operand s = SOME a /\
    read_result cx raw es = (INL v,es) /\
    immutable_holds ce cx ty (Value v) a es s
Proof
  strip_tac >>
  gvs[vv_holds_def, immutable_holds_def, vyperStateTheory.read_result_def,
      vyperStateTheory.return_def] >>
  qexistsl_tac [`name`, `off`, `itv`, `iv`, `k`] >> simp[]
QED

Theorem immutable_typed_unwrap_path:
  unwrap_value ce (LocatedValue sty p) sa = (op,sb) /\
  p.ptr_location = LocCode /\ ~is_word_type sty /\ fn_has_code sa sb func /\
  type_memory_bytes ce sty < dimword(:256) /\
  sa.cs_next_id NOTIN FDOM s.vs_allocas /\
  alloca_room ctx func s /\ fn_directly_calls ctx func.fn_name name /\
  MEM func ctx.ctx_functions /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ expr_sim_inv ce cx env es /\
  vv_holds ce cx ty raw (LocatedValue sty p) es s /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  ?z v u b a sm buf.
    gas_marked_path F ctx func s 0 (OK z) /\
    read_result cx raw es = (INL v,es) /\ expr_val_rel cx ty v op z /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    FLOOKUP z.vs_allocas sa.cs_next_id = SOME (b,type_memory_bytes ce sty) /\
    val_wf tv v /\ val_in_memory tv v b z.vs_memory /\
    val_footprint tv v <= type_memory_size tv /\
    compile_alloc_buffer (type_memory_bytes ce sty) sa = (buf,sm) /\
    op = buf.buf_operand /\ b = s.vs_alloca_next /\
    gas_marked_path F ctx func s 0 (OK u) /\
    LENGTH u.vs_memory <= LENGTH z.vs_memory /\
    (!off len. off+len <= b \/ b+type_memory_size tv <= off ==>
      mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory) /\
    (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x u) /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    copy_static z = copy_static u /\
    u.vs_allocas = s.vs_allocas |+ (sa.cs_next_id,(b,type_memory_bytes ce sty)) /\
    u.vs_alloca_next = b + type_memory_bytes ce sty /\ u.vs_memory = s.vs_memory /\
    (u with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
      vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|>) = s
Proof
  strip_tac >>
  `p.ptr_location <> LocMemory` by simp[] >>
  drule_all held_nonmemory_layout >> strip_tac >>
  drule_all immutable_held_read_value >> strip_tac >>
  drule_all immutable_unwrap_layout >> strip_tac >>
  `type_memory_size tv = type_memory_bytes ce sty` by simp[] >>
  drule_all immutable_typed_allocation_path >> strip_tac >>
  drule storage_copy_alloc_layout >> strip_tac >>
  `copy_old_operand sm p.ptr_operand /\ copy_old_operand sm buf.buf_operand` by
    (gvs[copy_old_operand_def, not_fresh_at_def] >> rpt strip_tac >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_ADD]) >>
  `local_ptrs_reserved ce sm` by
    metis_tac[local_ptrs_reserved_next_var, arithmeticTheory.LESS_EQ_ADD] >>
  `(ce.ce_is_ctor ==> regions_disjoint (w2n a) (type_memory_size tv)
      (w2n (n2w b:bytes32)) (type_memory_size tv))` by
    (strip_tac >>
     qpat_assum `stmt_state_rel ctx func ce cx es s`
       (mp_then Any mp_tac ctor_immutable_frontier) >>
     simp[] >> disch_then drule >> strip_tac >>
     gvs[regions_disjoint_def, w2n_n2w] >> decide_tac) >>
  `b < dimword(:256)` by decide_tac >>
  `w2n (n2w b:bytes32) + type_memory_size tv < dimword(:256)` by
    simp[w2n_n2w] >>
  qpat_x_assum `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  qpat_assum `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _`
    (mp_then Any mp_tac immutable_typed_copy_path) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `immutable_holds _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
  disch_then (qspec_then `n2w b` mp_tac) >>
  (impl_tac >- gvs[]) >> strip_tac >>
  `gas_marked_path F ctx func s 0 (OK z)` by
    metis_tac[gas_marked_path_then, arithmeticTheory.ADD_0] >>
  `b < dimword(:256)` by decide_tac >>
  `expr_val_rel cx ty v op z` by
    (simp[expr_val_rel_def] >> gvs[w2n_n2w]) >>
  `z.vs_allocas = u.vs_allocas` by metis_tac[copy_static_fields] >>
  qexistsl_tac [`z`, `v`, `u`, `b`, `sm`, `buf`] >>
  gvs[w2n_n2w] >> asm_rewrite_tac[]
QED

Theorem immutable_unwrap_held_tail:
  unwrap_value ce (LocatedValue sty p) sa = (op,sb) /\
  p.ptr_location = LocCode /\ ~is_word_type sty /\ fn_has_code sa sb func /\
  type_memory_bytes ce sty < dimword(:256) /\
  sa.cs_next_id NOTIN FDOM s.vs_allocas /\
  alloca_room ctx func s /\ fn_directly_calls ctx func.fn_name name /\
  MEM func ctx.ctx_functions /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ expr_sim_inv ce cx env es /\
  vv_holds ce cx ty raw (LocatedValue sty p) es s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  intcall_held_args ce cx start sa es s H ==>
  ?z v b. gas_marked_path F ctx func s 0 (OK z) /\
    read_result cx raw es = (INL v,es) /\ expr_val_rel cx ty v op z /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    FLOOKUP z.vs_allocas sa.cs_next_id = SOME (b,type_memory_bytes ce sty) /\
    val_wf tv v /\ val_in_memory tv v b z.vs_memory /\
    val_footprint tv v <= type_memory_size tv /\ b = s.vs_alloca_next /\
    wb_frame ce es sa s z /\ intcall_held_args ce cx start sb es z H
Proof
  strip_tac >> drule_all immutable_typed_unwrap_path >> strip_tac >>
  `ci_mono sa sm /\ ci_mono sa sb` by
    metis_tac[ci_mono_compile_alloc_buffer, ci_mono_unwrap_value, pairTheory.SND] >>
  `z.vs_allocas = u.vs_allocas /\ z.vs_labels = s.vs_labels /\
   contract_storage z = contract_storage s /\
   contract_transient z = contract_transient s` by
    (drule copy_static_fields >> strip_tac >>
     qpat_x_assum `u with <|vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _|> = s` (mp_tac o GSYM) >>
     simp[venom_state_component_equality] >> strip_tac >>
     simp[contract_storage_def, contract_transient_def]) >>
  `type_memory_size tv = type_memory_bytes ce sty` by
    (`p.ptr_location <> LocMemory` by simp[] >>
     drule_all held_nonmemory_layout >> simp[]) >>
  `wb_frame ce es sa s z /\ intcall_held_args ce cx start sb es z H` by
    (irule intcall_held_allocation_bytes_frame >>
     goal_assum (drule_at (Pat `intcall_held_args _ _ _ _ _ _ _`)) >>
     simp[] >> conj_tac >- gvs[ci_mono_def] >>
     conj_tac >- gvs[ci_mono_def] >> conj_tac
     >- (qexistsl_tac [`sa.cs_next_id`, `type_memory_bytes ce sty`, `sm`, `u`] >>
         gvs[ci_mono_def] >> asm_rewrite_tac[]) >>
     metis_tac[]) >>
  qexistsl_tac [`z`, `v`, `b`] >> simp[]
QED
