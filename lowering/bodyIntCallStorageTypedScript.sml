(* Typed storage unwrap, retaining its actual allocation/copy endpoint. *)
Theory bodyIntCallStorageTyped
Ancestors
  bodyIntCallStorageRead bodyIntCallStorageAllocate bodyIntCallStorageWord
  bodyIntCallStorageLoop exprSimHyps exprSimFieldLayout valueEncodingProps
  fragGasMode loweringPosts compileEnv exprSimStorageCopy exprLoweringProps
  venomState venomExecSemantics words finite_map
Libs
  monadsyntax

Theorem held_nonmemory_layout:
  vv_holds ce cx ty raw (LocatedValue sty p) es s /\
  p.ptr_location <> LocMemory /\ expr_sim_inv ce cx env es /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  sty = ty /\ type_memory_bytes ce sty = type_memory_size tv /\
  type_memory_bytes ce sty = 32 * type_slot_size tv /\
  (type_memory_bytes ce sty + 31) DIV 32 = type_slot_size tv
Proof
  strip_tac >>
  `sty = ty` by gvs[vv_holds_def] >>
  drule_all expr_sim_inv_memory_size >>
  metis_tac[type_memory_size_slots, slot_count_of_memory_size]
QED

Theorem storage_copy_suffix_owned_path:
  (loc = LocStorage \/ loc = LocTransient) /\
  (if type_slot_size tv = 1 then
     do w <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [src];
        emit_void MSTORE [dst;w] od
   else do compile_word_copy_loop src dst (type_slot_size tv) loc LocMemory F;
           return () od) sm = ((),sb) /\
  fn_has_code sm sb func /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sm x) /\
  eval_operand src u = SOME a /\ eval_operand dst u = SOME (n2w b) /\
  type_slot_size tv < 2**256 /\ b + 32 * type_slot_size tv < 2**256 /\
  ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
  u.vs_inst_idx = LENGTH sm.cs_current_insts /\
  stmt_state_rel ctx func ce cx es u /\
  storage_holds cx (loc = LocTransient) ty (Value v) a es u /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  FLOOKUP u.vs_allocas aid = SOME (b,sz) /\ type_memory_size tv <= sz ==>
  ?z. gas_marked_path F ctx func u 0 (OK z) /\
      copy_prefix loc a b (type_slot_size tv) u (type_slot_size tv) z /\
      LENGTH u.vs_memory <= LENGTH z.vs_memory /\
      (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x u) /\
      z.vs_current_bb = sb.cs_current_bb /\
      z.vs_inst_idx = LENGTH sb.cs_current_insts /\
      copy_static z = copy_static u /\
      FLOOKUP z.vs_allocas aid = SOME (b,sz) /\
      val_wf tv v /\ val_in_memory tv v b z.vs_memory /\
      val_footprint tv v <= type_memory_size tv /\
      eval_operand dst z = SOME (n2w b)
Proof
  strip_tac >> (Cases_on `type_slot_size tv = 1`
  >- (irule storage_copy_word_owned_path >> metis_tac[]) >>
  fs[comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >>
  irule storage_copy_loop_owned_path >> simp[] >> metis_tac[])
QED

Theorem storage_typed_allocation_path:
  compile_alloc_buffer nb sa = (buf,sm) /\ fn_has_code sa sm func /\
  nb < dimword(:256) /\ sa.cs_next_id NOTIN FDOM s.vs_allocas /\
  alloca_room ctx func s /\ fn_directly_calls ctx func.fn_name name /\
  MEM func ctx.ctx_functions /\ 32 * type_slot_size tv <= nb /\
  (!x. src = Var x ==> not_fresh_at sa x) /\ eval_operand src s = SOME a /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ storage_holds cx tr ty raw a es s ==>
  ?u b. gas_marked_path F ctx func s 0 (OK u) /\ b = s.vs_alloca_next /\
    eval_operand buf.buf_operand u = SOME (n2w b) /\
    eval_operand src u = SOME a /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (b,nb) /\
    b + 32 * type_slot_size tv < 2**256 /\ type_slot_size tv < 2**256 /\
    ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
    u.vs_inst_idx = LENGTH sm.cs_current_insts /\
    stmt_state_rel ctx func ce cx es u /\ storage_holds cx tr ty raw a es u /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    u.vs_allocas = s.vs_allocas |+ (sa.cs_next_id,(b,nb)) /\
    u.vs_alloca_next = b+nb /\
    (u with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
      vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|>) = s
Proof
  strip_tac >>
  `s.vs_alloca_next + nb < dimword(:256)` by
    (drule_all bodyIntCallConsumerProbeTheory.alloc_buffer_own_site_reserve >> simp[]) >>
  drule_all fresh_buffer_allocation_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all fresh_buffer_allocation_state_rel >> strip_tac >>
  `storage_holds cx tr ty raw a es u` by metis_tac[] >>
  qexistsl_tac [`u`, `s.vs_alloca_next`] >> simp[] >>
  `!y. src = Var y ==> y <> x` by metis_tac[] >>
  qpat_x_assum `u = _` SUBST_ALL_TAC >>
  simp[update_var_def, lookup_var_def, eval_operand_def,
       venom_state_component_equality, FLOOKUP_UPDATE] >>
  conj_tac >- (Cases_on `src` >>
    gvs[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  rpt conj_tac >> rpt strip_tac >>
  gvs[FLOOKUP_UPDATE, dimword_def] >> decide_tac
QED

Theorem storage_held_read_value:
  vv_holds ce cx ty raw (LocatedValue sty p) es s /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) ==>
  ?a v. eval_operand p.ptr_operand s = SOME a /\
    read_result cx raw es = (INL v,es) /\
    storage_holds cx (p.ptr_location = LocTransient) ty (Value v) a es s
Proof
  strip_tac >>
  gvs[vv_holds_def, storage_holds_def, vyperStateTheory.read_result_def,
      vyperStateTheory.return_def] >> metis_tac[]
QED

Theorem storage_typed_unwrap_path:
  unwrap_value ce (LocatedValue sty p) sa = (op,sb) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  ~is_word_type sty /\ fn_has_code sa sb func /\
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
    copy_prefix p.ptr_location a b (type_slot_size tv) u (type_slot_size tv) z /\
    LENGTH u.vs_memory <= LENGTH z.vs_memory /\
    (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x u) /\
    copy_static z = copy_static u /\
    u.vs_allocas = s.vs_allocas |+ (sa.cs_next_id,(b,type_memory_bytes ce sty)) /\
    u.vs_alloca_next = b + type_memory_bytes ce sty /\
    (u with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
      vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|>) = s
Proof
  strip_tac >>
  `p.ptr_location <> LocMemory` by simp[] >>
  drule_all held_nonmemory_layout >> strip_tac >>
  drule storage_held_read_value >> simp[] >> strip_tac >>
  `?buf sm. compile_alloc_buffer (type_memory_bytes ce sty) sa = (buf,sm) /\
    op = buf.buf_operand /\
    (if type_slot_size tv = 1 then
       do w <- emit_op (if p.ptr_location = LocStorage then SLOAD else TLOAD)
                 [p.ptr_operand]; emit_void MSTORE [buf.buf_operand;w] od
     else do compile_word_copy_loop p.ptr_operand buf.buf_operand
               (type_slot_size tv) p.ptr_location LocMemory F; return () od)
        sm = ((),sb) /\ fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (drule (Q.INST [`margin` |-> `0`] storage_unwrap_site_reserve) >>
     disch_then (drule_at (Pat `alloca_room _ _ _`)) >>
     simp[] >> metis_tac[]) >>
  `?u b. gas_marked_path F ctx func s 0 (OK u) /\ b = s.vs_alloca_next /\
    eval_operand buf.buf_operand u = SOME (n2w b) /\
    eval_operand p.ptr_operand u = SOME a /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (b,type_memory_bytes ce sty) /\
    b + 32 * type_slot_size tv < 2**256 /\ type_slot_size tv < 2**256 /\
    ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
    u.vs_inst_idx = LENGTH sm.cs_current_insts /\
    stmt_state_rel ctx func ce cx es u /\
    storage_holds cx (p.ptr_location = LocTransient) ty (Value v) a es u /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    u.vs_allocas = s.vs_allocas |+ (sa.cs_next_id,(b,type_memory_bytes ce sty)) /\
    u.vs_alloca_next = b + type_memory_bytes ce sty /\
    (u with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
      vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|>) = s` by
    (irule storage_typed_allocation_path >> simp[] >> metis_tac[]) >>
  drule storage_copy_alloc_layout >> strip_tac >>
  `!x. p.ptr_operand = Var x \/ buf.buf_operand = Var x ==> not_fresh_at sm x` by
    (rpt strip_tac >> gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS,
      arithmeticTheory.LESS_EQ_ADD]) >>
  drule_at (Pat `(if _ then _ else _) _ = _`) storage_copy_suffix_owned_path >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `storage_holds _ _ _ _ _ _ _`)) >>
  (impl_tac >- (asm_rewrite_tac[] >> simp[])) >> strip_tac >>
  `gas_marked_path F ctx func s 0 (OK z)` by
    metis_tac[gas_marked_path_then, arithmeticTheory.ADD_0] >>
  `~z.vs_halted` by metis_tac[copy_static_fields] >>
  `b < dimword(:256)` by (gvs[dimword_def] >> decide_tac) >>
  `expr_val_rel cx ty v op z` by
    (simp[expr_val_rel_def] >> qexists_tac `n2w b` >> gvs[w2n_n2w]) >>
  qexistsl_tac [`z`, `v`, `u`, `a`, `sm`, `buf`] >> gvs[]
QED
