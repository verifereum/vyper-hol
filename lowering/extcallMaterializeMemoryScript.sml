(* Counted allocate/unwrap/store execution for nonword call defaults. *)
Theory extcallMaterializeMemory
Ancestors
  extcallStoreUnwrapMemory extcallAllocMemory bodyMemAggregateBounds
  bodyMemAggregateStore bodyDeclCopyMemory bodyDeclMemoryCore exprSimVVFrame
  exprSimIfExp exprSimBufferStore exprSimMemUnwrap fragGasPathMem
  exprLoweringProps exprLowering compileEnv exprSimMemDefs memSafeRun
  context fragExecMem loweringPosts venomState words list
  bodyMemAssignAttrStorage exprSimDefs

Theorem extcall_materialize_store_mem_ok[local]:
  compile_store_memory ce src dst lt lt sa = ((),sb) /\
  ~is_word_type lt /\ evaluate_type (get_tenv cx) lt = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  expr_val_rel cx lt v src s /\ expr_store_bound cx lt v src s /\
  type_memory_bytes ce lt = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  eval_operand dst s = SOME d /\
  w2n d + type_memory_size tv <= s.vs_alloca_next /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >>
  `?w. eval_operand src s = SOME w /\
    val_in_memory tv v (w2n w) s.vs_memory` by
    gvs[expr_val_rel_def] >>
  Cases_on `val_store_size tv v = 0`
  >- (`type_memory_size tv = 0` by
        (qspecl_then [`tv`, `v`] mp_tac val_store_size_pos >> simp[]) >>
      `~is_bytestring_type lt` by
        (strip_tac >> drule_all ifexp_copy_source_bounds >>
         strip_tac >> gvs[]) >>
      gvs[compile_store_memory_def, compile_copy_memory_def,
          comp_return_def, emitted_insts_def, run_inst_seq_mem_ok_def]) >>
  `w2n w + val_store_size tv v <= s.vs_alloca_next` by
    gvs[expr_store_bound_def] >>
  irule body_typed_store_memory_mem_ok >>
  goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
  qexistsl_tac [`d`, `get_tenv cx`, `tv`, `v`, `w`] >> simp[] >>
  first_assum ACCEPT_TAC
QED

Theorem extcall_materialize_store_path[local]:
  compile_store_memory ce src dst lt lt sa = ((),sb) /\
  ~is_word_type lt /\ evaluate_type (get_tenv cx) lt = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  expr_val_rel cx lt v src s /\ expr_store_bound cx lt v src s /\
  type_memory_bytes ce lt = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  eval_operand dst s = SOME d /\
  w2n d + type_memory_size tv <= s.vs_alloca_next /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?q. run_inst_seq (emitted_insts sa sb) s = OK q /\
    gas_path_mem ctx func s 0
      (OK (q with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    alloca_history func (q with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    val_in_memory tv v (w2n d) q.vs_memory /\
    (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s) /\
    (!a k. a + k <= w2n d \/ w2n d + type_memory_size tv <= a ==>
      mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) /\
    LENGTH s.vs_memory <= LENGTH q.vs_memory /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb
Proof
  strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (drule_all extcall_materialize_store_mem_ok >> simp[]) >>
  drule_all buffer_store_memory_encoding >> strip_tac >>
  drule_all buffer_store_memory_capacity >> strip_tac >>
  drule buffer_store_memory_shape >> strip_tac >>
  drule aggregate_store_memory_no_gas >> strip_tac >>
  drule_all straight_path_mem >> strip_tac >>
  qexists_tac `q` >> simp[] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem extcall_materialize_alloc_value[local]:
  compile_alloc_buffer sz sa = (buf,sm) /\ fn_has_code sa sm func /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ sz < dimword (:256) /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  vv_holds ce cx lt (Value v) vv es s /\
  vv_store_bound cx lt lt es (Value v) vv s /\
  vv_storage_live cx vv es s /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) ==>
  ?u w. gas_path_mem ctx func s 0 (OK u) /\
    ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
    u.vs_inst_idx = LENGTH sm.cs_current_insts /\
    stmt_state_rel ctx func ce cx es u /\ alloca_history func u /\
    eval_operand buf.buf_operand u = SOME w /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
    w2n w + sz < dimword (:256) /\ w2n w + sz <= u.vs_alloca_next /\
    vv_holds ce cx lt (Value v) vv es u /\
    vv_store_bound cx lt lt es (Value v) vv u /\
    vv_storage_live cx vv es u /\ u.vs_memory = s.vs_memory /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sa.cs_next_id /\
       FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
       regions_disjoint (w2n w) sz b len) /\
    (!name b len. local_region ce es.scopes u name b len ==>
       regions_disjoint (w2n w) sz b len) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sm p) /\
    s.vs_alloca_next <= u.vs_alloca_next /\
    contract_storage u = contract_storage s /\
    contract_transient u = contract_transient s /\ u.vs_labels = s.vs_labels /\
    (?q. run_inst_seq (emitted_insts sa sm) s = OK q /\
         u = q with vs_inst_idx := LENGTH sm.cs_current_insts)
Proof
  strip_tac >>
  `eval_operand (Lit 0w) s = SOME 0w` by simp[eval_operand_def] >>
  `!x. Lit 0w = Var x ==> not_fresh_at sa x` by simp[] >>
  drule_all alloc_buffer_source_path_mem_endpoint >> strip_tac >>
  `eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) s` by
    (Cases_on `vv_operand vv` >> simp[eval_operand_def] >> metis_tac[]) >>
  `vv_holds ce cx lt (Value v) vv es u` by
    (drule_all vv_holds_vars_frame >> simp[]) >>
  `vv_store_bound cx lt lt es (Value v) vv u` by
    (drule_all vv_store_bound_frame_mem_src >> simp[]) >>
  `vv_storage_live cx vv es u` by
    (Cases_on `vv` >> gvs[vv_operand_def]) >>
  qexistsl_tac [`u`, `w`] >> simp[] >> metis_tac[]
QED

Theorem extcall_materialize_store_result:
  compile_store_memory ce src dst lt lt sa = ((),sb) /\
  ~is_word_type lt /\ evaluate_type (get_tenv cx) lt = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  expr_val_rel cx lt v src s /\ expr_store_bound cx lt v src s /\
  type_memory_bytes ce lt = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  eval_operand dst s = SOME d /\
  w2n d + type_memory_size tv <= s.vs_alloca_next /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sa /\
  (!name b sz. local_region ce es.scopes s name b sz ==>
    b + sz <= w2n d \/ w2n d + type_memory_size tv <= b) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n d) (type_memory_size tv)) /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?z. gas_path_mem ctx func s 0 (OK z) /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand dst z = SOME d /\
    w2n d + type_memory_size tv <= z.vs_alloca_next /\
    expr_val_rel cx lt v dst z /\ expr_store_bound cx lt v dst z /\
    stmt_state_rel ctx func ce cx es z /\ alloca_history func z /\
    z.vs_alloca_next = s.vs_alloca_next /\ z.vs_allocas = s.vs_allocas /\
    (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s) /\
    (!a k. a + k <= w2n d \/ w2n d + type_memory_size tv <= a ==>
      mem_bytes_at a k z.vs_memory = mem_bytes_at a k s.vs_memory) /\
    LENGTH s.vs_memory <= LENGTH z.vs_memory
Proof
  strip_tac >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  drule_all extcall_materialize_store_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `stmt_state_rel ctx func ce cx es q` by
    (irule buffer_store_state_frame >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ s`)) >>
     qexistsl_tac [`w2n d`, `type_memory_size tv`, `sa`] >>
     simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `eval_operand dst q = eval_operand dst s` by
    (irule literal_operand_frame >> simp[] >>
     qexists_tac `sa` >> simp[] >> metis_tac[]) >>
  `q.vs_alloca_next = s.vs_alloca_next /\ q.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `_ with <|vs_vars := _; vs_memory := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `val_store_size tv v <= type_memory_size tv` by
    metis_tac[exprSimPropsTheory.val_store_size_le] >>
  `w2n d + val_store_size tv v <= s.vs_alloca_next` by decide_tac >>
  qexists_tac `q with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  gvs[stmt_state_rel_inst_idx, lookup_var_def, eval_operand_def,
      expr_val_rel_def, expr_store_bound_def] >>
  first_assum ACCEPT_TAC
QED

Theorem extcall_materialize_stages[local]:
  compile_materialize_vv ce lt vv sa = (op,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved ce sa /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) ==>
  ?buf sm src su.
    compile_alloc_buffer (type_memory_bytes ce lt) sa = (buf,sm) /\
    unwrap_value ce vv sm = (src,su) /\
    compile_store_memory ce src buf.buf_operand lt lt su = ((),sb) /\
    op = buf.buf_operand /\
    fn_has_code sa sm func /\ fn_has_code sm su func /\
    fn_has_code su sb func /\
    ci_mono sa sm /\ ci_mono sm su /\ ci_mono su sb /\
    local_ptrs_reserved ce sm /\ local_ptrs_reserved ce su /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
    (!x. src = Var x \/ op = Var x ==> not_fresh_at su x) /\
    (!x. op = Var x ==> not_fresh_at sm x)
Proof
  strip_tac >>
  Cases_on `compile_alloc_buffer (type_memory_bytes ce lt) sa` >>
  rename1 `compile_alloc_buffer _ sa = (buf,sm)` >>
  Cases_on `unwrap_value ce vv sm` >>
  rename1 `unwrap_value ce vv sm = (src,su)` >>
  Cases_on `compile_store_memory ce src buf.buf_operand lt lt su` >>
  Cases_on `q` >>
  gvs[compile_materialize_vv_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, pairTheory.pair_case_eq] >>
  rename1 `compile_store_memory ce src buf.buf_operand lt lt su = ((),sb)` >>
  `ci_mono sa sm /\ ci_mono sm su /\ ci_mono su sb` by
    (mp_tac ci_mono_compile_alloc_buffer >>
     mp_tac ci_mono_unwrap_value >> mp_tac ci_mono_compile_store_memory >>
     metis_tac[pairTheory.SND]) >>
  `fn_has_code sa sm func /\ fn_has_code sm su func /\
   fn_has_code su sb func` by
    (fs[ci_mono_def] >> metis_tac[fragExecTheory.fn_has_code_split,
                               cs_extends_trans]) >>
  `local_ptrs_reserved ce sm /\ local_ptrs_reserved ce su` by
    (fs[ci_mono_def] >> metis_tac[local_ptrs_reserved_next_var]) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    (fs[ci_mono_def] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `!x. src = Var x ==> not_fresh_at su x` by
    (drule exprOperandVarTheory.compiler_unwrap_value_var >>
     Cases_on `vv` >> gvs[vv_operand_def]) >>
  drule loweringHaltTheory.compile_alloc_buffer_parts >> strip_tac >>
  simp[] >>
  fs[ci_mono_def] >> metis_tac[freshWritesTheory.not_fresh_at_mono]
QED

Theorem extcall_materialize_vv_mem:
  compile_materialize_vv ce lt vv sa = (op,sb) /\
  ~is_word_type lt /\ fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sa /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  vv_holds ce cx lt (Value v) vv es s /\
  vv_store_bound cx lt lt es (Value v) vv s /\
  vv_storage_live cx vv es s /\
  evaluate_type (get_tenv cx) lt = SOME tv /\ val_wf tv v /\
  value_has_type tv v /\
  type_memory_bytes ce lt = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sa x) /\
  (!tag p. vv = LocatedValue tag p ==>
    (p.ptr_location <> LocMemory \/ is_word_type tag ==> tag = lt) /\
    (p.ptr_location = LocCode /\ ce.ce_is_ctor ==>
      !region. ce.ce_imm_alloca = SOME region ==>
        eval_operand region s = SOME 0w /\
        (!x. region = Var x ==> not_fresh_at sa x))) ==>
  ?z w. gas_path_mem ctx func s 0 (OK z) /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand op z = SOME w /\
    w2n w + type_memory_size tv <= z.vs_alloca_next /\
    expr_val_rel cx lt v op z /\ expr_store_bound cx lt v op z /\
    stmt_state_rel ctx func ce cx es z /\ alloca_history func z /\
    s.vs_alloca_next <= z.vs_alloca_next /\
    (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP z.vs_allocas aid = SOME entry) /\
    (!aid b sz off len. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
      aid < sa.cs_next_id /\ b <= off /\ off + len <= b + sz ==>
      mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
    (!name b sz off len. local_region ce es.scopes s name b sz /\
      b <= off /\ off + len <= b + sz ==>
      mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
    (!name io itv iv off len. ce.ce_is_ctor /\
      FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
      FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) /\
      io <= off /\ off + len <= io + type_memory_size itv ==>
      mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory)
Proof
  strip_tac >> drule_all extcall_materialize_stages >> strip_tac >>
  `type_memory_bytes ce lt < dimword (:256)` by simp[] >>
  drule_all extcall_materialize_alloc_value >> strip_tac >>
  suspend "unwrap"
QED

Resume extcall_materialize_vv_mem[unwrap]:
  qpat_x_assum `u = _ with vs_inst_idx := _` kall_tac >>
  `read_result cx (Value v) es = (INL v,es)` by EVAL_TAC >>
  `!tag src. vv = StackValue tag src ==>
    !x. src = Var x ==> not_fresh_at sm x` by
    (rpt strip_tac >> gvs[vv_operand_def]) >>
  `!tag ptr. vv = LocatedValue tag ptr ==>
    (ptr.ptr_location <> LocMemory \/ is_word_type tag \/ is_word_type lt ==> tag = lt) /\
    (!x. ptr.ptr_operand = Var x ==> not_fresh_at sm x) /\
    (ptr.ptr_location <> LocMemory ==> lt = lt) /\
    (is_word_type lt /\ ptr.ptr_location = LocMemory ==>
      !a. eval_operand ptr.ptr_operand u = SOME a ==>
        w2n a + 32 <= u.vs_alloca_next) /\
    (ptr.ptr_location = LocCode /\ ce.ce_is_ctor ==>
      !region. ce.ce_imm_alloca = SOME region ==>
        eval_operand region u = SOME 0w /\
        (!x. region = Var x ==> not_fresh_at sm x))` by
    (map_every qx_gen_tac [`tag`, `ap`] >> strip_tac >>
     `!x. ap.ptr_operand = Var x ==> not_fresh_at sm x` by
       gvs[vv_operand_def] >>
     simp[] >> rpt strip_tac
     >- metis_tac[]
     >- (`eval_operand region u = eval_operand region s` by
           (Cases_on `region` >> simp[eval_operand_def] >> metis_tac[]) >> metis_tac[]) >>
     fs[ci_mono_def] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  drule_all extcall_captured_unwrap_mem >> strip_tac >>
  suspend "store"
QED
Resume extcall_materialize_vv_mem[store]:
  `eval_operand buf.buf_operand z = SOME w` by
    (simp[eval_operand_def] >>
     qpat_x_assum `eval_operand buf.buf_operand u = SOME w` mp_tac >>
     simp[eval_operand_def] >> metis_tac[]) >>
  `w2n w + type_memory_size tv <= z.vs_alloca_next` by decide_tac >>
  `!name b sz. local_region ce es.scopes z name b sz ==>
    b + sz <= w2n w \/ w2n w + type_memory_size tv <= b` by
    (rpt strip_tac >>
     `local_region ce es.scopes u name b sz` by
       metis_tac[exprSimCopyTheory.copy_buffer_local_region_frame] >>
     qpat_x_assum `!name b len. local_region ce es.scopes u name b len ==> _`
       (qspecl_then [`name`, `b`, `sz`] mp_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
  `ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n w) (type_memory_size tv)` by
    (rpt strip_tac >>
     drule_all extcall_alloc_immutable_separation >>
     fs[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
  `!x. src = Var x \/ buf.buf_operand = Var x ==> not_fresh_at su x` by
    metis_tac[] >>
  drule_all extcall_materialize_store_result >> strip_tac >>
  suspend "join"
QED
Resume extcall_materialize_vv_mem[join]:
  `gas_path_mem ctx func s 0 (OK z')` by
    (qpat_assum `gas_path_mem ctx func s 0 (OK u)`
       (mp_then Any mp_tac gas_path_mem_then) >>
     disch_then drule >> simp[] >> strip_tac >>
     qpat_assum `gas_path_mem ctx func s 0 (OK z)`
       (mp_then Any mp_tac gas_path_mem_then) >>
     disch_then drule >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x /\ not_fresh_at su x` by
    (fs[ci_mono_def] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `sa.cs_next_id < sm.cs_next_id` by
    (drule loweringHaltTheory.compile_alloc_buffer_parts >> simp[]) >>
  `!name b sz. local_region ce es.scopes s name b sz ==>
    local_region ce es.scopes u name b sz` by
    metis_tac[exprSimCopyTheory.copy_buffer_local_region_frame] >>
  qexistsl_tac [`z'`, `w`] >> simp[] >>
  suspend "frames"
QED
Resume extcall_materialize_vv_mem[frames]:
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- suspend "registered" >>
  conj_tac >- suspend "locals" >>
  suspend "immutables"
QED
Resume extcall_materialize_vv_mem[registered]:
  map_every qx_gen_tac [`aid`, `b`, `sz`, `off`, `len`] >> strip_tac >>
  `regions_disjoint (w2n w) (type_memory_size tv) b sz` by metis_tac[] >>
  `off + len <= w2n w \/ w2n w + type_memory_size tv <= off` by
    (fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `mem_bytes_at off len z'.vs_memory = mem_bytes_at off len z.vs_memory` by
    (qpat_x_assum `!a k. _ ==> mem_bytes_at a k z'.vs_memory = _`
       (qspecl_then [`off`, `len`] irule) >> simp[]) >>
  `mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory` by
    (`aid < sm.cs_next_id` by decide_tac >>
     `FLOOKUP u.vs_allocas aid = SOME (b,sz)` by metis_tac[] >>
     qpat_x_assum `!aid b sz off len. _ ==> mem_bytes_at off len z.vs_memory = _`
       (qspecl_then [`aid`, `b`, `sz`, `off`, `len`] irule) >>
     qexistsl_tac [`aid`, `b`, `sz`] >> simp[]) >>
  simp[]
QED
Resume extcall_materialize_vv_mem[locals]:
  map_every qx_gen_tac [`name`, `b`, `sz`, `off`, `len`] >> strip_tac >>
  `local_region ce es.scopes u name b sz` by metis_tac[] >>
  `regions_disjoint (w2n w) (type_memory_size tv) b sz` by metis_tac[] >>
  `off + len <= w2n w \/ w2n w + type_memory_size tv <= off` by
    (fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `mem_bytes_at off len z'.vs_memory = mem_bytes_at off len z.vs_memory` by
    (qpat_x_assum `!a k. _ ==> mem_bytes_at a k z'.vs_memory = _`
       (qspecl_then [`off`, `len`] irule) >> simp[]) >>
  `mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory` by
    (qpat_x_assum `!name b sz off len. _ ==> mem_bytes_at off len z.vs_memory = _`
       (qspecl_then [`name`, `b`, `sz`, `off`, `len`] mp_tac) >> simp[]) >>
  simp[]
QED
Resume extcall_materialize_vv_mem[immutables]:
  map_every qx_gen_tac [`name`, `io`, `itv`, `iv`, `off`, `len`] >> strip_tac >>
  `regions_disjoint io (type_memory_size itv) (w2n w) (type_memory_size tv)` by
    metis_tac[] >>
  `off + len <= w2n w \/ w2n w + type_memory_size tv <= off` by
    (fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `mem_bytes_at off len z'.vs_memory = mem_bytes_at off len z.vs_memory` by
    (qpat_x_assum `!a k. _ ==> mem_bytes_at a k z'.vs_memory = _`
       (qspecl_then [`off`, `len`] irule) >> simp[]) >>
  `mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory` by
    (qpat_x_assum `!name io itv iv off len. _ ==> mem_bytes_at off len z.vs_memory = _`
       (qspecl_then [`name`, `io`, `itv`, `iv`, `off`, `len`] mp_tac) >> simp[]) >>
  simp[]
QED
Finalise extcall_materialize_vv_mem
