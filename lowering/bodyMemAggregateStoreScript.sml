(* Memory-counted store continuation for aggregate children. *)
Theory bodyMemAggregateStore
Ancestors
  exprSimAggregateLoops
  bodyMemAggregateUnwrap bodyCopyMemory exprSimAggregateChildren
  exprLowering context compileEnv vyperTypeSystem vyperTypeCallGraph
  loweringPosts exprSimMemDefs exprSimProps exprSimBufferStore valueEncodingProps
  bodyDeclMemoryCore exprSimMemoryValues emitHelperProps emitHelper
  instMemFrontier memSafeRun fragExecMem exprLoweringProps venomInst venomState list rich_list

Theorem aggregate_mem_store_lowered_elem:
  !ce e env src dst.
    well_typed_expr env e /\
    (int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) ==>
    compile_store_memory ce src dst (expr_type e) (lowered_value_type ce e) =
    compile_store_memory ce src dst (expr_type e) (expr_type e)
Proof
  rpt gen_tac >> strip_tac >>
  `lowered_value_type ce e = expr_type e \/ is_bytestring_type (expr_type e)` by
    metis_tac[aggregate_elem_lowered_type] >>
  simp[compile_store_memory_def] >> gvs[]
QED

Theorem aggregate_store_memory_mem_ok:
  compile_store_memory ce src dst (expr_type e) (lowered_value_type ce e) sa = ((),sb) /\
  well_typed_expr env e /\
  (int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  expr_val_rel cx (expr_type e) v src s /\
  expr_store_bound cx (expr_type e) v src s /\
  type_memory_bytes ce (expr_type e) = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  eval_operand dst s = SOME d /\
  w2n d + type_memory_size tv <= s.vs_alloca_next /\
  (~is_word_type (expr_type e) /\ lowered_value_type ce e = expr_type e ==>
   !sw. eval_operand src s = SOME sw ==>
        type_memory_size tv = 0 \/ w2n sw + type_memory_size tv <= s.vs_alloca_next) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >> (
  `compile_store_memory ce src dst (expr_type e) (expr_type e) sa = ((),sb)` by
    metis_tac[aggregate_mem_store_lowered_elem] >>
  Cases_on `is_word_type (expr_type e)`
  >- (gvs[compile_store_memory_def] >>
      drule emitted_insts_emit_void >> strip_tac >>
      simp[run_inst_seq_mem_ok_last, below_frontier_MSTORE] >>
      `type_memory_size tv = 32` by metis_tac[word_tv_memory_size] >>
      gvs[]) >>
  `?sw. eval_operand src s = SOME sw /\
        val_in_memory tv v (w2n sw) s.vs_memory` by gvs[expr_val_rel_def] >>
  Cases_on `is_bytestring_type (expr_type e)`
  >- (`?len. mload (w2n sw) s = n2w len /\
             val_store_size tv v = 32 + 32 * word_size len` by
        metis_tac[buffer_typed_bytestring_header] >>
      `val_store_size tv v <= type_memory_size tv` by metis_tac[val_store_size_le] >>
      `w2n sw + val_store_size tv v <= s.vs_alloca_next` by
        (fs[expr_store_bound_def] >>
         qpat_x_assum `!tv'. _` (qspec_then `tv` mp_tac) >> simp[]) >>
      gvs[compile_store_memory_def] >>
      irule compile_store_bytestring_body_mem_ok >>
      qexistsl_tac [`d`, `dst`, `len`, `src`, `sw`] >> simp[] >>
      rpt strip_tac >> gvs[] >> decide_tac) >>
  `lowered_value_type ce e = expr_type e` by
    metis_tac[aggregate_elem_lowered_type] >>
  Cases_on `type_memory_size tv = 0`
  >- gvs[compile_store_memory_def, compile_copy_memory_def, comp_return_def,
         emitted_insts_def, run_inst_seq_mem_ok_def] >>
  `w2n sw + type_memory_size tv <= s.vs_alloca_next` by metis_tac[] >>
  gvs[compile_store_memory_def] >>
  irule compile_copy_memory_body_mem_ok >>
  qexistsl_tac [`d`, `dst`, `type_memory_size tv`, `src`, `sw`] >> simp[])
QED

Theorem aggregate_store_memory_no_gas:
  compile_store_memory ce src dst ty ty sa = ((),sb) ==>
  EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
    ~is_terminator i.inst_opcode) (emitted_insts sa sb)
Proof
  strip_tac >> Cases_on `is_word_type ty` >>
  Cases_on `is_bytestring_type ty` >>
  gvs[compile_store_memory_def, compile_store_bytestring_def,
      compile_bytestring_copy_len_def, compile_copy_memory_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def,
      emit_op_def, emit_void_def, fresh_id_def, fresh_var_def, emit_def] >>
  simp[emitted_insts_def, DROP_APPEND1, mk_inst_def, is_terminator_def] >>
  Cases_on `type_memory_bytes ce ty` >>
  gvs[compile_copy_memory_def, comp_return_def, emit_void_def,
      comp_bind_def, comp_ignore_bind_def, fresh_id_def, emit_def,
      emitted_insts_def, DROP_APPEND1, mk_inst_def, is_terminator_def]
QED

(* A shared concrete run endpoint is the boundary between the semantic
   rebased-store theorem and memory counting. *)
Theorem aggregate_store_memory_path_mem:
  compile_store_memory ce src dst (expr_type e) (lowered_value_type ce e) sa = ((),sb) /\
  well_typed_expr env e /\
  (int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  expr_val_rel cx (expr_type e) v src s /\
  expr_store_bound cx (expr_type e) v src s /\
  type_memory_bytes ce (expr_type e) = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  eval_operand dst s = SOME d /\
  w2n d + type_memory_size tv <= s.vs_alloca_next /\
  (~is_word_type (expr_type e) /\ lowered_value_type ce e = expr_type e ==>
   !sw. eval_operand src s = SOME sw ==>
        type_memory_size tv = 0 \/ w2n sw + type_memory_size tv <= s.vs_alloca_next) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  gas_path_mem ctx func s 0
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  alloca_history func (t with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  t.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> (
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    (irule aggregate_store_memory_mem_ok >>
     goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
     simp[] >> goal_assum (drule_at (Pat `evaluate_type _ _ = _`)) >>
     simp[] >> qexistsl_tac [`env`, `v`] >> fs[arithmeticTheory.ADD_COMM] >>
     first_assum ACCEPT_TAC) >>
  `compile_store_memory ce src dst (expr_type e) (expr_type e) sa = ((),sb)` by
    metis_tac[aggregate_mem_store_lowered_elem] >>
  drule_all (SRULE [] buffer_store_memory_encoding) >> strip_tac >>
  gvs[] >> rename1 `run_inst_seq _ s = OK t` >>
  `t.vs_alloca_next = s.vs_alloca_next` by
    (qpat_x_assum `_ with <|vs_memory := _; vs_vars := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  drule buffer_store_memory_shape >> strip_tac >>
  drule aggregate_store_memory_no_gas >> strip_tac >>
  drule_all exprSimMemUnwrapTheory.straight_path_mem >> simp[])
QED

Theorem aggregate_store_rebased_slice_mem_cursor:
  compile_store_memory ce op (Var x) (expr_type e) (lowered_value_type ce e) su = ((),sb) /\
  expr_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
    su r es' v op s /\
  not_fresh_at sm x /\ lookup_var x r = SOME w /\
  sm.cs_next_var <= su.cs_next_var /\
  (!z. op = Var z ==> not_fresh_at su z) /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce su /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce (expr_type e) = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  stmt_state_rel ctx func ce cx es' r /\
  (!n b k. local_region ce es'.scopes r n b k ==>
    b + k <= w2n w \/ w2n w + type_memory_size tv <= b) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n w) (type_memory_size tv)) /\
  well_typed_expr env e /\
  (int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) /\
  expr_store_bound cx (expr_type e) v op s /\
  w2n w + type_memory_size tv <= s.vs_alloca_next /\
  (~is_word_type (expr_type e) /\ lowered_value_type ce e = expr_type e ==>
   !sw. eval_operand op s = SOME sw ==>
        type_memory_size tv = 0 \/ w2n sw + type_memory_size tv <= s.vs_alloca_next) /\
  fn_has_code su sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\
  ~s.vs_halted /\ s.vs_current_bb = su.cs_current_bb /\
  s.vs_inst_idx = LENGTH su.cs_current_insts ==>
  ?q. gas_path_mem ctx func s 0 (OK q) /\
    val_in_memory tv v (w2n w) q.vs_memory /\
    stmt_state_rel ctx func ce cx es' q /\
    (!z a. not_fresh_at sm z /\ lookup_var z r = SOME a ==>
      lookup_var z q = SOME a) /\
    (!aid b. FLOOKUP r.vs_allocas aid = SOME b ==>
      FLOOKUP q.vs_allocas aid = SOME b) /\
    (!aid off sz a k.
      FLOOKUP r.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
      (!n b len. local_region ce es'.scopes r n b len ==>
        off + sz <= b \/ b + len <= off) /\
      off <= a /\ a + k <= off + sz /\
      (a + k <= w2n w \/ w2n w + type_memory_size tv <= a) ==>
      mem_bytes_at a k q.vs_memory = mem_bytes_at a k r.vs_memory) /\
    locals_kept ce es' es' r q /\
    q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func q /\ q.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> (
  `compile_store_memory ce op (Var x) (expr_type e) (expr_type e) su = ((),sb)` by
    metis_tac[aggregate_mem_store_lowered_elem] >>
  `eval_operand (Var x) s = SOME w` by
    (drule_at (Pos hd) expr_post_rebased_lookup >> simp[eval_operand_def]) >>
  `!z. op = Var z \/ Var x = Var z ==> not_fresh_at su z` by
    (rpt strip_tac >> gvs[] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  drule_all aggregate_store_rebased_slice_run >> strip_tac >>
  `expr_val_rel cx (expr_type e) v op s` by gvs[expr_post_def] >>
  `gas_path_mem ctx func s 0
     (OK (q with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
   alloca_history func (q with vs_inst_idx := LENGTH sb.cs_current_insts) /\
   q.vs_alloca_next = s.vs_alloca_next` by
    (irule aggregate_store_memory_path_mem >> simp[] >>
     goal_assum (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
     simp[] >> goal_assum (drule_at (Pat `evaluate_type _ _ = _`)) >>
     simp[] >> qexistsl_tac [`env`, `v`] >> simp[arithmeticTheory.ADD_COMM] >>
     conj_tac >- (rpt strip_tac >> gvs[] >> metis_tac[]) >>
     fs[arithmeticTheory.ADD_COMM]) >>
  `q.vs_current_bb = sb.cs_current_bb` by
    (drule_all (SRULE [] buffer_store_memory_encoding) >> strip_tac >>
     drule buffer_store_memory_shape >> strip_tac >>
     gvs[] >>
     qpat_x_assum `_ with <|vs_memory := _; vs_vars := _|> = s` mp_tac >>
     simp[venom_state_component_equality] >> strip_tac >>
     fs[same_blocks_def]) >>
  qexists_tac `q with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  fs[stmt_state_rel_inst_idx, lookup_var_def,
     arithmeticTheory.ADD_COMM] >>
  conj_tac >> first_assum ACCEPT_TAC)
QED

(* Compatibility interface: callers not needing the block may forget it. *)
Theorem aggregate_store_rebased_slice_mem:
  compile_store_memory ce op (Var x) (expr_type e) (lowered_value_type ce e) su = ((),sb) /\
  expr_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
    su r es' v op s /\
  not_fresh_at sm x /\ lookup_var x r = SOME w /\
  sm.cs_next_var <= su.cs_next_var /\
  (!z. op = Var z ==> not_fresh_at su z) /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce su /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce (expr_type e) = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  stmt_state_rel ctx func ce cx es' r /\
  (!n b k. local_region ce es'.scopes r n b k ==>
    b + k <= w2n w \/ w2n w + type_memory_size tv <= b) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n w) (type_memory_size tv)) /\
  well_typed_expr env e /\
  (int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) /\
  expr_store_bound cx (expr_type e) v op s /\
  w2n w + type_memory_size tv <= s.vs_alloca_next /\
  (~is_word_type (expr_type e) /\ lowered_value_type ce e = expr_type e ==>
   !sw. eval_operand op s = SOME sw ==>
        type_memory_size tv = 0 \/ w2n sw + type_memory_size tv <= s.vs_alloca_next) /\
  fn_has_code su sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ alloca_inv s /\
  ~s.vs_halted /\ s.vs_current_bb = su.cs_current_bb /\
  s.vs_inst_idx = LENGTH su.cs_current_insts ==>
  ?q. gas_path_mem ctx func s 0 (OK q) /\
    val_in_memory tv v (w2n w) q.vs_memory /\
    stmt_state_rel ctx func ce cx es' q /\
    (!z a. not_fresh_at sm z /\ lookup_var z r = SOME a ==>
      lookup_var z q = SOME a) /\
    (!aid b. FLOOKUP r.vs_allocas aid = SOME b ==>
      FLOOKUP q.vs_allocas aid = SOME b) /\
    (!aid off sz a k.
      FLOOKUP r.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
      (!n b len. local_region ce es'.scopes r n b len ==>
        off + sz <= b \/ b + len <= off) /\
      off <= a /\ a + k <= off + sz /\
      (a + k <= w2n w \/ w2n w + type_memory_size tv <= a) ==>
      mem_bytes_at a k q.vs_memory = mem_bytes_at a k r.vs_memory) /\
    locals_kept ce es' es' r q /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func q /\ q.vs_alloca_next = s.vs_alloca_next
Proof
  disch_tac >> mp_tac aggregate_store_rebased_slice_mem_cursor >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  strip_tac >> qexists_tac `q` >> fs[] >> first_assum ACCEPT_TAC
QED
