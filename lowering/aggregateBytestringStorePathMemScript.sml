(* Counted bytestring stores depend on the actual payload, not source capacity. *)
Theory aggregateBytestringStorePathMem
Ancestors
  typedCopyPrimitivePathMem typedCopyAgreement exprSimMemDefs exprSimBufferStore exprSimProps
  loweringPosts exprLowering typedMemoryCopy context compileEnv venomState
  exprSimAggregateChildren fragGasPathFrameMem bodyMemAggregatePath exprLoweringProps

Theorem aggregate_bytestring_store_path_mem[local]:
  is_bytestring_type ty /\ ~is_word_type ty /\
  compile_store_memory ce src dst ty sty sa = ((),sb) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  expr_val_rel cx ty v src s /\ expr_store_bound cx ty v src s /\
  type_memory_size tv < dimword(:256) /\
  eval_operand dst s = SOME d /\
  w2n d + type_memory_size tv <= s.vs_alloca_next /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?q. gas_path_mem ctx fn s 0 (OK (q with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    val_in_memory tv v (w2n d) q.vs_memory /\
    (!a k. a+k <= w2n d \/ w2n d + type_memory_size tv <= a ==>
      mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) /\
    (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x s)
Proof
  strip_tac >>
  `?p. eval_operand src s = SOME p /\ val_in_memory tv v (w2n p) s.vs_memory` by
    gvs[expr_val_rel_def] >>
  `?len. mload (w2n p) s = n2w len /\
    val_store_size tv v = 32 + 32 * word_size len` by
    metis_tac[buffer_typed_bytestring_header] >>
  `val_store_size tv v <= type_memory_size tv` by metis_tac[val_store_size_le] >>
  `w2n p + val_store_size tv v <= s.vs_alloca_next` by
    (fs[expr_store_bound_def] >>
     qpat_x_assum `!tv'. _` (qspec_then `tv` mp_tac) >> simp[]) >>
  `compile_store_memory_typed ce dst ty src ty sa = ((),sb)` by
    gvs[compile_store_memory_def, compile_store_memory_typed_bytes] >>
  `32 + 32 * word_size len < dimword(:256) /\
   w2n p + (32 + 32 * word_size len) <= s.vs_alloca_next /\
   w2n d + (32 + 32 * word_size len) <= s.vs_alloca_next /\
   val_footprint tv v <= 32 + 32 * word_size len` by
    (mp_tac (Q.SPECL [`tv`,`v`] val_footprint_le_store_size) >> decide_tac) >>
  drule_all normalize_bytestring_window_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists `q` >> simp[] >> rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Theorem aggregate_bytestring_rebased_store_path_mem:
  post_value_type ce e = expr_type e /\
  is_bytestring_type (expr_type e) /\ ~is_word_type (expr_type e) /\
  compile_store_memory ce op dst (expr_type e) sty su = ((),sb) /\
  expr_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
    su r es' v op s /\
  sm.cs_next_var <= su.cs_next_var /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce su /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  expr_store_bound cx (expr_type e) v op s /\
  type_memory_size tv < dimword(:256) /\
  eval_operand dst s = SOME dw /\
  w2n dw + type_memory_size tv <= s.vs_alloca_next /\
  (!x. op = Var x \/ dst = Var x ==> not_fresh_at su x) /\
  (!name b k. local_region ce es'.scopes s name b k ==>
    b+k <= w2n dw \/ w2n dw + type_memory_size tv <= b) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n dw) (type_memory_size tv)) /\
  fn_has_code su sb func /\ fn_inst_ids_distinct func /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = su.cs_current_bb /\
  s.vs_inst_idx = LENGTH su.cs_current_insts ==>
  ?q. gas_path_mem ctx func s 0 (OK q) /\
    val_in_memory tv v (w2n dw) q.vs_memory /\
    stmt_state_rel ctx func ce cx es' q /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!z a. not_fresh_at sm z /\ lookup_var z r = SOME a ==> lookup_var z q = SOME a) /\
    (!aid b. FLOOKUP r.vs_allocas aid = SOME b ==> FLOOKUP q.vs_allocas aid = SOME b) /\
    (!aid off sz a len.
      FLOOKUP r.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
      (!name b k. local_region ce es'.scopes r name b k ==>
        off+sz <= b \/ b+k <= off) /\
      off <= a /\ a+len <= off+sz /\
      (a+len <= w2n dw \/ w2n dw+type_memory_size tv <= a) ==>
      mem_bytes_at a len q.vs_memory = mem_bytes_at a len r.vs_memory) /\
    locals_kept ce es' r q /\ alloca_history func q /\
    q.vs_alloca_next = s.vs_alloca_next
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_val_rel cx (expr_type e) v op s` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `post_value_type ce e = _`
       (fn th => rewrite_tac[expr_post_def, th]) >>
     rpt strip_tac >> first_assum ACCEPT_TAC) >>
  drule_all aggregate_bytestring_store_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qabbrev_tac `t = q with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `LENGTH s.vs_memory <= LENGTH t.vs_memory` by
    metis_tac[fragGasPathFrameMemTheory.gas_path_mem_memory_length] >>
  `(t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
    vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
    vs_inst_idx := s.vs_inst_idx|>) = s` by
    (simp[Abbr `t`, venom_state_component_equality] >>
     fs[venom_state_component_equality]) >>
  `!z. not_fresh_at su z ==> lookup_var z t = lookup_var z s` by
    (simp[Abbr `t`, lookup_var_def] >> metis_tac[lookup_var_def]) >>
  `!a len. a+len <= w2n dw \/ w2n dw+type_memory_size tv <= a ==>
    mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory` by
    (simp[Abbr `t`] >> gvs[]) >>
  drule_all exprSimAggregateChildrenTheory.aggregate_store_rebased_control_frame >> strip_tac >>
  `alloca_inv s` by gvs[expr_post_def, stmt_state_rel_def, state_rel_def] >>
  `alloca_history func t` by
    (irule fragGasPathFrameMemTheory.gas_path_mem_zero_history >> simp[] >>
     metis_tac[bodyMemAggregatePathTheory.aggregate_mem_path_alloca_inv]) >>
  qexists `t` >> simp[] >>
  gvs[Abbr `t`, venom_state_component_equality, arithmeticTheory.ADD_COMM] >>
  conj_tac
  >- (`compile_store_memory ce op dst (expr_type e) (expr_type e) su = ((),sb)` by
        gvs[compile_store_memory_def] >>
      drule buffer_store_memory_shape >> simp[same_blocks_def]) >>
  first_assum ACCEPT_TAC
QED
