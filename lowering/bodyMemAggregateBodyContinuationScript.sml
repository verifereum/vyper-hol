(* Physical-post aggregate relayout with the child's rebased frame. *)
Theory bodyMemAggregateBodyContinuation
Ancestors
  bodyMemAggregatePhysicalRead bodyMemAggregateTypedStore wideningZeroLayout
  aggregateBytestringStorePathMem
  exprSimAggregateChildren exprSimHyps exprSimHypsDefs typedMemoryCopy
  exprLoweringProps loweringPosts compileEnv context venomState externalNormalizePremises
  vyperInterpreter vyperState fragGasPathMem

(* A layout-equal tuple is stored by a bulk copy of its whole window. *)
Theorem aggregate_layout_copy_path_mem[local]:
  compile_copy_memory dst src (type_memory_size tv) sa = ((),sb) /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  type_memory_size tv < dimword (:256) /\
  w2n p + type_memory_size tv <= s.vs_alloca_next /\
  w2n d + type_memory_size tv <= s.vs_alloca_next /\
  val_in_memory tv v (w2n p) s.vs_memory /\ val_wf tv v /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?q. gas_path_mem ctx fn s 0 (OK (q with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    val_in_memory tv v (w2n d) q.vs_memory /\
    (!a k. a + k <= w2n d \/ w2n d + type_memory_size tv <= a ==>
      mem_bytes_at a k q.vs_memory = mem_bytes_at a k s.vs_memory) /\
    (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory|>) = s /\
    (!x. lookup_var x q = lookup_var x s)
Proof
  strip_tac >>
  Cases_on `type_memory_size tv = 0`
  >- (mp_tac (INST [``d:num`` |-> ``w2n (d:bytes32)``,
                    ``p:num`` |-> ``w2n (p:bytes32)``]
                typedCopyPrimitivePathMemTheory.normalize_empty_window_path_mem) >>
      gvs[] >> strip_tac >> qexists `s` >>
      simp[venom_state_component_equality]) >>
  `emit_void MCOPY [dst; src; Lit (n2w (type_memory_size tv))] sa = ((),sb)` by
    (Cases_on `type_memory_size tv` >> gvs[compile_copy_memory_def]) >>
  `val_footprint tv v <= type_memory_size tv` by
    metis_tac[exprSimPropsTheory.val_footprint_le] >>
  mp_tac (INST [``n:num`` |-> ``type_memory_size tv``]
            typedCopyPrimitivePathMemTheory.normalize_bulk_window_path_mem) >>
  simp[]
QED

Theorem aggregate_body_physical_store_path_mem:
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  expr_body_pre ce cx env e es /\
  (do res <- eval_expr cx e; read_result cx res od) es = (INL v,es') /\
  post_value_type ce e <> expr_type e /\
  compile_store_memory ce op dst (expr_type e) (lowered_value_type ce e) su = ((),sb) /\
  expr_post H ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
    su r es' v op s /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME dtv /\
  value_has_type dtv v /\ val_wf dtv v /\
  (!stv sw. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
    eval_operand op s = SOME sw ==>
    w2n sw + type_memory_size stv <= s.vs_alloca_next) /\
  eval_operand dst s = SOME dw /\
  FLOOKUP s.vs_allocas did = SOME (b,k) /\ did < sa.cs_next_id /\
  b <= w2n dw /\ w2n dw + type_memory_size dtv <= b+k /\
  w2n dw + type_memory_size dtv <= s.vs_alloca_next /\
  w2n dw + type_memory_size dtv < dimword(:256) /\
  fn_has_code su sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = su.cs_current_bb /\
  s.vs_inst_idx = LENGTH su.cs_current_insts /\
  (!x. dst = Var x \/ op = Var x ==> not_fresh_at su x) /\
  sm.cs_next_var <= su.cs_next_var /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce su /\
  (!name a n. local_region ce es'.scopes s name a n ==>
    a+n <= w2n dw \/ w2n dw + type_memory_size dtv <= a) /\
  (ce.ce_is_ctor ==> !name tv v off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv,v) ==>
    regions_disjoint off (type_memory_size tv) (w2n dw) (type_memory_size dtv)) /\
  alloca_history func s ==>
  ?q. gas_path_mem ctx func s 0 (OK q) /\
    val_in_memory dtv v (w2n dw) q.vs_memory /\
    stmt_state_rel H ctx func ce cx es' q /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!z a. not_fresh_at sm z /\ lookup_var z r = SOME a ==> lookup_var z q = SOME a) /\
    (!aid a. FLOOKUP r.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
    (!aid off sz a len.
      FLOOKUP r.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
      (!name b k. local_region ce es'.scopes r name b k ==>
        off+sz <= b \/ b+k <= off) /\
      off <= a /\ a+len <= off+sz /\
      (a+len <= w2n dw \/ w2n dw+type_memory_size dtv <= a) ==>
      mem_bytes_at a len q.vs_memory = mem_bytes_at a len r.vs_memory) /\
    locals_kept ce es' es' r q /\ alloca_history func q /\
    q.vs_alloca_next = s.vs_alloca_next /\
    q.vs_accounts = s.vs_accounts /\ q.vs_transient = s.vs_transient /\
    q.vs_requests = s.vs_requests /\ q.vs_call_ctx = s.vs_call_ctx
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e)` by
    metis_tac[post_value_type_word, post_value_type_bytestring] >>
  `~is_word_type (post_value_type ce e)` by
    (fs[expr_body_pre_def] >>
     metis_tac[post_value_type_widens, return_source_word_widens_eq]) >>
  drule_all aggregate_child_physical_encoding >> strip_tac >>
  `~is_bytestring_type (post_value_type ce e)` by
    metis_tac[externalNormalizePremisesTheory.normalize_return_source_kinds] >>
  `post_value_type ce e = lowered_value_type ce e` by
    (Cases_on `e` >> gvs[post_value_type_def, vyperASTTheory.expr_type_def] >>
     rename1 `Call _ tgt _ _` >> Cases_on `tgt` >> gvs[post_value_type_def, vyperASTTheory.expr_type_def]) >>
  `expr_val_at ce cx (post_value_type ce e)
     (sa with cs_next_var := sm.cs_next_var) su es' v op s /\
   stmt_state_rel H ctx func ce cx es' s` by fs[expr_post_def] >>
  `did < (sa with cs_next_var := sm.cs_next_var).cs_next_id` by simp[] >>
  drule_all aggregate_physical_source_slot_bounds >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `w2n sw + type_memory_size stv <= s.vs_alloca_next` by metis_tac[] >>
  Cases_on `tuple_memory_layout_eq (expr_type e) (lowered_value_type ce e)`
  >- (`compile_copy_memory dst op (type_memory_bytes ce (expr_type e)) su =
        ((),sb)` by
        (qpat_x_assum `compile_store_memory _ _ _ _ _ _ = _` mp_tac >>
         simp[compile_store_memory_def]) >>
      `type_memory_bytes ce (expr_type e) = type_memory_size dtv` by
        (irule typedMemoryCopyTheory.typed_copy_memory_size >>
         qexists `get_tenv cx` >> simp[] >> metis_tac[]) >>
      `type_memory_bytes ce (lowered_value_type ce e) = type_memory_size stv` by
        (irule typedMemoryCopyTheory.typed_copy_memory_size >>
         qexists `get_tenv cx` >> fs[] >> metis_tac[]) >>
      `type_memory_size stv = type_memory_size dtv` by
        metis_tac[memoryLayoutDefsTheory.tuple_memory_layout_eq_bytes] >>
      `tuple_memory_layout_eq (expr_type e) (post_value_type ce e)` by fs[] >>
      drule_all aggregate_child_tuple_layout_val_rel >> strip_tac >>
      `val_in_memory dtv v (w2n sw) s.vs_memory` by
        (qpat_x_assum `expr_val_rel _ _ _ _ _` mp_tac >>
         simp[expr_val_rel_def]) >>
      `w2n sw + type_memory_size dtv <= s.vs_alloca_next /\
       type_memory_size dtv < dimword (:256)` by fs[] >>
      `compile_copy_memory dst op (type_memory_size dtv) su = ((),sb)` by fs[] >>
      drule_all aggregate_layout_copy_path_mem >>
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
        (simp[Abbr `t`, lookup_var_def] >> fs[lookup_var_def]) >>
      `!a len. a+len <= w2n dw \/ w2n dw+type_memory_size dtv <= a ==>
        mem_bytes_at a len t.vs_memory = mem_bytes_at a len s.vs_memory` by
        (simp[Abbr `t`] >> gvs[]) >>
      drule_all exprSimAggregateChildrenTheory.aggregate_store_rebased_control_frame >>
      strip_tac >>
      `alloca_inv s` by
        (qpat_x_assum `stmt_state_rel H ctx func ce cx es' s` mp_tac >>
         simp[stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def]) >>
      `alloca_history func t` by
        (irule fragGasPathFrameMemTheory.gas_path_mem_zero_history >> simp[] >>
         metis_tac[bodyMemAggregatePathTheory.aggregate_mem_path_alloca_inv]) >>
      `compile_store_memory ce op dst (expr_type e) (expr_type e) su = ((),sb)` by
        simp[compile_store_memory_def] >>
      drule exprSimBufferStoreTheory.buffer_store_memory_shape >> strip_tac >>
      qexists `t` >> simp[] >>
      gvs[Abbr `t`, venom_state_component_equality, arithmeticTheory.ADD_COMM,
          exprLoweringPropsTheory.same_blocks_def] >>
      first_assum ACCEPT_TAC) >>
  `compile_store_memory_typed ce dst (expr_type e) op
     (post_value_type ce e) su = ((),sb)` by
    gvs[compile_store_memory_def] >>
  drule_all aggregate_typed_store_path_mem >> simp[]
QED
