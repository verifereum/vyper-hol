(* Semantic frames for checked stores of a rebased expression result. *)
Theory stmtSimCustomErrorMemStoreSlice
Ancestors
  stmtSimCustomErrorMemSameStore stmtSimCustomErrorMemTypedCopy
  stmtSimCustomErrorMemZeroCopy exprSimAggregateBodyCounted
  exprSimAggregateChildren exprSimAggregateLoops exprSimSource
  gasSummary fragGasMode fragGasPath vyperInterpreter vyperState exprSimHypsDefs
  exprSimHyps exprSimUnwrap exprSimUnwrapProps exprSimMemoryRead
  exprLoweringProps loweringPosts compileEnv loweringStateRelDefs placeTypedCopyRecursivePath
  placeMemoryPrimitiveForward localMemoryStorePath freshWrites exprSimProps
  vyperAST vyperTypeCallGraph aggregateStoreSizePath exprSimMemDefs
  placeMemoryTypeInterfaces
Libs monadsyntax

Theorem aggregate_store_body_rebased_slice_path_mem:
  compile_store_memory ce op (Var x) (expr_type e) (lowered_value_type ce e)
    su = ((),sb) /\
  expr_body_pre ce cx env e es /\
  (do res <- eval_expr cx e; read_result cx res od) es = (INL v,es') /\
  (int_calls_expr e <> [] /\ lowered_value_type ce e <> expr_type e ==>
    acyclic_struct_metadata ce.ce_struct_fields) /\
  not_fresh_at sm x /\ lookup_var x r = SOME w /\
  sm.cs_next_var <= su.cs_next_var /\
  (!z. op = Var z ==> not_fresh_at su z) /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce su /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce (expr_type e) = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  stmt_state_rel ctx func ce cx es' r /\
  FLOOKUP r.vs_allocas did = SOME (b,k) /\ did < sa.cs_next_id /\
  b <= w2n w /\ w2n w + type_memory_size tv <= b+k /\
  w2n w + type_memory_size tv < dimword (:256) /\
  (!name a len. local_region ce es'.scopes r name a len ==>
    a+len <= w2n w \/ w2n w + type_memory_size tv <= a) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n w) (type_memory_size tv)) /\
  expr_post ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
    su r es' v op s /\
  expr_store_bound cx (expr_type e) v op s /\
  (post_value_type ce e <> expr_type e /\
   ~is_word_type (post_value_type ce e) /\
   ~is_bytestring_type (expr_type e) ==>
   !stv sw. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME stv /\
     eval_operand op s = SOME sw ==>
     type_memory_size stv = 0 \/
     w2n sw + type_memory_size stv <= s.vs_alloca_next) /\
  w2n w + type_memory_size tv <= s.vs_alloca_next /\
  alloca_history func s /\
  fn_has_code su sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = su.cs_current_bb /\
  s.vs_inst_idx = LENGTH su.cs_current_insts ==>
  ?q. gas_marked_path T ctx func s 0 (OK q) /\
    alloca_history func q /\ q.vs_alloca_next = s.vs_alloca_next /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\
    val_in_memory tv v (w2n w) q.vs_memory /\
    stmt_state_rel ctx func ce cx es' q /\
    (!z a. not_fresh_at sm z /\ lookup_var z r = SOME a ==> lookup_var z q = SOME a) /\
    (!aid a. FLOOKUP r.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
    (!aid off sz a len.
      FLOOKUP r.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
      (!name b k. local_region ce es'.scopes r name b k ==>
        off+sz <= b \/ b+k <= off) /\
      off <= a /\ a+len <= off+sz /\
      (a+len <= w2n w \/ w2n w+type_memory_size tv <= a) ==>
      mem_bytes_at a len q.vs_memory = mem_bytes_at a len r.vs_memory) /\
    locals_kept ce es' es' r q /\
    (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==>
      FLOOKUP q.vs_allocas aid = SOME a) /\
    (!a len. a + len <= w2n w \/ w2n w + type_memory_size tv <= a ==>
      mem_bytes_at a len q.vs_memory = mem_bytes_at a len s.vs_memory)
Proof
  strip_tac >>
  `well_typed_expr env e` by fs[expr_body_pre_def] >>
  drule compile_store_memory_post_type >>
  disch_then (qspecl_then [`ce`, `op`, `Var x`] assume_tac) >>
  gvs[] >>
  `lookup_var x s = SOME w` by metis_tac[expr_post_rebased_lookup] >>
  `not_fresh_at su x` by metis_tac[not_fresh_at_mono] >>
  `stmt_state_rel ctx func ce cx es' s /\
   FLOOKUP s.vs_allocas did = SOME (b,k)` by fs[expr_post_def] >>
  `!name a len. local_region ce es'.scopes s name a len ==>
    a+len <= w2n w \/ w2n w + type_memory_size tv <= a` by
    (rpt strip_tac >>
     `local_region ce es'.scopes r name a len` by
       (irule local_region_frame >> conj_tac
        >- (qexists_tac `func` >> fs[stmt_state_rel_def, state_rel_def]) >>
        qexistsl_tac [`sm`, `es'.scopes`, `s`] >> simp[] >>
        metis_tac[expr_post_rebased_lookup]) >>
     first_x_assum drule >> simp[arithmeticTheory.ADD_COMM]) >>
  Cases_on `post_value_type ce e = expr_type e \/
    tuple_memory_layout_eq (expr_type e) (post_value_type ce e)`
  >- suspend "same_layout" >>
  pop_assum (strip_assume_tac o SRULE [DE_MORGAN_THM]) >>
  `~is_word_type (expr_type e) /\ ~is_bytestring_type (expr_type e)` by
    metis_tac[post_value_type_word, post_value_type_bytestring] >>
  `acyclic_struct_metadata ce.ce_struct_fields` by
    (qpat_x_assum `_ ==> acyclic_struct_metadata _` irule >>
     conj_tac
     >- (Cases_on `e` >>
         fs[post_value_type_def, expr_type_def] >>
         rename1 `Call _ tgt _ _` >> Cases_on `tgt` >>
         fs[post_value_type_def, expr_type_def] >>
         simp[Once int_calls_expr_def]) >>
     metis_tac[post_value_type_lowered]) >>
  `type_widens_to (get_tenv cx) (post_value_type ce e) (expr_type e)` by
    (`expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
     drule_all post_value_type_widens >>
     fs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
        vyperTypeInvariantsTheory.env_context_consistent_def]) >>
  `~is_word_type (post_value_type ce e) /\
   ~is_bytestring_type (post_value_type ce e)` by
    metis_tac[typedMemoryCopyTheory.return_source_word_widens_eq,
              typedMemoryCopyTheory.type_widens_from_bytestring] >>
  drule_all aggregate_child_physical_encoding >> strip_tac >>
  `w2n sw + type_memory_size stv < dimword (:256) /\
   (w2n sw + type_memory_size stv <= w2n w \/
    w2n w + type_memory_size tv <= w2n sw)` by
    (`expr_val_at ce cx (post_value_type ce e)
       (sa with cs_next_var := sm.cs_next_var) su es' v op s` by
       fs[expr_post_def] >>
     irule aggregate_physical_source_slot_bounds >>
     goal_assum (drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `type_widens_to _ _ _`)) >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ s`)) >>
     goal_assum (drule_at (Pat `FLOOKUP _ _ = SOME (b,k)`)) >>
     simp[arithmeticTheory.ADD_COMM] >>
     first_assum (ACCEPT_TAC o SRULE [arithmeticTheory.ADD_COMM])) >>
  `compile_store_memory_typed ce (Var x) (expr_type e) op
     (post_value_type ce e) su = ((),sb)` by
    fs[contextTheory.compile_store_memory_def] >>
  drule aggregate_body_copy_metadata >> strip_tac >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `type_memory_size stv = 0 ==>
     type_memory_size tv = 0` by
    metis_tac[type_widens_to_zero_memory_size] >>
  `?t. gas_marked_path T ctx func s 0 (OK t) /\
      val_in_memory tv v (w2n w) t.vs_memory /\
      typed_copy_state_frame su (w2n w) (type_memory_size tv) s t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ t.vs_alloca_next = s.vs_alloca_next` by
    (Cases_on `type_memory_size stv = 0`
     >- (`type_memory_size tv = 0` by metis_tac[] >>
         qspecl_then [`ce`, `get_tenv cx`, `Var x`, `expr_type e`, `op`,
           `post_value_type ce e`, `tv`, `stv`, `v`, `su`, `sb`, `ctx`,
           `func`, `s`, `w`, `sw`] mp_tac compile_store_memory_typed_zero_run_mem >>
         impl_tac >- (simp[venomStateTheory.eval_operand_def,
                           arithmeticTheory.ADD_COMM] >>
                      rpt conj_tac >> first_assum ACCEPT_TAC) >>
         strip_tac >> qexists_tac `t` >> simp[]) >>
     `w2n sw + type_memory_size stv <= s.vs_alloca_next` by
       metis_tac[arithmeticTheory.ADD_COMM] >>
     qspecl_then [`ce`, `get_tenv cx`, `Var x`, `expr_type e`, `op`,
       `post_value_type ce e`, `tv`, `stv`, `v`, `su`, `sb`, `ctx`,
       `func`, `s`, `w`, `sw`] mp_tac compile_store_memory_typed_forward_run_mem >>
     impl_tac >- (simp[venomStateTheory.eval_operand_def,
                       arithmeticTheory.ADD_COMM] >>
                  rpt conj_tac >> first_assum ACCEPT_TAC) >>
     strip_tac >> qexists_tac `t` >> simp[]) >>
  suspend "frame"
QED

Resume aggregate_store_body_rebased_slice_path_mem[frame]:
  markerLib.RESUME_TAC >>
  qexists_tac `t` >> simp[] >>
  drule aggregate_store_rebased_control_frame >>
  disch_then (qspecl_then [`t`, `type_memory_size tv`, `w2n w`] mp_tac) >>
  (impl_tac
   >- (gvs[typedMemoryCopyTheory.typed_copy_state_frame_def,
           typedMemoryCopyTheory.typed_copy_frame_def] >>
       rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >> gvs[] >>
  gvs[typedMemoryCopyTheory.typed_copy_state_frame_def,
      typedMemoryCopyTheory.typed_copy_frame_def,
      arithmeticTheory.ADD_COMM] >>
  qpat_x_assum `t with <|vs_memory := _; vs_vars := _; vs_prev_bb := _;
    vs_current_bb := _; vs_inst_idx := _|> = s`
    (mp_tac o Q.AP_TERM `\z. z.vs_allocas`) >> simp[] >>
  strip_tac >> simp[] >> rpt conj_tac >>
  first_assum (MATCH_ACCEPT_TAC o SRULE [arithmeticTheory.ADD_COMM])
QED

Resume aggregate_store_body_rebased_slice_path_mem[same_layout]:
  (* Equal types, or tuples with equal member layouts: both store by a
     same-type bulk copy. *)
  `compile_store_memory ce op (Var x) (expr_type e) (expr_type e) su = ((),sb) /\
   expr_val_rel cx (expr_type e) v op s` by
    (qpat_x_assum `post_value_type ce e = expr_type e \/ _` strip_assume_tac
     >- gvs[expr_post_def] >>
     conj_tac
     >- (qpat_x_assum `compile_store_memory _ _ _ _ _ _ = _` mp_tac >>
         simp[contextTheory.compile_store_memory_def]) >>
     drule_all aggregate_child_tuple_layout_val_rel >> simp[]) >>
  `type_memory_size tv + 64 < dimword (:256)` by
    (Cases_on `is_word_type (expr_type e)`
     >- (drule_all word_tv_memory_size >> simp[wordsTheory.dimword_def]) >>
     drule_all expr_body_pre_copy_ok >> simp[wordsTheory.dimword_def]) >>
  `?sw. eval_operand op s = SOME sw /\
    (if is_word_type (expr_type e) then sw = typed_val_to_w256 tv v
     else val_in_memory tv v (w2n sw) s.vs_memory)` by
    (fs[expr_val_rel_def] >> metis_tac[]) >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `~is_word_type (expr_type e) /\ val_store_size tv v <> 0 ==>
      w2n sw + val_store_size tv v <= s.vs_alloca_next` by
    (strip_tac >> fs[expr_store_bound_def] >> metis_tac[]) >>
  drule compile_store_memory_same_type_size_forward_mem >>
  disch_then (drule_at (Pat `evaluate_type _ _ = SOME tv`)) >>
  disch_then (drule_at (Pat `eval_operand op s = SOME sw`)) >>
  disch_then (qspecl_then [`v`, `func`, `w`, `ctx`] mp_tac) >>
  (impl_tac >- simp[venomStateTheory.eval_operand_def]) >>
  strip_tac >> suspend "frame_same"
QED

Resume aggregate_store_body_rebased_slice_path_mem[frame_same]:
  qexists_tac `t` >> simp[] >>
  drule aggregate_store_rebased_control_frame >>
  disch_then (qspecl_then [`t`, `type_memory_size tv`, `w2n w`] mp_tac) >>
  (impl_tac >- (simp[] >> conj_tac
    >- (qpat_x_assum `t with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|> = s`
          (mp_tac o Q.AP_TERM `\z. z with <|vs_prev_bb := s.vs_prev_bb;
            vs_current_bb := s.vs_current_bb|>`) >> simp[]) >>
    rpt conj_tac >> first_assum (ACCEPT_TAC o SRULE [arithmeticTheory.ADD_COMM]))) >>
  strip_tac >> gvs[] >>
  gvs[typedMemoryCopyTheory.typed_copy_state_frame_def,
      typedMemoryCopyTheory.typed_copy_frame_def,
      arithmeticTheory.ADD_COMM] >>
  rpt conj_tac >>
  first_assum (MATCH_ACCEPT_TAC o SRULE [arithmeticTheory.ADD_COMM])
QED

Finalise aggregate_store_body_rebased_slice_path_mem
