(*
 * A tuple element stored at a member type it only fits (#636)
 *
 * A tuple literal's element whose declared member type dty is an aggregate
 * wider than the element's own type (DynArray[String[5],2] at
 * DynArray[String[40],2], say) is stored by compile_store_memory at dty:
 * a typed recursive copy, or a bulk copy when the two tuple layouts agree.
 * Either way the zero-mark path ends with the value laid out at dty.
 *
 * TOP-LEVEL:
 *   aggregate_store_nested_path — exprSimAggregateBodyCounted's
 *     aggregate_store_body_rebased_slice_path at a nested member type
 *)
Theory exprSimAggregateNestedStore
Ancestors
  exprSimAggregateChildren exprSimHyps exprSimHypsDefs exprSimProps
  exprSimSource placeTypedCopyRecursivePath aggregateStoreSizePath
  typedMemoryCopy typedCopyCompatibility aggregateEvaluatedLayout
  memoryLayoutDefs memoryLayoutSource memoryLayoutRel memoryValueEncoding
  loweringPosts exprLowering exprLoweringProps compileEnv context
  loweringStateRelDefs freshWrites gasSummary fragGasMode venomState
  vyperTypeSystem vyperTypeArgFits vyperTypeInvariants
Libs
  monadsyntax

(* Off bytestrings and words, an element's lowered type is its post type. *)
Theorem aggregate_nested_lowered_post:
  !ce e env.
    well_typed_expr env e /\ ~is_word_type (expr_type e) /\
    ~is_bytestring_type (expr_type e) ==>
    lowered_value_type ce e = post_value_type ce e
Proof
  ho_match_mp_tac lowered_value_type_ind >>
  simp[lowered_value_type_def, post_value_type_def, vyperASTTheory.expr_type_def,
       is_bytestring_type_def, well_typed_expr_def, type_builtin_result_ok_def] >>
  rpt strip_tac >> gvs[is_bytestring_type_def] >>
  gvs[well_typed_builtin_app_def] >>
  rpt (pop_assum mp_tac) >> rw[] >> gvs[is_bytestring_type_def]
QED

Theorem aggregate_store_nested_path:
  compile_store_memory ce op (Var x) dty (lowered_value_type ce e)
    su = ((),sb) /\
  arg_type_fits (expr_type e) dty /\ dty <> expr_type e /\
  ~is_bytestring_type dty /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  expr_body_pre ce cx env e es /\
  (do res <- eval_expr cx e; read_result cx res od) es = (INL v,es') /\
  not_fresh_at sm x /\ lookup_var x r = SOME w /\
  sm.cs_next_var <= su.cs_next_var /\
  (!z. op = Var z ==> not_fresh_at su z) /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce su /\
  evaluate_type (get_tenv cx) dty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce dty = type_memory_size tv /\
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
  fn_has_code su sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = su.cs_current_bb /\
  s.vs_inst_idx = LENGTH su.cs_current_insts ==>
  ?q. gas_marked_path F ctx func s 0 (OK q) /\
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
  `well_typed_expr env e /\ expr_sim_inv ce cx env es` by
    fs[expr_body_pre_def] >>
  `type_widens_to (get_tenv cx) (expr_type e) dty` by
    simp[type_widens_to_def, well_formed_type_def] >>
  `~is_word_type dty` by metis_tac[compileEnvTheory.type_widens_to_word] >>
  `~is_word_type (expr_type e)` by
    metis_tac[typedMemoryCopyTheory.return_source_word_widens_eq] >>
  `~is_bytestring_type (expr_type e)` by
    metis_tac[typedMemoryCopyTheory.type_widens_from_bytestring] >>
  `lowered_value_type ce e = post_value_type ce e` by
    metis_tac[aggregate_nested_lowered_post] >>
  `type_widens_to (get_tenv cx) (post_value_type ce e) (expr_type e)` by
    (drule_all post_value_type_widens >>
     fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def]) >>
  `type_widens_to (get_tenv cx) (post_value_type ce e) dty` by
    metis_tac[typedCopyCompatibilityTheory.type_widens_to_trans] >>
  `~is_word_type (post_value_type ce e) /\
   ~is_bytestring_type (post_value_type ce e)` by
    metis_tac[typedMemoryCopyTheory.return_source_word_widens_eq,
              typedMemoryCopyTheory.type_widens_from_bytestring] >>
  qpat_x_assum `compile_store_memory _ _ _ _ (lowered_value_type _ _) _ = _`
    (assume_tac o SRULE [ASSUME ``lowered_value_type ce e = post_value_type ce e``]) >>
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
  drule_all aggregate_child_physical_encoding >> strip_tac >>
  Cases_on `dty = post_value_type ce e \/
    tuple_memory_layout_eq dty (post_value_type ce e)`
  >- suspend "same_layout" >>
  pop_assum (strip_assume_tac o SRULE [DE_MORGAN_THM]) >>
  suspend "typed"
QED

Resume aggregate_store_nested_path[typed]:
  `w2n sw + type_memory_size stv < dimword (:256) /\
   (w2n sw + type_memory_size stv <= w2n w \/
    w2n w + type_memory_size tv <= w2n sw)` by
    (`expr_val_at ce cx (post_value_type ce e)
       (sa with cs_next_var := sm.cs_next_var) su es' v op s` by
       fs[expr_post_def] >>
     irule aggregate_physical_source_slot_bounds >>
     goal_assum (drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `type_widens_to _ _ dty`)) >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ s`)) >>
     goal_assum (drule_at (Pat `FLOOKUP _ _ = SOME (b,k)`)) >>
     simp[arithmeticTheory.ADD_COMM] >>
     first_assum (ACCEPT_TAC o SRULE [arithmeticTheory.ADD_COMM])) >>
  `compile_store_memory_typed ce (Var x) dty op
     (post_value_type ce e) su = ((),sb)` by
    (qpat_x_assum `_ su = ((),sb)` mp_tac >>
     asm_simp_tac bool_ss [compile_store_memory_def]) >>
  `sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
   (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv.
       evaluate_type (get_tenv cx) fty = SOME tv ==>
       sz = type_memory_size tv) fields)` by
    (fs[expr_body_pre_def, expr_sim_inv_def] >>
     rpt strip_tac >> first_x_assum drule >> simp[]) >>
  drule compile_store_memory_typed_forward_run >>
  disch_then (drule_at (Pat `type_widens_to _ _ dty`)) >>
  disch_then (drule_at (Pat `evaluate_type _ dty = _`)) >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ s.vs_memory`)) >>
  disch_then (qspecl_then [`tv`, `ctx`, `func`, `w`] mp_tac) >>
  (impl_tac
   >- (simp[venomStateTheory.eval_operand_def, arithmeticTheory.ADD_COMM] >>
       first_assum ACCEPT_TAC)) >>
  strip_tac >> qexists_tac `t` >> simp[] >>
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

Resume aggregate_store_nested_path[same_layout]:
  (* The post type itself, or a tuple of equal member layouts: a bulk copy
     of dty's bytes, which reads back at dty. *)
  `compile_store_memory ce op (Var x) dty dty su = ((),sb)` by
    (qpat_x_assum `_ su = ((),sb)` mp_tac >>
     simp_tac bool_ss [compile_store_memory_def] >>
     qpat_x_assum `_ \/ _` strip_assume_tac >>
     asm_simp_tac bool_ss []) >>
  `type_memory_size stv = type_memory_size tv` by
    (qpat_x_assum `_ \/ _` strip_assume_tac >- gvs[] >>
     drule tuple_memory_layout_eq_bytes >>
     disch_then (qspec_then `ce` mp_tac) >>
     metis_tac[expr_sim_inv_memory_size]) >>
  `val_in_memory tv v (w2n sw) s.vs_memory` by
    (qpat_x_assum `_ \/ _` strip_assume_tac >- gvs[] >>
     `memory_layout_key dty = memory_layout_key (post_value_type ce e)` by
       (Cases_on `dty` >> Cases_on `post_value_type ce e` >>
        fs[tuple_memory_layout_eq_def, memory_layout_key_tuple]) >>
     drule_all memory_layout_key_evaluated >> strip_tac >>
     irule memory_value_rel_val_in_memory >> simp[] >>
     irule memory_layout_rel_value >> qexists_tac `stv` >> simp[] >>
     irule val_in_memory_memory_value_rel >> simp[]) >>
  `?etv. evaluate_type (get_tenv cx) (expr_type e) = SOME etv` by
    metis_tac[type_widens_to_value_has_type] >>
  `type_memory_size stv <= type_memory_size etv` by
    (qpat_x_assum `type_widens_to _ (post_value_type _ _) (expr_type _)`
       (strip_assume_tac o REWRITE_RULE [type_widens_to_def]) >- gvs[] >>
     metis_tac[cj 1 arg_fits_evaluated_memory_size]) >>
  `type_memory_size etv < 2 ** 64` by
    metis_tac[expr_body_pre_copy_ok] >>
  `type_memory_size tv + 64 < dimword (:256)` by
    (fs[wordsTheory.dimword_def] >> decide_tac) >>
  drule compile_store_memory_same_type_size_forward >>
  disch_then (drule_at (Pat `evaluate_type _ _ = SOME tv`)) >>
  disch_then (drule_at (Pat `eval_operand op s = SOME sw`)) >>
  disch_then (qspecl_then [`v`, `func`, `w`, `ctx`] mp_tac) >>
  (impl_tac >- simp[venomStateTheory.eval_operand_def]) >>
  strip_tac >> qexists_tac `t` >> simp[] >>
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

Finalise aggregate_store_nested_path
