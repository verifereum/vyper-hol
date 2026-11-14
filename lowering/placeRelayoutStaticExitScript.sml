Theory placeRelayoutStaticExit
Ancestors
  placeRelayoutContinuation placeStaticCopyExit exprSimTypedAlloc
  placeStoreStorage placeStoreSlots placeRelayoutNormalizeFrame exprSimHyps
  typedMemoryCopy stmtLoweringMono entryArgPtrs stmtSimReturn vyperTypeArgFits
  vyperTypeSystem fragGasMode compileEnv loweringStateRelDefs
  placeDestinationBounds allocaSiteResource allocLimitsProps loweringPosts
  stmtSimDefs exprSimProps venomMemDefs exprLoweringProps fragExec loweringHalt
  emitHelperProps venomInst venomState venomExecSemantics

Theorem owned_target_relayout_store_static_exit:
  compile_assign_value cenv dst loc op (is_word_type dty) src_loc dty sty
    (type_memory_bytes cenv dty) sb = ((),sf) /\
  compile_get_target_ptr cfn cenv bt sa = ((dst,SOME loc,SOME (ValPT dty)),sb) /\
  target_post ctx func cenv cx es sa sb s0 ee (PlaceR p) (Type dty)
    (dst,SOME loc,SOME (ValPT dty)) s /\
  expr_val_own cenv cx sty si sj es v op s0 /\
  sj.cs_next_id <= sa.cs_next_id /\ sa.cs_next_id <= sb.cs_next_id /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\ dty <> sty /\
  ~is_word_type sty /\ ~is_bytestring_type sty /\
  type_widens_to (get_tenv cx) sty dty /\ assignable_type (get_tenv cx) sty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  val_in_memory stv v (w2n sw) s0.vs_memory /\ eval_operand op s0 = SOME sw /\
  (!x. op = Var x ==> not_fresh_at sa x /\ not_fresh_at sb x) /\
  (!l. op <> Label l) /\ 0 < type_memory_size stv /\
  expr_sim_inv cenv cx env ee /\ acyclic_struct_metadata cenv.ce_struct_fields /\
  assign_alloc_ok cenv bt e /\ lowered_value_type cenv e = sty /\
  ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
  storage_place_region cx p /\
  local_ptrs_reserved cenv sb /\
  fn_has_code sb sf func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  cx.txn.is_static /\ (loc = LocStorage \/ loc = LocTransient) ==>
  ?r. gas_marked_path F ctx func s 0 r /\ exit_result r /\
      stmt_exit RetQ ee (INR (Error (RuntimeError "write in static context"))) r
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `stmt_state_rel ctx func cenv cx ee s` by fs[target_post_def] >>
  `!x. op = Var x ==> not_fresh_at sa x` by simp[] >>
  drule_all target_post_owned_source_registered >> strip_tac >>
  qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac [target_post_def, pairTheory.FST, pairTheory.SND] >>
  disch_then (CONJUNCTS_THEN2 kall_tac
    (CONJUNCTS_THEN2 (qx_choose_then `dw` strip_assume_tac) strip_assume_tac)) >>
  `0 < type_slot_size dtv` by
    metis_tac[type_widens_to_assignable_type, assignable_type_slot_size_pos] >>
  `type_alloc_ok cenv dty` by
    (simp[allocLimitsTheory.type_alloc_ok_def] >>
     drule storage_target_normalization_bound >> simp[] >>
     disch_then drule >> metis_tac[]) >>
  drule_all place_store_destination_alloc_bound >> strip_tac >>
  `sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
   (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
       sz = type_memory_size tv) fields)` by
    (fs[exprSimHypsDefsTheory.expr_sim_inv_def] >> metis_tac[]) >>
  `w2n sw + type_memory_size stv < dimword (:256)` by
    (`alloca_inv s` by fs[stmt_state_rel_def] >>
     `s.vs_alloca_next < dimword (:256)` by
       (fs[stmt_state_rel_def, alloca_room_def] >> decide_tac) >>
     drule_all alloca_site_registered_below >> decide_tac) >>
  suspend "normalize"
QED

Resume owned_target_relayout_store_static_exit[normalize]:
  `loc = slot_loc (loc = LocTransient)` by (Cases_on `loc` >> gvs[slot_loc_def]) >>
  `?buf sm sn.
     compile_alloc_buffer (type_memory_bytes cenv dty) sb = (buf,sm) /\
     compile_store_memory_typed cenv buf.buf_operand dty op sty sm = ((),sn) /\
     compile_store_slots cenv buf.buf_operand dst dty (loc = LocTransient) sn = ((),sf)` by
    (mp_tac (Q.INST [`tr` |-> `loc = LocTransient`, `src` |-> `op`,
                    `sa` |-> `sb`, `sb` |-> `sf`]
       (SPEC_ALL place_store_storage_compile)) >>
     (impl_tac >- metis_tac[]) >> strip_tac >> gvs[] >> metis_tac[]) >>
  `cs_extends sb sm` by metis_tac[compile_alloc_buffer_extends] >>
  `ci_mono sm sn` by (drule typed_return_store_mono >> simp[]) >>
  `ci_mono sn sf` by
    metis_tac[cj 1 ci_mono_compile_store_slots, pairTheory.SND] >>
  `fn_has_code sb sn func /\ fn_has_code sn sf func /\ fn_has_code sb sm func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split, cs_extends_trans]) >>
  `MEM (mk_inst sb.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv dty))]
    [STRING #"%" (toString sb.cs_next_var)]) (fn_insts func)` by
    (irule entry_alloc_buffer_inst >> goal_assum (drule_at Any) >> simp[]) >>
  drule place_normalize_framed_path >>
  disch_then (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ s`)) >>
  disch_then (drule_at (Pat `eval_operand _ s = _`)) >>
  disch_then (qspecl_then [`stv`, `dtv`, `v`] mp_tac) >>
  (impl_tac >- (simp[arithmeticTheory.ADD_COMM] >>
     conj_tac >- first_assum ACCEPT_TAC >> disj1_tac >>
     qexistsl_tac [`aid`, `b`, `sz`] >> simp[arithmeticTheory.ADD_COMM])) >>
  disch_then (qx_choosel_then [`u`, `uw`] strip_assume_tac) >>
  suspend "suffix"
QED

Resume owned_target_relayout_store_static_exit[suffix]:
  `!x. buf.buf_operand = Var x ==> not_fresh_at sm x` by
    (drule compile_alloc_buffer_emission >> strip_tac >> gvs[]) >>
  `sb.cs_next_var <= sm.cs_next_var` by
    (drule compile_alloc_buffer_emission >> simp[] >> strip_tac >> simp[]) >>
  `sm.cs_next_var <= sn.cs_next_var` by fs[ci_mono_def] >>
  `!x. buf.buf_operand = Var x \/ dst = Var x ==> not_fresh_at sn x` by
    (gen_tac >> strip_tac
     >- (irule freshWritesTheory.not_fresh_at_mono >>
         qexists_tac `sm` >> simp[]) >>
     irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sb` >> simp[]) >>
  `u.vs_labels = s.vs_labels` by
    metis_tac[stmtSimAugAssignPlaceMemoryTheory.aug_place_marked_path_labels] >>
  `eval_operand dst u = SOME dw` by
    (qspecl_then [`sb`, `s`, `u`, `dst`] mp_tac eval_operand_old_vars >> simp[]) >>
  `w2n dw + type_slot_size dtv <= dimword (:256)` by
    (drule_all place_store_storage_destination >> strip_tac >> gvs[] >>
     drule_all place_store_storage_leaf_bounds >> simp[]) >>
  `u.vs_call_ctx.cc_static` by
    fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  drule_all place_store_slots_static_exit >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  qexists_tac `r` >> simp[] >>
  metis_tac[gas_marked_path_then, arithmeticTheory.ADD_CLAUSES]
QED

Finalise owned_target_relayout_store_static_exit
