Theory placeRelayoutOutcome
Ancestors
  placeRelayoutStaticExit stmtSimAugAssignPlaceMemory vyperPlaceFrames

Theorem memory_write_admissible_success:
  write_place cx (MemoryPlace id path) v st = (res,st') /\
  stmt_res_ok lctx res ==> res = INL ()
Proof
  strip_tac >>
  qpat_x_assum `write_place _ _ _ _ = _` mp_tac >>
  simp[vyperStateTheory.write_place_def, vyperStateTheory.get_scopes_def,
    vyperStateTheory.bind_def, vyperStateTheory.lift_option_type_def,
    vyperStateTheory.type_check_def, vyperStateTheory.assert_def,
    vyperStateTheory.lift_sum_def, vyperStateTheory.set_scopes_def,
    vyperStateTheory.return_def, vyperStateTheory.raise_def, AllCaseEqs()] >>
  Cases_on `find_containing_scope id st.scopes` >>
  gvs[vyperStateTheory.return_def, vyperStateTheory.raise_def,
      stmtSimDefsTheory.stmt_res_ok_def] >>
  rename1 `find_containing_scope id st.scopes = SOME fc` >> PairCases_on `fc` >>
  gvs[vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_def,
      vyperStateTheory.assert_def, vyperStateTheory.return_def,
      vyperStateTheory.raise_def, vyperStateTheory.set_scopes_def,
      vyperStateTheory.replace_memory_entry_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `evaluate_subscripts fc2.type fc2.value path` >>
  gvs[vyperStateTheory.return_def, vyperStateTheory.raise_def] >>
  Cases_on `assign_subscripts fc2.type fc2.value path (Replace v)` >>
  gvs[vyperStateTheory.return_def, vyperStateTheory.raise_def] >>
  drule_all stmtSimAugAssignPlaceMemoryTheory.aug_place_replace_read_error >> simp[]
QED

Theorem owned_target_relayout_store_outcome:
  compile_assign_value cenv dst loc op (is_word_type dty) src_loc dty sty
    (type_memory_bytes cenv dty) sb = ((),sf) /\
  compile_get_target_ptr cfn cenv bt sa = ((dst,SOME loc,SOME (ValPT dty)),sb) /\
  target_post ctx func cenv cx es sa sb s0 ee (PlaceR p) (Type dty)
    (dst,SOME loc,SOME (ValPT dty)) s /\
  expr_val_own cenv cx sty si sj es v op s0 /\
  sj.cs_next_id <= sa.cs_next_id /\ sa.cs_next_id <= sb.cs_next_id /\
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  (src_loc = NONE \/ src_loc = SOME LocMemory) /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\ dty <> sty /\
  ~is_word_type sty /\ ~is_bytestring_type sty /\
  type_widens_to (get_tenv cx) sty dty /\ assignable_type (get_tenv cx) sty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  val_in_memory stv v (w2n sw) s0.vs_memory /\ eval_operand op s0 = SOME sw /\
  (!x. op = Var x ==> not_fresh_at sa x /\ not_fresh_at sb x) /\
  (!l. op <> Label l) /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  0 < type_memory_size stv /\ type_memory_bytes cenv sty < dimword (:256) /\
  expr_sim_inv cenv cx env ee /\ acyclic_struct_metadata cenv.ce_struct_fields /\
  assign_alloc_ok cenv bt e /\ lowered_value_type cenv e = sty /\
  ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
  cenv.ce_target CapMcopy /\ storage_place_region cx p /\
  write_place cx p v ee = (res,ff) /\ stmt_res_ok lctx res /\
  local_ptrs_reserved cenv sb /\
  fn_has_code sb sf func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  ?r. gas_marked_path F ctx func s 0 r /\
    ((?t. r = OK t /\ res = INL () /\
       stmt_state_rel ctx func cenv cx ff t /\
       (!x. not_fresh_at sb x ==> lookup_var x t = lookup_var x s) /\
       (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
       ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
       t.vs_inst_idx = LENGTH sf.cs_current_insts /\
       alloca_frame cenv ee sb s cenv ff t) \/
     (exit_result r /\ stmt_exit RetQ ff res r))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~cx.txn.is_static` by
    fs[exprLoweringPropsTheory.stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def] >>
  `res = INL ()` by
    (Cases_on `p`
     >- (gvs[vyperPlaceFramesTheory.write_storage_place_eq, AllCaseEqs(),
             stmtSimDefsTheory.stmt_res_ok_def])
     >- metis_tac[memory_write_admissible_success] >>
     fs[loweringPostsTheory.target_post_def, loweringPostsTheory.place_ptr_rel_def]) >>
  qpat_x_assum `res = INL ()` SUBST_ALL_TAC >>
  drule_all placeRelayoutContinuationTheory.owned_target_relayout_store_run >>
  strip_tac >> qexists_tac `OK t` >> simp[] >> metis_tac[]
QED
