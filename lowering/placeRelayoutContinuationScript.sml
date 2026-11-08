Theory placeRelayoutContinuation
Ancestors
  placeRelayoutSource placeRelayoutPhysicalSource placeRelayoutMemoryRun
  placeRelayoutStorageRun placeRelayoutCode exprSimProps loweringPosts
  stmtSimDefs compileEnv exprLoweringProps exprSimHypsDefs
  placeMemoryLiveRegion bodySimAugPlaceLoad annassignRelayoutSource

(* Ownership is separated from the target's input locals.  The target frame
   carries the destination's live local region back to precisely those locals. *)
Theorem target_post_owned_source_local_disjoint:
  target_post ctx func cenv cx es sa sb s0 ee pv vt r s /\
  expr_val_own cenv cx ty si sj es v op s0 /\
  stmt_state_rel ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  eval_operand op s0 = SOME w /\
  local_region cenv ee.scopes s name b len ==>
  w2n w + val_footprint tv v <= b \/ b + len <= w2n w \/
  val_footprint tv v = 0
Proof
  strip_tac >>
  `local_region cenv es.scopes s0 name b len` by
    (irule local_region_frame >>
     conj_tac
     >- (qexists_tac `func` >> fs[stmt_state_rel_def, state_rel_def]) >>
     qexistsl_tac [`sa`, `ee.scopes`, `s`] >>
     fs[target_post_def]) >>
  qpat_x_assum `expr_val_own _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_own_def] >> strip_tac >>
  gvs[] >>
  qpat_x_assum `!n lb lsz. local_region _ _ _ _ _ _ ==> _` drule >>
  decide_tac
QED

Theorem target_post_owned_memory_destination_disjoint:
  target_post ctx func cenv cx es sa sb s0 ee pv vt r s /\
  expr_val_own cenv cx ty si sj es v op s0 /\
  stmt_state_rel ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  eval_operand op s0 = SOME w /\
  val_footprint tv v = type_memory_size tv /\ 0 < type_memory_size tv /\
  expr_sim_inv cenv cx env ee /\
  place_ptr_rel cenv cx s (PlaceR p) dw (SOME LocMemory) (Type dty) /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  write_place cx p v ee = (INL (),ff) ==>
  w2n w + type_memory_size tv <= w2n dw \/
  w2n dw + type_memory_size dtv <= w2n w
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx ee s` by fs[target_post_def] >>
  `!id path entry t0. p = MemoryPlace id path /\
    lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type` by
    (rpt strip_tac >> metis_tac[aug_place_entry_type_agrees]) >>
  drule_all memory_place_live_region >> strip_tac >>
  drule_all target_post_owned_source_local_disjoint >> decide_tac
QED

(* Full-size registration is obtained from the non-bytes layout, not from
   a value-dependent footprint estimate. *)
Theorem target_post_owned_source_registered:
  target_post ctx func cenv cx es sa sb s0 ee pv vt r s /\
  expr_val_own cenv cx ty si sj es v op s0 /\
  sj.cs_next_id <= sa.cs_next_id /\ sa.cs_next_id <= sb.cs_next_id /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
  ~is_bytestring_type ty /\ 0 < type_memory_size tv /\
  val_wf tv v /\ val_in_memory tv v (w2n w) s0.vs_memory /\
  eval_operand op s0 = SOME w /\
  (!x. op = Var x ==> not_fresh_at sa x) /\ (!l. op <> Label l) ==>
  eval_operand op s = SOME w /\ expr_val_rel cx ty v op s /\
  val_in_memory tv v (w2n w) s.vs_memory /\
  ?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
     aid < sb.cs_next_id /\ b <= w2n w /\
     w2n w + type_memory_size tv <= b + sz
Proof
  strip_tac >>
  `val_footprint tv v = type_memory_size tv` by
    metis_tac[nonbytes_evaluated_val_footprint] >>
  drule_all target_post_owned_source >> strip_tac >> gvs[] >>
  qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >> decide_tac
QED

Theorem owned_target_relayout_store_run:
  compile_assign_value cenv dst loc op (is_word_type dty) src_loc dty sty
    (case dty of ArrayT et (Dynamic _) =>
       SOME ((type_memory_bytes cenv et + 31) DIV 32, type_memory_bytes cenv et)
     | _ => NONE) (type_memory_bytes cenv dty) sb = ((),sf) /\
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
  write_place cx p v ee = (INL (),ff) /\ local_ptrs_reserved cenv sb /\
  fn_has_code sb sf func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      stmt_state_rel ctx func cenv cx ff t /\
      (!x. not_fresh_at sb x ==> lookup_var x t = lookup_var x s) /\
      (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!x. op = Var x ==> not_fresh_at sa x` by simp[] >>
  `!x. op = Var x ==> not_fresh_at sb x` by simp[] >>
  `val_footprint stv v = type_memory_size stv` by
    metis_tac[nonbytes_evaluated_val_footprint] >>
  drule_all target_post_owned_source_registered >> strip_tac >>
  `stmt_state_rel ctx func cenv cx ee s` by fs[target_post_def] >>
  `?dw. eval_operand dst s = SOME dw /\
        place_ptr_rel cenv cx s (PlaceR p) dw (SOME loc) (Type dty)` by
    fs[target_post_def] >>
  `!x. dst = Var x ==> not_fresh_at sb x` by fs[target_post_def] >>
  Cases_on `loc = LocMemory`
  >- suspend "memory" >>
  `loc = LocStorage \/ loc = LocTransient` by
    (Cases_on `p` >> gvs[place_ptr_rel_def, slot_loc_def] >>
     Cases_on `b'` >> gvs[slot_loc_def]) >>
  qpat_x_assum `lowered_value_type cenv e = sty` (SUBST_ALL_TAC o SYM) >>
  irule place_relayout_storage_run >> simp[] >>
  goal_assum (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `compile_get_target_ptr _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
  goal_assum (drule_at (Pat `write_place _ _ _ _ = _`)) >>
  simp[] >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Resume owned_target_relayout_store_run[memory]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  `w2n sw + type_memory_size stv <= w2n dw \/
   w2n dw + type_memory_size dtv <= w2n sw` by
    (irule target_post_owned_memory_destination_disjoint >> metis_tac[]) >>
  `w2n sw + type_memory_size stv < dimword (:256)` by
    (drule stmt_state_rel_region_lt >> strip_tac >>
     first_x_assum drule >> decide_tac) >>
  qpat_x_assum `loc = LocMemory` SUBST_ALL_TAC >>
  qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[] >> strip_tac >>
  irule place_relayout_memory_run >> simp[] >>
  goal_assum (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
  goal_assum (drule_at (Pat `write_place _ _ _ _ = _`)) >>
  simp[] >> metis_tac[]
QED

Finalise owned_target_relayout_store_run
