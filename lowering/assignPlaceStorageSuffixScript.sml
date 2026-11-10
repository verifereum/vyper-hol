Theory assignPlaceStorageSuffix
Ancestors
  placeRelayoutStorageFrame placeStoreStorage stmtSimDefs exprSimHyps
  loweringPosts compileEnv stmtLowering valueEncodingProps vyperScopePreservation
  vyperTyping vyperValue words
Libs monadsyntax

(* Storage consumes destination-typed memory regardless of its provenance. *)
Theorem assign_place_typed_storage_suffix_run:
  (case dty of ArrayT et (Dynamic n) =>
     compile_dynarray_to_storage src dst
       ((type_memory_bytes cenv et + 31) DIV 32) (type_memory_bytes cenv et)
       (loc = LocTransient) sa = ((),sb)
   | _ =>
     if type_memory_size dtv <= 32 then
       ?loaded sm. emit_op MLOAD [src] sa = (loaded,sm) /\
         emit_void (if loc = LocTransient then TSTORE else SSTORE)
           [dst;loaded] sm = ((),sb)
     else ?r. (if loc = LocTransient then compile_memory_to_transient
               else compile_memory_to_storage)
       src dst (type_memory_size dtv DIV 32) sa = (r,sb)) /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  0 < type_slot_size dtv /\ well_formed_type_value dtv /\
  value_has_type dtv v /\ val_in_memory dtv v (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size dtv < dimword (:256) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME w /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  (loc = LocStorage \/ loc = LocTransient) /\
  expr_sim_inv cenv cx env ee /\ stmt_state_rel ctx func cenv cx ee s /\
  place_ptr_rel cenv cx s (PlaceR p) w (SOME loc) (Type dty) /\
  storage_place_region cx p /\ write_place cx p v ee = (INL (),ff) /\
  local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx ff t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_frame cenv ee sa s cenv ff t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?t. gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx ff t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (Cases_on `?et n. dty = ArrayT et (Dynamic n)`
     >- suspend "dynamic" >>
     suspend "static") >>
  qexists_tac `t` >> simp[] >>
  `MAP FDOM ff.scopes = MAP FDOM ee.scopes` by
    metis_tac[write_place_scopes_dom] >>
  irule alloca_frame_of_mem_frame >> simp[] >>
  goal_assum (drule_at Any)
QED

Resume assign_place_typed_storage_suffix_run[dynamic]:
  pop_assum strip_assume_tac >> gvs[] >>
  qpat_x_assum `evaluate_type _ (ArrayT _ _) = _` mp_tac >>
  pure_rewrite_tac [cj 3 vyperValueTheory.evaluate_type_def] >>
  strip_tac >> gvs[AllCaseEqs()] >>
  gvs[] >> rename1 `evaluate_type (get_tenv cx) et = SOME etv` >>
  `type_memory_bytes cenv et = type_memory_size etv` by
    metis_tac[expr_sim_inv_memory_size] >>
  `type_memory_size etv = 32 * type_slot_size etv` by
    simp[type_memory_size_slots] >>
  `?vs. v = ArrayV (DynArrayV vs)` by
    (Cases_on `v` >> fs[value_has_type_def] >>
     rename1 `value_has_type _ (ArrayV av)` >> Cases_on `av` >> fs[value_has_type_def]) >>
  pop_assum SUBST_ALL_TAC >>
  irule place_relayout_dyn_storage_suffix_framed_run >> simp[] >>
  goal_assum (drule_at (Pat `write_place _ _ _ _ = _`)) >> simp[] >>
  goal_assum (drule_at (Pat `expr_sim_inv _ _ _ _`)) >> simp[] >>
  goal_assum (drule_at (Pat `val_in_memory _ _ _ s.vs_memory`)) >>
  goal_assum (drule_at (Pat `place_ptr_rel _ _ s _ _ _ _`)) >>
  qexistsl_tac [`dst`, `src`] >>
  simp[cj 3 vyperValueTheory.evaluate_type_def] >>
  fs[arithmeticTheory.ADD_DIV_ADD_DIV, arithmeticTheory.MULT_DIV] >>
  first_assum ACCEPT_TAC
QED

Resume assign_place_typed_storage_suffix_run[static]:
  drule_all place_store_storage_destination >> strip_tac >>
  qpat_x_assum `loc = LocStorage \/ loc = LocTransient` kall_tac >> gvs[] >>
  drule_all place_store_storage_write_inv >> strip_tac >> gvs[] >>
  drule_all place_store_storage_leaf_bounds >> strip_tac >>
  `type_memory_size dtv = 32 * type_slot_size dtv` by
    simp[type_memory_size_slots] >>
  `n2w (w2n root + delta) = root + n2w delta` by
    simp[GSYM wordsTheory.word_add_n2w] >>
  drule_at (Pat `val_in_memory _ _ _ s.vs_memory`)
    place_relayout_typed_storage_suffix_framed_run >>
  disch_then (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ s`)) >>
  disch_then (drule_at (Pat `storage_subregion _ _ _ _`)) >>
  disch_then (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `encode_value _ _ = _`)) >>
  disch_then (qspec_then `w2n root + delta` mp_tac) >>
  disch_then (qspecl_then [`src`, `sb`, `sa`, `dst`] mp_tac) >>
  (impl_tac >-
    (Cases_on `tr` >> fs[slot_loc_def] >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     Cases_on `dty` >> fs[] >>
     rename1 `ArrayT et bd` >> Cases_on `bd` >> fs[])) >>
  strip_tac >> qexists_tac `t` >> gvs[]
QED
Finalise assign_place_typed_storage_suffix_run
