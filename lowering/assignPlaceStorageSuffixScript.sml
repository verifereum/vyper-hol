Theory assignPlaceStorageSuffix
Ancestors
  placeStoreSlots placeStoreStorage stmtSimDefs exprSimHyps
  loweringPosts compileEnv stmtLowering valueEncodingProps vyperScopePreservation
  vyperTyping vyperValue words
Libs monadsyntax

(* Storage consumes destination-typed memory regardless of its provenance. *)
Theorem assign_place_typed_storage_suffix_run:
  compile_store_slots cenv src dst dty (loc = LocTransient) sa = ((),sb) /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  0 < type_slot_size dtv /\ well_formed_type_value dtv /\
  value_has_type dtv v /\ val_in_memory dtv v (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size dtv < dimword (:256) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME w /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  (loc = LocStorage \/ loc = LocTransient) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
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
    (drule_all place_store_storage_destination >> strip_tac >>
     qpat_x_assum `loc = LocStorage \/ loc = LocTransient` kall_tac >> gvs[] >>
     drule_all place_store_storage_write_inv >> strip_tac >> gvs[] >>
     drule_all place_store_storage_leaf_bounds >> strip_tac >>
     `n2w (w2n root + delta) = root + n2w delta` by
       simp[GSYM wordsTheory.word_add_n2w] >>
     `(slot_loc tr = LocTransient) <=> tr` by (Cases_on `tr` >> simp[slot_loc_def]) >>
     pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
     drule_at (Pat `val_in_memory _ _ _ s.vs_memory`) place_store_slots_suffix_run >>
     disch_then (drule_at (Pat `declared_storage_region _ _ _ _ = _`)) >>
     disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ s`)) >>
     disch_then (drule_at (Pat `storage_subregion _ _ _ _`)) >>
     disch_then (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
     disch_then (drule_at (Pat `encode_value _ _ = _`)) >>
     disch_then (drule_at (Pat `compile_store_slots _ _ _ _ _ _ = _`)) >>
     disch_then (qspec_then `w2n root + delta` mp_tac) >>
     (impl_tac >- (simp[] >> Cases_on `tr` >> fs[slot_loc_def] >> metis_tac[])) >>
     disch_then (qx_choose_then `t` strip_assume_tac) >>
     qexists_tac `t` >> simp[] >> metis_tac[]) >>
  qexists_tac `t` >> simp[] >>
  `MAP FDOM ff.scopes = MAP FDOM ee.scopes` by
    metis_tac[write_place_scopes_dom] >>
  irule alloca_frame_of_mem_frame >> simp[] >>
  goal_assum (drule_at Any)
QED
