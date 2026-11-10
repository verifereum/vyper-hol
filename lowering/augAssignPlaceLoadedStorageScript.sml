(* The storage old-value load and the original-entry frame. *)
Theory augAssignPlaceLoadedStorage
Ancestors
  augAssignPlaceMemoryTarget augAssignPlaceSourceMemory
  stmtSimAugAssignPlaceStorage stmtSimAugAssignPlaceMemory exprSimHypsDefs
  exprSimProps exprSimWordArgs freshWrites exprBopSimProps loweringPosts

Theorem aug_place_storage_loaded:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env e es /\
  EVERY (supported_pure_expr tops) (target_indices bt) /\
  eval_target_place cx bt (es with gas_obs := gs) =
    (INL (StoragePlace tr slot tv),mid) /\
  target_post ctx func cenv cx es sa sp s0 mid
    (PlaceR (StoragePlace tr slot tv)) (Type ty) r t /\
  is_word_type ty /\
  emit_op (if tr then TLOAD else SLOAD) [FST r] sp = (cur,sl) /\
  fn_has_code sp sl func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sp /\ alloca_history func t /\ ~t.vs_halted /\
  t.vs_current_bb = sp.cs_current_bb /\
  t.vs_inst_idx = LENGTH sp.cs_current_insts /\
  (!z. not_fresh_at sa z ==> not_fresh_at sp z) ==>
  ?old u. read_place cx (StoragePlace tr slot tv) mid = (INL old,mid) /\
    place_type_value cx (StoragePlace tr slot tv) mid = (INL tv,mid) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv old /\
    gas_marked_path T ctx func t 0 (OK u) /\
    eval_operand cur u = SOME (typed_val_to_w256 tv old) /\
    eval_operand (FST r) u = SOME slot /\
    place_ptr_rel cenv cx u (PlaceR (StoragePlace tr slot tv)) slot
      (SOME (slot_loc tr)) (Type ty) /\
    stmt_state_rel ctx func cenv cx mid u /\
    ~u.vs_halted /\ u.vs_current_bb = sl.cs_current_bb /\
    u.vs_inst_idx = LENGTH sl.cs_current_insts /\
    local_ptrs_reserved cenv sl /\ alloca_history func u /\
    (!z v. not_fresh_at sa z /\ lookup_var z s0 = SOME v ==>
      lookup_var z u = SOME v) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
      FLOOKUP u.vs_allocas aid = SOME b) /\
    u.vs_alloca_next = t.vs_alloca_next /\
    (!z. FST r = Var z ==> not_fresh_at sl z) /\
    (?out. cur = Var out /\ not_fresh_at sl out)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
  `contract_storage_well_formed cx (es with gas_obs := gs)` by
    (qpat_x_assum `expr_body_pre _ _ _ _ (_ with gas_obs := _)`
       (mp_tac o PURE_REWRITE_RULE
         [exprSimHypsDefsTheory.expr_body_pre_def,
          exprSimHypsDefsTheory.expr_sim_inv_def]) >>
     metis_tac[]) >>
  `target_post ctx func cenv cx (es with gas_obs := gs) sa sp s0 mid
    (PlaceR (StoragePlace tr slot tv)) (Type ty) r t` by
    (fs[target_post_def, locals_kept_def] >> metis_tac[]) >>
  drule_at (Pat `target_post`) aug_place_storage_read_path >>
  disch_then (drule_at (Pat `eval_target_place`)) >>
  disch_then (drule_at (Pat `emit_op`)) >> simp[] >>
  disch_then (qspec_then `tops` mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `target_post _ _ _ _ es _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [target_post_def]) >>
  `place_ptr_rel cenv cx u (PlaceR (StoragePlace tr slot tv)) slot
    (SOME (slot_loc tr)) (Type ty)` by fs[place_ptr_rel_def] >>
  qexistsl_tac [`cur'`, `u`] >> simp[] >>
  metis_tac[freshWritesTheory.not_fresh_at_mono]
QED
