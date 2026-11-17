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
  valid_horizon cx st0 H mid.storage_trace /\
  target_post H ctx func cenv cx es sa sp s0 mid
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
    stmt_state_rel H ctx func cenv cx mid u /\
    ~u.vs_halted /\ u.vs_current_bb = sl.cs_current_bb /\
    u.vs_inst_idx = LENGTH sl.cs_current_insts /\
    local_ptrs_reserved cenv sl /\ alloca_history func u /\
    (!z v. not_fresh_at sa z /\ lookup_var z s0 = SOME v ==>
      lookup_var z u = SOME v) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
      FLOOKUP u.vs_allocas aid = SOME b) /\
    u.vs_alloca_next = t.vs_alloca_next /\ u.vs_memory = t.vs_memory /\
    (!z. not_fresh_at sp z ==> lookup_var z u = lookup_var z t) /\
    (!z. FST r = Var z ==> not_fresh_at sl z) /\
    (?out. cur = Var out /\ not_fresh_at sl out) /\
    u.vs_accounts = t.vs_accounts /\ u.vs_transient = t.vs_transient /\
    u.vs_requests = t.vs_requests /\ u.vs_call_ctx = t.vs_call_ctx
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
  `target_post H ctx func cenv cx (es with gas_obs := gs) sa sp s0 mid
    (PlaceR (StoragePlace tr slot tv)) (Type ty) r t` by
    (qpat_assum `target_post _ _ _ _ _ es _ _ _ _ _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[target_post_def, locals_kept_def, popped_kept_def] >>
     strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `evaluate_type (get_tenv cx) ty = SOME tv /\
   stmt_state_rel H ctx func cenv cx mid t /\
   storage_well_formed_on cx mid (FST H) /\
   eval_operand (FST r) t = SOME slot /\
   (!x. FST r = Var x ==> not_fresh_at sp x)` by
    gvs[target_post_def, place_ptr_rel_def] >>
  qspecl_then [`cx`, `st0`, `H`, `mid`, `ty`, `tv`, `bt`,
    `es with gas_obs := gs`, `tr`, `slot`]
    mp_tac aug_place_target_storage_ready >>
  impl_tac >- simp[] >> strip_tac >>
  drule_all aug_place_storage_read_ready >> strip_tac >>
  drule_all aug_place_storage_load_ready >> strip_tac >>
  drule_all aug_place_storage_access_path >> strip_tac >>
  qpat_x_assum `target_post _ _ _ _ _ es _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [target_post_def]) >>
  `place_ptr_rel cenv cx u (PlaceR (StoragePlace tr slot tv)) slot
    (SOME (slot_loc tr)) (Type ty)` by fs[place_ptr_rel_def] >>
  qexistsl_tac [`cur'`, `u`] >> simp[] >>
  metis_tac[freshWritesTheory.not_fresh_at_mono]
QED
