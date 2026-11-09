(* The old-value load preserves the saved pointer and original-entry frame. *)
Theory augAssignPlaceLoadedMemory
Ancestors
  augAssignPlaceMemoryTarget augAssignPlaceTargetReadiness
  stmtSimAugAssignPlaceMemory exprSimHypsDefs freshWrites exprBopSimProps
  loweringPosts

Theorem aug_place_memory_loaded:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (AugAssign ty bt bop e) /\
  ((?b fld. bt = AttributeTarget b fld) \/ (?b k. bt = SubscriptTarget b k)) /\
  type_stmt env ret_ty (AugAssign ty bt bop e) = SOME env' /\
  expr_body_pre cenv cx env e es /\ target_indices_pre cenv cx env bt /\
  eval_target_place cx bt (es with gas_obs := gs) =
    (INL (MemoryPlace id path),mid) /\
  target_post ctx func cenv cx es sa sp s0 mid
    (PlaceR (MemoryPlace id path)) (Type ty) r t /\
  emit_op MLOAD [FST r] sp = (cur,sl) /\
  fn_has_code sp sl func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sp /\ alloca_history func t /\ ~t.vs_halted /\
  t.vs_current_bb = sp.cs_current_bb /\
  t.vs_inst_idx = LENGTH sp.cs_current_insts /\
  (!z. not_fresh_at sa z ==> not_fresh_at sp z) ==>
  expr_body_pre cenv cx env e mid /\
  ?old tv w u. read_place cx (MemoryPlace id path) mid = (INL old,mid) /\
    place_type_value cx (MemoryPlace id path) mid = (INL tv,mid) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv old /\
    type_bits ty MOD 8 = 0 /\ w2n w + 32 <= u.vs_alloca_next /\
    gas_marked_path T ctx func t 0 (OK u) /\
    eval_operand cur u = SOME (typed_val_to_w256 tv old) /\
    eval_operand (FST r) u = SOME w /\
    place_ptr_rel cenv cx u (PlaceR (MemoryPlace id path)) w
      (SOME LocMemory) (Type ty) /\
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
  drule_at (Pat `target_post`) aug_place_memory_target_ready >>
  disch_then (drule_at (Pat `eval_target_place`)) >>
  disch_then (drule_at (Pat `supported_stmt`)) >>
  disch_then (drule_at (Pat `type_stmt`)) >> simp[] >> strip_tac >>
  `expr_sim_inv cenv cx env es /\
   expr_sim_inv cenv cx env (es with gas_obs := gs) /\
   expr_sim_inv cenv cx env mid` by fs[expr_body_pre_def] >>
  qpat_x_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [target_post_def]) >>
  `FST (SND r) = SOME LocMemory` by fs[place_ptr_rel_def] >>
  drule_at (Pat `emit_op`) aug_place_memory_access_path >>
  disch_then (drule_at (Pat `eval_target_place`)) >>
  disch_then (drule_at (Pat `supported_stmt`)) >>
  disch_then (drule_at (Pat `type_stmt`)) >> simp[] >>
  disch_then (drule_at (Pat `place_ptr_rel`)) >>
  disch_then (drule_at (Pat `stmt_state_rel`)) >>
  simp[expr_body_pre_def] >> strip_tac >>
  `eval_operand (FST r) u = SOME w` by
    (irule aug_place_saved_operand >>
     goal_assum (drule_at (Pat `gas_marked_path`)) >>
     qexists_tac `sp` >> simp[]) >>
  `place_ptr_rel cenv cx u (PlaceR (MemoryPlace id path)) w
      (SOME LocMemory) (Type ty)` by
    (irule aug_place_memory_ptr_frame >>
     qexistsl_tac [`t`, `sp`] >> gvs[]) >>
  qexistsl_tac [`w`, `u`] >> simp[] >>
  metis_tac[freshWritesTheory.not_fresh_at_mono]
QED
