(* Memory-place reconstruction depends on the actual copy effect, not on
   the stronger address margin of the generic forward store interface. *)
Theory placeRelayoutState
Ancestors
  placeMemoryStateRebuild placeMemoryCopyEffect loweringPosts placeMemoryProtectedFrame
  stmtSimDefs compileEnv loweringStateRelDefs venomState placeMemoryLiveRegion exprLoweringProps

Theorem memory_place_write_copy_effect:
  stmt_state_rel H ctx func cenv cx ee s /\
  expr_sim_inv cenv cx env ee /\ local_ptrs_reserved cenv sa /\
  place_ptr_rel cenv cx s (PlaceR p) w (SOME LocMemory) (Type dty) /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\ value_has_type dtv v /\
  write_place cx p v ee = (INL (),ff) /\
  (!id path entry t0. p = MemoryPlace id path /\
    lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
  val_in_memory dtv v (w2n w) t.vs_memory /\
  typed_copy_effect ctx func sa sb s t (w2n w) (type_memory_size dtv) ==>
  stmt_state_rel H ctx func cenv cx ff t
Proof
  strip_tac >>
  drule_all memory_place_live_region >> strip_tac >>
  `cenv.ce_is_ctor ==> !src nm tv iv off.
    (src = cenv.ce_module \/ IS_SOME (ALOOKUP cenv.ce_modules src)) /\
    FLOOKUP cenv.ce_module_vars (src,nm) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables src imms) nm = SOME (tv,iv) ==>
    mem_bytes_at off (type_memory_size tv) t.vs_memory =
    mem_bytes_at off (type_memory_size tv) s.vs_memory` by
    (strip_tac >> rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
     irule typed_copy_effect_bytes >>
     goal_assum (drule_at (Pat `typed_copy_effect _ _ _ _ _ _ _ _`)) >>
     irule immutable_local_slice_disjoint >>
     goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
     simp[] >> metis_tac[]) >>
  irule memory_place_write_stmt_state >>
  goal_assum (drule_at (Pat `write_place _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `place_ptr_rel _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
  qexistsl_tac [`dtv`, `s`, `sa`] >>
  gvs[typed_copy_effect_def] >>
  metis_tac[]
QED
