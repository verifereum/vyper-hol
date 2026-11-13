(* Memory-place reconstruction depends on the actual copy effect, not on
   the stronger address margin of the generic forward store interface. *)
Theory placeRelayoutState
Ancestors
  placeMemoryStateRebuild placeMemoryCopyEffect loweringPosts
  stmtSimDefs compileEnv loweringStateRelDefs venomState placeMemoryLiveRegion exprLoweringProps

Theorem memory_place_write_copy_effect:
  stmt_state_rel ctx func cenv cx ee s /\
  expr_sim_inv cenv cx env ee /\ local_ptrs_reserved cenv sa /\
  place_ptr_rel cenv cx s (PlaceR p) w (SOME LocMemory) (Type dty) /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\ value_has_type dtv v /\
  write_place cx p v ee = (INL (),ff) /\
  (!id path entry t0. p = MemoryPlace id path /\
    lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
  val_in_memory dtv v (w2n w) t.vs_memory /\
  typed_copy_effect ctx func sa sb s t (w2n w) (type_memory_size dtv) ==>
  stmt_state_rel ctx func cenv cx ff t
Proof
  strip_tac >>
  drule_all memory_place_live_region >> strip_tac >>
  `cenv.ce_is_ctor ==> !nm tv iv off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,nm) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) nm = SOME (tv,iv) ==>
    mem_bytes_at off (type_memory_size tv) t.vs_memory =
    mem_bytes_at off (type_memory_size tv) s.vs_memory` by
    (rpt strip_tac >> irule typed_copy_effect_bytes >>
     goal_assum (drule_at (Pat `typed_copy_effect _ _ _ _ _ _ _ _`)) >>
     `immutable_alloca_sep func cenv cx ee s` by fs[stmt_state_rel_def] >>
     qpat_x_assum `immutable_alloca_sep _ _ _ _ _` mp_tac >>
     simp[immutable_alloca_sep_def] >>
     disch_then (qspecl_then [`nm`, `tv`, `iv`, `off`] mp_tac o CONJUNCT2) >>
     simp[] >> strip_tac >>
     qpat_x_assum `!id b sz. local_region _ _ _ _ _ _ ==> _` drule >>
     simp[regions_disjoint_def] >> decide_tac) >>
  irule memory_place_write_stmt_state >>
  goal_assum (drule_at (Pat `write_place _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `place_ptr_rel _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
  qexistsl_tac [`dtv`, `s`, `sa`] >>
  gvs[typed_copy_effect_def] >>
  metis_tac[]
QED
