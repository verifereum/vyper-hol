(* Typed live local selections strengthen the ordinary value post. *)
Theory bodyIntCallPostProvenanceLivePost
Ancestors
  bodyIntCallProducerInterface bodyIntCallArgType bodySimAugPlaceLoad
  exprSimHypsDefs vyperTypeStatePreservation loweringPosts bodyIntCallPathLayout
  loweringStateRelDefs

Theorem vv_post_live_memory_intcall_provenance:
  expr_sim_inv cenv cx env ee /\
  vv_post ctx func cenv cx e es sa sb s0 ee
    (PlaceR (MemoryPlace n path)) vv s /\
  ~expr_has_effect e /\
  (!v. read_result cx (PlaceR (MemoryPlace n path)) ee = (INL v,ee) ==>
    ?entry. lookup_scopes n ee.scopes = SOME entry /\
      evaluate_subscripts entry.type entry.value path = INL v) ==>
  intcall_vv_provenance cenv cx (expr_type e) sa sb ee
    (PlaceR (MemoryPlace n path)) vv s
Proof
  strip_tac >>
  `post_value_type cenv e = expr_type e` by
    metis_tac[effect_free_post_value_type] >>
  gvs[vv_post_def, intcall_vv_provenance_def] >>
  Cases_on `vv` >> gvs[vv_at_def, expr_val_at_def] >>
  rpt strip_tac >> gvs[]
  >>~- ([`FLOOKUP s.vs_allocas aid = SOME (b,sz)`], metis_tac[])
  >>~- ([`local_place_at cenv cx id (w2n w - b) tvt (PlaceR (MemoryPlace n path))`],
      gvs[local_place_at_def] >>
      `tv0 = entry.type` by
        (drule aug_place_entry_type_agrees >>
         disch_then (qspecl_then [`t0`, `ee`, `id`, `entry`] mp_tac) >> simp[]) >>
      `value_has_type entry.type entry.value` by
        (irule lookup_scopes_state_well_typed_value_has_type >>
         gvs[expr_sim_inv_def] >> metis_tac[]) >>
      `sub_layout entry.type entry.value (w2n w - b) tvt v` by
        (irule mem_path_selection_sub_layout >> metis_tac[]) >>
      gvs[local_region_def] >>
      ntac 3 disj2_tac >>
      qexistsl [`id`, `sz`, `entry`, `p'`, `w'`, `w2n w - w2n w'`] >>
      simp[local_region_def] >> metis_tac[]) >>
  gvs[vv_holds_def, immutable_holds_def] >> metis_tac[]
QED
