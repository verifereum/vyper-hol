(* Conditional boundary for an immutable target across an index effect.
   Root lookup equality is a diagnostic hypothesis, not a body premise. *)
Theory popNestedImmutableTransport
Ancestors
  popNestedImmutableIndexFrame exprSimPopImmutableTarget

Theorem imm_place_at_root_lookup[local]:
  FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
             NONE => FEMPTY | SOME imms => get_source_immutables src imms) id =
  FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of
             NONE => FEMPTY | SOME imms => get_source_immutables src imms) id /\
  imm_place_at cenv cx es (PlaceR (ImmutablePlace src id path)) w ty ==>
  imm_place_at cenv cx ee (PlaceR (ImmutablePlace src id path)) w ty
Proof
  simp[imm_place_at_def] >> metis_tac[]
QED

Theorem imm_target_post_index_root_lookup:
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM em.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_var <= sn.cs_next_var /\
  imm_target_post ctx func cenv cx es sa sm s0 em
    (PlaceR (ImmutablePlace src id path)) ty rb t /\
  FLOOKUP (case ALOOKUP em.immutables cx.txn.target of
             NONE => FEMPTY | SOME imms => get_source_immutables src imms) id =
  FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of
             NONE => FEMPTY | SOME imms => get_source_immutables src imms) id /\
  (!l. FST rb <> Label l) /\
  expr_post ctx func cenv cx e em sm sn t ee v op u ==>
  imm_target_post ctx func cenv cx es sa sn s0 ee
    (PlaceR (ImmutablePlace src id path)) ty rb u
Proof
  strip_tac >> irule imm_target_post_index >>
  goal_assum (drule_at Any) >> simp[] >>
  metis_tac[imm_place_at_root_lookup]
QED
