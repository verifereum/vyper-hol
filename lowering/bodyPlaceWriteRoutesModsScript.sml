(* Source resources at the reached cut of a linked place write. *)
Theory bodyPlaceWriteRoutesMods
Ancestors
  bodyFullPredsMods bodyWriteSubscriptSourceMods tuplePlaceSourceHead

Theorem place_write_reached_source_mods[local]:
  expr_sim_inv_mods mods cenv cx env es /\
  body_const_cells_agree_mods mods cx env es /\
  IS_SOME (type_place_target env bt) /\
  (!i st. MEM i (target_indices bt) /\ expr_sim_inv_mods mods cenv cx env st ==>
          expr_body_pre_mods mods cenv cx env i st) /\
  eval_target_place cx bt es = (INL p,mid) ==>
  expr_sim_inv_mods mods cenv cx env mid /\
  body_const_cells_agree_mods mods cx env mid
Proof
  strip_tac >> drule_then assume_tac tuple_place_target_base_inversion >>
  drule_all_then ACCEPT_TAC write_base_reached_source_mods
QED
