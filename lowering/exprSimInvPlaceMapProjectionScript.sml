Theory exprSimInvPlaceMapProjection
Ancestors exprSimHypsDefs

Theorem expr_sim_inv_place_map_tables_agree_on_defined:
  expr_sim_inv cenv cx env es ==>
  place_map_tables_agree_on_defined cenv env
Proof
  rewrite_tac[expr_sim_inv_def] >> strip_tac >> first_assum ACCEPT_TAC
QED
