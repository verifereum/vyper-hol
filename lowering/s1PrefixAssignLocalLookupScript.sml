Theory s1PrefixAssignLocalLookup
Ancestors
  exprSimHypsDefs finite_map

Theorem expr_sim_inv_local_ce_var_type:
  !cenv cx env es id ty.
    expr_sim_inv cenv cx env es /\ FLOOKUP env.var_types id = SOME ty ==>
    cenv.ce_var_type id = SOME ty
Proof
  rw[expr_sim_inv_def] >>
  qpat_x_assum `!id ty. _ ==> cenv.ce_var_type id = SOME ty` drule >>
  simp[]
QED
