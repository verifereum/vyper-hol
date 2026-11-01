(* Boundary probes for the internal-call simulation interfaces. *)
Theory bodyIntCallInterfaces
Ancestors
  bodySim supportedDecls vyperInterpreter exprSimHyps

Theorem body_inv_func_info_update:
  !tops ctx cenv cx info.
    body_inv tops ctx (cenv with ce_func_info := info) cx <=>
    body_inv tops ctx cenv cx
Proof
  simp[body_inv_def]
QED

Theorem expr_sim_inv_func_info_update:
  !cenv cx env es info.
    expr_sim_inv (cenv with ce_func_info := info) cx env es <=>
    expr_sim_inv cenv cx env es
Proof
  simp[expr_sim_inv_def]
QED

