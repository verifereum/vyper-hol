(*
 * The create body cases over the finite-horizon joint judgment, one per
 * create kind.
 *
 * TOP-LEVEL: create_minimal_proxy_expr_full_ok, create_copy_expr_full_ok,
 *   create_blueprint_expr_full_ok, raw_create_expr_full_ok
 *
 * Each is admitted, held on the creation body case. They discharge case 47
 * of body_sim_full_mutual (the CreateTarget call).
 *)
Theory bodyFullCreateHeld
Ancestors
  bodyFullPreds

(* GATE_ADMISSION: held, creation body case; create_minimal_proxy_to *)
Theorem create_minimal_proxy_expr_full_ok:
  !cx ty s r ks es d.
    body_exprs_full_ok cx es ==>
    body_expr_full_ok cx (Call ty (CreateTarget CreateMinimalProxy s r ks) es d)
Proof
  cheat
QED

(* GATE_ADMISSION: held, creation body case; create_copy_of *)
Theorem create_copy_expr_full_ok:
  !cx ty s r ks es d.
    body_exprs_full_ok cx es ==>
    body_expr_full_ok cx (Call ty (CreateTarget CreateCopyOf s r ks) es d)
Proof
  cheat
QED

(* GATE_ADMISSION: held, creation body case; create_from_blueprint *)
Theorem create_blueprint_expr_full_ok:
  !cx ty b s r ks es d.
    body_exprs_full_ok cx es ==>
    body_expr_full_ok cx
      (Call ty (CreateTarget (CreateFromBlueprint b) s r ks) es d)
Proof
  cheat
QED

(* GATE_ADMISSION: held, creation body case; raw_create *)
Theorem raw_create_expr_full_ok:
  !cx ty s r ks es d.
    body_exprs_full_ok cx es ==>
    body_expr_full_ok cx (Call ty (CreateTarget RawCreate s r ks) es d)
Proof
  cheat
QED
