(* Request-prefix companion to bodyFullCreateHeld. *)
Theory s1PrefixCreateHeld
Ancestors
  s1PrefixPreds bodyFullCreateHeld

Theorem create_minimal_proxy_expr_prefix_ok:
  !cx ty s r ks es d.
  body_exprs_full_ok cx (create_operand_order CreateMinimalProxy s es) /\
  body_exprs_prefix_ok cx (create_operand_order CreateMinimalProxy s es) ==>
  body_expr_prefix_ok cx (Call ty (CreateTarget CreateMinimalProxy s r ks) es d)
Proof
  cheat
QED

Theorem create_copy_expr_prefix_ok:
  !cx ty s r ks es d.
  body_exprs_full_ok cx (create_operand_order CreateCopyOf s es) /\
  body_exprs_prefix_ok cx (create_operand_order CreateCopyOf s es) ==>
  body_expr_prefix_ok cx (Call ty (CreateTarget CreateCopyOf s r ks) es d)
Proof
  cheat
QED

Theorem create_blueprint_expr_prefix_ok:
  !cx ty b s r ks es d.
  body_exprs_full_ok cx (create_operand_order (CreateFromBlueprint b) s es) /\
  body_exprs_prefix_ok cx (create_operand_order (CreateFromBlueprint b) s es) ==>
  body_expr_prefix_ok cx
      (Call ty (CreateTarget (CreateFromBlueprint b) s r ks) es d)
Proof
  cheat
QED

Theorem raw_create_expr_prefix_ok:
  !cx ty s r ks es d.
  body_exprs_full_ok cx (create_operand_order RawCreate s es) /\
  body_exprs_prefix_ok cx (create_operand_order RawCreate s es) ==>
  body_expr_prefix_ok cx (Call ty (CreateTarget RawCreate s r ks) es d)
Proof
  cheat
QED
