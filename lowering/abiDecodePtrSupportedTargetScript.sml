(* Supported-program target metadata, independent of the expression bridge. *)
Theory abiDecodePtrSupportedTarget
Ancestors
  abiDecodePtrSupportExpr abiDecodePtrSupportStmt abiDecodePtrTarget
  supportedProgram supportedDecls supportedExprForms supportedTypes gasContext bodySim
  vyperAST list

Theorem abi_decode_target_root_shape[local]:
  !e. expr_abi_decode_target_root target e ==>
    ?ann tb decoded args. e = TypeBuiltin ann tb decoded args
Proof
  Cases >> simp[expr_abi_decode_target_root_def] >>
  rename1 `TypeBuiltin ann tb decoded args` >> Cases_on `tb` >>
  simp[expr_abi_decode_target_root_def]
QED

Theorem supported_abi_decode_root_target[local]:
  supported_type_builtin_form tops ann tb decoded args /\
  expr_abi_decode_target_root target (TypeBuiltin ann tb decoded args) ==>
  ?tys. target = TupleT tys /\ EVERY supported_scalar_type tys /\ 2 <= LENGTH tys
Proof
  Cases_on `tb` >> simp[expr_abi_decode_target_root_def] >>
  rename1 `AbiDecode unwrap` >> Cases_on `unwrap` >>
  namedCases_on `args` ["", "head tail"] >>
  simp[supported_type_builtin_form_def] >>
  Cases_on `tail` >> gvs[] >> rpt strip_tac >> gvs[] >>
  rename1 `supported_tuple_type ty` >>
  Cases_on `ty` >> gvs[supported_tuple_type_def]
QED

Theorem supported_occurring_abi_decode_target:
  supported_program tops /\ occurs_abi_decode_target target tops ==>
  ?tys. target = TupleT tys /\ EVERY supported_scalar_type tys /\ 2 <= LENGTH tys
Proof
  strip_tac >> spose_not_then assume_tac >>
  `!ann tb decoded args. supported_type_builtin_form tops ann tb decoded args ==>
    ~expr_abi_decode_target_root target (TypeBuiltin ann tb decoded args)` by
    metis_tac[supported_abi_decode_root_target] >>
  `!e. supported_expr tops e ==> ~supported_expr_exists (expr_abi_decode_target_root target) e` by
    metis_tac[supported_expr_type_builtin_exclusion, abi_decode_target_root_shape] >>
  assume_tac abi_decode_target_root_shape >>
  drule supported_stmts_type_builtin_exclusion >>
  strip_tac >>
  gvs[occurs_abi_decode_target_def, EXISTS_MEM] >>
  drule_all supported_program_declaration >> strip_tac >>
  rename1 `declaration_abi_decode_target target decl` >> Cases_on `decl` >>
  gvs[declaration_abi_decode_target_def, supported_declaration_body_def,
      supported_function_body_def, supported_declaration_header_def] >> metis_tac[]
QED

Theorem abi_decode_body_target_metadata:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (TypeBuiltin ann (AbiDecode unwrap) target args) es ==>
  ?tys. target = TupleT tys /\ EVERY supported_scalar_type tys /\ 2 <= LENGTH tys
Proof
  strip_tac >> drule abi_decode_body_target_occurs >>
  `cx_tops cx = tops` by (gvs[body_inv_def] >> metis_tac[cx_tops_module]) >>
  gvs[body_inv_def] >> metis_tac[supported_occurring_abi_decode_target]
QED
