Theory exprSimAbiEncodeSourceSuccess
Ancestors
  vyperContext vyperABI vyperABIRoundtrip list arithmetic
  exprSimDefs exprSimHypsDefs vyperTypeSystem

Theorem abi_encode_source_success_list:
  evaluate_type_builtin cx (AbiEncode ensure mid) (TupleT ts) ts vs = INL out ==>
  ?avs. vyper_to_abi_list (get_tenv cx) ts vs = SOME avs
Proof
  simp[evaluate_type_builtin_def, needs_external_call_wrap_def] >>
  Cases_on `~ensure /\ LENGTH ts <= 1` >> simp[]
  >- (Cases_on `ts` >> simp[] >> Cases_on `t` >> simp[] >>
      Cases_on `vs` >> simp[] >> Cases_on `t` >>
      simp[evaluate_abi_encode_bytes_def, AllCaseEqs()] >> rpt strip_tac >>
      gvs[] >> simp[vyper_to_abi_def]) >>
  simp[evaluate_abi_encode_bytes_def, vyper_to_abi_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem abi_encode_source_success_indexed:
  evaluate_type_builtin cx (AbiEncode ensure mid) (TupleT (MAP expr_type args))
    (MAP expr_type args) vs = INL out ==>
  LENGTH args = LENGTH vs /\
  !i. i < LENGTH vs ==> ?av.
    vyper_to_abi (get_tenv cx) (expr_type (EL i args)) (EL i vs) = SOME av
Proof
  strip_tac >> drule abi_encode_source_success_list >> strip_tac >>
  drule vyper_to_abi_list_EL >> strip_tac >> gvs[] >>
  rpt strip_tac >> first_x_assum drule >> simp[EL_MAP] >> metis_tac[]
QED

Theorem abi_encode_body_source_success_indexed:
  expr_body_pre ce cx env (TypeBuiltin ann (AbiEncode ensure mid) target args) es /\
  evaluate_type_builtin cx (AbiEncode ensure mid) target (MAP expr_type args) vs = INL out ==>
  LENGTH args = LENGTH vs /\
  !i. i < LENGTH vs ==> ?av.
    vyper_to_abi (get_tenv cx) (expr_type (EL i args)) (EL i vs) = SOME av
Proof
  strip_tac >>
  `target = TupleT (MAP expr_type args)` by
    gvs[expr_body_pre_def, well_typed_expr_def, well_typed_type_builtin_args_def] >>
  gvs[] >> drule abi_encode_source_success_indexed >> simp[]
QED
