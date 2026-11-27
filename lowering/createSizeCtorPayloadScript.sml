(* Constructor arguments use the direct ABI tuple encoder at their physical
   types, whereas source CREATE uses the expression annotations. *)
Theory createSizeCtorPayload
Ancestors
  bodyFullExtCallDirectLayout abiEncoderStaticRepresentative exprLowering
  vyperCreate vyperABI vyperAST contractABI emitHelper list rich_list

Theorem create_ctor_payload_empty[simp]:
  encode_create_ctor_args tenv [] [] = SOME []
Proof
  simp[encode_create_ctor_args_def, REV_DEF]
QED

Theorem create_ctor_payload_layout:
  LENGTH args = LENGTH vs /\ LENGTH args = LENGTH saved /\
  sfields_tenv_consistent sf tenv /\
  (!i. i < LENGTH args ==>
    ?tv stv. evaluate_type tenv (lowered_value_type ce (EL i args)) = SOME tv /\
      evaluate_type tenv (expr_type (EL i args)) = SOME stv /\
      arg_type_fits (lowered_value_type ce (EL i args)) (expr_type (EL i args)) /\
      value_has_type tv (EL i vs) /\ value_has_type stv (EL i vs)) ==>
  ?avs ats bytes.
    vyper_to_abi_list tenv (MAP (lowered_value_type ce) args) vs = SOME avs /\
    ats = vyper_to_abi_types tenv (MAP (lowered_value_type ce) args) /\
    bytes = enc (Tuple ats) (ListV avs) /\
    encode_create_ctor_args tenv (MAP expr_type args) vs = SOME bytes /\
    LENGTH bytes <= abi_size_bound sf (TupleT (MAP (lowered_value_type ce) args)) /\
    LIST_REL abi_encoder_layout_valid ats avs /\
    LIST_REL (\row at. abi_embedded_static_size sf (SND row) = abi_member_head_size at)
      (ZIP (saved,MAP (lowered_value_type ce) args)) ats
Proof
  strip_tac >>
  mp_tac (Q.INST [`tys` |-> `MAP (lowered_value_type ce) args`,
                 `arg_types` |-> `MAP expr_type args`, `env` |-> `tenv`,
                 `fname` |-> `""`] extcall_direct_args_layout) >>
  impl_tac >- simp[EL_MAP] >>
  disch_then (qx_choosel_then [`avs`, `ats`, `bytes`] strip_assume_tac) >>
  qexistsl_tac [`avs`, `ats`, `bytes`] >> simp[] >>
  qpat_x_assum `build_ext_calldata _ _ _ _ = _` mp_tac >>
  `TAKE (LENGTH vs) (MAP expr_type args) = MAP expr_type args` by
    metis_tac[TAKE_LENGTH_ID_rwt, LENGTH_MAP] >>
  simp[build_ext_calldata_def, encode_create_ctor_args_def, AllCaseEqs()]
QED

Theorem create_ctor_args_snapshots:
  !args.
    compile_create_ctor_args cfn ce args =
    compile_abi_encode_args cfn ce args
Proof
  Induct >> simp[compile_abi_encode_args_def, compile_create_ctor_args_def,
                 compile_ext_call_args_def]
QED
