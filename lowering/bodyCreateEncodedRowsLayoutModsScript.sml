(* Constructor encoding uses the same tuple payload at the source types
   and at the physical row types; only the latter set the buffer bound. *)
Theory bodyCreateEncodedRowsLayoutMods
Ancestors
  bodyFullExtCallDirectLayout[qualified] exprLowering compileEnv vyperCreate
  vyperState vyperAST vyperTyping vyperTypeArgFits vyperABI vyperValue
  abiEncodeValuesMetadata context contractABI list

Theorem create_encoded_rows_layout_mods:
  LENGTH args = LENGTH vs /\ LENGTH args = LENGTH (vals:vyper_value list) /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!i. i < LENGTH args ==> ?tv ftv.
    evaluate_type (get_tenv cx) (lowered_value_type ce (EL i args)) = SOME tv /\
    evaluate_type (get_tenv cx) (expr_type (EL i args)) = SOME ftv /\
    arg_type_fits (lowered_value_type ce (EL i args)) (expr_type (EL i args)) /\
    value_has_type tv (EL i vs) /\ value_has_type ftv (EL i vs)) ==>
  ?ats avs bytes.
    encode_create_ctor_args (get_tenv cx) (MAP expr_type args) vs = SOME bytes /\
    vyper_to_abi_list (get_tenv cx) (MAP (lowered_value_type ce) args) vs = SOME avs /\
    ats = vyper_to_abi_types (get_tenv cx) (MAP (lowered_value_type ce) args) /\
    bytes = contractABI$enc (contractABI$Tuple ats) (contractABI$ListV avs) /\
    LENGTH bytes <= abi_size_bound ce.ce_struct_fields (TupleT (MAP (lowered_value_type ce) args)) /\
    LIST_REL abi_encoder_layout_valid ats avs /\
    LIST_REL (\row at. abi_embedded_static_size ce.ce_struct_fields (SND row) =
                         abi_member_head_size at) (ZIP (vals,MAP (lowered_value_type ce) args)) ats
Proof
  strip_tac >>
  qabbrev_tac `tys = MAP (lowered_value_type ce) args` >>
  qabbrev_tac `src = MAP expr_type args` >>
  `?avs ats bytes.
    vyper_to_abi_list (get_tenv cx) tys vs = SOME avs /\
    ats = vyper_to_abi_types (get_tenv cx) tys /\
    bytes = contractABI$enc (contractABI$Tuple ats) (contractABI$ListV avs) /\
    build_ext_calldata (get_tenv cx) "" src vs =
      SOME (function_selector "" (vyper_to_abi_types (get_tenv cx) src) ++ bytes) /\
    LENGTH bytes <= abi_size_bound ce.ce_struct_fields (TupleT tys) /\
    LIST_REL abi_encoder_layout_valid ats avs /\
    LIST_REL (\row at. abi_embedded_static_size ce.ce_struct_fields (SND row) =
                    abi_member_head_size at) (ZIP (vals,tys)) ats` by
    (irule bodyFullExtCallDirectLayoutTheory.extcall_direct_args_layout >>
     simp[Abbr `tys`, Abbr `src`, EL_MAP]) >>
  qexistsl [`ats`,`avs`,`bytes`] >> asm_rewrite_tac[] >>
  `TAKE (LENGTH vs) src = src` by simp[Abbr `src`, TAKE_LENGTH_ID_rwt] >>
  qpat_x_assum `build_ext_calldata _ _ _ _ = SOME _` mp_tac >>
  simp[vyperABITheory.build_ext_calldata_def, encode_create_ctor_args_def] >>
  Cases_on `vyper_to_abi_list (get_tenv cx) src vs` >> simp[]
QED
