(* TOP-LEVEL: compatibility with an event field survives the smaller
   bytelike layout bounds produced by literal and ABI-result lowering.
   Helpers expose exactly the declared types compatible with bytelikes. *)
Theory logArgumentTypes
Ancestors
  vyperEventArgCompat
  typedCopyCompatibility abiTypeBounds abiTypeShape
  vyperTypeSystem vyperAST vyperValue vyperABI exprLowering compileEnv list arithmetic

Theorem event_arg_compatible_bytes_bound:
  !bd n. event_arg_compatible (BaseT (BytesT bd)) (BaseT (BytesT (Dynamic n))) <=>
    ?capacity. bd = Dynamic capacity /\ n <= capacity
Proof
  Cases_on `bd` >> simp[event_arg_compatible_def]
QED

Theorem event_arg_compatible_base_bytestring:
  (!bt n. event_arg_compatible (BaseT bt) (BaseT (StringT n)) <=>
    ?capacity. bt = StringT capacity /\ n <= capacity) /\
  (!bt n. event_arg_compatible (BaseT bt) (BaseT (BytesT (Dynamic n))) <=>
    ?capacity. bt = BytesT (Dynamic capacity) /\ n <= capacity)
Proof
  conj_tac >> rpt gen_tac >> Cases_on `bt` >>
  simp[event_arg_compatible_def, event_arg_compatible_bytes_bound]
QED

Theorem event_arg_compatible_bytestring_rhs:
  (!fty n. event_arg_compatible fty (BaseT (StringT n)) <=>
    ?capacity. fty = BaseT (StringT capacity) /\ n <= capacity) /\
  (!fty n. event_arg_compatible fty (BaseT (BytesT (Dynamic n))) <=>
    ?capacity. fty = BaseT (BytesT (Dynamic capacity)) /\ n <= capacity)
Proof
  conj_tac >> rpt gen_tac >> Cases_on `fty` >>
  simp[event_arg_compatible_def, event_arg_compatible_base_bytestring]
QED

Theorem event_arg_compatible_bytestring_narrow:
  (!fty bound size. event_arg_compatible fty (BaseT (StringT bound)) /\ size <= bound ==>
    event_arg_compatible fty (BaseT (StringT size))) /\
  (!fty bound size. event_arg_compatible fty (BaseT (BytesT (Dynamic bound))) /\ size <= bound ==>
    event_arg_compatible fty (BaseT (BytesT (Dynamic size))))
Proof
  conj_tac >> rw[event_arg_compatible_bytestring_rhs] >> gvs[] >> decide_tac
QED

Theorem literal_bytes_event_arg_compatible:
  !cenv fty bd bs.
    well_typed_literal (BaseT (BytesT bd)) (BytesL bs) /\ event_arg_compatible fty (BaseT (BytesT bd)) ==>
    event_arg_compatible fty (lowered_value_type cenv (Literal (BaseT (BytesT bd)) (BytesL bs)))
Proof
  rpt gen_tac >> Cases_on `bd` >>
  simp[well_typed_literal_def, compatible_bound_def, lowered_value_type_def, expr_type_def] >>
  strip_tac >> gvs[] >> drule_all (CONJUNCT2 event_arg_compatible_bytestring_narrow) >> simp[]
QED

Theorem literal_base_event_arg_compatible:
  !cenv fty bt lit.
    well_typed_literal (BaseT bt) lit /\ event_arg_compatible fty (BaseT bt) ==>
    event_arg_compatible fty (lowered_value_type cenv (Literal (BaseT bt) lit))
Proof
  rpt gen_tac >> Cases_on `bt` >> Cases_on `lit` >> rw[] >>
  FIRST [drule_all literal_bytes_event_arg_compatible >> simp[],
    gvs[well_typed_literal_def, lowered_value_type_def, expr_type_def, AllCaseEqs()] >>
    drule_all (CONJUNCT1 event_arg_compatible_bytestring_narrow) >> simp[]]
QED

Theorem literal_event_arg_compatible:
  !cenv fty ty lit.
    well_typed_literal ty lit /\ event_arg_compatible fty ty ==>
    event_arg_compatible fty (lowered_value_type cenv (Literal ty lit))
Proof
  rpt gen_tac >> Cases_on `ty` >> strip_tac >>
  FIRST [irule literal_base_event_arg_compatible >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC,
         fs[well_typed_literal_def]]
QED

Theorem concat_event_arg_compatible:
  !cenv fty ty n args.
    well_typed_builtin_app ty (Concat n) (MAP expr_type args) /\ event_arg_compatible fty ty ==>
    event_arg_compatible fty (lowered_value_type cenv (Builtin ty (Concat n) args))
Proof
  rpt gen_tac >> simp_tac bool_ss [well_typed_builtin_app_def] >> strip_tac >>
  rpt BasicProvers.VAR_EQ_TAC >>
  `MAP bytelike_type_bound (MAP expr_type args) = MAP concat_payload_capacity (MAP expr_type args)` by
    (irule concat_payload_capacity_bound >> fs[EVERY_MEM]) >>
  `SUM (MAP (concat_payload_capacity o expr_type) args) <= n` by
    (qpat_x_assum `SUM _ <= n` mp_tac >>
     qpat_x_assum `MAP _ _ = MAP _ _` (fn th => REWRITE_TAC [th, GSYM MAP_MAP_o])) >>
  simp[lowered_value_type_def, concat_buffer_type_def] >>
  FIRST [MATCH_MP_TAC (CONJUNCT1 event_arg_compatible_bytestring_narrow),
         MATCH_MP_TAC (CONJUNCT2 event_arg_compatible_bytestring_narrow)] >>
  qexists_tac `n` >> conj_tac >> first_assum ACCEPT_TAC
QED

Theorem abi_encode_source_argument_type:
  !args ensure.
    (case TupleT (MAP expr_type args) of
       TupleT [ty] => if ensure then TupleT (MAP expr_type args) else ty
     | _ => TupleT (MAP expr_type args)) =
    (if LENGTH args = 1 /\ ~ensure then expr_type (HD args) else TupleT (MAP expr_type args))
Proof
  rpt gen_tac >> Cases_on `args` >- simp[] >>
  rename1 `MAP expr_type (first::rest)` >> Cases_on `rest` >> Cases_on `ensure` >> simp[]
QED

Theorem checked_abi_encode_method_id_size:
  !ensure method_id target_ty tys.
    well_typed_type_builtin_args (AbiEncode ensure method_id) target_ty tys ==>
    abi_encode_method_id_size method_id = (if IS_SOME method_id then 4 else 0)
Proof
  rpt gen_tac >> Cases_on `method_id` >>
  simp[well_typed_type_builtin_args_def, abi_encode_method_id_size_def, abi_encode_method_id_bytes_def]
QED

Theorem abi_encode_argument_size_bound:
  !tenv sfields args tvs ensure.
    abi_struct_env_rel tenv sfields /\
    LIST_REL (\e tv. evaluate_type tenv (expr_type e) = SOME tv) args tvs ==>
    abi_size_bound sfields
      (if LENGTH args = 1 /\ ~ensure then expr_type (HD args) else TupleT (MAP expr_type args)) =
    vyper_abi_size_bound tenv
      (if LENGTH args = 1 /\ ~ensure then expr_type (HD args) else TupleT (MAP expr_type args))
Proof
  rpt gen_tac >> strip_tac >> Cases_on `LENGTH args = 1 /\ ~ensure` >> simp[] >-
   (`?tv. evaluate_type tenv (expr_type (HD args)) = SOME tv` by
      (Cases_on `args` >> Cases_on `tvs` >> gvs[]) >>
    drule_all (CONJUNCT1 abi_type_size_bound_joint) >> simp[]) >>
  simp_tac bool_ss [Once vyper_abi_size_bound_def] >>
  qspecl_then [`tenv`, `sfields`, `MAP expr_type args`, `tvs`] mp_tac evaluated_abi_tuple_size_bound >>
  impl_tac >- simp[LIST_REL_MAP1, combinTheory.o_DEF] >> simp[]
QED

Theorem abi_encode_event_arg_compatible:
  !tenv cenv fty ann ensure method_id target_ty args tvs.
    abi_struct_env_rel tenv cenv.ce_struct_fields /\
    LIST_REL (\e tv. evaluate_type tenv (expr_type e) = SOME tv) args tvs /\
    well_typed_type_builtin_args (AbiEncode ensure method_id) target_ty (MAP expr_type args) /\
    type_builtin_result_ok tenv (AbiEncode ensure method_id) ann target_ty (MAP expr_type args) /\
    event_arg_compatible fty ann ==>
    event_arg_compatible fty (lowered_value_type cenv (TypeBuiltin ann (AbiEncode ensure method_id) target_ty args))
Proof
  rpt gen_tac >> strip_tac >>
  `abi_size_bound cenv.ce_struct_fields
    (if LENGTH args = 1 /\ ~ensure then expr_type (HD args) else TupleT (MAP expr_type args)) =
    vyper_abi_size_bound tenv (if LENGTH args = 1 /\ ~ensure then expr_type (HD args) else TupleT (MAP expr_type args))` by
    (drule_all abi_encode_argument_size_bound >> simp[]) >>
  drule_all checked_abi_encode_method_id_size >> DISCH_TAC >>
  qpat_x_assum `type_builtin_result_ok _ _ _ _ _` (mp_tac o REWRITE_RULE [type_builtin_result_ok_def, abi_encode_size_ok_def]) >>
  disch_then (qx_choose_then `annotation_bound` strip_assume_tac) >> gvs[] >>
  `abi_size_bound cenv.ce_struct_fields
    (if LENGTH args = 1 /\ ~ensure then expr_type (HD args) else TupleT (MAP expr_type args)) +
    (if IS_SOME method_id then 4 else 0) <= annotation_bound` by
    (qpat_x_assum `vyper_abi_size_bound tenv _ + _ <= annotation_bound` mp_tac >>
     asm_simp_tac bool_ss [abi_encode_source_argument_type,
       SIMP_RULE (srw_ss()) [] abi_encode_source_argument_type]) >>
  simp_tac bool_ss [lowered_value_type_def, LET_THM] >>
  qspecl_then [`fty`, `annotation_bound`,
    `abi_size_bound cenv.ce_struct_fields
      (if LENGTH args = 1 /\ ~ensure then expr_type (HD args) else TupleT (MAP expr_type args)) +
      (if IS_SOME method_id then 4 else 0)`] mp_tac (CONJUNCT2 event_arg_compatible_bytestring_narrow) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >> first_assum MATCH_ACCEPT_TAC
QED
