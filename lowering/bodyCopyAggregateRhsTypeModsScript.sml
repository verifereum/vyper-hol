Theory bodyCopyAggregateRhsTypeMods
Ancestors
  exprSimHyps exprSimConcatSource exprSimAbiEncodeArgsPhysicalCapacity
  vyperTypeArgFits vyperTypeDefaults vyperTypeExprSoundness vyperContext
  vyperTypeSystem vyperTyping vyperValue exprLowering allocLimits exprSimProps
  list vfmConstants

(* Transfer the supplied operand layout to the annotations used by Concat. *)
Theorem copy_typed_annotation_list[local]:
  !ts tvs vs.
    LIST_REL (\t tv. evaluate_type tenv t = SOME tv) ts tvs /\
    values_have_types tvs vs ==>
    LIST_REL (\t v. ?tv. evaluate_type tenv t = SOME tv /\ value_has_type tv v) ts vs
Proof
  simp[values_have_types_LIST_REL] >>
  Induct >> Cases_on `tvs` >> Cases_on `vs` >>
  simp[PULL_EXISTS] >> metis_tac[]
QED

Theorem copy_concat_lowered_from_args_mods:
  well_typed_expr env (Builtin ty (Concat n) args) /\
  alloc_limits_expr ce (Builtin ty (Concat n) args) /\
  arg_types_fit (MAP (lowered_value_type ce) args) (MAP expr_type args) /\
  LIST_REL (\t tv. evaluate_type env.type_defs t = SOME tv)
    (MAP (lowered_value_type ce) args) ptvs /\
  LIST_REL (\t tv. evaluate_type env.type_defs t = SOME tv)
    (MAP expr_type args) stvs /\
  values_have_types ptvs vs /\ evaluate_concat n vs = INL v ==>
  value_runtime_typed env (lowered_value_type ce (Builtin ty (Concat n) args)) v
Proof
  strip_tac >>
  drule_all (CONJUNCT2 arg_type_fits_value_has_type) >> strip_tac >>
  drule_all copy_typed_annotation_list >> strip_tac >>
  qpat_x_assum `well_typed_expr _ _` mp_tac >>
  simp[Once well_typed_expr_def, well_typed_builtin_app_def] >> strip_tac >>
  `concat_alloc_size (MAP expr_type args) < 2 ** 64` by
    fs[alloc_limits_expr_def] >>
  `SUM (MAP (concat_payload_capacity o expr_type) args) < 2 ** 64` by
    (qspec_then `MAP expr_type args` strip_assume_tac concat_alloc_size_bounds >>
     fs[MAP_MAP_o]) >>
  `(SUM (MAP (concat_payload_capacity o expr_type) args) + 31) DIV 32 <=
   SUM (MAP (concat_payload_capacity o expr_type) args) + 31` by
    simp[arithmeticTheory.DIV_LESS_EQ] >>
  `MAP bytelike_type_bound (MAP expr_type args) =
   MAP concat_payload_capacity (MAP expr_type args)` by
    (irule concat_payload_capacity_bound >> fs[EVERY_MEM]) >>
  gvs[lowered_value_type_def]
  >- (drule_all typed_bytes_operands >> strip_tac >>
      mp_tac (Q.INST [`ts` |-> `MAP expr_type args`, `tenv` |-> `env.type_defs`]
        evaluate_concat_typed_bytes) >>
      (impl_tac >- fs[]) >> strip_tac >>
      gvs[concat_map_ctor_11, concat_buffer_type_def, value_runtime_typed_def, evaluate_type_def,
          type_slot_size_def, value_has_type_def, MAP_MAP_o,
          vfmConstantsTheory.word_size_def, wordsTheory.dimword_def]) >>
  drule_all typed_string_operands >> strip_tac >>
  mp_tac (Q.INST [`ts` |-> `MAP expr_type args`, `tenv` |-> `env.type_defs`]
    evaluate_concat_typed_string) >>
  (impl_tac >- fs[]) >> strip_tac >>
  gvs[concat_map_ctor_11, concat_buffer_type_def, value_runtime_typed_def, evaluate_type_def,
      type_slot_size_def, value_has_type_def, MAP_MAP_o,
      vfmConstantsTheory.word_size_def, wordsTheory.dimword_def]
QED

(* Both ABI branches type the value in the same dynamic bytes layout. *)
Theorem copy_abi_bytes_runtime_typed[local]:
  LENGTH (abi_encode_method_id_bytes mid ++ bs) <= cap + abi_encode_method_id_size mid /\
  (case mid of NONE => T | SOME sel => LENGTH sel = 4) /\
  32 + 32 * word_size (cap + (case mid of NONE => 0 | SOME _ => 4)) < 2 ** 64 ==>
  value_runtime_typed env (BaseT (BytesT (Dynamic (cap + if IS_SOME mid then 4 else 0))))
    (BytesV (abi_encode_method_id_bytes mid ++ bs))
Proof
  `!k. 32 + 32 * word_size k < 2 ** 64 ==>
       k < dimword(:256) /\ word_size k + 1 <= dimword(:256)` by
    (gen_tac >> qspec_then `k` assume_tac le_word_size_mul >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  Cases_on `mid` >>
  simp[abi_encode_method_id_size_def, vyperASTTheory.abi_encode_method_id_bytes_def] >>
  strip_tac >> fs[] >> res_tac >>
  fs[value_runtime_typed_def, evaluate_type_def, type_slot_size_def,
     value_has_type_def]
QED

Theorem copy_abiencode_lowered_from_args_mods:
  well_typed_type_builtin_args (AbiEncode ensure mid) target (MAP expr_type args) /\
  alloc_limits_expr ce (TypeBuiltin ann (AbiEncode ensure mid) target args) /\
  env.type_defs = get_tenv cx /\ sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  arg_types_fit (MAP (lowered_value_type ce) args) (MAP expr_type args) /\
  LIST_REL (\t tv. evaluate_type (get_tenv cx) t = SOME tv)
    (MAP (lowered_value_type ce) args) ptvs /\
  LIST_REL (\t tv. evaluate_type (get_tenv cx) t = SOME tv)
    (MAP expr_type args) stvs /\
  values_have_types ptvs vs /\
  evaluate_type_builtin cx (AbiEncode ensure mid) target (MAP expr_type args) vs = INL v ==>
  value_runtime_typed env
    (lowered_value_type ce (TypeBuiltin ann (AbiEncode ensure mid) target args)) v
Proof
  strip_tac >> drule alloc_limits_abi_encode_output >> strip_tac >>
  gvs[well_typed_type_builtin_args_def] >>
  Cases_on `LENGTH args = 1 /\ ~ensure`
  >- (Cases_on `args` >> gvs[arg_type_fits_def, values_have_types_LIST_REL] >>
      gvs[evaluate_type_builtin_def, vyperABITheory.needs_external_call_wrap_def,
          CaseEq "sum", lowered_value_type_def] >>
      drule_all abi_args_physical_singleton_capacity >>
      disch_then (qspec_then `mid` assume_tac) >>
      irule copy_abi_bytes_runtime_typed >> simp[]) >>
  `1 <= LENGTH args` by (Cases_on `args` >> fs[]) >>
  `~(~ensure /\ needs_external_call_wrap (TupleT (MAP expr_type args)))` by
    (simp[vyperABITheory.needs_external_call_wrap_def] >>
     metis_tac[arithmeticTheory.EQ_LESS_EQ]) >>
  gvs[evaluate_type_builtin_def, CaseEq "sum", lowered_value_type_def, SF ETA_ss] >>
  drule_all abi_args_physical_tuple_capacity >>
  disch_then (qspec_then `mid` assume_tac) >>
  irule copy_abi_bytes_runtime_typed >>
  simp[] >>
  Cases_on `LENGTH args = 1` >> gvs[]
QED
