Theory extRetRecursiveDynamicProbePtr
Ancestors extRetRecursiveDomainProbePtr extRetStaticUnrestrictedProbePtr
  compileEnv exprLowering supportedTypes vyperTypeSystem

Theorem recursive_dynamic_empty_array_excluded:
  supported_place_type recursive_probe_tops
    (ArrayT (StructT (NONE,"E")) (Dynamic 2)) /\
  ~well_formed_type empty_probe_tenv
    (ArrayT (StructT (NONE,"E")) (Dynamic 2)) /\
  evaluate_type empty_probe_tenv
    (ArrayT (StructT (NONE,"E")) (Dynamic 2)) = NONE /\
  is_abi_dynamic empty_probe_cenv.ce_struct_fields
    (ArrayT (StructT (NONE,"E")) (Dynamic 2))
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def, vyperValueTheory.type_slot_size_def] >> EVAL_TAC
QED

Theorem recursive_dynamic_mixed_array_domain:
  supported_place_type recursive_probe_tops
    (ArrayT (TupleT [StructT (NONE,"E"); BaseT (UintT 256)]) (Dynamic 2)) /\
  well_formed_type empty_probe_tenv
    (ArrayT (TupleT [StructT (NONE,"E"); BaseT (UintT 256)]) (Dynamic 2)) /\
  ~assignable_type empty_probe_tenv
    (ArrayT (TupleT [StructT (NONE,"E"); BaseT (UintT 256)]) (Dynamic 2)) /\
  evaluate_type empty_probe_tenv
    (ArrayT (TupleT [StructT (NONE,"E"); BaseT (UintT 256)]) (Dynamic 2)) =
    SOME (ArrayTV (TupleTV [StructTV []; BaseTV (UintT 256)]) (Dynamic 2)) /\
  type_to_abi_enc_info empty_probe_cenv.ce_struct_fields empty_probe_cenv
    (ArrayT (TupleT [StructT (NONE,"E"); BaseT (UintT 256)]) (Dynamic 2)) =
    AbiDynArray (AbiCopy 32) 32 32 F
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def, vyperValueTheory.type_slot_size_def] >> EVAL_TAC
QED

Theorem recursive_dynamic_tuple_domain:
  supported_place_type recursive_probe_tops
    (TupleT [StructT (NONE,"E"); BaseT (BytesT (Dynamic 2))]) /\
  well_formed_type empty_probe_tenv
    (TupleT [StructT (NONE,"E"); BaseT (BytesT (Dynamic 2))]) /\
  ~assignable_type empty_probe_tenv
    (TupleT [StructT (NONE,"E"); BaseT (BytesT (Dynamic 2))]) /\
  type_to_abi_enc_info empty_probe_cenv.ce_struct_fields empty_probe_cenv
    (TupleT [StructT (NONE,"E"); BaseT (BytesT (Dynamic 2))]) =
    AbiComplex [(AbiCopy 0,0,0,F); (AbiBytestring 2,32,64,T)]
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def, vyperValueTheory.type_slot_size_def] >> EVAL_TAC
QED

Definition widening_probe_cenv_def:
  widening_probe_cenv = empty_probe_cenv with ce_func_return_type :=
    (\name. ArrayT (BaseT (UintT 256)) (Dynamic 1))
End

Theorem recursive_array_widening_dispatch:
  type_widens_to empty_probe_tenv
    (ArrayT (BaseT (UintT 256)) (Dynamic 1))
    (ArrayT (BaseT (UintT 256)) (Dynamic 2)) /\
  (let ty = ArrayT (BaseT (UintT 256)) (Dynamic 2) in
   let e = Call ty (IntCall (NONE,"f")) [] NONE in
   let src_ty = lowered_value_type widening_probe_cenv e in
     src_ty = ArrayT (BaseT (UintT 256)) (Dynamic 1) /\
     ~is_word_type ty /\
     ~(is_bytestring_type ty /\ is_bytestring_type src_ty) /\ src_ty <> ty)
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED
