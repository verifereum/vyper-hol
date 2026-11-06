Theory extRetRecursiveDomainProbePtr
Ancestors extRetStaticUnrestrictedProbePtr extRetFrameFactsPtr
  extRetStaticCapacityPtr supportedTypes supportedDecls vyperTypeSystem

Definition recursive_probe_tops_def:
  recursive_probe_tops = [StructDecl "E" []]
End

Theorem recursive_probe_maps:
  type_env recursive_probe_tops = empty_probe_tenv /\
  make_struct_fields_map recursive_probe_tops = empty_probe_cenv.ce_struct_fields
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def, vyperValueTheory.type_slot_size_def]
QED

Theorem recursive_mixed_tuple_domain:
  supported_place_type recursive_probe_tops
    (TupleT [StructT (NONE,"E"); BaseT (UintT 256)]) /\
  well_formed_type empty_probe_tenv
    (TupleT [StructT (NONE,"E"); BaseT (UintT 256)]) /\
  ~assignable_type empty_probe_tenv
    (TupleT [StructT (NONE,"E"); BaseT (UintT 256)])
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def, vyperValueTheory.type_slot_size_def]
QED

Theorem recursive_empty_array_domain:
  supported_place_type recursive_probe_tops
    (ArrayT (StructT (NONE,"E")) (Fixed 2)) /\
  ~well_formed_type empty_probe_tenv
    (ArrayT (StructT (NONE,"E")) (Fixed 2)) /\
  ~assignable_type empty_probe_tenv
    (ArrayT (StructT (NONE,"E")) (Fixed 2))
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def, vyperValueTheory.type_slot_size_def]
QED

Theorem recursive_mixed_array_probe:
  supported_place_type recursive_probe_tops
    (ArrayT (TupleT [StructT (NONE,"E"); BaseT (UintT 256)]) (Fixed 2)) /\
  well_formed_type empty_probe_tenv
    (ArrayT (TupleT [StructT (NONE,"E"); BaseT (UintT 256)]) (Fixed 2)) /\
  ~assignable_type empty_probe_tenv
    (ArrayT (TupleT [StructT (NONE,"E"); BaseT (UintT 256)]) (Fixed 2)) /\
  evaluate_type empty_probe_tenv
    (ArrayT (TupleT [StructT (NONE,"E"); BaseT (UintT 256)]) (Fixed 2)) =
    SOME (ArrayTV (TupleTV [StructTV []; BaseTV (UintT 256)]) (Fixed 2)) /\
  ~is_abi_dynamic empty_probe_cenv.ce_struct_fields
    (ArrayT (TupleT [StructT (NONE,"E"); BaseT (UintT 256)]) (Fixed 2)) /\
  type_to_abi_enc_info empty_probe_cenv.ce_struct_fields empty_probe_cenv
    (ArrayT (TupleT [StructT (NONE,"E"); BaseT (UintT 256)]) (Fixed 2)) = AbiCopy 64 /\
  type_memory_bytes empty_probe_cenv
    (ArrayT (TupleT [StructT (NONE,"E"); BaseT (UintT 256)]) (Fixed 2)) = 64
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def, vyperValueTheory.type_slot_size_def]
QED

(* The representation premises of the static statement consumer compute
   without assignability, including the mixed array's nonzero copy size. *)
Theorem recursive_mixed_array_consumer_layout:
  ~is_dynamic (vyper_to_abi_type empty_probe_tenv
    (ArrayT (TupleT [StructT (NONE,"E"); BaseT (UintT 256)]) (Fixed 2))) /\
  type_memory_size
    (ArrayTV (TupleTV [StructTV []; BaseTV (UintT 256)]) (Fixed 2)) = 64 /\
  vyper_abi_size_bound empty_probe_tenv
    (ArrayT (TupleT [StructT (NONE,"E"); BaseT (UintT 256)]) (Fixed 2)) = 64
Proof
  EVAL_TAC
QED
