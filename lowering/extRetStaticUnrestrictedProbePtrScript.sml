Theory extRetStaticUnrestrictedProbePtr
Ancestors extRetStaticPlanSelectionPtr extRetStaticLoweredFramePtr
  compileEnv exprLowering vyperValue vyperABI contractABI finite_map

(* The unrestricted selector is already type_to_abi_enc_info_static_copy. *)
Definition empty_probe_tenv_def:
  empty_probe_tenv = FEMPTY |+ ((NONE,"E"), StructArgs [])
End
Definition empty_probe_cenv_def:
  empty_probe_cenv = (ARB : compile_env) with
    ce_struct_fields := FEMPTY |+ ("E", [])
End

Theorem empty_struct_static_probe:
  evaluate_type empty_probe_tenv (StructT (NONE,"E")) = SOME (StructTV []) /\
  type_memory_size (StructTV []) = 0 /\
  type_memory_bytes empty_probe_cenv (StructT (NONE,"E")) = 0 /\
  ~is_abi_dynamic empty_probe_cenv.ce_struct_fields (StructT (NONE,"E")) /\
  type_to_abi_enc_info empty_probe_cenv.ce_struct_fields empty_probe_cenv
    (StructT (NONE,"E")) = AbiCopy 0 /\
  abi_size_bound empty_probe_cenv.ce_struct_fields (StructT (NONE,"E")) = 0
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

Theorem empty_struct_array_static_probe:
  evaluate_type empty_probe_tenv (ArrayT (StructT (NONE,"E")) (Fixed 2)) = NONE /\
  type_memory_size (ArrayTV (StructTV []) (Fixed 2)) = 0 /\
  type_memory_bytes empty_probe_cenv (ArrayT (StructT (NONE,"E")) (Fixed 2)) = 0 /\
  ~is_abi_dynamic empty_probe_cenv.ce_struct_fields (ArrayT (StructT (NONE,"E")) (Fixed 2)) /\
  type_to_abi_enc_info empty_probe_cenv.ce_struct_fields empty_probe_cenv
    (ArrayT (StructT (NONE,"E")) (Fixed 2)) = AbiCopy 0 /\
  abi_size_bound empty_probe_cenv.ce_struct_fields (ArrayT (StructT (NONE,"E")) (Fixed 2)) = 0
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED

Theorem empty_struct_word_tuple_static_probe:
  evaluate_type empty_probe_tenv
    (TupleT [StructT (NONE,"E"); BaseT (UintT 256)]) =
    SOME (TupleTV [StructTV []; BaseTV (UintT 256)]) /\
  type_memory_size (TupleTV [StructTV []; BaseTV (UintT 256)]) = 32 /\
  type_memory_bytes empty_probe_cenv
    (TupleT [StructT (NONE,"E"); BaseT (UintT 256)]) = 32 /\
  ~is_abi_dynamic empty_probe_cenv.ce_struct_fields
    (TupleT [StructT (NONE,"E"); BaseT (UintT 256)]) /\
  type_to_abi_enc_info empty_probe_cenv.ce_struct_fields empty_probe_cenv
    (TupleT [StructT (NONE,"E"); BaseT (UintT 256)]) = AbiCopy 32 /\
  abi_size_bound empty_probe_cenv.ce_struct_fields
    (TupleT [StructT (NONE,"E"); BaseT (UintT 256)]) = 32
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def]
QED
