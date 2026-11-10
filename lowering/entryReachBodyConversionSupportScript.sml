Theory entryReachBodyConversionSupport
Ancestors
  supportedTypes vyperTypeDefaults vyperABIRoundtrip finite_map list combin

(* The ABI leaves of the entry decode chain: the supported scalars, flags,
   and every fixed bytesM (bytes0 and bytes20 included). *)
Definition entry_abi_leaf_def:
  entry_abi_leaf ty <=>
    supported_scalar_type ty \/ (?nsid. ty = FlagT nsid) \/
    (?n. ty = BaseT (BytesT (Fixed n)) /\ n <= 32)
End

Theorem entry_abi_leaf_aggregate[simp]:
  ~entry_abi_leaf (ArrayT t bd) /\ ~entry_abi_leaf (TupleT ts) /\
  ~entry_abi_leaf (StructT id)
Proof
  simp[entry_abi_leaf_def, supported_scalar_type_def, supported_word_type_def,
       supported_string_type_def]
QED

Theorem entry_abi_leaf_scalar:
  supported_scalar_type ty ==> entry_abi_leaf ty
Proof
  simp[entry_abi_leaf_def]
QED

Inductive entry_abi_support:
  (!env ty. entry_abi_leaf ty ==> entry_abi_support env ty) /\
  (!env t bd. entry_abi_support env t ==>
              entry_abi_support env (ArrayT t bd)) /\
  (!env ts. EVERY (entry_abi_support env) ts ==>
            entry_abi_support env (TupleT ts)) /\
  (!env id fields.
    FLOOKUP env id = SOME (StructArgs fields) /\
    EVERY (\f. entry_abi_support (env \\ id) (SND f)) fields ==>
    entry_abi_support env (StructT id))
End

Theorem entry_abi_support_array:
  entry_abi_support env (ArrayT t bd) <=> entry_abi_support env t
Proof
  CONV_TAC (LHS_CONV (REWR_CONV entry_abi_support_cases)) >>
  simp[o_DEF]
QED

Theorem entry_abi_support_tuple:
  entry_abi_support env (TupleT ts) <=> EVERY (entry_abi_support env) ts
Proof
  CONV_TAC (LHS_CONV (REWR_CONV entry_abi_support_cases)) >>
  simp[o_DEF]
QED

Theorem entry_abi_support_struct:
  entry_abi_support env (StructT id) <=>
  ?fields. FLOOKUP env id = SOME (StructArgs fields) /\
           EVERY (entry_abi_support (env \\ id) o SND) fields
Proof
  CONV_TAC (LHS_CONV (REWR_CONV entry_abi_support_cases)) >>
  simp[o_DEF]
QED

Theorem entry_conversion_default_boundary[local]:
  evaluate_type env ty = SOME tv ==>
  value_has_type tv (default_value tv) /\
  vyper_to_abi env ty (default_value tv) = SOME (default_to_abi tv)
Proof
  metis_tac[default_value_has_type_thm, vyper_to_abi_default_value]
QED

