Theory entryReachBodyConversionSupport
Ancestors
  supportedTypes vyperTypeDefaults vyperTypeSystem vyperABIRoundtrip finite_map
  list combin

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

(* So narrowing a supported_scalar_type premise to entry_abi_leaf minus
   bytes0 is a weakening. *)
Theorem supported_scalar_type_not_bytes0:
  supported_scalar_type ty ==> ty <> BaseT (BytesT (Fixed 0))
Proof
  rpt strip_tac >>
  gvs[supported_scalar_type_def, supported_word_type_def,
      supported_string_type_def]
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

Theorem uint_width_at_least_8[local]:
  0 < m /\ m MOD 8 = 0 ==> 8 <= m
Proof
  strip_tac >> spose_not_then assume_tac >>
  `m < 8` by decide_tac >> gvs[arithmeticTheory.LESS_MOD]
QED

(* What the checker admits as a parameter type (params_ok) is an entry
   ABI type: every base type evaluate_type accepts is a leaf. *)
Theorem assignable_type_entry_abi_support:
  !env ty. assignable_type env ty ==> entry_abi_support env ty
Proof
  recInduct assignable_type_ind >> rpt strip_tac
  >~ [`assignable_type _ (BaseT bt)`]
  >- (irule (cj 1 entry_abi_support_rules) >>
      Cases_on `bt` >> TRY (Cases_on `b`) >>
      gvs[assignable_type_def, well_formed_type_def,
          vyperValueTheory.evaluate_type_def, COND_RAND,
          entry_abi_leaf_def, supported_scalar_type_def,
          supported_word_type_def, supported_string_type_def,
          supported_int_width_def, uint_width_at_least_8])
  >~ [`assignable_type _ (TupleT tys)`]
  >- gvs[assignable_type_def, entry_abi_support_tuple, EVERY_MEM]
  >~ [`assignable_type _ (ArrayT elem bd)`]
  >- gvs[assignable_type_def, entry_abi_support_array]
  >~ [`assignable_type _ (StructT nsid)`]
  >- (gvs[assignable_type_def, entry_abi_support_struct] >>
      Cases_on `FLOOKUP tenv nsid` >> gvs[] >>
      rename1 `FLOOKUP tenv nsid = SOME targs` >> Cases_on `targs` >>
      gvs[EVERY_MEM])
  >~ [`assignable_type _ (FlagT nsid)`]
  >- (irule (cj 1 entry_abi_support_rules) >> simp[entry_abi_leaf_def])
  >> gvs[assignable_type_def]
QED

Theorem entry_conversion_default_boundary[local]:
  evaluate_type env ty = SOME tv ==>
  value_has_type tv (default_value tv) /\
  vyper_to_abi env ty (default_value tv) = SOME (default_to_abi tv)
Proof
  metis_tac[default_value_has_type_thm, vyper_to_abi_default_value]
QED

