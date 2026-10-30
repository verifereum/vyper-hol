(* TOP-LEVEL: pure typed values describe concrete native field rows.
   These predicates contain no memory state or execution assumptions. *)
Theory abiFieldValueDefs
Ancestors
  abiFieldDefs abiFlatFieldsDefs valueEncoding vyperABI vyperValue vyperTyping contractABI list words

Definition abi_field_value_def:
  (abi_field_value tenv (AbiFieldFlat (AbiFlatStatic info mem_size payload)) tv v <=>
    mem_size = type_memory_size tv /\ abi_flat_valid (AbiFlatStatic info mem_size payload) /\
    ?ty av. evaluate_type tenv ty = SOME tv /\ vyper_to_abi tenv ty v = SOME av /\
      ~is_dynamic (vyper_to_abi_type tenv ty) /\ payload = enc (vyper_to_abi_type tenv ty) av) /\
  (abi_field_value tenv (AbiFieldFlat (AbiFlatBytes cap mem_size bs)) tv v <=>
    mem_size = type_memory_size tv /\ ?ty.
      is_bytestring_type ty /\ evaluate_type tenv ty = SOME tv /\ raw_return_bytes v = SOME bs) /\
  (abi_field_value tenv (AbiFieldDynBytes ty elem_tv bound vs bss) tv v <=>
    tv = ArrayTV elem_tv (Dynamic bound) /\ v = ArrayV (DynArrayV vs) /\
    is_bytestring_type ty /\ evaluate_type tenv ty = SOME elem_tv /\
    LIST_REL (\value bytes. raw_return_bytes value = SOME bytes) vs bss)
End

Definition abi_field_values_def:
  (abi_field_values tenv [] [] [] <=> T) /\
  (abi_field_values tenv (row::rows) (tv::tvs) (v::vs) <=>
    abi_field_value tenv row tv v /\ abi_field_values tenv rows tvs vs) /\
  (abi_field_values tenv _ _ _ <=> F)
End

Theorem abi_field_value_stride:
  !tenv row tv v. abi_field_value tenv row tv v ==> abi_field_mem_size row = type_memory_size tv
Proof
  rpt gen_tac >> Cases_on `row`
  >- (rename1 `AbiFieldFlat leaf` >> Cases_on `leaf` >> simp[abi_field_value_def, abi_field_mem_size_def, abi_flat_mem_size_def]) >>
  simp[abi_field_value_def, abi_field_mem_size_def]
QED

Theorem abi_field_value_valid:
  !tenv row tv v.
    abi_field_value tenv row tv v /\ value_has_type tv v ==> abi_field_valid tenv row
Proof
  rpt gen_tac >> Cases_on `row`
  >- (rename1 `AbiFieldFlat leaf` >> Cases_on `leaf` >> simp[abi_field_value_def, abi_field_valid_def, abi_flat_valid_def]) >>
  simp[abi_field_value_def, abi_field_valid_def] >> rpt strip_tac >> gvs[]
QED

Theorem abi_field_values_valid:
  !rows tenv tvs vs.
    abi_field_values tenv rows tvs vs /\ values_have_types tvs vs ==> EVERY (abi_field_valid tenv) rows
Proof
  Induct_on `rows` >- simp[] >> rpt gen_tac >> Cases_on `tvs` >> Cases_on `vs` >>
  simp[abi_field_values_def, value_has_type_def] >> strip_tac >>
  conj_tac >- (drule_all abi_field_value_valid >> simp[]) >> first_x_assum drule_all >> simp[]
QED
