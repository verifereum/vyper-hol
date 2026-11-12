Theory logEncoderEntryPtr
Ancestors
  logAbiInputPtr stmtSimLogEncodeLayout stmtSimLogDataInput
  representationCleanPtr bodyPtrDefs vyperABIValid
  supportedTypes compileEnv exprLowering vyperABI contractABI
  list arithmetic words

Theorem scalar_abi_embedded_capacity[local]:
  supported_scalar_type ty ==>
  vyper_abi_embedded_size env ty =
    abi_embedded_static_size sf ty +
      (if is_abi_dynamic sf ty then abi_size_bound sf ty else 0)
Proof
  Cases_on `ty` >> simp[supported_scalar_type_def,
    supported_word_type_def, supported_string_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[supported_word_type_def, supported_string_type_def,
    vyper_abi_size_bound_def, vyper_is_dynamic_def,
    abi_embedded_static_size_def, is_abi_dynamic_def,
    abi_static_size_def, abi_size_bound_def, ceil32_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  simp[supported_word_type_def, supported_string_type_def,
    vyper_abi_size_bound_def, vyper_is_dynamic_def,
    abi_embedded_static_size_def, is_abi_dynamic_def,
    abi_static_size_def, abi_size_bound_def, ceil32_def]
QED

Theorem scalar_tuple_abi_capacity:
  !tys. EVERY supported_scalar_type tys ==>
  vyper_abi_size_bound env (TupleT tys) = abi_size_bound sf (TupleT tys)
Proof
  simp[vyper_abi_size_bound_def, abi_size_bound_def] >>
  Induct >> simp[vyper_abi_size_bound_def] >> rpt strip_tac >>
  drule scalar_abi_embedded_capacity >>
  simp[vyper_abi_size_bound_def, ADD_COMM]
QED

Theorem scalar_tuple_encoder_shape:
  EVERY supported_scalar_type tys /\
  SUM (MAP (type_memory_bytes ce) tys) < dimword(:256) ==>
  ((?n. type_to_abi_enc_info sf ce (TupleT tys) = AbiCopy n /\
         n < dimword(:256)) \/
   (?infos. type_to_abi_enc_info sf ce (TupleT tys) = AbiComplex infos /\
     EXISTS (\(_,_,_,dyn). dyn) infos /\
     EVERY (\(child,asz,mz,dyn). log_scalar_enc_info child) infos))
Proof
  strip_tac >> rewrite_tac[log_tuple_enc_info_selected] >>
  Cases_on `is_abi_dynamic ce.ce_struct_fields (TupleT tys)` >> simp[] >>
  conj_tac
  >- gvs[is_abi_dynamic_def, EXISTS_MAP, combinTheory.o_DEF] >>
  gvs[EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
  irule log_scalar_enc_info_selected >> metis_tac[]
QED

Theorem supported_log_encoder_entry_ptr:
  EVERY supported_scalar_type tys /\
  LIST_REL (\ty v. ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
                        value_has_type tv v) tys vs /\
  (!mem'. mem_agree_outside m mem mem' ==> log_data_layout cx tys vs a mem') /\
  SUM (MAP (type_memory_bytes ce) tys) < dimword(:256) ==>
  ?avs. vyper_to_abi_list (get_tenv cx) tys vs = SOME avs /\
    (!mem'. mem_agree_outside m mem mem' ==>
      abi_encoder_input (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT tys))
        (Tuple (vyper_to_abi_types (get_tenv cx) tys)) (ListV avs) a
        (SUM (MAP (type_memory_bytes ce) tys)) mem') /\
    LENGTH (enc (Tuple (vyper_to_abi_types (get_tenv cx) tys)) (ListV avs)) <=
      abi_size_bound ce.ce_struct_fields (TupleT tys) /\
    ((?n. type_to_abi_enc_info ce.ce_struct_fields ce (TupleT tys) = AbiCopy n /\
           n < dimword(:256)) \/
     (?infos. type_to_abi_enc_info ce.ce_struct_fields ce (TupleT tys) = AbiComplex infos /\
       EXISTS (\(_,_,_,dyn). dyn) infos /\
       EVERY (\(child,asz,mz,dyn). log_scalar_enc_info child) infos))
Proof
  strip_tac >>
  `log_data_layout cx tys vs a mem` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  drule_all (ISPEC ``(ce:compile_env).ce_struct_fields``
    (Q.GEN `sf` robust_log_data_layout_input)) >> strip_tac >>
  qexists_tac `avs` >>
  asm_simp_tac bool_ss [vyper_to_abi_type_def] >>
  conj_tac >- gvs[vyper_to_abi_type_def] >>
  reverse conj_tac >- (irule scalar_tuple_encoder_shape >> simp[]) >>
  drule_all log_data_layout_typed_tuple >> strip_tac >>
  `vyper_to_abi (get_tenv cx) (TupleT tys) (ArrayV (TupleV vs)) =
     SOME (ListV avs)` by simp[vyper_to_abi_def] >>
  drule_all (cj 1 vyper_to_abi_enc_le_size_bound) >>
  `vyper_abi_size_bound (get_tenv cx) (TupleT tys) =
     abi_size_bound ce.ce_struct_fields (TupleT tys)` by
    (irule scalar_tuple_abi_capacity >> simp[]) >>
  simp_tac bool_ss [vyper_to_abi_type_def] >> simp[]
QED

(* These interfaces must be closed kernel theorems, not conditional exports. *)
val _ = List.app (fn (name,th) =>
  if null (hyp th) then () else
    (print (name ^ " has hypotheses:\n"); List.app print_term (hyp th);
     raise Fail (name ^ " is not closed")))
  [("scalar_abi_embedded_capacity",scalar_abi_embedded_capacity),
   ("log_tuple_enc_info_selected",log_tuple_enc_info_selected),
   ("log_scalar_enc_info_selected",log_scalar_enc_info_selected),
   ("scalar_tuple_abi_capacity",scalar_tuple_abi_capacity),
   ("scalar_tuple_encoder_shape",scalar_tuple_encoder_shape),
   ("robust_log_data_layout_input",robust_log_data_layout_input),
   ("supported_log_encoder_entry_ptr",supported_log_encoder_entry_ptr)];
