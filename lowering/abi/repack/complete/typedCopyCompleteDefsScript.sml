(* TOP-LEVEL: completeness means the raw typed-copy contract holds for
   every compatible, fully evaluated source type. Helpers invert aggregate
   compatibility and close the leaf cases without source restrictions. *)
Theory typedCopyCompleteDefs
Ancestors
  typedCopyTypeContract typedTupleLeafContract typedCopyBulkContract typedCopyContract
  context compileEnv valueEncoding vyperTypeSystem vyperValue
  list words arithmetic

Definition typed_copy_complete_def:
  typed_copy_complete tenv ctx func cenv fty <=>
    !aty ftv atv.
      event_arg_compatible fty aty /\ evaluate_type tenv fty = SOME ftv /\
      evaluate_type tenv aty = SOME atv ==>
      typed_copy_type_contract ctx func cenv fty aty ftv atv
End

Theorem typed_copy_complete_instance:
  !tenv ctx func cenv fty aty ftv atv.
    typed_copy_complete tenv ctx func cenv fty /\ event_arg_compatible fty aty /\
    evaluate_type tenv fty = SOME ftv /\ evaluate_type tenv aty = SOME atv ==>
    typed_copy_type_contract ctx func cenv fty aty ftv atv
Proof
  simp[typed_copy_complete_def]
QED

Theorem compatible_fixed_array_source:
  !fty copy_count aty.
    event_arg_compatible (ArrayT fty (Fixed copy_count)) aty ==>
    ?elem. aty = ArrayT elem (Fixed copy_count) /\ event_arg_compatible fty elem
Proof
  rpt gen_tac >> Cases_on `aty` >> simp[event_arg_compatible_def] >>
  rename1 `event_arg_compatible _ (ArrayT elem bd)` >> Cases_on `bd` >> rw[event_arg_compatible_def] >> simp[]
QED

Theorem compatible_dynamic_array_source:
  !fty dst_capacity aty.
    event_arg_compatible (ArrayT fty (Dynamic dst_capacity)) aty ==>
    ?elem src_capacity. aty = ArrayT elem (Dynamic src_capacity) /\
      src_capacity <= dst_capacity /\ event_arg_compatible fty elem
Proof
  rpt gen_tac >> Cases_on `aty` >> simp[event_arg_compatible_def] >>
  rename1 `event_arg_compatible _ (ArrayT elem bd)` >> Cases_on `bd` >> rw[event_arg_compatible_def] >> simp[]
QED

Theorem compatible_tuple_source:
  !fts aty. event_arg_compatible (TupleT fts) aty ==>
    ?ats. aty = TupleT ats /\ event_arg_compatible_list fts ats
Proof
  rpt gen_tac >> Cases_on `aty` >> simp[event_arg_compatible_def]
QED

Theorem evaluated_base_copy_kind:
  !tenv bt tv. evaluate_type tenv (BaseT bt) = SOME tv ==>
    is_word_type (BaseT bt) \/ is_bytestring_type (BaseT bt)
Proof
  rpt gen_tac >> Cases_on `bt` >> simp[is_word_type_def, is_bytestring_type_def] >>
  rename1 `BaseT (BytesT bd)` >> Cases_on `bd` >>
  simp[is_word_type_def, is_bytestring_type_def, evaluate_type_def, AllCaseEqs()]
QED

Theorem typed_copy_complete_base:
  !tenv ctx func cenv bt. typed_copy_complete tenv ctx func cenv (BaseT bt)
Proof
  rpt gen_tac >> simp_tac bool_ss [typed_copy_complete_def] >>
  MAP_EVERY qx_gen_tac [`aty`, `ftv`, `atv`] >> strip_tac >>
  mp_tac (Q.SPECL [`tenv`, `bt`, `ftv`] evaluated_base_copy_kind) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >> DISCH_TAC >>
  mp_tac (Q.SPECL [`tenv`, `ctx`, `func`, `cenv`, `BaseT bt`, `aty`, `ftv`, `atv`]
    typed_copy_type_contract_leaf) >> simp[]
QED

Theorem typed_copy_complete_flag:
  !tenv ctx func cenv nsid. typed_copy_complete tenv ctx func cenv (FlagT nsid)
Proof
  rpt gen_tac >> simp_tac bool_ss [typed_copy_complete_def] >>
  MAP_EVERY qx_gen_tac [`aty`, `ftv`, `atv`] >> strip_tac >>
  mp_tac (Q.SPECL [`tenv`, `ctx`, `func`, `cenv`, `FlagT nsid`, `aty`, `ftv`, `atv`]
    typed_copy_type_contract_leaf) >> simp[is_word_type_def]
QED

Theorem typed_copy_complete_none:
  !tenv ctx func cenv. acyclic_struct_metadata cenv.ce_struct_fields ==>
    typed_copy_complete tenv ctx func cenv NoneT
Proof
  rpt gen_tac >> DISCH_TAC >> simp_tac bool_ss [typed_copy_complete_def] >>
  MAP_EVERY qx_gen_tac [`aty`, `ftv`, `atv`] >> strip_tac >>
  Cases_on `aty` >> gvs[event_arg_compatible_def, evaluate_type_def] >>
  simp_tac bool_ss [typed_copy_type_contract_def] >>
  MAP_EVERY qx_gen_tac [`dst`, `src`, `cs`, `ret`, `cs'`] >> DISCH_TAC >>
  `compile_copy_memory dst src (type_memory_size NoneTV) cs = (ret,cs')` by
    (qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
     asm_simp_tac (srw_ss()) [Once compile_store_memory_typed_def, is_word_type_def,
       is_bytestring_type_def, type_memory_bytes_def, type_memory_size_def]) >>
  mp_tac (Q.SPECL [`ctx`, `func`, `dst`, `src`, `NoneTV`, `cs`, `ret`, `cs'`]
    compile_copy_memory_contract) >> impl_tac >- first_assum MATCH_ACCEPT_TAC >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed compatible typed-copy leaf completeness: " ^ name)
  end) (DB.thms "typedCopyCompleteDefs")
