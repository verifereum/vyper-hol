(* TOP-LEVEL: complete struct values bridge to the existing tuple-field
   copy contract without losing field names, values or typed memory frames. *)
Theory typedStructMemory
Ancestors
  typedFieldsContract typedCopyContract typedSArrayDynInvariant memoryValueAbiTuple
  memoryValueDefs valueEncoding vyperTyping vyperValue abiStaticLoopCode
  compileEnv fragExec venomState venomInst list pair words arithmetic

Theorem memory_fields_rel_from_typed_tuple:
  !tvs fields offset mem.
    struct_has_type tvs fields /\
    memory_tuple_rel (MAP SND tvs) (MAP SND fields) offset mem ==>
    memory_fields_rel tvs fields offset mem
Proof
  Induct_on `tvs` >> Cases_on `fields` >> simp[value_has_type_def, memory_value_rel_def] >>
  rpt gen_tac >> rename1 `struct_has_type (entry::rest) _` >> PairCases_on `entry` >>
  rename1 `struct_has_type _ (value_entry::values)` >> PairCases_on `value_entry` >>
  simp[value_has_type_def, memory_value_rel_def]
QED

Theorem typed_struct_value_cases:
  !tvs value. value_has_type (StructTV tvs) value ==>
    ?fields. value = StructV fields /\ struct_has_type tvs fields
Proof
  rpt gen_tac >> Cases_on `value` >> simp[value_has_type_def]
QED

Theorem array_copy_frame_struct:
  !tvs dst_off before_mem after_mem.
    array_copy_frame (TupleTV (MAP SND tvs)) 1 dst_off before_mem after_mem ==>
    array_copy_frame (StructTV tvs) 1 dst_off before_mem after_mem
Proof
  simp[array_copy_frame_def, type_memory_size_def, type_memory_size_fields_list]
QED

Theorem typed_fields_copy_contract_struct:
  !ctx func dst src tvs cs cs'.
    typed_fields_copy_contract ctx func dst src (MAP SND tvs) (MAP SND tvs) 0 0 cs cs' ==>
    typed_copy_contract ctx func dst src (StructTV tvs) (StructTV tvs) cs cs'
Proof
  rpt gen_tac >> DISCH_TAC >> simp_tac bool_ss [typed_copy_contract_def] >>
  MAP_EVERY qx_gen_tac [`ss`, `value`, `dst_addr`, `src_addr`] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  drule typed_struct_value_cases >> disch_then (qx_choose_then `fields` strip_assume_tac) >>
  qpat_x_assum `value = StructV fields` SUBST_ALL_TAC >>
  qpat_assum `memory_value_rel (StructTV tvs) _ _ _`
    (ASSUME_TAC o PURE_REWRITE_RULE [memory_value_rel_def]) >>
  drule struct_has_type_tuple >> DISCH_TAC >> drule memory_fields_rel_tuple >> DISCH_TAC >>
  `type_memory_size (StructTV tvs) = type_memory_size (TupleTV (MAP SND tvs))` by
    simp[type_memory_size_def, type_memory_size_fields_list] >>
  qpat_assum `type_memory_size (StructTV tvs) = _`
    (fn eq => RULE_ASSUM_TAC (PURE_REWRITE_RULE [eq])) >>
  qpat_x_assum `typed_fields_copy_contract _ _ _ _ _ _ _ _ _ _`
    (mp_tac o SIMP_RULE bool_ss [typed_fields_copy_contract_def, ADD_CLAUSES]) >>
  disch_then (qspecl_then [`ss`, `MAP SND fields`, `dst_addr`, `src_addr`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  `memory_fields_rel tvs fields (w2n dst_addr) out.vs_memory` by
    (mp_tac (Q.SPECL [`tvs`, `fields`, `w2n (dst_addr:bytes32)`, `out.vs_memory`]
       memory_fields_rel_from_typed_tuple) >> simp[]) >>
  drule array_copy_frame_struct >> DISCH_TAC >>
  qexists_tac `out` >> simp_tac bool_ss [memory_value_rel_def] >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED
