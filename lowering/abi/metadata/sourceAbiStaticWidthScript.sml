(* TOP-LEVEL: evaluated static source types have the ABI's exact static
   width, including recursive arrays, tuples and named structs. *)
Theory sourceAbiStaticWidth
Ancestors
  typeLayoutProps memoryValueAbiTuple valueEncoding vyperABI vyperValue
  vyperTypeDefaults contractABI list rich_list pair finite_map option arithmetic

Theorem source_abi_static_width:
  (!env ty tv.
    evaluate_type env ty = SOME tv /\ ~is_dynamic (vyper_to_abi_type env ty) ==>
    type_memory_size tv = static_length (vyper_to_abi_type env ty)) /\
  (!env tys acc tvs.
    evaluate_types env tys acc = SOME tvs /\ ~any_dynamic (vyper_to_abi_types env tys) ==>
    type_memory_size_list tvs = type_memory_size_list acc +
      static_length (Tuple (vyper_to_abi_types env tys)))
Proof
  ho_match_mp_tac evaluate_type_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[evaluate_type_def, vyper_to_abi_type_def, AllCaseEqs(), LET_THM, PULL_EXISTS] >>
  rpt strip_tac >>
  TRY (Cases_on `bd`) >>
  gvs[vyper_to_abi_type_def, type_memory_size_def, type_memory_size_list_sum,
    type_memory_size_fields_list, static_length_Tuple_SUM, MAP_REVERSE, SUM_REVERSE] >>
  imp_res_tac evaluate_types_length >> gvs[MAP_ZIP]
QED
