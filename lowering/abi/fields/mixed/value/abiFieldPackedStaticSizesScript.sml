(* TOP-LEVEL: a source-typed packed tuple supplies the exact static field
   sizes needed by ABI tuple encoding, without ABI format assumptions. *)
Theory abiFieldPackedStaticSizes
Ancestors
  sourceAbiStaticWidth memoryValueAbiStatic memoryValueAbiTuple memoryValueDefs valueEncodingProps sourceAbiTypingLists
  valueEncoding vyperABI vyperValue vyperTyping contractABI list option

Theorem memory_value_source_static_size:
  !env ty tv v av offset mem.
    evaluate_type env ty = SOME tv /\ value_has_type tv v /\
    memory_value_rel tv v offset mem /\ vyper_to_abi env ty v = SOME av /\
    ~is_dynamic (vyper_to_abi_type env ty) ==>
    LENGTH (enc (vyper_to_abi_type env ty) av) = static_length (vyper_to_abi_type env ty)
Proof
  rpt gen_tac >> strip_tac >> drule_all (CONJUNCT1 source_abi_static_width) >> DISCH_TAC >>
  drule_all memory_value_rel_static_abi >>
  disch_then (mp_tac o AP_TERM ``LENGTH : word8 list -> num``) >> simp[]
QED

Theorem memory_tuple_source_static_sizes:
  !tys env tvs vs avs offset mem.
    LIST_REL (\ty tv. evaluate_type env ty = SOME tv) tys tvs /\
    values_have_types tvs vs /\ memory_tuple_rel tvs vs offset mem /\
    vyper_to_abi_list env tys vs = SOME avs ==>
    LIST_REL (\ty av. ~is_dynamic ty ==> LENGTH (enc ty av) = static_length ty)
      (MAP (vyper_to_abi_type env) tys) avs
Proof
  Induct_on `tys`
  >- (rpt gen_tac >> Cases_on `tvs` >> Cases_on `vs` >> simp[value_has_type_def]) >>
  qx_gen_tac `ty` >> rpt gen_tac >> Cases_on `tvs` >> Cases_on `vs` >>
  simp[value_has_type_def, memory_value_rel_def, AllCaseEqs(), PULL_EXISTS] >> rpt strip_tac >> gvs[] >>
  conj_tac >- (strip_tac >> drule_all memory_value_source_static_size >> simp[]) >>
  first_x_assum drule_all >> simp[]
QED

Theorem memory_tuple_static_source_bytes:
  !env tys tvs vs avs offset mem.
    LIST_REL (\ty tv. evaluate_type env ty = SOME tv) tys tvs /\
    values_have_types tvs vs /\ memory_tuple_rel tvs vs offset mem /\
    vyper_to_abi_list env tys vs = SOME avs /\
    ~EXISTS (\ty. is_dynamic (vyper_to_abi_type env ty)) tys ==>
    mem_bytes_at offset (type_memory_size_list tvs) mem =
      enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs) /\
    LENGTH (enc (Tuple (MAP (vyper_to_abi_type env) tys)) (ListV avs)) = type_memory_size_list tvs
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPEC `tvs` (CONJUNCT2 (CONJUNCT2 (CONJUNCT2 memory_value_abi_types)))) >>
  PURE_REWRITE_TAC [memory_tuple_abi_types_def] >>
  disch_then (qspecl_then [`env`, `tys`] mp_tac) >> impl_tac >- simp[] >>
  PURE_REWRITE_TAC [memory_tuple_abi_def] >>
  disch_then (qspecl_then [`vs`, `avs`, `offset`, `mem`] mp_tac) >>
  impl_tac >- simp[source_abi_types_map, any_dynamic_EXISTS, EXISTS_MAP] >> DISCH_TAC >>
  conj_tac >- fs[source_abi_types_map] >>
  qpat_x_assum `mem_bytes_at _ _ _ = _` (mp_tac o AP_TERM ``LENGTH : word8 list -> num``) >>
  simp[source_abi_types_map]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed packed source ABI static sizes: " ^ name)
  end) (DB.thms "abiFieldPackedStaticSizes")
