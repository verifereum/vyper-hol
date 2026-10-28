(* TOP-LEVEL: compose heterogeneous recursive source encodings over the
   complete tuple memory layout, and assemble their source ABI bytes. *)
Theory abiMemoryTypedFields
Ancestors
  abiMemoryTypedDefs abiMemoryTypedLeaf abiMemoryEncoding abiFieldSource abiFieldPackedStaticSizes
  sourceAbiStaticWidth memoryValueDefs memoryValueAbiStatic memoryValueAbiTuple valueEncoding
  vyperABI vyperTyping vyperValue vyperTypeValues vyperTypeDefaults contractABI list pair arithmetic

Theorem abi_typed_fields_nil:
  !env. abi_typed_fields env [] []
Proof
  simp[abi_typed_fields_def, abi_memory_encoding_fields_nil]
QED

Theorem abi_typed_fields_cons:
  !env ty tys info abi_sz mem_sz is_dyn entries.
    abi_typed_memory env ty info /\ abi_typed_fields env tys entries /\
    (!tv. evaluate_type env ty = SOME tv ==>
      is_dyn = is_dynamic (vyper_to_abi_type env ty) /\
      mem_sz = type_memory_size tv /\ abi_sz = (if is_dyn then 32 else type_memory_size tv)) ==>
    abi_typed_fields env (ty::tys) ((info,abi_sz,mem_sz,is_dyn)::entries)
Proof
  rpt gen_tac >> strip_tac >> PURE_REWRITE_TAC [abi_typed_fields_def] >>
  rpt gen_tac >> Cases_on `tvs` >> Cases_on `vs` >>
  simp[value_has_type_def, memory_value_rel_def, AllCaseEqs(), PULL_EXISTS] >>
  rpt strip_tac >> gvs[] >>
  rename1 `evaluate_type env ty = SOME head_tv` >>
  rename1 `LIST_REL (\ty tv. evaluate_type env ty = SOME tv) tys tail_tvs` >>
  rename1 `vyper_to_abi env ty head_v = SOME head_av` >>
  rename1 `vyper_to_abi_list env tys tail_vs = SOME tail_avs` >>
  `type_memory_size head_tv <= span /\
   type_memory_size_list tail_tvs <= span - type_memory_size head_tv` by
    (fs[type_memory_size_def] >> decide_tac) >>
  `abi_memory_encoding info source (type_memory_size head_tv) mem
     (enc (vyper_to_abi_type env ty) head_av)` by
    (qpat_x_assum `abi_typed_memory env ty info` (mp_tac o REWRITE_RULE [abi_typed_memory_def]) >>
     disch_then (qspecl_then [`head_tv`, `head_v`, `head_av`, `source`,
       `type_memory_size head_tv`, `mem`] mp_tac) >> simp[]) >>
  `~is_dynamic (vyper_to_abi_type env ty) ==>
   LENGTH (enc (vyper_to_abi_type env ty) head_av) = type_memory_size head_tv` by
    (strip_tac >> drule_all memory_value_rel_static_abi >>
     disch_then (mp_tac o AP_TERM ``LENGTH : word8 list -> num``) >> simp[]) >>
  irule abi_memory_encoding_fields_cons >> simp[] >>
  qpat_x_assum `abi_typed_fields env tys entries` (mp_tac o REWRITE_RULE [abi_typed_fields_def]) >>
  disch_then (qspecl_then [`tail_tvs`, `tail_vs`, `tail_avs`, `source + type_memory_size head_tv`,
    `span - type_memory_size head_tv`, `mem`] mp_tac) >> simp[]
QED

Theorem abi_typed_fields_tuple:
  !env tys entries.
    abi_typed_fields env tys entries ==> abi_typed_memory env (TupleT tys) (AbiComplex entries)
Proof
  rpt gen_tac >> DISCH_TAC >> PURE_REWRITE_TAC [abi_typed_memory_def] >>
  rpt gen_tac >> strip_tac >> drule evaluate_type_TupleT_cases >> strip_tac >> gvs[] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  rename1 `ArrayV array_value` >> Cases_on `array_value` >> gvs[value_has_type_def] >>
  gvs[memory_value_rel_def, AllCaseEqs()] >>
  rename1 `memory_tuple_rel tvs vs source mem` >>
  rename1 `vyper_to_abi_list env tys vs = SOME avs` >>
  `LIST_REL (\ty av. ~is_dynamic ty ==> LENGTH (enc ty av) = static_length ty)
     (MAP (vyper_to_abi_type env) tys) avs` by
    (qspecl_then [`tys`, `env`, `tvs`, `vs`, `avs`, `source`, `mem`]
       mp_tac memory_tuple_source_static_sizes >> simp[]) >>
  drule enc_tuple_head_size >>
  disch_then (ASSUME_TAC o SIMP_RULE bool_ss [LET_THM] o
    CONV_RULE (LAND_CONV (ONCE_REWRITE_CONV [enc_def]))) >>
  simp_tac bool_ss [Once vyper_to_abi_type_def, sourceAbiTypingListsTheory.source_abi_types_map] >>
  asm_simp_tac bool_ss [] >> irule abi_memory_encoding_complex >>
  qpat_x_assum `abi_typed_fields env tys entries` (mp_tac o REWRITE_RULE [abi_typed_fields_def]) >>
  disch_then (qspecl_then [`tvs`, `vs`, `avs`, `source`, `span`, `mem`] mp_tac) >>
  fs[type_memory_size_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed typed ABI memory fields: " ^ name)
  end) (DB.thms "abiMemoryTypedFields")
