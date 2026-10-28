(* TOP-LEVEL: every complete checked static value layout contains exactly
   its source ABI encoding. Helpers invert type evaluation and compose the
   scalar, array, tuple and struct cases by type-value induction. *)
Theory memoryValueAbiStatic
Ancestors
  memoryValueAbiWord memoryValueAbiArray memoryValueAbiTuple memoryValueDefs
  sourceAbiArray valueEncoding compileEnv vyperABI vyperValue vyperTyping
  vyperTypeValues vyperTypeABI vyperTypeDefaults contractABI
  finite_map list rich_list pair option arithmetic words

Theorem evaluate_type_BaseTV_result:
  !env ty bt.
    evaluate_type env ty = SOME (BaseTV bt) ==> ty = BaseT bt
Proof
  Cases_on `ty` >> gvs[evaluate_type_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem evaluate_type_ArrayTV_result:
  !env ty tv array_bound.
    evaluate_type env ty = SOME (ArrayTV tv array_bound) ==>
    ?elem_ty. ty = ArrayT elem_ty array_bound /\ evaluate_type env elem_ty = SOME tv
Proof
  rpt strip_tac >> Cases_on `ty` >>
  FIRST [drule evaluate_type_ArrayT_cases >> strip_tac >> gvs[],
    gvs[evaluate_type_def, AllCaseEqs()]]
QED

Theorem evaluate_type_TupleTV_result:
  !env ty tvs.
    evaluate_type env ty = SOME (TupleTV tvs) ==>
    ?ts. ty = TupleT ts /\ LIST_REL (\ty tv. evaluate_type env ty = SOME tv) ts tvs
Proof
  rpt strip_tac >> Cases_on `ty` >>
  FIRST [drule evaluate_type_TupleT_cases >> strip_tac >> gvs[],
    gvs[evaluate_type_def, AllCaseEqs()]]
QED

Theorem evaluate_type_StructTV_result:
  !env ty tvs.
    evaluate_type env ty = SOME (StructTV tvs) ==>
    ?nsid args field_types.
      ty = StructT nsid /\ FLOOKUP env nsid = SOME (StructArgs args) /\
      evaluate_types (env \\ nsid) (MAP SND args) [] = SOME field_types /\
      tvs = ZIP (MAP FST args,field_types)
Proof
  Cases_on `ty` >> gvs[evaluate_type_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem evaluate_type_FlagTV_result:
  !env ty flag_width.
    evaluate_type env ty = SOME (FlagTV flag_width) ==> ?nsid. ty = FlagT nsid
Proof
  Cases_on `ty` >> gvs[evaluate_type_def, AllCaseEqs()]
QED

Theorem evaluated_static_base_layout:
  !env bt.
    evaluate_type env (BaseT bt) = SOME (BaseTV bt) /\
    ~is_dynamic (vyper_base_to_abi_type bt) ==>
    is_word_type (BaseT bt) /\ type_memory_size (BaseTV bt) = 32
Proof
  Cases_on `bt` >>
  simp[evaluate_type_def, is_word_type_def, type_memory_size_def, AllCaseEqs()] >>
  rename1 `BytesT byte_bound` >> Cases_on `byte_bound` >>
  simp[evaluate_type_def, is_word_type_def, type_memory_size_def, AllCaseEqs()]
QED

Definition memory_value_abi_type_def:
  memory_value_abi_type tv <=>
    !env ty. evaluate_type env ty = SOME tv ==> memory_value_abi env ty tv
End

Definition memory_tuple_abi_types_def:
  memory_tuple_abi_types tvs <=>
    !env ts.
      LIST_REL (\ty tv. evaluate_type env ty = SOME tv) ts tvs ==>
      memory_tuple_abi env ts tvs
End

Theorem memory_value_abi_type_base:
  !bt. memory_value_abi_type (BaseTV bt)
Proof
  gen_tac >> PURE_REWRITE_TAC [memory_value_abi_type_def] >> rpt strip_tac >>
  drule evaluate_type_BaseTV_result >> DISCH_TAC >> gvs[] >>
  PURE_REWRITE_TAC [memory_value_abi_def] >>
  simp_tac bool_ss [vyper_to_abi_type_def, vyper_to_abi_def] >> rpt strip_tac >>
  drule_all evaluated_static_base_layout >> strip_tac >>
  drule_all memory_value_rel_base_abi >> simp[]
QED

Theorem memory_value_abi_type_flag:
  !flag_width. memory_value_abi_type (FlagTV flag_width)
Proof
  gen_tac >> PURE_REWRITE_TAC [memory_value_abi_type_def] >> rpt strip_tac >>
  drule evaluate_type_FlagTV_result >> strip_tac >> gvs[] >>
  PURE_REWRITE_TAC [memory_value_abi_def] >> rpt gen_tac >> Cases_on `v` >>
  simp[value_has_type_def, type_memory_size_def] >> rpt strip_tac >>
  drule memory_value_rel_flag_abi >> gvs[]
QED

Theorem memory_value_abi_type_none:
  memory_value_abi_type NoneTV
Proof
  PURE_REWRITE_TAC [memory_value_abi_type_def] >> rpt strip_tac >>
  drule evaluate_type_NoneTV_imp_NoneT >> DISCH_TAC >> gvs[] >>
  simp[memory_value_abi_def, value_has_type_def, type_memory_size_def,
    mem_bytes_at_def, Once enc_def, REV_REVERSE_LEM]
QED

Theorem memory_value_abi_type_array:
  !tv array_bound.
    memory_value_abi_type tv ==> memory_value_abi_type (ArrayTV tv array_bound)
Proof
  rpt gen_tac >> DISCH_TAC >> PURE_REWRITE_TAC [memory_value_abi_type_def] >>
  rpt strip_tac >> drule evaluate_type_ArrayTV_result >> strip_tac >> gvs[] >>
  rename1 `evaluate_type env elem_ty = SOME tv` >>
  qpat_x_assum `memory_value_abi_type tv`
    (mp_tac o REWRITE_RULE [memory_value_abi_type_def]) >>
  disch_then (qspecl_then [`env`, `elem_ty`] mp_tac) >>
  impl_tac >- simp[] >> DISCH_TAC >> irule memory_value_abi_array >> simp[]
QED

Theorem memory_value_abi_type_tuple:
  !tvs.
    memory_tuple_abi_types tvs ==> memory_value_abi_type (TupleTV tvs)
Proof
  rpt gen_tac >> DISCH_TAC >> PURE_REWRITE_TAC [memory_value_abi_type_def] >>
  rpt strip_tac >> drule evaluate_type_TupleTV_result >> strip_tac >> gvs[] >>
  rename1 `LIST_REL (\ty tv. evaluate_type env ty = SOME tv) ts tvs` >>
  qpat_x_assum `memory_tuple_abi_types tvs`
    (mp_tac o REWRITE_RULE [memory_tuple_abi_types_def]) >>
  disch_then (qspecl_then [`env`, `ts`] mp_tac) >>
  impl_tac >- simp[] >> DISCH_TAC >> irule memory_value_abi_tuple >> simp[]
QED

Theorem memory_value_abi_type_struct:
  !tvs.
    memory_tuple_abi_types (MAP SND tvs) ==> memory_value_abi_type (StructTV tvs)
Proof
  rpt gen_tac >> DISCH_TAC >> PURE_REWRITE_TAC [memory_value_abi_type_def] >>
  rpt strip_tac >> drule evaluate_type_StructTV_result >> strip_tac >>
  rename1 `evaluate_types (env \\ nsid) (MAP SND args) [] = SOME field_types` >>
  `LIST_REL (\ty tv. evaluate_type (env \\ nsid) ty = SOME tv) (MAP SND args) field_types` by
    (irule evaluate_types_LIST_REL >> simp[]) >>
  `LENGTH args = LENGTH field_types` by (drule LIST_REL_LENGTH >> simp[]) >>
  `MAP SND tvs = field_types` by fs[MAP_ZIP] >>
  `memory_tuple_abi (env \\ nsid) (MAP SND args) (MAP SND tvs)` by
    (qpat_x_assum `memory_tuple_abi_types (MAP SND tvs)`
       (mp_tac o REWRITE_RULE [memory_tuple_abi_types_def]) >>
     disch_then (qspecl_then [`env \\ nsid`, `MAP SND args`] mp_tac) >>
     impl_tac >- fs[] >> simp[]) >>
  mp_tac (Q.SPECL [`env`, `nsid`, `args`, `tvs`] memory_value_abi_struct) >>
  impl_tac >- simp[] >> gvs[]
QED

Theorem memory_tuple_abi_types_nil:
  memory_tuple_abi_types []
Proof
  PURE_REWRITE_TAC [memory_tuple_abi_types_def] >> rpt gen_tac >> Cases_on `ts` >>
  simp[memory_tuple_abi_nil]
QED

Theorem memory_tuple_abi_types_cons:
  !tv tvs.
    memory_value_abi_type tv /\ memory_tuple_abi_types tvs ==>
    memory_tuple_abi_types (tv::tvs)
Proof
  rpt gen_tac >> strip_tac >> PURE_REWRITE_TAC [memory_tuple_abi_types_def] >>
  rpt gen_tac >> Cases_on `ts` >> simp[] >> rpt strip_tac >>
  rename1 `evaluate_type env head_ty = SOME tv` >>
  rename1 `LIST_REL (\ty tv. evaluate_type env ty = SOME tv) tail_tys tvs` >>
  `memory_value_abi env head_ty tv` by
    (qpat_x_assum `memory_value_abi_type tv`
       (mp_tac o REWRITE_RULE [memory_value_abi_type_def]) >>
     disch_then (qspecl_then [`env`, `head_ty`] mp_tac) >> impl_tac >- simp[] >> simp[]) >>
  `memory_tuple_abi env tail_tys tvs` by
    (qpat_x_assum `memory_tuple_abi_types tvs`
       (mp_tac o REWRITE_RULE [memory_tuple_abi_types_def]) >>
     disch_then (qspecl_then [`env`, `tail_tys`] mp_tac) >> impl_tac >- simp[] >> simp[]) >>
  irule memory_tuple_abi_cons >> simp[]
QED

Theorem memory_value_abi_types:
  (!tv. memory_value_abi_type tv) /\
  (!tvs:(string # type_value) list. memory_tuple_abi_types (MAP SND tvs)) /\
  (!p:string # type_value. memory_value_abi_type (SND p)) /\
  (!tvs. memory_tuple_abi_types tvs)
Proof
  ho_match_mp_tac (TypeBase.induction_of ``:type_value``) >>
  simp[memory_value_abi_type_base, memory_value_abi_type_flag, memory_value_abi_type_none,
    memory_value_abi_type_array, memory_value_abi_type_tuple, memory_value_abi_type_struct,
    memory_tuple_abi_types_nil, memory_tuple_abi_types_cons] >>
  rpt gen_tac >> strip_tac >>
  qmatch_asmsub_rename_tac `memory_value_abi_type (SND field_entry)` >>
  PairCases_on `field_entry` >> fs[memory_tuple_abi_types_cons]
QED

Theorem memory_value_rel_static_abi:
  !env ty tv v av offset mem.
    evaluate_type env ty = SOME tv /\
    memory_value_rel tv v offset mem /\ value_has_type tv v /\
    vyper_to_abi env ty v = SOME av /\ ~is_dynamic (vyper_to_abi_type env ty) ==>
    mem_bytes_at offset (type_memory_size tv) mem = enc (vyper_to_abi_type env ty) av
Proof
  rpt strip_tac >> mp_tac (Q.SPEC `tv` (CONJUNCT1 memory_value_abi_types)) >>
  PURE_REWRITE_TAC [memory_value_abi_type_def] >>
  disch_then (qspecl_then [`env`, `ty`] mp_tac) >> impl_tac >- simp[] >>
  PURE_REWRITE_TAC [memory_value_abi_def] >>
  disch_then (qspecl_then [`v`, `av`, `offset`, `mem`] mp_tac) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed complete memory/static ABI theorem: " ^ name)
  end) (DB.thms "memoryValueAbiStatic")
