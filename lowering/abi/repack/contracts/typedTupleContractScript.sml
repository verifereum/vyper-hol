(* TOP-LEVEL: the actual tuple dispatcher copies complete tuple values.
   Child contracts may emit their own blocks and recursive array loops. *)
Theory typedTupleContract
Ancestors
  vyperEventArgCompat
  typedFieldsList typedFieldsContract typedCopyTypeContract typedCopyContract
  checkedCopyAcyclic memoryValueDefs valueEncoding vyperTyping vyperValue
  context compileEnv compileVyper vyperTypeContract vyperContext vyperTypeSystem
  fragExec venomState venomInst list words arithmetic

Theorem compile_typed_tuple_dispatch:
  !cenv dst fts src ats.
    acyclic_struct_metadata cenv.ce_struct_fields ==>
    compile_store_memory_typed cenv dst (TupleT fts) src (TupleT ats) =
      compile_typed_copy_fields cenv dst src fts ats 0 0
Proof
  rpt gen_tac >> DISCH_TAC >>
  simp[Once compile_store_memory_typed_def, is_word_type_def, is_bytestring_type_def]
QED

Theorem typed_tuple_value_cases:
  !tvs value. value_has_type (TupleTV tvs) value ==>
    ?vs. value = ArrayV (TupleV vs) /\ values_have_types tvs vs
Proof
  rpt gen_tac >> Cases_on `value` >> simp[value_has_type_def] >>
  rename1 `value_has_type (TupleTV tvs) (ArrayV arr)` >>
  Cases_on `arr` >> simp[value_has_type_def]
QED

Theorem typed_fields_copy_contract_tuple:
  !ctx func dst src ftvs atvs cs cs'.
    typed_fields_copy_contract ctx func dst src ftvs atvs 0 0 cs cs' ==>
    typed_copy_contract ctx func dst src (TupleTV ftvs) (TupleTV atvs) cs cs'
Proof
  rpt gen_tac >> DISCH_TAC >> simp_tac bool_ss [typed_copy_contract_def] >>
  MAP_EVERY qx_gen_tac [`ss`, `value`, `dst_addr`, `src_addr`] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  drule typed_tuple_value_cases >> disch_then (qx_choose_then `vs` strip_assume_tac) >>
  qpat_x_assum `value = ArrayV (TupleV vs)` SUBST_ALL_TAC >>
  qpat_assum `memory_value_rel (TupleTV atvs) _ _ _`
    (ASSUME_TAC o PURE_REWRITE_RULE [memory_value_rel_def]) >>
  qpat_x_assum `typed_fields_copy_contract _ _ _ _ _ _ _ _ _ _`
    (mp_tac o SIMP_RULE bool_ss [typed_fields_copy_contract_def, ADD_CLAUSES]) >>
  disch_then (qspecl_then [`ss`, `vs`, `dst_addr`, `src_addr`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  qexists_tac `out` >> simp_tac bool_ss [memory_value_rel_def] >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theorem checked_compile_typed_tuple_contract:
  !tops in_deploy layouts addr art ctx func cenv dst src fts ats ftvs atvs cs ret cs'.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    event_arg_compatible_list fts ats /\
    LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv) fts ftvs /\
    LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv) ats atvs /\
    LIST_REL (\fty aty. !ftv atv.
      evaluate_type (type_env tops) fty = SOME ftv /\
      evaluate_type (type_env tops) aty = SOME atv ==>
      typed_copy_type_contract ctx func cenv fty aty ftv atv) fts ats /\
    compile_store_memory_typed cenv dst (TupleT fts) src (TupleT ats) cs = (ret,cs') ==>
    typed_copy_contract ctx func dst src (TupleTV ftvs) (TupleTV atvs) cs cs'
Proof
  rpt gen_tac >> strip_tac >>
  `acyclic_struct_metadata cenv.ce_struct_fields` by
    (asm_rewrite_tac [] >> drule_all checked_struct_metadata_acyclic >> simp[]) >>
  `compile_typed_copy_fields cenv dst src fts ats 0 0 cs = (ret,cs')` by
    (qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
     asm_simp_tac bool_ss [compile_typed_tuple_dispatch]) >>
  irule typed_fields_copy_contract_tuple >>
  mp_tac (Q.SPECL [`tops`, `in_deploy`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`]
    checked_compile_typed_fields_contract) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qspecl_then [`fts`, `ats`, `ftvs`, `atvs`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qspecl_then [`dst`, `src`, `0`, `0`, `cs`, `ret`, `cs'`] mp_tac) >> simp[]
QED

Theorem typed_copy_type_contract_tuple:
  !tops in_deploy layouts addr art ctx func cenv fts ats ftvs atvs.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    event_arg_compatible_list fts ats /\
    LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv) fts ftvs /\
    LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv) ats atvs /\
    LIST_REL (\fty aty. !ftv atv.
      evaluate_type (type_env tops) fty = SOME ftv /\
      evaluate_type (type_env tops) aty = SOME atv ==>
      typed_copy_type_contract ctx func cenv fty aty ftv atv) fts ats ==>
    typed_copy_type_contract ctx func cenv (TupleT fts) (TupleT ats) (TupleTV ftvs) (TupleTV atvs)
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [typed_copy_type_contract_def] >>
  MAP_EVERY qx_gen_tac [`dst`, `src`, `cs`, `ret`, `cs'`] >> DISCH_TAC >>
  mp_tac (Q.SPECL [`tops`, `in_deploy`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`,
    `dst`, `src`, `fts`, `ats`, `ftvs`, `atvs`, `cs`, `ret`, `cs'`]
    checked_compile_typed_tuple_contract) >> simp[]
QED
