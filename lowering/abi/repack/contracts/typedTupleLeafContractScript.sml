(* TOP-LEVEL: closed tuple-copy contracts for arbitrary scalar and
   bytes/string fields, including widening event argument tuples. *)
Theory typedTupleLeafContract
Ancestors
  typedTupleContract typedStaticCompatibility typedCopyTypeContract
  compileEnv compileVyper vyperTypeContract vyperContext vyperTypeSystem vyperValue list

Theorem word_type_abi_static:
  !sfields ty. is_word_type ty ==> ~is_abi_dynamic sfields ty
Proof
  rpt gen_tac >> Cases_on `ty` >> gvs[is_word_type_def, is_abi_dynamic_def] >>
  rename1 `is_word_type (BaseT bt)` >> Cases_on `bt` >>
  gvs[is_word_type_def, is_abi_dynamic_def] >>
  rename1 `is_word_type (BaseT (BytesT bd))` >> Cases_on `bd` >>
  gvs[is_word_type_def, is_abi_dynamic_def]
QED

Theorem typed_copy_type_contract_leaf:
  !tenv ctx func cenv fty aty ftv atv.
    (is_word_type fty \/ is_bytestring_type fty) /\ event_arg_compatible fty aty /\
    evaluate_type tenv fty = SOME ftv /\ evaluate_type tenv aty = SOME atv ==>
    typed_copy_type_contract ctx func cenv fty aty ftv atv
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  Cases_on `is_word_type fty`
  >- (`fty = aty` by
        (mp_tac (Q.SPECL [`fty`, `aty`] (CONJUNCT1 event_arg_compatible_static_type)) >>
         impl_tac >- first_assum MATCH_ACCEPT_TAC >>
         disch_then (qspec_then `cenv.ce_struct_fields` mp_tac) >> simp[word_type_abi_static]) >>
      pop_assum (SUBST_ALL_TAC o SYM) >> `ftv = atv` by fs[] >> pop_assum SUBST_ALL_TAC >>
      mp_tac (Q.SPECL [`tenv`, `ctx`, `func`, `cenv`, `fty`, `atv`, `fty`]
        typed_copy_type_contract_word) >> simp[]) >>
  `is_bytestring_type fty` by fs[] >>
  mp_tac (Q.SPECL [`tenv`, `ctx`, `func`, `cenv`, `fty`, `aty`, `ftv`, `atv`]
    typed_copy_type_contract_bytes) >> simp[]
QED

Theorem typed_tuple_leaf_children:
  !tenv ctx func cenv fts.
    !ats. event_arg_compatible_list fts ats /\
      EVERY (\ty. is_word_type ty \/ is_bytestring_type ty) fts ==>
      LIST_REL (\fty aty. !ftv atv.
        evaluate_type tenv fty = SOME ftv /\ evaluate_type tenv aty = SOME atv ==>
        typed_copy_type_contract ctx func cenv fty aty ftv atv) fts ats
Proof
  MAP_EVERY qx_gen_tac [`tenv`, `ctx`, `func`, `cenv`] >> Induct_on `fts`
  >- (Cases >> simp[event_arg_compatible_def]) >>
  MAP_EVERY qx_gen_tac [`fty`, `ats`] >> Cases_on `ats` >- simp[event_arg_compatible_def] >>
  rename1 `event_arg_compatible_list (fty::fts) (aty::ats)` >>
  simp_tac (srw_ss()) [LIST_REL_def, event_arg_compatible_def] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >> conj_tac
  >- (MAP_EVERY qx_gen_tac [`ftv`, `atv`] >> strip_tac >>
      mp_tac (Q.SPECL [`tenv`, `ctx`, `func`, `cenv`, `fty`, `aty`, `ftv`, `atv`]
        typed_copy_type_contract_leaf) >> simp[]) >>
  first_x_assum irule >> simp[]
QED

Theorem typed_copy_type_contract_tuple_leaf:
  !tops in_deploy layouts addr art ctx func cenv fts ats ftvs atvs.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    event_arg_compatible_list fts ats /\
    EVERY (\ty. is_word_type ty \/ is_bytestring_type ty) fts /\
    LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv) fts ftvs /\
    LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv) ats atvs ==>
    typed_copy_type_contract ctx func cenv (TupleT fts) (TupleT ats) (TupleTV ftvs) (TupleTV atvs)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`type_env tops`, `ctx`, `func`, `cenv`, `fts`, `ats`] typed_tuple_leaf_children) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  mp_tac (Q.SPECL [`tops`, `in_deploy`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`, `fts`, `ats`, `ftvs`, `atvs`]
    typed_copy_type_contract_tuple) >> simp[]
QED
