(* TOP-LEVEL: compatible-copy completeness lifts through tuple fields
   and checked struct metadata, retaining the original compiler environment. *)
Theory typedCopyCompleteAggregate
Ancestors
  vyperEventArgCompat
  typedCopyCompleteDefs typedCopyCompatibility typedStructContract typedTupleContract
  vyperTypeValues vyperValue context compileEnv compileVyper vyperTypeContract vyperContext vyperTypeSystem
  list pair combin

Theorem typed_copy_complete_field_list:
  !tenv ctx func cenv fts ats.
    EVERY (typed_copy_complete tenv ctx func cenv) fts /\ event_arg_compatible_list fts ats ==>
    LIST_REL (\fty aty. !ftv atv.
      evaluate_type tenv fty = SOME ftv /\ evaluate_type tenv aty = SOME atv ==>
      typed_copy_type_contract ctx func cenv fty aty ftv atv) fts ats
Proof
  MAP_EVERY qx_gen_tac [`tenv`, `ctx`, `func`, `cenv`] >> Induct_on `fts`
  >- (Cases >> simp[event_arg_compatible_def]) >>
  MAP_EVERY qx_gen_tac [`fty`, `ats`] >> Cases_on `ats` >- simp[event_arg_compatible_def] >>
  rename1 `event_arg_compatible_list (fty::fts) (aty::ats)` >>
  simp_tac (srw_ss()) [event_arg_compatible_def, LIST_REL_def] >> strip_tac >> conj_tac
  >- (MAP_EVERY qx_gen_tac [`ftv`, `atv`] >> strip_tac >>
      mp_tac (Q.SPECL [`tenv`, `ctx`, `func`, `cenv`, `fty`, `aty`, `ftv`, `atv`]
        typed_copy_complete_instance) >> simp[]) >>
  first_x_assum irule >> simp[]
QED

Theorem typed_copy_complete_tuple:
  !tops in_deploy layouts addr art ctx func cenv fts.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    EVERY (typed_copy_complete (type_env tops) ctx func cenv) fts ==>
    typed_copy_complete (type_env tops) ctx func cenv (TupleT fts)
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [typed_copy_complete_def] >>
  MAP_EVERY qx_gen_tac [`aty`, `ftv`, `atv`] >> strip_tac >>
  qpat_assum `event_arg_compatible _ _`
    (qx_choose_then `ats` strip_assume_tac o MATCH_MP compatible_tuple_source) >>
  qpat_x_assum `aty = TupleT ats` SUBST_ALL_TAC >>
  qpat_assum `evaluate_type _ (TupleT fts) = SOME ftv`
    (qx_choose_then `ftvs` strip_assume_tac o MATCH_MP evaluate_type_TupleT_cases) >>
  qpat_assum `evaluate_type _ (TupleT ats) = SOME atv`
    (qx_choose_then `atvs` strip_assume_tac o MATCH_MP evaluate_type_TupleT_cases) >>
  qpat_x_assum `ftv = TupleTV ftvs` SUBST_ALL_TAC >> qpat_x_assum `atv = TupleTV atvs` SUBST_ALL_TAC >>
  mp_tac (Q.SPECL [`type_env tops`, `ctx`, `func`, `cenv`, `fts`, `ats`] typed_copy_complete_field_list) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  mp_tac (Q.SPECL [`tops`, `in_deploy`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`, `fts`, `ats`, `ftvs`, `atvs`]
    typed_copy_type_contract_tuple) >> simp[]
QED

Theorem typed_copy_complete_struct:
  !tops in_deploy layouts addr art ctx func cenv nsid.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    EVERY (typed_copy_complete (type_env tops) ctx func cenv)
      (MAP (FST o SND) (get_struct_fields cenv.ce_struct_fields (nsid_to_string nsid))) ==>
    typed_copy_complete (type_env tops) ctx func cenv (StructT nsid)
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [typed_copy_complete_def] >>
  MAP_EVERY qx_gen_tac [`aty`, `ftv`, `atv`] >> strip_tac >>
  `aty = StructT nsid` by (Cases_on `aty` >> fs[event_arg_compatible_def]) >> pop_assum SUBST_ALL_TAC >>
  `ftv = atv` by fs[] >> pop_assum SUBST_ALL_TAC >>
  mp_tac (Q.SPECL [`tops`, `in_deploy`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`, `nsid`, `atv`]
    typed_copy_type_contract_struct) >> impl_tac
  >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC,
        MAP_EVERY qx_gen_tac [`field_ty`, `field_tv`] >> strip_tac >>
        `typed_copy_complete (type_env tops) ctx func cenv field_ty` by fs[EVERY_MEM] >>
        mp_tac (Q.SPECL [`type_env tops`, `ctx`, `func`, `cenv`, `field_ty`, `field_ty`, `field_tv`, `field_tv`]
          typed_copy_complete_instance) >> simp[CONJUNCT1 event_arg_compatible_reflexive]]) >> simp[]
QED
