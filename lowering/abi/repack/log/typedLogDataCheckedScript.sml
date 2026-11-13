(* TOP-LEVEL: the checker and complete type evaluations supply actual
   declared-field strides. Per-field contracts then verify full data packing. *)
Theory typedLogDataChecked
Ancestors
  typedLogDataList typedLogDataContract typedLogFieldsContract typedLogFieldContract
  typeLayoutProps typedCopyProducer context stmtLowering compileEnv compileVyper
  vyperTypeContract vyperContext vyperTypeSystem vyperValue list pair

Theorem log_field_list_contract_checked:
  !tops in_deploy layouts addr art ctx func cenv.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops ==>
    !fts ops ftvs atvs.
      LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv) fts ftvs /\
      LIST_REL (\arg tv. evaluate_type (type_env tops) (SND arg) = SOME tv) ops atvs /\
      LIST_REL (\fty arg. !ftv atv.
        evaluate_type (type_env tops) fty = SOME ftv /\
        evaluate_type (type_env tops) (SND arg) = SOME atv ==>
        log_field_type_contract ctx func cenv fty (SND arg) ftv atv) fts ops ==>
      log_field_list_contract ctx func cenv fts ops ftvs atvs
Proof
  rpt gen_tac >> strip_tac >> drule checked_contract_struct_args_unique >> DISCH_TAC >> Induct_on `fts`
  >- (rpt gen_tac >> Cases_on `ops` >> Cases_on `ftvs` >> Cases_on `atvs` >>
      simp[LIST_REL_def, log_field_list_contract_def]) >>
  MAP_EVERY qx_gen_tac [`fty`, `ops`, `ftvs`, `atvs`] >>
  Cases_on `ops` >- simp[LIST_REL_def] >> Cases_on `ftvs` >- simp[LIST_REL_def] >>
  Cases_on `atvs` >- simp[LIST_REL_def] >>
  rename1 `log_field_list_contract _ _ _ (fty::fts) (arg::ops) (ftv::ftvs) (atv::atvs)` >>
  Cases_on `arg` >> rename1 `log_field_list_contract _ _ _ (fty::fts) ((src,aty)::ops) (ftv::ftvs) (atv::atvs)` >>
  simp_tac bool_ss [LIST_REL_def, pairTheory.SND] >> strip_tac >>
  `type_memory_bytes cenv fty = type_memory_size ftv` by
    (mp_tac (Q.SPECL [`tops`, `cenv`, `fty`, `ftv`] type_memory_bytes_evaluated) >>
     impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  `log_field_type_contract ctx func cenv fty aty ftv atv` by
    (qpat_x_assum `!ftv atv. _ ==> log_field_type_contract _ _ _ _ _ _ _`
       (qspecl_then [`ftv`, `atv`] mp_tac) >> simp[]) >>
  qpat_x_assum `!ops ftvs atvs. _` (qspecl_then [`ops`, `ftvs`, `atvs`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  simp[log_field_list_contract_def]
QED

Theorem checked_compile_log_data_store_contract:
  !tops in_deploy layouts addr art ctx func cenv fts ops ftvs atvs buf field_offset cs ret cs'.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv) fts ftvs /\
    LIST_REL (\arg tv. evaluate_type (type_env tops) (SND arg) = SOME tv) ops atvs /\
    LIST_REL (\fty arg. !ftv atv.
      evaluate_type (type_env tops) fty = SOME ftv /\
      evaluate_type (type_env tops) (SND arg) = SOME atv ==>
      log_field_type_contract ctx func cenv fty (SND arg) ftv atv) fts ops /\
    compile_log_store_data cenv ops fts buf field_offset cs = (ret,cs') ==>
    log_data_store_contract ctx func ops ftvs atvs buf field_offset cs cs'
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`tops`, `in_deploy`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`]
    log_field_list_contract_checked) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qspecl_then [`fts`, `ops`, `ftvs`, `atvs`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cenv`, `fts`, `ops`, `ftvs`, `atvs`] compile_log_data_store_contract) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >>
  disch_then (qspecl_then [`buf`, `field_offset`, `cs`, `ret`, `cs'`] mp_tac) >> simp[]
QED
