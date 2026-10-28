(* TOP-LEVEL: arbitrary checked tuple field lists copy their complete
   layouts using per-type child contracts, with actual compiler cuts. *)
Theory typedFieldsList
Ancestors
  typedFieldsCons typedFieldsTypes typedFieldsContract typedCopyTypeContract
  compileVyper compileEnv vyperTypeContract vyperContext vyperTypeSystem vyperValue list

Theorem checked_compile_typed_fields_contract:
  !tops in_deploy layouts addr art ctx func cenv.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops ==>
    !fts ats ftvs atvs.
      event_arg_compatible_list fts ats /\
      LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv) fts ftvs /\
      LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv) ats atvs /\
      LIST_REL (\fty aty. !ftv atv.
        evaluate_type (type_env tops) fty = SOME ftv /\
        evaluate_type (type_env tops) aty = SOME atv ==>
        typed_copy_type_contract ctx func cenv fty aty ftv atv) fts ats ==>
      !dst src dst_off src_off cs ret cs'.
        compile_typed_copy_fields cenv dst src fts ats dst_off src_off cs = (ret,cs') ==>
        typed_fields_copy_contract ctx func dst src ftvs atvs dst_off src_off cs cs'
Proof
  rpt gen_tac >> strip_tac >> Induct_on `fts`
  >- (rpt gen_tac >> Cases_on `ats` >> Cases_on `ftvs` >> Cases_on `atvs` >>
      simp[LIST_REL_def, event_arg_compatible_def] >> rpt strip_tac >>
      drule typed_fields_copy_contract_nil >> simp[]) >>
  MAP_EVERY qx_gen_tac [`fty`, `ats`, `ftvs`, `atvs`] >>
  Cases_on `ats` >- simp[event_arg_compatible_def] >>
  Cases_on `ftvs` >- simp[LIST_REL_def] >> Cases_on `atvs` >- simp[LIST_REL_def] >>
  rename1 `event_arg_compatible_list (fty::fts) (aty::ats)` >>
  rename1 `LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv) (fty::fts) (ftv::ftvs)` >>
  rename1 `LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv) (aty::ats) (atv::atvs)` >>
  simp_tac bool_ss [LIST_REL_def, event_arg_compatible_def] >> strip_tac >>
  MAP_EVERY qx_gen_tac [`dst`, `src`, `dst_off`, `src_off`, `cs`, `ret`, `cs'`] >> DISCH_TAC >>
  mp_tac (Q.SPECL [`tops`, `in_deploy`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`, `fty`, `aty`, `ftv`, `atv`]
    checked_typed_field_pair) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `!ats ftvs atvs. _` (qspecl_then [`ats`, `ftvs`, `atvs`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cenv`, `dst`, `src`, `fty`, `fts`, `aty`, `ats`, `ftv`, `ftvs`, `atv`, `atvs`,
    `dst_off`, `src_off`, `cs`, `ret`, `cs'`] typed_fields_copy_contract_cons) >>
  impl_tac
  >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC,
        qx_gen_tac `after` >> DISCH_TAC >> first_x_assum irule >> first_assum MATCH_ACCEPT_TAC]) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed checked tuple field-list copy: " ^ name)
  end) (DB.thms "typedFieldsList")
