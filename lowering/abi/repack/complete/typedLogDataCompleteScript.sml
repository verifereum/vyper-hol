(* TOP-LEVEL: checked compatibility closes all Log data-field contracts,
   including nested arrays, tuples and structs. No recursive-copy callback
   or supported_log restriction remains in the data-packing theorem. *)
Theory typedLogDataComplete
Ancestors
  typedCopyComplete typedLogFieldChecked typedLogFieldContract
  typedLogDataChecked typedLogDataContract
  context stmtLowering compileEnv compileVyper vyperTypeContract vyperContext
  vyperTypeSystem vyperValue list pair

Theorem checked_log_field_type_contract:
  !tops in_deploy layouts addr art ctx func cenv fty aty ftv atv.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    event_arg_compatible fty aty /\
    evaluate_type (type_env tops) fty = SOME ftv /\
    evaluate_type (type_env tops) aty = SOME atv ==>
    log_field_type_contract ctx func cenv fty aty ftv atv
Proof
  rpt gen_tac >> strip_tac >> drule_all checked_typed_copy_type_contract >> DISCH_TAC >>
  mp_tac (Q.SPECL [`tops`, `in_deploy`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`,
    `fty`, `aty`, `ftv`, `atv`] log_field_type_contract_checked) >> simp[]
QED

Theorem checked_log_field_list_contract:
  !tops in_deploy layouts addr art ctx func cenv fts ops.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    LIST_REL (\fty arg. event_arg_compatible fty (SND arg)) fts (ops:(operand # type) list) ==>
    LIST_REL (\fty arg. !ftv atv.
      evaluate_type (type_env tops) fty = SOME ftv /\
      evaluate_type (type_env tops) (SND arg) = SOME atv ==>
      log_field_type_contract ctx func cenv fty (SND arg) ftv atv) fts ops
Proof
  MAP_EVERY qx_gen_tac [`tops`, `in_deploy`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`] >>
  Induct_on `fts` >- (Cases >> simp[]) >>
  MAP_EVERY qx_gen_tac [`fty`, `ops`] >> Cases_on `ops` >- simp[] >>
  rename1 `LIST_REL _ (fty::fts) (arg::ops)` >>
  simp_tac (srw_ss()) [LIST_REL_def] >> strip_tac >> conj_tac
  >- (MAP_EVERY qx_gen_tac [`ftv`, `atv`] >> strip_tac >>
      mp_tac (Q.SPECL [`tops`, `in_deploy`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`,
        `fty`, `SND (arg:operand # type)`, `ftv`, `atv`] checked_log_field_type_contract) >> simp[]) >>
  first_x_assum irule >> simp[]
QED

Theorem checked_compile_log_data_complete:
  !tops in_deploy layouts addr art ctx func cenv fts ops ftvs atvs buf field_offset cs ret cs'.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\
    LIST_REL (\fty arg. event_arg_compatible fty (SND arg)) fts ops /\
    LIST_REL (\ty tv. evaluate_type (type_env tops) ty = SOME tv) fts ftvs /\
    LIST_REL (\arg tv. evaluate_type (type_env tops) (SND arg) = SOME tv) ops atvs /\
    compile_log_store_data cenv ops fts buf field_offset cs = (ret,cs') ==>
    log_data_store_contract ctx func ops ftvs atvs buf field_offset cs cs'
Proof
  rpt gen_tac >> strip_tac >> drule_all checked_log_field_list_contract >> DISCH_TAC >>
  mp_tac (Q.SPECL [`tops`, `in_deploy`, `layouts`, `addr`, `art`, `ctx`, `func`, `cenv`,
    `fts`, `ops`, `ftvs`, `atvs`, `buf`, `field_offset`, `cs`, `ret`, `cs'`]
    checked_compile_log_data_store_contract) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed complete checked Log data packing: " ^ name)
  end) (DB.thms "typedLogDataComplete")
