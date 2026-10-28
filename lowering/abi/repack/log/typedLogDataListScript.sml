(* TOP-LEVEL: arbitrary aligned field contracts prove complete execution
   of the actual Log data-packing compiler, including recursive fields. *)
Theory typedLogDataList
Ancestors
  typedLogDataCons typedLogDataContract typedLogFieldsContract typedLogFieldContract
  context stmtLowering compileEnv venomInst list pair

Theorem compile_log_data_store_contract:
  !ctx func cenv fts ops ftvs atvs.
    log_field_list_contract ctx func cenv fts ops ftvs atvs ==>
    !buf field_offset cs ret cs'.
      compile_log_store_data cenv ops fts buf field_offset cs = (ret,cs') ==>
      log_data_store_contract ctx func ops ftvs atvs buf field_offset cs cs'
Proof
  MAP_EVERY qx_gen_tac [`ctx`, `func`, `cenv`] >> Induct_on `fts`
  >- (MAP_EVERY qx_gen_tac [`ops`, `ftvs`, `atvs`] >> Cases_on `ops`
      >- (Cases_on `ftvs` >> Cases_on `atvs` >> simp[log_field_list_contract_def] >>
          rpt strip_tac >> drule log_data_store_contract_nil >> simp[]) >>
      rename1 `log_field_list_contract _ _ _ [] (arg::ops) ftvs atvs` >>
      Cases_on `arg` >> Cases_on `ftvs` >> Cases_on `atvs` >> simp[log_field_list_contract_def]) >>
  MAP_EVERY qx_gen_tac [`fty`, `ops`, `ftvs`, `atvs`] >>
  Cases_on `ops` >- (Cases_on `ftvs` >> Cases_on `atvs` >> simp[log_field_list_contract_def]) >>
  rename1 `log_field_list_contract _ _ _ (fty::fts) (arg::ops) ftvs atvs` >> Cases_on `arg` >>
  Cases_on `ftvs` >- (Cases_on `atvs` >> simp[log_field_list_contract_def]) >>
  Cases_on `atvs` >- simp[log_field_list_contract_def] >>
  rename1 `log_field_list_contract _ _ _ (fty::fts) ((src,aty)::ops) (ftv::ftvs) (atv::atvs)` >>
  simp_tac bool_ss [log_field_list_contract_def] >> strip_tac >>
  MAP_EVERY qx_gen_tac [`buf`, `field_offset`, `cs`, `ret`, `cs'`] >> DISCH_TAC >>
  qpat_x_assum `!ops ftvs atvs. _` (qspecl_then [`ops`, `ftvs`, `atvs`] mp_tac) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >> DISCH_TAC >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cenv`, `src`, `aty`, `ops`, `fty`, `fts`, `ftv`, `ftvs`, `atv`, `atvs`,
    `buf`, `field_offset`, `cs`, `ret`, `cs'`] log_data_store_contract_cons) >> impl_tac
  >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC,
        qx_gen_tac `mid` >> DISCH_TAC >>
        qpat_x_assum `!buf field_offset cs ret cs'. _`
          (qspecl_then [`buf`, `field_offset + type_memory_bytes cenv fty`, `mid`, `ret`, `cs'`] mp_tac) >> simp[]]) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed complete Log data store list: " ^ name)
  end) (DB.thms "typedLogDataList")
