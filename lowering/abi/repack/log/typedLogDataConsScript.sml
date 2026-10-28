(* TOP-LEVEL: compose actual head and tail data stores into the full
   declared tuple layout, preserving all saved source arguments. *)
Theory typedLogDataCons
Ancestors
  typedCopyStateFrame typedLogDataContract typedLogDataHead typedLogArgs typedLogArgsFrames typedLogRanges
  typedLogFieldContract typedFieldsCompose typedSArrayDynInvariant
  valueLoadProps memoryValueDefs valueEncoding vyperTyping vyperValue abiStaticLoopCode
  context stmtLowering compileEnv fragExec fragBlockPath venomState venomInst list words arithmetic

Theorem log_data_store_contract_cons:
  !ctx func cenv src aty ops fty fts ftv ftvs atv atvs buf field_offset cs ret cs'.
    type_memory_bytes cenv fty = type_memory_size ftv /\
    log_field_type_contract ctx func cenv fty aty ftv atv /\
    (!mid. compile_log_store_data cenv ops fts buf (field_offset + type_memory_bytes cenv fty) mid = (ret,cs') ==>
      log_data_store_contract ctx func ops ftvs atvs buf (field_offset + type_memory_bytes cenv fty) mid cs') /\
    compile_log_store_data cenv ((src,aty)::ops) (fty::fts) buf field_offset cs = (ret,cs') ==>
    log_data_store_contract ctx func ((src,aty)::ops) (ftv::ftvs) (atv::atvs) buf field_offset cs cs'
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [log_data_store_contract_def] >>
  MAP_EVERY qx_gen_tac [`ss`, `values`, `buf_addr`] >> strip_tac >>
  Cases_on `values` >- fs[log_args_rel_def] >>
  rename1 `log_args_rel ((src,aty)::ops) (atv::atvs) (v::vs) ss` >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cenv`, `src`, `aty`, `ops`, `fty`, `fts`, `ftv`, `ftvs`, `atv`, `atvs`,
    `buf`, `field_offset`, `cs`, `ret`, `cs'`, `ss`, `v`, `vs`, `buf_addr`] log_store_cons_head_path) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `mid` (qx_choose_then `middle` strip_assume_tac)) >>
  `log_data_store_contract ctx func ops ftvs atvs buf (field_offset + type_memory_size ftv) mid cs'` by
    (qpat_x_assum `!mid. _ ==> log_data_store_contract _ _ _ _ _ _ _ _ _` (qspec_then `mid` mp_tac) >>
     impl_tac >- first_assum MATCH_ACCEPT_TAC >> asm_simp_tac bool_ss []) >>
  mp_tac (Q.SPECL [`ftv`, `ftvs`, `w2n (buf_addr:bytes32) + field_offset`, `dimword(:256)`]
    log_target_cons_bounds) >> impl_tac >- first_assum MATCH_ACCEPT_TAC >> strip_tac >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [ADD_ASSOC]) >>
  qpat_x_assum `log_data_store_contract _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [log_data_store_contract_def]) >>
  disch_then (qspecl_then [`middle`, `vs`, `buf_addr`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC,
    asm_simp_tac bool_ss [ADD_ASSOC] >> NO_TAC]) >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [ADD_ASSOC]) >>
  mp_tac (Q.SPECL [`ctx`, `func`, `ftv`, `ftvs`, `v`, `vs`, `w2n (buf_addr:bytes32) + field_offset`,
    `cs.cs_next_var`, `mid.cs_next_var`, `cs'.cs_next_var`, `ss`, `middle`, `out`] tuple_fields_copy_compose) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC,
    asm_simp_tac bool_ss [ADD_ASSOC] >> NO_TAC]) >> strip_tac >>
  mp_tac (Q.SPECL [`(src,aty)::ops`, `atv::atvs`, `v::vs`, `ss`, `out`, `TupleTV (ftv::ftvs)`, `1`,
    `w2n (buf_addr:bytes32) + field_offset`,
    `compiler_var_names cs.cs_next_var (cs'.cs_next_var - cs.cs_next_var)`] log_args_frame) >>
  simp_tac bool_ss [MULT_CLAUSES] >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  `copy_state_frame ss out` by
    (irule copy_state_frame_trans >> qexists_tac `middle` >> simp[]) >>
  qexists_tac `out` >> rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC,
    asm_simp_tac bool_ss [value_has_type_def] >> NO_TAC]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed full Log data cons composition: " ^ name)
  end) (DB.thms "typedLogDataCons")
