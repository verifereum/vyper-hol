(* TOP-LEVEL: lift an actual child copy and the actual remaining field
   contract to the complete tuple cons. Strides are physical type sizes. *)
Theory typedFieldsCons
Ancestors
  typedCopyStateFrame typedFieldsContract typedFieldsReady typedFieldsCompose typedFieldsSafety
  typedCopyTypeContract typedSArrayDynInvariant abiStaticLoopCode
  memoryValueDefs valueEncoding vyperTyping vyperValue
  context compileEnv fragExec fragBlockPath venomState venomInst list words arithmetic

Theorem typed_fields_copy_contract_cons:
  !ctx func cenv dst src fty fts aty ats ftv ftvs atv atvs dst_off src_off cs ret cs'.
    type_memory_bytes cenv fty = type_memory_size ftv /\
    type_memory_bytes cenv aty = type_memory_size atv /\
    (!v. value_has_type atv v ==> value_has_type ftv v) /\
    typed_copy_type_contract ctx func cenv fty aty ftv atv /\
    (!after. compile_typed_copy_fields cenv dst src fts ats
      (dst_off + type_memory_bytes cenv fty) (src_off + type_memory_bytes cenv aty) after = (ret,cs') ==>
      typed_fields_copy_contract ctx func dst src ftvs atvs
        (dst_off + type_memory_bytes cenv fty) (src_off + type_memory_bytes cenv aty) after cs') /\
    compile_typed_copy_fields cenv dst src (fty::fts) (aty::ats) dst_off src_off cs = (ret,cs') ==>
    typed_fields_copy_contract ctx func dst src (ftv::ftvs) (atv::atvs) dst_off src_off cs cs'
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  simp_tac bool_ss [typed_fields_copy_contract_def] >>
  MAP_EVERY qx_gen_tac [`ss`, `values`, `dst_addr`, `src_addr`] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  Cases_on `values` >- fs[value_has_type_def] >> rename1 `values_have_types (atv::atvs) (v::vs)` >>
  qpat_assum `values_have_types (atv::atvs) (v::vs)`
    (strip_assume_tac o PURE_REWRITE_RULE [value_has_type_def]) >>
  mp_tac (Q.SPECL [`ctx`, `func`, `cenv`, `dst`, `src`, `fty`, `fts`, `aty`, `ats`, `ftv`, `ftvs`, `atv`, `atvs`,
    `dst_off`, `src_off`, `cs`, `ret`, `cs'`, `ss`, `v`, `vs`, `dst_addr`, `src_addr`] typed_fields_copy_head_ready) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `after_child` (qx_choose_then `mid` strip_assume_tac)) >>
  mp_tac (Q.SPECL [`dst`, `src`, `cs.cs_next_var`, `after_child.cs_next_var`, `cs'.cs_next_var`, `ss`, `mid`]
    compiler_operands_survive_prefix) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  `typed_fields_copy_contract ctx func dst src ftvs atvs
      (dst_off + type_memory_size ftv) (src_off + type_memory_size atv) after_child cs'` by
    (qpat_x_assum `!after. _ ==> typed_fields_copy_contract _ _ _ _ _ _ _ _ _ _`
       (qspec_then `after_child` mp_tac) >> asm_simp_tac bool_ss []) >>
  mp_tac (Q.SPECL [`atv`, `atvs`, `ftv`, `ftvs`, `w2n (src_addr:bytes32) + src_off`,
    `w2n (dst_addr:bytes32) + dst_off`, `dimword(:256)`] tuple_copy_parts_safety) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [ADD_ASSOC]) >>
  qpat_x_assum `typed_fields_copy_contract _ _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [typed_fields_copy_contract_def]) >>
  disch_then (qspecl_then [`mid`, `vs`, `dst_addr`, `src_addr`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC,
    asm_simp_tac bool_ss [ADD_ASSOC] >> NO_TAC]) >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [ADD_ASSOC]) >>
  `value_has_type ftv v` by
    (qpat_x_assum `!v. value_has_type atv v ==> _` irule >> first_assum MATCH_ACCEPT_TAC) >>
  mp_tac (Q.SPECL [`ctx`, `func`, `ftv`, `ftvs`, `v`, `vs`, `w2n (dst_addr:bytes32) + dst_off`,
    `cs.cs_next_var`, `after_child.cs_next_var`, `cs'.cs_next_var`, `ss`, `mid`, `out`]
    tuple_fields_copy_compose) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC,
    asm_simp_tac bool_ss [ADD_ASSOC] >> NO_TAC]) >> strip_tac >>
  `copy_state_frame ss out` by
    (irule copy_state_frame_trans >> qexists_tac `mid` >> simp[]) >>
  qexists_tac `out` >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED
