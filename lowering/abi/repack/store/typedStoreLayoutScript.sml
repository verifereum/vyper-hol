(* TOP-LEVEL: layout-compatible outer stores preserve complete typed
   layouts. Source typing may widen while its physical layout is retained. *)
Theory typedStoreLayout
Ancestors
  typedCopyContract typedCopyBulkContract typedSArrayDynInvariant
  memoryLayoutSource memoryLayoutRel layoutStoreProps typeLayoutProps typedCopyProducer
  memoryValueDefs valueEncoding vyperEventCompatibility
  context compileEnv compileVyper vyperTypeContract vyperContext vyperTypeSystem vyperValue
  fragExec fragBlockPath venomState venomInst list words arithmetic

Theorem typed_copy_contract_source_layout:
  !ctx func dst src ftv atv cs cs'.
    memory_layout_rel ftv atv /\
    (!v. value_has_type atv v ==> value_has_type ftv v) /\
    typed_copy_contract ctx func dst src ftv ftv cs cs' ==>
    typed_copy_contract ctx func dst src ftv atv cs cs'
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `memory_layout_rel _ _` (strip_assume_tac o REWRITE_RULE [memory_layout_rel_def]) >>
  simp_tac bool_ss [typed_copy_contract_def] >>
  MAP_EVERY qx_gen_tac [`ss`, `v`, `dst_addr`, `src_addr`] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  qpat_assum `type_memory_size ftv = type_memory_size atv`
    (fn eq => RULE_ASSUM_TAC (PURE_REWRITE_RULE [eq]) >> ASSUME_TAC eq) >>
  `value_has_type ftv v` by (first_assum irule >> first_assum MATCH_ACCEPT_TAC) >>
  `memory_value_rel ftv v (w2n src_addr) ss.vs_memory` by
    (qpat_x_assum `!v offset mem. _ = _`
       (qspecl_then [`v`, `w2n (src_addr:bytes32)`, `ss.vs_memory`] mp_tac) >> simp[]) >>
  qpat_x_assum `typed_copy_contract _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [typed_copy_contract_def]) >>
  disch_then (qspecl_then [`ss`, `v`, `dst_addr`, `src_addr`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> FIRST [first_assum MATCH_ACCEPT_TAC,
    asm_simp_tac bool_ss [] >> NO_TAC]) >> simp[]
QED

Theorem checked_compile_copy_layout_contract:
  !tops in_deploy layouts addr art ctx func cenv dst src fty aty ftv atv cs ret cs'.
    check_contract in_deploy layouts addr [(NONE,tops)] = SOME art /\
    cenv.ce_struct_fields = make_struct_fields_map tops /\ event_arg_compatible fty aty /\
    evaluate_type (type_env tops) fty = SOME ftv /\ evaluate_type (type_env tops) aty = SOME atv /\
    (fty = aty \/ tuple_memory_layout_eq fty aty) /\
    compile_copy_memory dst src (type_memory_bytes cenv fty) cs = (ret,cs') ==>
    typed_copy_contract ctx func dst src ftv atv cs cs'
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  drule checked_contract_struct_args_unique >> DISCH_TAC >>
  mp_tac (Q.SPECL [`tops`, `cenv`, `fty`, `ftv`] type_memory_bytes_evaluated) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  drule_all bulk_store_layout_keys >> strip_tac >>
  mp_tac (Q.SPECL [`fty`, `aty`, `type_env tops`, `ftv`, `atv`] memory_layout_key_evaluated) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  mp_tac (Q.SPECL [`fty`, `aty`] (CONJUNCT1 event_arg_compatible_value_has_type)) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >>
  disch_then (qspecl_then [`type_env tops`, `ftv`, `atv`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  qpat_assum `type_memory_bytes cenv fty = type_memory_size ftv`
    (fn sz => qpat_assum `compile_copy_memory _ _ _ _ = _`
      (ASSUME_TAC o PURE_REWRITE_RULE [sz])) >>
  `typed_copy_contract ctx func dst src ftv ftv cs cs'` by
    (mp_tac (Q.SPECL [`ctx`, `func`, `dst`, `src`, `ftv`, `cs`, `ret`, `cs'`]
       compile_copy_memory_contract) >> impl_tac >- first_assum MATCH_ACCEPT_TAC >> simp[]) >>
  mp_tac (Q.SPECL [`ctx`, `func`, `dst`, `src`, `ftv`, `atv`, `cs`, `cs'`]
    typed_copy_contract_source_layout) >> simp[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed outer layout store contract: " ^ name)
  end) (DB.thms "typedStoreLayout")
