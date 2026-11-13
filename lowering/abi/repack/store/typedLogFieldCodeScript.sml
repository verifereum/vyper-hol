(* TOP-LEVEL: actual Log field code determines its destination temporary,
   child span and complete allocation interval, without fixed name counts. *)
Theory typedLogFieldCode
Ancestors
  typedStoreCode typedSArrayDynFieldCode fieldStoreComposition fieldAddressProps
  abiBytestringCode abiStaticLoopCode
  context stmtLowering compileEnv fragExec venomInst list words arithmetic

Theorem compile_log_field_store_cuts:
  !cenv src aty fty buf field_offset cs ret cs' func.
    compile_log_store_data cenv [(src,aty)] [fty] buf field_offset cs = (ret,cs') /\
    fn_has_code cs cs' func /\
    EVERY (\name. src <> Var name)
      (compiler_var_names cs.cs_next_var (cs'.cs_next_var - cs.cs_next_var)) ==>
    ?dst mid.
      emit_op ADD [buf; Lit (n2w field_offset)] cs = (dst,mid) /\
      compile_store_memory cenv src dst fty aty mid = (ret,cs') /\
      fn_has_code cs mid func /\ fn_has_code mid cs' func /\
      mid.cs_next_var <= cs'.cs_next_var /\
      cs'.cs_next_var - cs.cs_next_var = SUC (cs'.cs_next_var - mid.cs_next_var) /\
      src <> dst /\
      EVERY (\name. dst <> Var name /\ src <> Var name)
        (compiler_var_names mid.cs_next_var (cs'.cs_next_var - mid.cs_next_var))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_log_store_field_contains >>
  disch_then (qx_choose_then `dst` (qx_choose_then `mid` strip_assume_tac)) >>
  drule emit_field_address_code >> strip_tac >>
  drule compile_store_memory_next_var >> DISCH_TAC >>
  `cs'.cs_next_var - cs.cs_next_var = SUC (cs'.cs_next_var - mid.cs_next_var)` by decide_tac >>
  qpat_assum `cs'.cs_next_var - cs.cs_next_var = SUC _`
    (fn delta => qpat_assum `EVERY _ (compiler_var_names cs.cs_next_var _)`
      (ASSUME_TAC o PURE_REWRITE_RULE [delta])) >>
  mp_tac (Q.SPECL [`buf`, `field_offset`, `cs`, `dst`, `mid`, `src`, `cs'.cs_next_var - mid.cs_next_var`]
    emit_field_address_copy_names) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  qexistsl_tac [`dst`, `mid`] >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theorem compile_log_store_field_continuation:
  !cenv src aty fty buf field_offset cs ret cs' func.
    compile_log_store_data cenv [(src,aty)] [fty] buf field_offset cs = (ret,cs') /\
    fn_has_code cs cs' func /\ cut_continuation_no_phi cs' func ==>
    cut_continuation_no_phi cs func
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_log_store_field_contains >>
  disch_then (qx_choose_then `dst` (qx_choose_then `mid` strip_assume_tac)) >>
  drule_all compile_store_memory_continuation >> DISCH_TAC >>
  mp_tac (Q.SPEC `ADD` typedCopyCutRulesTheory.compiler_cut_continuation_emit_helpers) >> simp[] >>
  disch_then (mp_tac o CONJUNCT1 o CONJUNCT2) >>
  disch_then (qspec_then `[buf; Lit (n2w field_offset)]` mp_tac) >>
  simp_tac bool_ss [typedCopyCutTheory.compiler_cut_continuation_def] >>
  disch_then (qspecl_then [`cs`, `dst`, `mid`, `func`] mp_tac) >> simp[]
QED
