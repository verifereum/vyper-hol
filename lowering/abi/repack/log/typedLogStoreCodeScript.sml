(* TOP-LEVEL: complete Log data-store actions allocate monotonically and
   transport continuation facts. Actual head/tail spans retain both cuts. *)
Theory typedLogStoreCode
Ancestors
  logStoreComposition typedStoreCode typedCopyVarFlow compileVarFlow
  typedCopyCut typedCopyCutRules typedCopyAppend
  context stmtLowering compileEnv emitHelper fragExec venomInst list pair arithmetic

val log_mono_rules = [compiler_vars_mono_return, compiler_vars_mono_emit_helpers,
  compiler_vars_mono_store_memory];

fun log_mono_step goal = FIRST
  [CHANGED_TAC (asm_simp_tac (srw_ss()) log_mono_rules), gen_tac,
   irule compiler_vars_mono_bind >> conj_tac,
   irule compiler_vars_mono_ignore_bind >> conj_tac] goal;

Theorem compiler_vars_mono_log_store_data:
  !cenv ops fts buf field_offset.
    compiler_vars_mono (compile_log_store_data cenv ops fts buf field_offset)
Proof
  Induct_on `ops` >> Cases_on `fts` >> rpt gen_tac >>
  simp_tac bool_ss [Once compile_log_store_data_def, LET_THM] >> rpt log_mono_step
QED

Theorem compile_log_store_data_next_var:
  !cenv ops fts buf field_offset cs ret cs'.
    compile_log_store_data cenv ops fts buf field_offset cs = (ret,cs') ==>
    cs.cs_next_var <= cs'.cs_next_var
Proof
  rpt gen_tac >> DISCH_TAC >>
  mp_tac (Q.SPECL [`cenv`, `ops`, `fts`, `buf`, `field_offset`] compiler_vars_mono_log_store_data) >>
  simp_tac bool_ss [compiler_vars_mono_def] >>
  disch_then (qspec_then `cs` mp_tac) >> simp[]
QED

val log_cut_rules = [compiler_cut_continuation_return, compiler_cut_continuation_emit_helpers,
  compiler_cut_continuation_store_memory, cs_appends_return, cs_appends_emit_helpers,
  cs_appends_compile_store_memory, cs_appends_compile_log_store_data];

fun log_cut_step goal = FIRST
  [CHANGED_TAC (asm_simp_tac (srw_ss()) log_cut_rules), gen_tac,
   irule compiler_cut_continuation_bind >> rpt conj_tac,
   irule compiler_cut_continuation_ignore_bind >> rpt conj_tac,
   irule cs_appends_bind >> rpt conj_tac,
   irule cs_appends_ignore_bind >> rpt conj_tac] goal;

Theorem compiler_cut_continuation_log_store_data:
  !cenv ops fts buf field_offset.
    compiler_cut_continuation (compile_log_store_data cenv ops fts buf field_offset)
Proof
  Induct_on `ops` >> Cases_on `fts` >> rpt gen_tac >>
  simp_tac bool_ss [Once compile_log_store_data_def, LET_THM] >> rpt log_cut_step
QED

Theorem compile_log_store_data_continuation =
  REWRITE_RULE [compiler_cut_continuation_def] compiler_cut_continuation_log_store_data;

Theorem compile_log_store_data_cons_cuts:
  !cenv arg ops fty fts buf field_offset cs ret cs' func.
    compile_log_store_data cenv (arg::ops) (fty::fts) buf field_offset cs = (ret,cs') /\
    fn_has_code cs cs' func /\ cut_continuation_no_phi cs' func ==>
    ?mid. compile_log_store_data cenv [arg] [fty] buf field_offset cs = ((),mid) /\
      compile_log_store_data cenv ops fts buf (field_offset + type_memory_bytes cenv fty) mid = (ret,cs') /\
      fn_has_code cs mid func /\ fn_has_code mid cs' func /\
      cs.cs_next_var <= mid.cs_next_var /\ mid.cs_next_var <= cs'.cs_next_var /\
      cut_continuation_no_phi mid func
Proof
  rpt gen_tac >> strip_tac >> drule_all compile_log_store_data_split_code >>
  disch_then (qx_choose_then `mid` strip_assume_tac) >>
  `cs.cs_next_var <= mid.cs_next_var` by
    (first_assum (ACCEPT_TAC o MATCH_MP compile_log_store_data_next_var)) >>
  `mid.cs_next_var <= cs'.cs_next_var` by
    (first_assum (ACCEPT_TAC o MATCH_MP compile_log_store_data_next_var)) >>
  mp_tac (Q.SPECL [`cenv`, `ops`, `fts`, `buf`, `field_offset + type_memory_bytes cenv fty`,
    `mid`, `ret`, `cs'`, `func`] compile_log_store_data_continuation) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  qexists_tac `mid` >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed full Log data-store compiler cuts: " ^ name)
  end) (DB.thms "typedLogStoreCode")
