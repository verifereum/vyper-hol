(* TOP-LEVEL: outer memory stores allocate names monotonically and
   transport actual continuation facts through every dispatcher branch. *)
Theory typedStoreCode
Ancestors
  typedCopyVarFlow compileVarFlow typedCopyCut typedCopyCutRules typedCopyContinuations
  context compileEnv fragExec venomInst

Theorem compile_store_memory_next_var:
  !cenv src dst fty aty cs ret cs'.
    compile_store_memory cenv src dst fty aty cs = (ret,cs') ==>
    cs.cs_next_var <= cs'.cs_next_var
Proof
  rpt gen_tac >> DISCH_TAC >>
  mp_tac (Q.SPECL [`cenv`, `src`, `dst`, `fty`, `aty`] compiler_vars_mono_store_memory) >>
  simp_tac bool_ss [compiler_vars_mono_def] >>
  disch_then (qspec_then `cs` mp_tac) >> simp[]
QED

Theorem compiler_cut_continuation_store_memory:
  !cenv src dst fty aty.
    compiler_cut_continuation (compile_store_memory cenv src dst fty aty)
Proof
  rpt gen_tac >> simp_tac bool_ss [compile_store_memory_def] >>
  rpt (FIRST [CHANGED_TAC (simp_tac (srw_ss())
    [compiler_cut_continuation_emit_helpers, compiler_cut_continuation_store_bytestring,
     compiler_cut_continuation_copy_memory, CONJUNCT1 compiler_cut_continuation_typed_copy_mutual]),
    IF_CASES_TAC])
QED

Theorem compile_store_memory_continuation =
  REWRITE_RULE [compiler_cut_continuation_def] compiler_cut_continuation_store_memory;
