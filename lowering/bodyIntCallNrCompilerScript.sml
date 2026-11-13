Theory bodyIntCallNrCompiler
Ancestors
  bodyIntCallCompilerBoundary exprLoweringProps exprLowering compileEnv stmtLoweringMono

Theorem nr_staged_prefix:
  compile_stage_intcall_args compile_expr ce es flags tys st2 = (ops,st2a) /\
  compile_stage_intcall_args compile_expr ce' es' flags' tys' st2a = (ops',si) /\
  ci_mono sa st2 ==>
  ci_mono sa si
Proof
  strip_tac >>
  `ci_mono st2 st2a` by
    (qspecl_then [`compile_expr`,`ce`,`es`,`flags`,`tys`,`st2`]
       mp_tac ci_mono_compile_stage_intcall_args >>
     simp[cj 1 ci_mono_compile_expr_sa]) >>
  `ci_mono st2a si` by
    (qspecl_then [`compile_expr`,`ce'`,`es'`,`flags'`,`tys'`,`st2a`]
       mp_tac ci_mono_compile_stage_intcall_args >>
     simp[cj 1 ci_mono_compile_expr_sa]) >>
  metis_tac[ci_mono_trans]
QED
