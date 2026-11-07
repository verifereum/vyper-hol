Theory bodyPtrPopMutualBoundary
Ancestors bodyPtrPopCompileDomain bodyPtrPopExprBoundary bodyPtrPopBuiltinBoundary
  bodyPtrPopTypeBuiltinBoundary bodyPtrPopCompilerRecursionBoundary

Theorem pop_compile_mutual_boundary:
  (!cenv ty e sa r sb. pop_compile_domain tops e /\ pop_comp_boundary sa /\
    compile_expr cenv ty e sa = (r,sb) ==> pop_comp_boundary sb) /\
  (!cenv rt ty bi args sa r sb. supported_builtin_form tops rt bi args /\
    EVERY (supported_pure_expr tops) args /\ pop_comp_boundary sa /\
    compile_builtin_dispatch cenv rt ty bi args sa = (r,sb) ==> pop_comp_boundary sb) /\
  (!cenv vt ty tb rt args sa r sb. supported_type_builtin_form tops vt tb rt args /\
    EVERY (supported_pure_expr tops) args /\ pop_comp_boundary sa /\
    compile_type_builtin_dispatch cenv vt ty tb rt args sa = (r,sb) ==>
    pop_comp_boundary sb)
Proof
  qspecl_then [`pop_compile_domain tops`,
    `\rt bi args. supported_builtin_form tops rt bi args /\
      EVERY (supported_pure_expr tops) args`,
    `\vt tb rt args. supported_type_builtin_form tops vt tb rt args /\
      EVERY (supported_pure_expr tops) args`] mp_tac
    pop_compile_mutual_boundary_closure >>
  BETA_TAC >> pure_rewrite_tac [GSYM CONJ_ASSOC] >>
  (impl_tac >-
    (conj_tac >- MATCH_ACCEPT_TAC pop_expr_open_boundary >>
     conj_tac >- MATCH_ACCEPT_TAC pop_builtin_open_boundary >>
     MATCH_ACCEPT_TAC pop_type_builtin_open_boundary)) >>
  simp_tac bool_ss []
QED

Theorem pop_compile_supported_boundary:
  supportedExprs$supported_expr tops e /\ pop_comp_boundary sa /\
  compile_expr cenv ty e sa = (r,sb) ==> pop_comp_boundary sb
Proof
  rpt strip_tac >> drule pop_domain_supported >> strip_tac >>
  drule_all (cj 1 pop_compile_mutual_boundary) >> simp[]
QED
