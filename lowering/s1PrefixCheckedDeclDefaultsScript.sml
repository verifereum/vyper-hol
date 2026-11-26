Theory s1PrefixCheckedDeclDefaults
Ancestors
  groupedDefaultSyntax whitelistCheckerDecls vyperTypeContract vyperAST list

Theorem checked_external_decl_default_facts:
  check_contract F layouts addr [(NONE,tops)] = SOME art /\
  MEM (FunctionDecl External mut nr rr name args dflts ret fbody) tops ==>
  EVERY (runtime_constant_expr [(NONE,tops)]) dflts /\
  (name = "__default__" ==> dflts = [])
Proof
  strip_tac >>
  drule_all grouped_checked_default_syntax >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  disch_tac >> drule_all check_contract_fallback_no_arguments >>
  rw[NULL_EQ] >> gvs[]
QED
