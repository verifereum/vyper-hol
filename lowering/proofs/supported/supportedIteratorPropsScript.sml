Theory supportedIteratorProps
Ancestors supportedStmts supportedExprs supportedDecls vyperAST

Theorem supported_non_name_array_iterator:
  (!t name. e <> Name t name) /\ (!t id. e <> TopLevelName t id) ==>
  (supported_iterator tops ty (Array e) n <=>
   supported_expr tops e /\
   (!t fid args drv. e = Call t (IntCall fid) args drv /\ FST fid = NONE ==>
      ?m nr rr ps ds b.
        supported_function_decl tops fid Internal = SOME (m,nr,rr,ps,ds,t,b)) /\
   ?bd. expr_type e = ArrayT ty bd /\ bound_length bd <= n)
Proof
  Cases_on `e` >> simp[supported_iterator_def] >>
  Cases_on `c` >> simp[] >>
  rename1 `FST fid = NONE` >>
  Cases_on `supported_function_decl tops fid Internal` >> simp[] >>
  rename1 `supported_function_decl tops fid Internal = SOME decl` >>
  PairCases_on `decl` >> simp[]
QED
