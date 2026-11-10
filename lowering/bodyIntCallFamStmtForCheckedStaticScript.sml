(* Static boundary for computed Range bounds.  Typing inversion is supplied
   by body_range_typing; only the support inversion is specific here. *)
Theory bodyIntCallFamStmtForCheckedStatic
Ancestors
  bodySimDeclCases supportedStmts

Theorem supported_checked_range_contract:
  ~(?a1 n1 a2 n2. e1 = Literal a1 (IntL n1) /\
                     e2 = Literal a2 (IntL n2)) ==>
  (supported_iterator tops ty (Range e1 e2) bound <=>
   supported_pure_expr tops e1 /\ supported_pure_expr tops e2 /\ 0 < bound)
Proof
  Cases_on `e1` >> Cases_on `e2` >>
  simp[supported_iterator_def] >>
  rename1 `_ <=> (supported_pure_expr tops (Literal ty1 lit1) /\
           supported_pure_expr tops (Literal ty2 lit2) /\ 0 < bound)` >>
  Cases_on `lit1` >> Cases_on `lit2` >> simp[]
QED
