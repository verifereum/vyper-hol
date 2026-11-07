Theory bodyPtrPopPlaceDomainProbe
Ancestors supportedExprs supportedExprForms supportedDecls supportedTypes
  vyperAST list

(* Closed counterexample to a proposed callback-domain bridge only.
   The storage declaration's type and the place expression's annotation differ. *)
Theorem pop_place_outside_expr_domain:
  supported_place_expr
    [VariableDecl Private Storage "x" (BaseT (UintT 256)) (SOME 0)]
    (TopLevelName (BaseT BoolT) (NONE,"x")) /\
  ~supportedExprs$supported_expr
    [VariableDecl Private Storage "x" (BaseT (UintT 256)) (SOME 0)]
    (TopLevelName (BaseT BoolT) (NONE,"x"))
Proof
  EVAL_TAC
QED
