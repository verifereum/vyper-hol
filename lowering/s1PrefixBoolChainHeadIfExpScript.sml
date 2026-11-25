(* IfExp row for the BoolChain head certificate. *)
Theory s1PrefixBoolChainHeadIfExp
Ancestors
  s1PrefixIfExpChildren s1PrefixCheckedContextFull s1PrefixPreds
  exprCallBounds vyperAST
Theorem bool_chain_head_ifexp_prefix_ok:
  !cx ty c a b.
  (!x. expr_size x < expr_size (IfExp ty c a b) ==> body_expr_prefix_ok cx x) ==>
  body_expr_prefix_ok cx (IfExp ty c a b)
Proof
  rpt gen_tac >> strip_tac >>
  simp[Once body_expr_prefix_ok_def] >>
  rpt gen_tac >> strip_tac >>
  `(!x. body_expr_full_ok cx x) /\ (!xs. body_exprs_full_ok cx xs)` by
    (irule checked_context_full_exprs >>
     qexistsl [`env`,`es`,`tops`] >> first_assum ACCEPT_TAC) >>
  `body_expr_full_ok cx c /\ body_expr_full_ok cx a /\
   body_expr_full_ok cx b` by metis_tac[] >>
  `expr_size c < expr_size (IfExp ty c a b) /\
   expr_size a < expr_size (IfExp ty c a b) /\
   expr_size b < expr_size (IfExp ty c a b)` by
    irule expr_ifexp_child_bounds >>
  `body_expr_prefix_ok cx c /\ body_expr_prefix_ok cx a /\
   body_expr_prefix_ok cx b` by metis_tac[] >>
  metis_tac[ifexp_prefix_from_child_cases]
QED
