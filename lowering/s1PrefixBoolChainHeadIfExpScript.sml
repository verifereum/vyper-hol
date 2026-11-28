(* IfExp row for the BoolChain head certificate. *)
Theory s1PrefixBoolChainHeadIfExp
Ancestors
  s1PrefixIfExpChildren s1PrefixCheckedContextFull s1PrefixPreds
  exprCallBounds vyperAST vyperTypeCallGraph list alist
Theorem bool_chain_head_ifexp_prefix_ok:
  !cx ty c a b.
  (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
    EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
      (vyperTypeCallGraph$int_calls_expr (IfExp ty c a b))) /\
  (!x. expr_size x < expr_size (IfExp ty c a b) /\
        (!ts. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,ts)] ==>
          EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,ts)] []))
            (vyperTypeCallGraph$int_calls_expr x)) ==> body_expr_prefix_ok cx x) ==>
  body_expr_prefix_ok cx (IfExp ty c a b)
Proof
  rpt gen_tac >> strip_tac >>
  simp[Once body_expr_prefix_ok_def] >>
  rpt gen_tac >> strip_tac >>
  drule_then strip_assume_tac checked_context_full_exprs >>
  `ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]` by
    fs[bodyFullPredsTheory.body_const_cells_agree_def] >>
  fs[int_calls_expr_def, EVERY_APPEND] >>
  `body_expr_full_ok cx c /\ body_expr_full_ok cx a /\
   body_expr_full_ok cx b` by metis_tac[] >>
  `expr_size c < expr_size (IfExp ty c a b) /\
   expr_size a < expr_size (IfExp ty c a b) /\
   expr_size b < expr_size (IfExp ty c a b)` by
    irule expr_ifexp_child_bounds >>
  `body_expr_prefix_ok cx c /\ body_expr_prefix_ok cx a /\
   body_expr_prefix_ok cx b` by (fs[expr_size_def] >> metis_tac[]) >>
  metis_tac[ifexp_prefix_from_child_cases]
QED
