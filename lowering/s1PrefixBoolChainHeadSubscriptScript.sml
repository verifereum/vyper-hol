(* Subscript is closed under the same-context prefix induction hypothesis. *)
Theory s1PrefixBoolChainHeadSubscript
Ancestors
  s1PrefixSubscriptCase s1PrefixCheckedContextFull s1PrefixPreds vyperAST

Theorem bool_chain_head_subscript_prefix_ok:
  !cx ann obj idx.
    (!a. expr_size a < expr_size (Subscript ann obj idx) ==>
         body_expr_prefix_ok cx a) ==>
    body_expr_prefix_ok cx (Subscript ann obj idx)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `?tops env es. body_const_cells_agree [(NONE,tops)] cx env es`
  >- (qpat_x_assum `?tops env es. _` strip_assume_tac >>
      `body_expr_prefix_ok cx obj /\ body_expr_prefix_ok cx idx` by
        (conj_tac >> first_x_assum irule >> simp[expr_size_def]) >>
      drule_then strip_assume_tac checked_context_full_exprs >>
      irule body_subscript_case_prefix >> simp[]) >>
  once_rewrite_tac[body_expr_prefix_ok_def] >> simp[] >> metis_tac[]
QED
