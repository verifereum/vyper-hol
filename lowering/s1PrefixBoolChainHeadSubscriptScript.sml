(* Subscript is closed under the same-context prefix induction hypothesis. *)
Theory s1PrefixBoolChainHeadSubscript
Ancestors
  s1PrefixSubscriptCase s1PrefixCheckedContextFull s1PrefixPreds vyperAST vyperTypeCallGraph list alist

Theorem bool_chain_head_subscript_prefix_ok:
  !cx ann obj idx.
    (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
      EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
        (vyperTypeCallGraph$int_calls_expr (Subscript ann obj idx))) /\
    (!a. expr_size a < expr_size (Subscript ann obj idx) /\
         (!ts. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,ts)] ==>
           EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,ts)] []))
             (vyperTypeCallGraph$int_calls_expr a)) ==>
         body_expr_prefix_ok cx a) ==>
    body_expr_prefix_ok cx (Subscript ann obj idx)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `?tops env es. body_const_cells_agree [(NONE,tops)] cx env es`
  >- (qpat_x_assum `?tops env es. _` strip_assume_tac >>
      `ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]` by
        fs[bodyFullPredsTheory.body_const_cells_agree_def] >>
      fs[int_calls_expr_def, EVERY_APPEND] >>
      `body_expr_prefix_ok cx obj /\ body_expr_prefix_ok cx idx` by
        (conj_tac >> first_x_assum irule >> simp[expr_size_def]) >>
      drule_then strip_assume_tac checked_context_full_exprs >>
      irule body_subscript_case_prefix >> simp[] >> metis_tac[]) >>
  once_rewrite_tac[body_expr_prefix_ok_def] >> simp[] >> metis_tac[]
QED
