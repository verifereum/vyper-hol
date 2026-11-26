(* The ExtCall row of the same-context expression induction. *)
Theory s1PrefixBoolChainHeadExtCall
Ancestors
  s1PrefixBoolChainExtArgDescent s1PrefixBoolChainExtArgDomain
  s1PrefixCheckedContextFull s1PrefixPreds

Theorem bool_chain_head_extcall_prefix_ok:
  !cx ann stat skip fname ats rt opts args dr.
    (!a. expr_size a < expr_size (Call ann (ExtCall stat skip (fname,ats,rt) opts) args dr) ==>
         body_expr_prefix_ok cx a) ==>
    body_expr_prefix_ok cx (Call ann (ExtCall stat skip (fname,ats,rt) opts) args dr)
Proof
  rpt gen_tac >> disch_tac >> simp[Once body_expr_prefix_ok_def] >>
  rpt gen_tac >> strip_tac >>
  drule_then strip_assume_tac checked_context_full_exprs >>
  `body_expr_prefix_ok cx (Call ann (ExtCall stat skip (fname,ats,rt) opts) args dr)` by
    (irule (CONJUNCT2 (REWRITE_RULE [IMP_CONJ_THM] bool_chain_extcall_contracts)) >>
     gen_tac >> conj_tac >- simp[] >>
     disch_tac >> first_x_assum irule >> drule bool_chain_ext_arg_smaller >> simp[]) >>
  qpat_x_assum `body_expr_prefix_ok cx (Call _ _ _ _)` mp_tac >>
  simp[Once body_expr_prefix_ok_def] >> metis_tac[]
QED
