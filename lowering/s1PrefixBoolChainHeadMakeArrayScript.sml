(* The MakeArray head inherits prefix facts from its strictly smaller elements. *)
Theory s1PrefixBoolChainHeadMakeArray
Ancestors
  s1PrefixPreds s1PrefixMakeArray s1PrefixCheckedContextFull
  bodyFullPreds vyperAST list

Theorem prefix_list_from_members:
  !cx ys. (!a. MEM a ys ==> body_expr_prefix_ok cx a) ==>
    body_exprs_prefix_ok cx ys
Proof
  rpt gen_tac >> strip_tac >>
  Induct_on `ys` >- simp[body_exprs_prefix_ok_def] >>
  rpt gen_tac >> strip_tac >>
  simp[body_exprs_prefix_ok_def]
QED

Theorem expr_size_lt_make_array_member:
  !ann t n xs a. MEM a xs ==>
    expr_size a < expr_size (Builtin ann (MakeArray t n) xs)
Proof
  rpt gen_tac >> strip_tac >>
  Induct_on `xs` >- simp[] >>
  rpt gen_tac >> strip_tac >> gvs[expr_size_def] >>
  Cases_on `a = h` >> gvs[] >> first_x_assum irule >> metis_tac[]
QED

Theorem bool_chain_head_make_array_prefix_ok:
  !cx ann t n xs.
    (!a. expr_size a < expr_size (Builtin ann (MakeArray t n) xs) ==>
       body_expr_prefix_ok cx a) ==>
    body_expr_prefix_ok cx (Builtin ann (MakeArray t n) xs)
Proof
  rpt gen_tac >> strip_tac >>
  `body_exprs_prefix_ok cx xs` by
    (irule prefix_list_from_members >> rpt gen_tac >> strip_tac >>
     qpat_assum `!a. expr_size a < expr_size (Builtin ann (MakeArray t n) xs) ==> _`
       irule >>
     irule expr_size_lt_make_array_member >> first_assum ACCEPT_TAC) >>
  qpat_assum `body_exprs_prefix_ok cx xs`
    (fn th => simp[Once body_expr_prefix_ok_def, th]) >>
  rpt gen_tac >> strip_tac >>
  `body_exprs_full_ok cx xs` by
    (drule checked_context_full_exprs >> metis_tac[]) >>
  irule make_array_builtin_sim_prefix >> metis_tac[]
QED
