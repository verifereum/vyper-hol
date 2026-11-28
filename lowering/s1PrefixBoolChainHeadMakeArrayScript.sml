(* The MakeArray head inherits prefix facts from its strictly smaller elements. *)
Theory s1PrefixBoolChainHeadMakeArray
Ancestors
  s1PrefixPreds s1PrefixMakeArray s1PrefixCheckedContextFull
  bodyFullPreds exprCallBounds vyperAST vyperTypeCallGraph s1PrefixSyntaxCalls list alist

Theorem prefix_list_from_members:
  !cx ys. (!a. MEM a ys ==> body_expr_prefix_ok cx a) ==>
    body_exprs_prefix_ok cx ys
Proof
  rpt gen_tac >> strip_tac >>
  Induct_on `ys` >- simp[body_exprs_prefix_ok_def] >>
  rpt gen_tac >> strip_tac >>
  simp[body_exprs_prefix_ok_def]
QED

Theorem bool_chain_head_make_array_prefix_ok:
  !cx ann t n xs.
    (!tops. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] ==>
      EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
        (vyperTypeCallGraph$int_calls_expr (Builtin ann (MakeArray t n) xs))) /\
    (!a. expr_size a < expr_size (Builtin ann (MakeArray t n) xs) /\
       (!ts. ALOOKUP cx.sources cx.txn.target = SOME [(NONE,ts)] ==>
         EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,ts)] []))
           (vyperTypeCallGraph$int_calls_expr a)) ==>
       body_expr_prefix_ok cx a) ==>
    body_expr_prefix_ok cx (Builtin ann (MakeArray t n) xs)
Proof
  rpt gen_tac >> strip_tac >>
  `body_exprs_prefix_ok cx xs` by
    (irule prefix_list_from_members >> rpt gen_tac >> strip_tac >>
     qpat_assum `!a. expr_size a < expr_size (Builtin ann (MakeArray t n) xs) /\ _ ==> _`
       irule >>
     rpt conj_tac
     >- (rpt strip_tac >> res_tac >>
         fs[int_calls_expr_def, int_calls_exprs_members] >> metis_tac[])
     >> drule expr_list_member_bound >> simp[expr_size_def]) >>
  qpat_assum `body_exprs_prefix_ok cx xs`
    (fn th => simp[Once body_expr_prefix_ok_def, th]) >>
  rpt gen_tac >> strip_tac >>
  `body_exprs_full_ok cx xs` by
    (drule_then strip_assume_tac checked_context_full_exprs >>
     first_x_assum irule >>
     fs[body_const_cells_agree_def, int_calls_expr_def]) >>
  irule make_array_builtin_sim_prefix >> metis_tac[]
QED
