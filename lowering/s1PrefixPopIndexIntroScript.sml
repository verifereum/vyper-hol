(* Lift the expression prefixes of a Pop's indices through its target. *)
Theory s1PrefixPopIndexIntro
Ancestors
  s1PrefixPop s1PrefixPreds bodyFullPreds bodyFullShadowBodyInv bodySimFull
  exprSimHypsDefs supportedExprs targetPlaceSimCasesBase vyperAST list

Theorem pop_prefix_from_smaller_indices:
  (!tops ctx ce shadow_ctx env st.
    body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shadow_ctx /\
    body_const_cells_agree [(NONE,tops)] cx env st /\
    expr_body_pre ce cx env (Pop ann bt) st ==> body_base_target_full_ok cx bt) /\
  (!x. MEM x (target_indices bt) ==> body_expr_prefix_ok cx x) ==>
  body_expr_prefix_ok cx (Pop ann bt)
Proof
  strip_tac >>
  `!t. (!x. MEM x (target_indices t) ==> body_expr_prefix_ok cx x) ==>
       body_base_target_prefix_ok cx t` by
    (ho_match_mp_tac base_assignment_target_induct >>
     simp[target_indices_def,body_base_target_prefix_ok_def,MEM_APPEND] >>
     metis_tac[]) >>
  `body_base_target_prefix_ok cx bt` by metis_tac[] >>
  Cases_on `?tops ctx ce shadow_ctx env st.
    body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shadow_ctx /\
    body_const_cells_agree [(NONE,tops)] cx env st /\
    expr_body_pre ce cx env (Pop ann bt) st`
  >- (irule body_pop_case_prefix >> simp[] >> metis_tac[]) >>
  simp[Once body_expr_prefix_ok_def] >> rpt strip_tac >> metis_tac[]
QED
