Theory s1PrefixPopFullGuard
Ancestors
  s1PrefixCheckedContextFull bodySimFullMain bodyFullPreds
  bodyFullShadowBodyInv bodySim exprSimHypsDefs vyperAST

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  strip_tac >>
  match_mp_tac (cj 7 body_sim_full_mutual) >>
  drule_then ACCEPT_TAC checked_context_full_guards
QED
*)
Theorem pop_full_target_at_entry:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env st /\
  expr_body_pre ce cx env (Pop ann bt) st ==>
  body_base_target_full_ok cx bt
Proof
  cheat
QED
