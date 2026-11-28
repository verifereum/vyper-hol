Theory s1PrefixPopFullGuard
Ancestors
  bodyCallLiveness
  s1PrefixCheckedContextFull bodySimFullMain bodyFullPreds
  bodyFullShadowBodyInv bodySim exprSimHypsDefs vyperAST

Theorem pop_full_target_at_entry:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env st /\
  EVERY (\k. MEM k (vyperTypeContract$linked_live_functions [(NONE,tops)] []))
    (vyperTypeCallGraph$int_calls_target bt) /\
  expr_body_pre ce cx env (Pop ann bt) st ==>
  body_base_target_full_ok cx bt
Proof
  strip_tac >>
  drule_then assume_tac checked_context_full_guards >>
  drule_then assume_tac body_const_cells_agree_runtime_check >>
  `ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)]` by
    fs[body_const_cells_agree_def] >>
  match_mp_tac (cj 7 body_sim_full_mutual) >> gvs[] >> metis_tac[]
QED
