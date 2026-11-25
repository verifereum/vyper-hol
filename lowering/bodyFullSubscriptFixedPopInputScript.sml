(* Transport the captured fixed-Pop selector witness to the no-copy caller
   post.  The selector producer and the caller use the very same source,
   endpoint state, ghosts and itinerary; only the post predicate is adapted. *)
Theory bodyFullSubscriptFixedPopInput
Ancestors gasOutcomeFull

Theorem nocopy_fixed_pop_select_observed:
  !DF lo explicit ctx fn PG tops cx st0 source es s G tn Q R Q' R'.
    gas_outcome_full (DF,lo,explicit,ctx,fn,PG) tops cx st0 source
      (es,s,G,tn) Q R /\
    (!H res ee G' tn' t. Q H res ee G' tn' t ==> Q' H res ee G' tn' t) /\
    (!H res ee gt r. R H res ee gt r ==> R' H res ee gt r) ==>
    gas_outcome_full (DF,lo,explicit,ctx,fn,PG) tops cx st0 source
      (es,s,G,tn) Q' R'
Proof
  rpt gen_tac >> strip_tac >>
  irule gas_outcome_full_post_mono >>
  qexistsl_tac [`Q`,`R`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
