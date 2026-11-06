Theory vyperEvalScopesProgress
Ancestors
  pair sum vyperMisc vyperContext vyperState vyperCreate vyperCreateFrame vyperInterpreter vyperLookup
  vyperScopePreservation vyperStatePreservation vyperPlaceFrames vyperCallFrame vyperCallOutcomeFrame
  vyperCallOutcome[ignore_grammar] vyperEvalExprPreservesScopesDom

(* Every local of sc that sc' still has is unchanged in sc' or has more
   popped history.  Within an expression the only write to a local is a
   memory pop, which records one entry in the local's popped history
   (record_pop conses; replace_popped keeps the history's length); an
   internal call runs the callee in its own scopes and restores the
   caller's.  So a local whose entry is the same at both ends of an
   evaluation is the same at every point in between: the relation is
   transitive. *)
Definition scopes_progress_def:
  scopes_progress sc sc' <=>
    !n e e'. lookup_scopes n sc = SOME e /\ lookup_scopes n sc' = SOME e' ==>
             e' = e \/ LENGTH e.popped < LENGTH e'.popped
End

Theorem scopes_progress_refl[simp]:
  scopes_progress sc sc
Proof
  rw[scopes_progress_def] >> gvs[]
QED

Theorem lookup_scopes_dom_some[local]:
  !sc1 sc2 n e. MAP FDOM sc1 = MAP FDOM sc2 /\ lookup_scopes n sc1 = SOME e ==>
    ?e2. lookup_scopes n sc2 = SOME e2
Proof
  Induct >> Cases_on `sc2` >> simp[lookup_scopes_def] >> rpt gen_tac >>
  strip_tac >> Cases_on `FLOOKUP h' n` >> gvs[AllCaseEqs()] >>
  gvs[finite_mapTheory.FLOOKUP_DEF] >> metis_tac[]
QED

Theorem scopes_progress_trans:
  MAP FDOM sc1 = MAP FDOM sc2 /\
  scopes_progress sc1 sc2 /\ scopes_progress sc2 sc3 ==> scopes_progress sc1 sc3
Proof
  rw[scopes_progress_def] >>
  drule_all lookup_scopes_dom_some >> strip_tac >>
  rpt (first_x_assum drule_all >> strip_tac) >> gvs[]
QED

Theorem replace_popped_length[local]:
  !history tv path replacement history'.
    replace_popped tv path replacement history = SOME history' ==>
    LENGTH history' = LENGTH history
Proof
  Induct >> simp[Once replace_popped_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[Once replace_popped_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  first_x_assum drule >> simp[]
QED

Theorem scopes_progress_update[local]:
  find_containing_scope id sc = SOME (pre,env,entry,rest) /\
  (entry' = entry \/ LENGTH entry.popped < LENGTH entry'.popped) ==>
  scopes_progress sc (pre ++ (env |+ (id,entry'))::rest)
Proof
  strip_tac >>
  drule find_containing_scope_lookup >> strip_tac >>
  drule find_containing_scope_pre_none >> strip_tac >>
  drule find_containing_scope_structure >> strip_tac >>
  rw[scopes_progress_def] >> Cases_on `n = id` >>
  gvs[lookup_scopes_update, lookup_scopes_update_other] >> metis_tac[]
QED

Theorem eval_scopes_progress:
  (!cx e st res st'. eval_expr cx e st = (res,st') ==>
     scopes_progress st.scopes st'.scopes) /\
  (!cx es st res st'. eval_exprs cx es st = (res,st') ==>
     scopes_progress st.scopes st'.scopes) /\
  (!cx bt st res st'. eval_base_place cx bt st = (res,st') ==>
     scopes_progress st.scopes st'.scopes) /\
  (!cx bt st res st'. eval_target_place cx bt st = (res,st') ==>
     scopes_progress st.scopes st'.scopes) /\
  (!cx es st res st'. eval_expr_results cx es st = (res,st') ==>
     scopes_progress st.scopes st'.scopes)
Proof
  cheat
QED
