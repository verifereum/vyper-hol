Theory vyperEvalPreservesImmutablesDom
Ancestors
  pair vyperMisc vyperAST vyperValue vyperContext vyperState vyperStorageBackend vyperCreate vyperCreateFrame vyperInterpreter
  vyperLookup vyperScopePreservation vyperStatePreservation
  vyperPlaceFrames vyperEvalExprPreservesScopesDom
  vyperImmutablesPreservation vyperCallFrame vyperCallOutcomeFrame
  vyperImmutableMetadataFrame vyperAbiFrame vyperAbiMemoryProps

(* ===== Immutable domains: place metadata and delayed ABI captures ===== *)

Definition preserves_immutables_dom_def:
  preserves_immutables_dom cx (st:evaluation_state) (st':evaluation_state) ⇔
    (∀tgt. IS_SOME (ALOOKUP st.immutables tgt) ⇔
           IS_SOME (ALOOKUP st'.immutables tgt)) ∧
    (∀src n imms imms'.
       ALOOKUP st.immutables cx.txn.target = SOME imms ∧
       ALOOKUP st'.immutables cx.txn.target = SOME imms' ⇒
       (IS_SOME (FLOOKUP (get_source_immutables src imms) n) ⇔
        IS_SOME (FLOOKUP (get_source_immutables src imms') n)))
End

Theorem immutable_metadata_frame_preserves_dom[local]:
  immutable_metadata_frame st st' ==> preserves_immutables_dom cx st st'
Proof
  strip_tac >> rw[preserves_immutables_dom_def]
  >- fs[immutable_metadata_frame_def] >>
  `OPTION_MAP FST (FLOOKUP (get_source_immutables src imms) n) =
   OPTION_MAP FST (FLOOKUP (get_source_immutables src imms') n)` by
    metis_tac[immutable_metadata_frame_def] >>
  Cases_on `FLOOKUP (get_source_immutables src imms) n` >>
  Cases_on `FLOOKUP (get_source_immutables src imms') n` >> gvs[]
QED

(* The place refactor supplies the stronger metadata frame, including errors.
   ABI evaluation is included by the same evaluator frame, not by assuming
   that captures leave the whole evaluation state unchanged. *)
Theorem immutables_dom_extended[local]:
  (∀cx s st res st'. eval_stmt cx s st = (res, st') ⇒ preserves_immutables_dom cx st st') ∧
  (∀cx ss st res st'. eval_stmts cx ss st = (res, st') ⇒ preserves_immutables_dom cx st st') ∧
  (∀cx it st res st'. eval_iterator cx it st = (res, st') ⇒ preserves_immutables_dom cx st st') ∧
  (∀cx tyv nm body vs st res st'. eval_for cx tyv nm body vs st = (res, st') ⇒ preserves_immutables_dom cx st st') ∧
  (∀cx e st res st'. eval_expr cx e st = (res, st') ⇒ preserves_immutables_dom cx st st') ∧
  (∀cx es st res st'. eval_exprs cx es st = (res, st') ⇒ preserves_immutables_dom cx st st') /\
  (!cx t st res st'. eval_base_place cx t st = (res,st') ==> preserves_immutables_dom cx st st') /\
  (!cx t st res st'. eval_target_place cx t st = (res,st') ==> preserves_immutables_dom cx st st') /\
  (!cx g v st res st'. assign_tuple_targets cx g v st = (res,st') ==> preserves_immutables_dom cx st st') /\
  (!cx gs vs st res st'. assign_tuple_target_list cx gs vs st = (res,st') ==> preserves_immutables_dom cx st st') /\
  (!cx e st res st'. eval_abi_expr cx e st = (res,st') ==> preserves_immutables_dom cx st st') /\
  (!cx es st res st'. eval_abi_exprs cx es st = (res,st') ==> preserves_immutables_dom cx st st')
Proof
  rpt conj_tac >> rpt strip_tac >>
  irule immutable_metadata_frame_preserves_dom >>
  metis_tac[eval_metadata_frame_with_results]
QED

(* ===== Main theorems ===== *)

Theorem eval_expr_preserves_immutables_addr_dom:
  ∀cx e st res st'.
    eval_expr cx e st = (res, st') ⇒
    ∀tgt. IS_SOME (ALOOKUP st.immutables tgt) ⇔ IS_SOME (ALOOKUP st'.immutables tgt)
Proof
  metis_tac[immutables_dom_extended, preserves_immutables_dom_def]
QED

Theorem eval_expr_preserves_immutables_dom:
  ∀cx e st res st'.
    eval_expr cx e st = (res, st') ⇒
    ∀src n imms imms'.
      ALOOKUP st.immutables cx.txn.target = SOME imms ∧
      ALOOKUP st'.immutables cx.txn.target = SOME imms' ⇒
      (IS_SOME (FLOOKUP (get_source_immutables src imms) n) ⇔
       IS_SOME (FLOOKUP (get_source_immutables src imms') n))
Proof
  rpt strip_tac >> drule (cj 5 immutables_dom_extended) >>
  rw[preserves_immutables_dom_def]
QED

Theorem eval_base_place_preserves_immutables_addr_dom:
  ∀cx bt st res st'.
    eval_base_place cx bt st = (res, st') ⇒
    ∀tgt. IS_SOME (ALOOKUP st.immutables tgt) ⇒ IS_SOME (ALOOKUP st'.immutables tgt)
Proof
  metis_tac[immutables_dom_extended, preserves_immutables_dom_def]
QED

Theorem eval_base_place_preserves_immutables_dom:
  ∀cx bt st res st'.
    eval_base_place cx bt st = (res, st') ⇒
    ∀src n imms imms'.
      ALOOKUP st.immutables cx.txn.target = SOME imms ∧
      ALOOKUP st'.immutables cx.txn.target = SOME imms' ⇒
      (IS_SOME (FLOOKUP (get_source_immutables src imms) n) ⇔
       IS_SOME (FLOOKUP (get_source_immutables src imms') n))
Proof
  rpt strip_tac >> drule (cj 7 immutables_dom_extended) >>
  rw[preserves_immutables_dom_def]
QED

Theorem eval_exprs_preserves_immutables_dom:
  ∀cx es st res st'.
    eval_exprs cx es st = (res, st') ⇒
    ∀src n imms imms'.
      ALOOKUP st.immutables cx.txn.target = SOME imms ∧
      ALOOKUP st'.immutables cx.txn.target = SOME imms' ⇒
      (IS_SOME (FLOOKUP (get_source_immutables src imms) n) ⇔
       IS_SOME (FLOOKUP (get_source_immutables src imms') n))
Proof
  rpt strip_tac >> drule (cj 6 immutables_dom_extended) >>
  rw[preserves_immutables_dom_def]
QED

Theorem eval_exprs_preserves_immutables_addr_dom:
  ∀cx es st res st'.
    eval_exprs cx es st = (res, st') ⇒
    ∀tgt. IS_SOME (ALOOKUP st.immutables tgt) ⇔ IS_SOME (ALOOKUP st'.immutables tgt)
Proof
  metis_tac[immutables_dom_extended, preserves_immutables_dom_def]
QED

Theorem eval_stmts_preserves_immutables_addr_dom:
  ∀cx ss st res st'.
    eval_stmts cx ss st = (res, st') ⇒
    ∀tgt. IS_SOME (ALOOKUP st.immutables tgt) ⇔ IS_SOME (ALOOKUP st'.immutables tgt)
Proof
  metis_tac[immutables_dom_extended, preserves_immutables_dom_def]
QED

Theorem eval_stmts_preserves_immutables_dom:
  ∀cx ss st res st'.
    eval_stmts cx ss st = (res, st') ⇒
    ∀src n imms imms'.
      ALOOKUP st.immutables cx.txn.target = SOME imms ∧
      ALOOKUP st'.immutables cx.txn.target = SOME imms' ⇒
      (IS_SOME (FLOOKUP (get_source_immutables src imms) n) ⇔
       IS_SOME (FLOOKUP (get_source_immutables src imms') n))
Proof
  rpt strip_tac >> drule (cj 2 immutables_dom_extended) >>
  rw[preserves_immutables_dom_def]
QED

Theorem eval_abi_preserves_immutables_dom:
  (!cx e st res st'. eval_abi_expr cx e st = (res,st') ==>
    preserves_immutables_dom cx st st') /\
  (!cx es st res st'. eval_abi_exprs cx es st = (res,st') ==>
    preserves_immutables_dom cx st st')
Proof
  metis_tac[immutables_dom_extended]
QED

Theorem eval_expr_results_preserves_immutables_addr_dom:
  eval_expr_results cx es st = (res,st') ==>
    !tgt. IS_SOME (ALOOKUP st.immutables tgt) <=>
          IS_SOME (ALOOKUP st'.immutables tgt)
Proof
  metis_tac[eval_expr_results_immutable_metadata_frame,
            immutable_metadata_frame_def]
QED

Theorem eval_expr_results_preserves_immutables_dom:
  eval_expr_results cx es st = (res,st') ==>
    !src n imms imms'.
      ALOOKUP st.immutables cx.txn.target = SOME imms /\
      ALOOKUP st'.immutables cx.txn.target = SOME imms' ==>
      (IS_SOME (FLOOKUP (get_source_immutables src imms) n) <=>
       IS_SOME (FLOOKUP (get_source_immutables src imms') n))
Proof
  rpt strip_tac >> drule eval_expr_results_immutable_metadata_frame >>
  disch_then (mp_tac o MATCH_MP immutable_metadata_frame_preserves_dom) >>
  rw[preserves_immutables_dom_def]
QED

(* Integration audit: immutable-domain exports must remain kernel closed. *)
val () = List.app (fn (name,th) =>
  let val (oracles,_) = Tag.dest_tag (Thm.tag th)
  in if List.all (fn s => s = "DISK_THM") oracles then ()
     else raise Fail ("Immutable-domain oracle debt: " ^ name)
  end) (DB.thms "vyperEvalPreservesImmutablesDom");
