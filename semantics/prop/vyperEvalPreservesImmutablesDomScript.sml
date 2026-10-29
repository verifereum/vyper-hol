Theory vyperEvalPreservesImmutablesDom
Ancestors
  pair vyperMisc vyperAST vyperValue vyperContext vyperState vyperStorageBackend vyperCreate vyperCreateFrame vyperInterpreter
  vyperLookup vyperScopePreservation vyperStatePreservation
  vyperPlaceFrames vyperEvalExprPreservesScopesDom
  vyperImmutablesPreservation vyperCallFrame vyperCallOutcomeFrame vyperPlaceFrames
  vyperImmutableMetadataFrame

(* ========================================================================
   Preservation of immutables domain through eval_expr / eval_stmts.

   TOP-LEVEL:
     eval_expr_preserves_immutables_addr_dom
     eval_expr_preserves_immutables_dom
     eval_base_place_preserves_immutables_addr_dom
     eval_base_place_preserves_immutables_dom
     eval_exprs_preserves_immutables_addr_dom
     eval_stmts_preserves_immutables_addr_dom
     eval_stmts_preserves_immutables_dom
   ======================================================================== *)

(* ===== Predicate bundling both domain properties ===== *)

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

Theorem preserves_immutables_dom_eq[local]:
  s.immutables = t.immutables ==> preserves_immutables_dom cx s t
Proof
  rw[preserves_immutables_dom_def] >> gvs[]
QED

Theorem preserves_immutables_dom_trans[local]:
  preserves_immutables_dom cx s t /\ preserves_immutables_dom cx t u ==>
  preserves_immutables_dom cx s u
Proof
  rw[preserves_immutables_dom_def] >>
  `IS_SOME (ALOOKUP t.immutables cx.txn.target)` by
    metis_tac[optionTheory.IS_SOME_DEF] >>
  Cases_on `ALOOKUP t.immutables cx.txn.target` >> gvs[] >>
  metis_tac[]
QED

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
  (!cx gs vs st res st'. assign_tuple_target_list cx gs vs st = (res,st') ==> preserves_immutables_dom cx st st')
Proof
  rpt conj_tac >> rpt strip_tac >>
  irule immutable_metadata_frame_preserves_dom >>
  metis_tac[eval_metadata_frame_mutual]
QED


Theorem imm_dom_locals[local]:
  !s t. t.scopes = s.scopes /\ t.immutables = s.immutables ==>
    preserves_immutables_dom cx s t
Proof
  rpt strip_tac >> irule preserves_immutables_dom_eq >> simp[]
QED

val IMM_DOM_FRAME_PRIMITIVES =
  MATCH_MP state_rel_frame_locals_primitives imm_dom_locals;
val IMM_DOM_FRAME_TAKE =
  MATCH_MP state_rel_frame_locals_take imm_dom_locals;

Theorem imm_dom_frame_append_logs[local]:
  state_rel_frame (preserves_immutables_dom cx) (append_logs logs)
Proof
  simp[state_rel_frame_def, append_logs_def, update_pending_deletions_def, return_def] >> gen_tac >>
  irule preserves_immutables_dom_eq >> simp[]
QED

Theorem imm_dom_frame_bind_guarded[local]:
  state_rel_frame (preserves_immutables_dom cx) f /\
  (!s v t. f s = (INL v,t) ==> state_rel_frame (preserves_immutables_dom cx) (g v)) ==>
  state_rel_frame (preserves_immutables_dom cx) (vyperState$bind f g)
Proof
  rpt strip_tac >> irule state_rel_frame_bind_guarded >> simp[] >>
  metis_tac[preserves_immutables_dom_trans]
QED

Theorem imm_dom_frame_at[local]:
  state_rel_frame (preserves_immutables_dom cx) f /\ f st = (res,st') ==>
  preserves_immutables_dom cx st st'
Proof
  simp[state_rel_frame_result]
QED

(* Index primitive frames and bind decomposition once; recognition never
   traverses continuation arguments or the large guarded IHs. *)
val IMM_DOM_FRAME_LEAF_TAC =
  let
    val structural = Net.insert
      (concl imm_dom_frame_bind_guarded |> dest_imp |> snd,
       MATCH_MP_TAC imm_dom_frame_bind_guarded >> conj_tac) Net.empty
    val leaves = List.foldl (fn (th,net) =>
      Net.insert (concl th, MATCH_ACCEPT_TAC th) net) structural
      (imm_dom_frame_append_logs :: IMM_DOM_FRAME_TAKE ::
       CONJUNCTS IMM_DOM_FRAME_PRIMITIVES)
  in
    fn (asl,w) => FIRST (Net.match w leaves) (asl,w)
  end;

(* Reduce only exposed applications, never their continuation arguments. *)
val imm_dom_frame_head_conv =
  let
    val reduce = FIRST_CONV
      [BETA_CONV, REWR_CONV pair_case_thm, REWR_CONV UNCURRY]
    fun head tm = (reduce ORELSEC RATOR_CONV head) tm
  in head end;

(* Preserve CASE_TAC branch order using only fresh branch facts, rather
   than rebuilding its broad datatype rewrite set. *)
fun IMM_DOM_FRAME_CASE_TAC (g as (old,_)) =
  let
    fun simplify (asl,w) =
      let
        val fresh = List.filter (fn a => not (is_forall a) andalso
          not (List.exists (aconv a) old)) asl
        val rules = map ASSUME fresh
      in
        simp_tac bool_ss
          (optionTheory.option_CLAUSES :: pair_case_thm :: UNCURRY :: rules) >>
        RULE_ASSUM_TAC (REWRITE_RULE rules) >> MAP_EVERY assume_tac rules
      end (asl,w)
  in
    (BasicProvers.PURE_CASE_TAC >> simplify) g
  end;

val IMM_DOM_FRAME_TAC =
  rpt (FIRST [
    first_assum ACCEPT_TAC,
    IMM_DOM_FRAME_LEAF_TAC,
    CONV_TAC (HO_REWR_CONV FORALL_PROD),
    CONV_TAC (RAND_CONV imm_dom_frame_head_conv),
    gen_tac, strip_tac, conj_tac,
    CONV_TAC (RAND_CONV (REWR_CONV ignore_bind_def)),
    CONV_TAC (RAND_CONV ETA_CONV),
    CHANGED_TAC (fn (asl,w) =>
      simp_tac bool_ss (pair_case_thm :: UNCURRY ::
        List.map ASSUME (List.filter is_eq asl)) (asl,w)),
    IMM_DOM_FRAME_CASE_TAC]);

(* A bounded step exposes checkpoints without changing the existing frame tactic. *)
val IMM_DOM_FRAME_STEP_TAC = FIRST [
  CHANGED_TAC (simp_tac bool_ss [FORALL_PROD, pair_case_thm, UNCURRY]),
  gen_tac, strip_tac, conj_tac,
  first_assum ACCEPT_TAC,
  irule imm_dom_frame_bind_guarded >> conj_tac,
  IMM_DOM_FRAME_LEAF_TAC,
  CONV_TAC (RAND_CONV (REWR_CONV ignore_bind_def)),
  CHANGED_TAC (CONV_TAC (DEPTH_CONV ETA_CONV)),
  CHANGED_TAC (fn (asl,w) =>
    simp_tac bool_ss (pair_case_thm :: UNCURRY ::
      List.map ASSUME (List.filter is_eq asl)) (asl,w)),
  CASE_TAC];

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

(* Integration audit: immutable-domain exports must remain kernel closed. *)
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

val () = List.app (fn (name,th) =>
  let val (oracles,_) = Tag.dest_tag (Thm.tag th)
  in if List.all (fn s => s = "DISK_THM") oracles then ()
     else raise Fail ("Immutable-domain oracle debt: " ^ name)
  end) (DB.thms "vyperEvalPreservesImmutablesDom");
