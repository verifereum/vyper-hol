Theory vyperAssignTargetSpec

Ancestors
  vyperInterpreter vyperTypeValue vyperLookup vyperAssignTargetLemmas
  vyperScopePreservationLemmas

Definition assign_target_spec_def:
  assign_target_spec cx st (av : assignment_value) (ao : assign_operation) Q ⇔
    case assign_target cx av ao st of
    | (INL _, st') => Q st'
    | (INR _, _) => F
End

Theorem assign_target_spec_consequence:
  ∀cx st av ao Q Q'.
    (∀st'. Q st' ⇒ Q' st') ∧
    assign_target_spec cx st av ao Q ⇒
      assign_target_spec cx st av ao Q'
Proof
  rw[assign_target_spec_def] >> rpt strip_tac >>
  Cases_on `assign_target cx av ao st` >> gvs[] >>
  Cases_on `q` >> gvs[]
QED

Theorem assign_target_spec_scoped_var_replace_elim:
  ∀cx st n v Q. assign_target_spec cx st (BaseTargetV (ScopedVar n) []) (Replace v) Q ⇒
                Q (update_scoped_var st n v)
Proof
  rw[assign_target_spec_def, update_scoped_var_def, Once assign_target_def,
     bind_def, get_scopes_def, return_def, lift_option_def, lift_sum_def,
     set_scopes_def, assign_subscripts_def, ignore_bind_def] >>
  Cases_on `find_containing_scope (string_to_num n) st.scopes` >>
  gvs[return_def, raise_def, set_scopes_def, ignore_bind_def] >>
  PairCases_on `x` >> gvs[return_def, set_scopes_def, bind_def, ignore_bind_def]
QED

Theorem assign_target_spec_scoped_var_replace_intro:
  ∀cx st n v Q.
    var_in_scope st n ∧
    Q (update_scoped_var st n v) ⇒
    assign_target_spec cx st (BaseTargetV (ScopedVar n) []) (Replace v) Q
Proof
  rw[assign_target_spec_def] >>
  drule assign_target_scoped_var_replace >>
  disch_then (qspecl_then [`cx`, `v`] strip_assume_tac) >>
  simp[]
QED

Theorem assign_target_spec_scoped_var_update_elim:
  ∀cx st n bop v0 v v' Q.
    lookup_scoped_var st n = SOME v0 ∧
    evaluate_binop bop v0 v = INL v' ∧
    assign_target_spec cx st (BaseTargetV (ScopedVar n) []) (Update bop v) Q ⇒
    Q (update_scoped_var st n v')
Proof
  rw[assign_target_spec_def] >>
  drule_all assign_target_scoped_var_update >>
  disch_then (qspec_then `cx` mp_tac) >> strip_tac >> gvs[]
QED

Theorem assign_target_spec_scoped_var_update_intro:
  ∀cx st n bop v0 v v' Q.
    lookup_scoped_var st n = SOME v0 ∧
    evaluate_binop bop v0 v = INL v' ∧
    Q (update_scoped_var st n v') ⇒
    assign_target_spec cx st (BaseTargetV (ScopedVar n) []) (Update bop v) Q
Proof
  rw[assign_target_spec_def] >>
  drule_all assign_target_scoped_var_update >> simp[]
QED

Theorem assign_target_spec_pure:
  ∀cx st av ao P Q.
    P ∧ assign_target_spec cx st av ao Q ⇒
    assign_target_spec cx st av ao (λst'. P ∧ Q st')
Proof
  rw[assign_target_spec_def] >>
  Cases_on `assign_target cx av ao st` >> gvs[] >>
  Cases_on `q` >> gvs[]
QED

Theorem assign_target_spec_conj:
  ∀cx st av ao Q1 Q2.
    assign_target_spec cx st av ao Q1 ∧
    assign_target_spec cx st av ao Q2 ⇒
    assign_target_spec cx st av ao (λst'. Q1 st' ∧ Q2 st')
Proof
  rw[assign_target_spec_def] >>
  Cases_on `assign_target cx av ao st` >> gvs[] >>
  Cases_on `q` >> gvs[]
QED

Theorem assign_target_spec_preserves_toplevel_name_targets:
  ∀P cx st av ao n.
    lookup_toplevel_name_target cx st n = SOME av' ∧
    assign_target_spec cx st av ao P ⇒
    assign_target_spec cx st av ao (λst'. P st' ∧ lookup_toplevel_name_target cx st' n = SOME av')
Proof
  simp[assign_target_spec_def, lookup_toplevel_name_target_def, lookup_base_target_def] >>
  rpt strip_tac >>
  Cases_on `assign_target cx av ao st` >> Cases_on `q` >> gvs[] >>
  Cases_on `n` >>
  simp[Once evaluate_def, return_def] >>
  fs[Once evaluate_def, return_def]
QED

(* TODO: Proof needs to be updated for new immutables API (get_address_immutables) *)
Theorem assign_target_spec_preserves_name_targets:
  ∀P cx st av ao n.
    IS_SOME (ALOOKUP st.immutables cx.txn.target) ∧
    lookup_name_target cx st n = SOME av' ∧
    assign_target_spec cx st av ao P ⇒
    assign_target_spec cx st av ao (λst'. P st' ∧ lookup_name_target cx st' n = SOME av')
Proof
  cheat
QED

(* TODO: Proof needs to be updated for new immutables API (get_address_immutables) *)
Theorem assign_target_spec_lookup:
  ∀cx st n av v.
    valid_lookups cx st ∧
    lookup_name_target cx st n = SOME av ⇒
    assign_target_spec cx st av (Replace v) P ⇒
    assign_target_spec cx st av (Replace v) (λst'. P st' ∧ lookup_name cx st' n = SOME v)
Proof
  cheat
QED

(* TODO: Proof needs to be updated for new immutables API (get_address_immutables) *)
Theorem assign_target_spec_update:
  ∀cx st n bop av v1 v2 v.
    lookup_name cx st n = SOME v1 ∧
    lookup_name_target cx st n = SOME av ∧
    evaluate_binop bop v1 v2 = INL v ∧
    assign_target_spec cx st av (Update bop v2) P ⇒
    assign_target_spec cx st av (Update bop v2) (λst'. P st' ∧ lookup_name cx st' n = SOME v)
Proof
  cheat
QED

(* TODO: Proof needs to be updated for new immutables API *)
Theorem assign_target_spec_preserves_valid_lookups:
  ∀cx st n v.
    valid_lookups cx st ∧
    assign_target_spec cx st av ao P ⇒
    assign_target_spec cx st av ao (λst'. P st' ∧ valid_lookups cx st')
Proof
  cheat
QED

Theorem assign_target_spec_preserves_var_in_scope:
  ∀cx st n v.
    var_in_scope st n ∧
    assign_target_spec cx st av ao P ⇒
    assign_target_spec cx st av ao (λst'. P st' ∧ var_in_scope st' n)
Proof
  rpt strip_tac >>
  simp[assign_target_spec_def] >>
  Cases_on `assign_target cx av ao st` >> Cases_on `q` >> gvs[] >-
  (conj_tac >- fs[assign_target_spec_def] >>
   fs[var_in_scope_def, lookup_scoped_var_def] >>
   metis_tac[CONJUNCT1 assign_target_preserves_scopes_dom_lookup]) >>
  fs[assign_target_spec_def]
QED
