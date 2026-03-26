Theory vyperBareGlobalName

Ancestors
  vyperLookup vyperUpdateTarget vyperState vyperScopePreservation
  vyperLookupStorage vyperImmutablesPreservation

Definition lookup_immutable_def:
  lookup_immutable cx (st:evaluation_state) mid n =
  case ALOOKUP st.immutables cx.txn.target of
  | SOME imms => FLOOKUP (get_source_immutables mid imms) (string_to_num n)
  | NONE => NONE
End

Definition lookup_bare_global_name_def:
  lookup_bare_global_name cx st n = lookup_immutable cx st (current_module cx) n
End

Definition is_immutable_def:
  is_immutable cx n =
    case get_module_code cx (current_module cx) of
      NONE => F
    | SOME ts => is_immutable_decl (string_to_num n) ts
End

Definition update_bare_global_name_def:
  update_bare_global_name cx st n v =
    case lookup_bare_global_name cx st n of
    | NONE => st
    | SOME (tv, _) =>
      SND (set_immutable cx (current_module cx) (string_to_num n) tv v st)
End

(********************************************************)
(*                  Main theorems                       *)
(********************************************************)

Theorem immutables_preserved_after_update:
  ∀st n v. (update_name st n v).immutables = st.immutables
Proof
  rw[update_name_def, LET_THM] >>
  Cases_on `find_containing_scope (string_to_num n) st.scopes` >-
   (Cases_on `st.scopes` >> simp[evaluation_state_accfupds]) >>
  PairCases_on `x` >> simp[evaluation_state_accfupds]
QED

Theorem lookup_immutable_after_set_immutable:
  ∀cx n tv v st st'.
    set_immutable cx (current_module cx) (string_to_num n) tv v st = (INL (), st') ⇒
    lookup_immutable cx st' (current_module cx) n = SOME (tv, v)
Proof
  rw[set_immutable_def, lookup_immutable_def,
     bind_def, LET_THM, get_address_immutables_def,
     set_address_immutables_def, lift_option_def] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >> gvs[return_def, raise_def] >>
  simp[get_source_immutables_def, set_source_immutables_def,
       alistTheory.ALOOKUP_ADELKEY,
       finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem lookup_immutable_tl_scopes:
  ∀cx st mid n. lookup_immutable cx (tl_scopes st) mid n = lookup_immutable cx st mid n
Proof
  rw[lookup_immutable_def, tl_scopes_def]
QED

Theorem lookup_immutable_preserved_after_update:
  ∀cx st n v mid k.
    lookup_immutable cx (update_name st n v) mid k =
    lookup_immutable cx st mid k
Proof
  rw[lookup_immutable_def, immutables_preserved_after_update]
QED

(* ============================================================
   BareGlobalName theorems (scope/cross-domain independence)
   ============================================================ *)

(* lookup_bare_global_name ignores scopes *)
Theorem lookup_bare_global_name_scopes:
  ∀cx st n scopes'.
    lookup_bare_global_name cx (st with scopes := scopes') n =
    lookup_bare_global_name cx st n
Proof
  simp[lookup_bare_global_name_def, lookup_immutable_def]
QED

(* update_bare_global_name preserves scopes *)
Theorem update_bare_global_name_preserves_scopes:
  ∀cx st n v.
    (update_bare_global_name cx st n v).scopes = st.scopes
Proof
  rpt gen_tac >>
  simp[update_bare_global_name_def] >>
  Cases_on `lookup_bare_global_name cx st n` >> simp[] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `set_immutable cx (current_module cx) (string_to_num n) x0 v st` >>
  simp[] >>
  irule set_immutable_scopes >> metis_tac[]
QED

(* lookup_bare_global_name through update_name *)
Theorem lookup_bare_global_name_update_name:
  ∀cx st n1 n2 v.
    lookup_bare_global_name cx (update_name st n2 v) n1 =
    lookup_bare_global_name cx st n1
Proof
  rpt gen_tac >>
  simp[lookup_bare_global_name_def] >>
  irule lookup_immutable_preserved_after_update
QED

(* lookup_name through update_bare_global_name *)
Theorem lookup_name_update_bare_global_name:
  ∀cx st n1 n2 v.
    lookup_name (update_bare_global_name cx st n2 v) n1 =
    lookup_name st n1
Proof
  rpt gen_tac >>
  simp[lookup_name_def] >>
  simp[update_bare_global_name_preserves_scopes]
QED

(* var_in_scope through update_bare_global_name *)
Theorem var_in_scope_update_bare_global_name:
  ∀cx st n1 n2 v.
    var_in_scope (update_bare_global_name cx st n2 v) n1 ⇔
    var_in_scope st n1
Proof
  rpt gen_tac >>
  simp[var_in_scope_def] >>
  simp[update_bare_global_name_preserves_scopes,
       lookup_name_update_bare_global_name]
QED

(* scopes nonempty through update_bare_global_name *)
Theorem scopes_nonempty_update_bare_global_name:
  ∀cx st n v.
    (update_bare_global_name cx st n v).scopes ≠ [] ⇔ st.scopes ≠ []
Proof
  simp[update_bare_global_name_preserves_scopes]
QED

(* lookup_name_typed through update_bare_global_name *)
Theorem lookup_name_typed_update_bare_global_name:
  ∀cx st n1 n2 v.
    lookup_name_typed (update_bare_global_name cx st n2 v) n1 =
    lookup_name_typed st n1
Proof
  rpt gen_tac >>
  simp[lookup_name_typed_def] >>
  simp[update_bare_global_name_preserves_scopes]
QED

(* lookup_bare_global_name through tl_scopes *)
Theorem lookup_bare_global_name_tl_scopes:
  ∀cx st n.
    lookup_bare_global_name cx (tl_scopes st) n =
    lookup_bare_global_name cx st n
Proof
  rpt gen_tac >>
  simp[lookup_bare_global_name_def] >>
  irule lookup_immutable_tl_scopes
QED

(* lookup_bare_global_name through open_scope *)
Theorem lookup_bare_global_name_open_scope:
  ∀cx st n.
    lookup_bare_global_name cx (open_scope st) n =
    lookup_bare_global_name cx st n
Proof
  rpt gen_tac >>
  simp[lookup_bare_global_name_def, lookup_immutable_def,
       open_scope_def]
QED

(* lookup_bare_global_name through declare_name *)
Theorem lookup_bare_global_name_declare_name:
  ∀cx st n1 n2 tv v.
    lookup_bare_global_name cx (declare_name st n2 tv v) n1 =
    lookup_bare_global_name cx st n1
Proof
  rpt gen_tac >>
  simp[lookup_bare_global_name_def, lookup_immutable_def,
       declare_name_def, LET_THM] >>
  Cases_on `st.scopes` >> simp[]
QED

(* lookup_bare_global_name after update_bare_global_name (same name) *)
Theorem lookup_bare_global_name_after_update:
  ∀cx st n tv v v'.
    lookup_bare_global_name cx st n = SOME (tv, v) ⇒
    lookup_bare_global_name cx (update_bare_global_name cx st n v') n = SOME (tv, v')
Proof
  rpt strip_tac >>
  simp[update_bare_global_name_def] >>
  gvs[lookup_bare_global_name_def, lookup_immutable_def] >>
  simp[set_immutable_def, get_address_immutables_def, lift_option_def,
       set_address_immutables_def, bind_def, return_def] >>
  gvs[AllCaseEqs()] >>
  simp[return_def, set_source_immutables_def,
       get_source_immutables_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

(* lookup_bare_global_name through update_toplevel_name:
   update_toplevel_name modifies storage/transient, not immutables *)
Theorem lookup_bare_global_name_update_toplevel_name:
  ∀cx st mid id n v.
    lookup_bare_global_name cx (update_toplevel_name cx st mid id v) n =
    lookup_bare_global_name cx st n
Proof
  rpt gen_tac >>
  simp[lookup_bare_global_name_def, lookup_immutable_def,
       update_toplevel_name_def] >>
  Cases_on `set_global cx mid (string_to_num id) v st` >>
  `r.immutables = st.immutables` by
    (irule set_global_immutables >> metis_tac[]) >>
  simp[]
QED

(**********************************************************************)
(* Low-level lemmas about assign_target for ImmutableVar *)

Theorem assign_target_immutable_subscripts_state:
  ∀cx st n sbs ao tv a a'.
    lookup_bare_global_name cx st n = SOME (tv, a) ∧
    assign_subscripts tv a (REVERSE sbs) ao = INL a' ⇒
    SND (assign_target cx (BaseTargetV (ImmutableVar n) sbs) ao st) =
    update_bare_global_name cx st n a'
Proof
  rpt gen_tac >> strip_tac >>
  gvs[lookup_bare_global_name_def, lookup_immutable_def] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >> gvs[] >>
  simp[Once assign_target_def, LET_THM, bind_def,
       get_immutables_def, get_address_immutables_def,
       lift_option_def, return_def, lift_option_type_def, lift_sum_def] >>
  simp[set_immutable_def, bind_def, get_address_immutables_def,
       lift_option_def, return_def, set_address_immutables_def,
       ignore_bind_def, LET_THM] >>
  simp[update_bare_global_name_def, lookup_bare_global_name_def,
       lookup_immutable_def, set_immutable_def, bind_def,
       get_address_immutables_def, lift_option_def, return_def,
       set_address_immutables_def, LET_THM] >>
  Cases_on `ao` >>
  simp[assign_result_def, return_def, bind_def, lift_sum_def] >>
  rpt (CASE_TAC >> gvs[return_def, raise_def])
QED

Theorem assign_target_immutable_subscripts_valid:
  ∀cx st n sbs ao tv a a'.
    lookup_bare_global_name cx st n = SOME (tv, a) ∧
    assign_subscripts tv a (REVERSE sbs) ao = INL a' ⇒
    ISL (FST (assign_target cx (BaseTargetV (ImmutableVar n) sbs) ao st))
Proof
  rpt gen_tac >> strip_tac >>
  gvs[lookup_bare_global_name_def, lookup_immutable_def] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >> gvs[] >>
  simp[Once assign_target_def, LET_THM, bind_def,
       get_immutables_def, get_address_immutables_def,
       lift_option_def, return_def, lift_option_type_def, lift_sum_def] >>
  simp[set_immutable_def, bind_def, get_address_immutables_def,
       lift_option_def, return_def, set_address_immutables_def,
       ignore_bind_def, LET_THM] >>
  Cases_on `ao` >>
  simp[assign_result_def, return_def, bind_def, lift_sum_def] >>
  drule assign_subscripts_PopOp_assign_result >> strip_tac >>
  gvs[return_def, raise_def] >>
  Cases_on `popped_value v` >> gvs[return_def]
QED

(**********************************************************************)
(* valid_target / update_target lemmas for ImmutableVar *)

Theorem valid_target_immutable_subscripts:
  ∀cx st n sbs ao tv a a'.
    lookup_bare_global_name cx st n = SOME (tv, a) ∧
    assign_subscripts tv a (REVERSE sbs) ao = INL a' ⇒
    valid_target cx st (BaseTargetV (ImmutableVar n) sbs) ao
Proof
  metis_tac[valid_target_def, assign_target_immutable_subscripts_valid]
QED

Theorem update_target_immutable_subscripts:
  ∀cx st n sbs ao tv a a'.
    lookup_bare_global_name cx st n = SOME (tv, a) ∧
    assign_subscripts tv a (REVERSE sbs) ao = INL a' ⇒
    update_target cx st (BaseTargetV (ImmutableVar n) sbs) ao =
    update_bare_global_name cx st n a'
Proof
  metis_tac[update_target_def, assign_target_immutable_subscripts_state]
QED
