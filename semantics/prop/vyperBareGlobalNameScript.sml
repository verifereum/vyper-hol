Theory vyperBareGlobalName

Ancestors
  vyperPlaceFrames finite_map alist
  vyperLookup vyperState vyperScopePreservation
  vyperLookupStorage vyperImmutablesPreservation vyperMisc

Definition lookup_immutable_def:
  lookup_immutable cx (st:evaluation_state) mid n =
  case ALOOKUP st.immutables cx.txn.target of
  | SOME imms => FLOOKUP (get_source_immutables mid imms) n
  | NONE => NONE
End

Definition lookup_bare_global_name_def:
  lookup_bare_global_name cx st n = lookup_immutable cx st (current_module cx) n
End

Definition is_immutable_def:
  is_immutable cx n =
    case get_module_code cx (current_module cx) of
      NONE => F
    | SOME ts => is_immutable_decl n ts
End

Definition update_bare_global_name_def:
  update_bare_global_name cx st n v =
    case lookup_bare_global_name cx st n of
    | NONE => st
    | SOME (tv, _) =>
      SND (set_immutable cx (current_module cx) n tv v st)
End

(********************************************************)
(*                  Main theorems                       *)
(********************************************************)

Theorem immutables_preserved_after_update:
  ∀st n v. (update_name st n v).immutables = st.immutables
Proof
  rw[update_name_def, LET_THM] >>
  Cases_on `find_containing_scope n st.scopes` >-
   (Cases_on `st.scopes` >> simp[evaluation_state_accfupds]) >>
  PairCases_on `x` >> simp[evaluation_state_accfupds]
QED

Theorem lookup_immutable_after_set_immutable:
  ∀cx n tv v st st'.
    set_immutable cx (current_module cx) n tv v st = (INL (), st') ⇒
    lookup_immutable cx st' (current_module cx) n = SOME (tv, v)
Proof
  rw[set_immutable_def, lookup_immutable_def,
     bind_def, LET_THM, get_address_immutables_def,
     set_address_immutables_def, lift_option_type_def, lift_option_def] >>
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
  Cases_on `set_immutable cx (current_module cx) n x0 v st` >>
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

(* lookup_bare_global_name after update_bare_global_name (different name) *)
Theorem lookup_bare_global_name_update_bare_global_name_neq:
  ∀cx st n1 n2 v.
    n1 ≠ n2 ⇒
    lookup_bare_global_name cx (update_bare_global_name cx st n2 v) n1 =
    lookup_bare_global_name cx st n1
Proof
  rpt strip_tac >>
  simp[update_bare_global_name_def] >>
  Cases_on `lookup_bare_global_name cx st n2` >> simp[] >>
  PairCases_on `x` >> simp[] >>
  gvs[lookup_bare_global_name_def, lookup_immutable_def] >>
  simp[set_immutable_def, get_address_immutables_def, lift_option_type_def,
       lift_option_def, set_address_immutables_def, bind_def, return_def] >>
  gvs[AllCaseEqs()] >>
  simp[return_def, get_source_immutables_def, set_source_immutables_def,
       alistTheory.ALOOKUP_ADELKEY,
       finite_mapTheory.FLOOKUP_UPDATE]
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
  simp[set_immutable_def, get_address_immutables_def, lift_option_type_def,
       lift_option_def, set_address_immutables_def, bind_def, return_def] >>
  gvs[AllCaseEqs()] >>
  simp[return_def, set_source_immutables_def,
       get_source_immutables_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

(* lookup_bare_global_name after update_bare_global_name (same name, unconditional) *)
Theorem lookup_bare_global_name_update_bare_global_name:
  ∀cx st n v'.
    lookup_bare_global_name cx (update_bare_global_name cx st n v') n =
    case lookup_bare_global_name cx st n of
      SOME (tv, _) => SOME (tv, v')
    | NONE => NONE
Proof
  rpt gen_tac >>
  Cases_on `lookup_bare_global_name cx st n` >-
    simp[update_bare_global_name_def] >>
  PairCases_on `x` >>
  simp[lookup_bare_global_name_after_update]
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
  Cases_on `set_global cx mid id v st` >>
  `r.immutables = st.immutables` by
    (irule set_global_immutables >> metis_tac[]) >>
  simp[]
QED

Theorem lookup_immutable_set_other:
  (src',name') <> (src,name) /\
  set_immutable cx src' name' tv v es = (r,es') ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  simp[set_immutable_def, get_address_immutables_def,
       set_address_immutables_def, bind_def, lift_option_type_def,
       return_def, raise_def] >>
  Cases_on `ALOOKUP es.immutables cx.txn.target` >>
  simp[return_def, raise_def] >>
  rpt strip_tac >> gvs[lookup_immutable_def] >>
  Cases_on `src' = src` >>
  gvs[set_source_immutables_def, get_source_immutables_def, FLOOKUP_UPDATE,
      ALOOKUP_ADELKEY]
QED

Theorem lookup_global_immutable_root:
  lookup_global cx src id es =
    (INL (PlaceR (ImmutablePlace other_src other_id path)),es') ==>
  other_src = src /\ other_id = id /\ path = []
Proof
  simp[lookup_global_def, vyperMiscTheory.option_CASE_rator,
       vyperMiscTheory.prod_CASE_rator, var_decl_info_CASE_rator,
       bind_def, lift_option_type_def, return_def, raise_def,
       get_immutables_def, get_address_immutables_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[AllCaseEqs(), bind_def, ignore_bind_def, record_storage_event_def, return_def, raise_def]
QED

Theorem lookup_immutable_write_other:
  write_place cx p v es = (r,es') /\
  (!src' name' path. p = ImmutablePlace src' name' path ==>
                      (src',name') <> (src,name)) ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  Cases_on `p`
  >- (strip_tac >> drule write_storage_place_immutables >>
      simp[lookup_immutable_def])
  >- (strip_tac >> drule write_memory_place_immutables >>
      simp[lookup_immutable_def]) >>
  rename1 `write_place cx (ImmutablePlace other_src other_name path)` >>
  Cases_on `ALOOKUP es.immutables cx.txn.target` >>
  simp[write_place_def, bind_def, get_immutables_def,
       get_address_immutables_def, lift_option_type_def, lift_sum_def,
       return_def, raise_def] >>
  rename1 `ALOOKUP es.immutables cx.txn.target = SOME imms` >>
  Cases_on `FLOOKUP (get_source_immutables other_src imms) other_name` >>
  simp[return_def, raise_def] >>
  rename1 `FLOOKUP _ _ = SOME tva` >>
  Cases_on `assign_subscripts (FST tva) (SND tva) path (Replace v)` >>
  simp[return_def, raise_def] >>
  rpt strip_tac >> irule lookup_immutable_set_other >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem pop_place_immutable_other:
  (!other_src other_name path. p = ImmutablePlace other_src other_name path ==>
     (other_src,other_name) <> (src,name)) /\
  pop_place cx p es = (res,es') ==>
  lookup_immutable cx es' src name = lookup_immutable cx es src name
Proof
  Cases_on `p` >> strip_tac
  >- (drule vyperScopePreservationTheory.pop_storage_place_scopes_immutables >>
      simp[lookup_immutable_def])
  >- (rename1 `MemoryPlace id path` >>
      Cases_on `find_containing_scope id es.scopes` >>
      gvs[pop_place_def, bind_def, get_scopes_def, lift_option_type_def,
          return_def, raise_def] >>
      PairCases_on `x` >>
      gvs[bind_def, ignore_bind_def, lift_sum_def, type_check_def, assert_def,
          check_def, set_scopes_def, return_def, raise_def, AllCaseEqs()] >>
      fs[GSYM lift_sum_def, GSYM lift_option_type_def] >>
      imp_res_tac vyperStatePreservationTheory.lift_sum_state >>
      imp_res_tac vyperStatePreservationTheory.lift_option_type_state >>
      gvs[lookup_immutable_def] >>
      pairarg_tac >>
      gvs[bind_def, ignore_bind_def, set_scopes_def, return_def,
          lookup_immutable_def]) >>
  gvs[pop_place_def, bind_def, ignore_bind_def, get_immutables_def,
      get_address_immutables_def, lift_option_type_def, lift_sum_def,
      return_def, raise_def, AllCaseEqs()] >>
  gvs[vyperMiscTheory.option_CASE_rator, vyperMiscTheory.sum_CASE_rator,
      return_def, raise_def, AllCaseEqs()] >>
  irule lookup_immutable_set_other >> goal_assum (drule_at Any) >> simp[]
QED
