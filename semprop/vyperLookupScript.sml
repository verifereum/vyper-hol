Theory vyperLookup

Ancestors
  vyperInterpreter vyperTypeValue

Definition lookup_scoped_var_def:
  lookup_scoped_var st n = lookup_scopes (string_to_num n) st.scopes
End

Definition var_in_scope_def:
  var_in_scope st n ⇔ IS_SOME (lookup_scoped_var st n)
End

Definition lookup_immutable_def:
  lookup_immutable cx (st:evaluation_state) n =
  case ALOOKUP st.globals cx.txn.target of
  | SOME gbs => FLOOKUP (get_module_globals NONE gbs).immutables (string_to_num n)
  | NONE => NONE
End

(* For convenience, we define the case st.scopes = [] in such a way
   that looking up after update returns the updated variable value. *)
Definition update_scoped_var_def:
  update_scoped_var st id v =
    let n = string_to_num id in
    case find_containing_scope n st.scopes of
    | SOME (pre, env, _, rest) =>
        st with scopes := (pre ++ (env |+ (n, v))::rest)
    | NONE =>
        case st.scopes of
        | [] => st with scopes := [FEMPTY |+ (n, v)]
        | h :: t => st with scopes := (h |+ (n, v)) :: t
End

Definition valid_lookups_def:
  valid_lookups cx st ⇔
    ∃gbs. ALOOKUP st.globals cx.txn.target = SOME gbs ∧
          ∀n. var_in_scope st n ⇒ FLOOKUP (get_module_globals NONE gbs).immutables (string_to_num n) = NONE
End

Definition lookup_name_def:
  lookup_name cx st n =
    case eval_expr cx (Name n) st of
    | (INL (Value v), _) => SOME v
    | (_, _) => NONE
End

Definition lookup_base_target_def:
  lookup_base_target cx st tgt =
    case eval_base_target cx tgt st of
    | (INL (loc, sbs), _) => SOME (BaseTargetV loc sbs)
    | (INR _, _) => NONE
End

Definition lookup_name_target_def:
  lookup_name_target cx st n = lookup_base_target cx st (NameTarget n)
End

Definition lookup_toplevel_name_target_def:
  lookup_toplevel_name_target cx st n = lookup_base_target cx st (TopLevelNameTarget n)
End

(****************************************)
(* Helpers *)

Theorem lookup_scopes_to_lookup_name[local]:
  ∀cx st n v gbs.
    lookup_scopes (string_to_num n) st.scopes = SOME v ∧
    ALOOKUP st.globals cx.txn.target = SOME gbs ∧
    FLOOKUP (get_module_globals NONE gbs).immutables (string_to_num n) = NONE ⇒
    lookup_name cx st n = SOME v
Proof
  rpt strip_tac >>
  simp[lookup_name_def, Once evaluate_def, bind_def, get_scopes_def, return_def,
       get_immutables_def, get_immutables_module_def, get_current_globals_def,
       lift_option_def, exactly_one_option_def, lift_sum_def]
QED

Theorem lookup_scopes_find_containing:
  ∀id sc. IS_SOME (lookup_scopes id sc) ⇒ IS_SOME (find_containing_scope id sc)
Proof
  Induct_on `sc` >- rw[lookup_scopes_def] >>
  rpt strip_tac >>
  simp[lookup_scopes_def, find_containing_scope_def] >>
  Cases_on `FLOOKUP h id` >-
   (simp[] >>
    first_x_assum (qspec_then `id` mp_tac) >>
    impl_tac >- fs[lookup_scopes_def] >>
    strip_tac >> Cases_on `find_containing_scope id sc` >> gvs[]) >>
  simp[]
QED

Theorem find_containing_scope_pre_none:
  ∀id sc pre env v rest.
    find_containing_scope id sc = SOME (pre,env,v,rest) ⇒
    lookup_scopes id pre = NONE
Proof
  Induct_on `sc` >- rw[find_containing_scope_def] >>
  simp[find_containing_scope_def] >>
  rpt gen_tac >> Cases_on `FLOOKUP h id` >> gvs[] >-
   (strip_tac >> PairCases_on `z` >> gvs[] >> simp[lookup_scopes_def]) >>
  simp[lookup_scopes_def]
QED

Theorem lookup_scopes_update:
  ∀id pre env v rest.
    lookup_scopes id pre = NONE ⇒
    lookup_scopes id (pre ++ env |+ (id,v) :: rest) = SOME v
Proof
  Induct_on `pre` >-
   simp[lookup_scopes_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[lookup_scopes_def, AllCaseEqs()]
QED

Theorem find_containing_scope_structure:
  ∀id sc pre env v rest.
    find_containing_scope id sc = SOME (pre, env, v, rest) ⇒
    sc = pre ++ env :: rest ∧ FLOOKUP env id = SOME v
Proof
  Induct_on `sc` >- rw[find_containing_scope_def] >>
  rpt gen_tac >> strip_tac >> qpat_x_assum `_ = SOME _` mp_tac >>
  simp[find_containing_scope_def] >>
  Cases_on `FLOOKUP h id` >> simp[] >-
  (strip_tac >> PairCases_on `z` >> gvs[] >> first_x_assum drule >> simp[]) >>
  strip_tac >> gvs[]
QED

Theorem find_containing_scope_lookup:
  ∀id sc pre env v rest.
    find_containing_scope id sc = SOME (pre, env, v, rest) ⇒
    lookup_scopes id sc = SOME v
Proof
  Induct_on `sc` >- rw[find_containing_scope_def] >>
  rw[find_containing_scope_def, lookup_scopes_def] >>
  Cases_on `FLOOKUP h id` >> gvs[] >>
  PairCases_on `z` >> gvs[]
QED

Theorem find_containing_scope_lookup_scopes:
  ∀id sc. IS_SOME (find_containing_scope id sc) ⇒ IS_SOME (lookup_scopes id sc)
Proof
  rpt strip_tac >>
  Cases_on `find_containing_scope id sc` >> gvs[] >>
  PairCases_on `x` >> drule find_containing_scope_lookup >> simp[]
QED

Theorem lookup_scopes_update_preserves[local]:
  ∀n pre env id v rest.
    FLOOKUP env id = SOME w ⇒
    (IS_SOME (lookup_scopes n (pre ++ [env] ++ rest)) ⇔
     IS_SOME (lookup_scopes n (pre ++ env |+ (id, v) :: rest)))
Proof
  Induct_on `pre` >-
  (rw[lookup_scopes_def] >>
   simp[finite_mapTheory.FLOOKUP_UPDATE] >>
   Cases_on `id = n` >> gvs[] >>
   Cases_on `FLOOKUP env n` >> gvs[]) >>
  rw[lookup_scopes_def] >>
  Cases_on `FLOOKUP h n` >> gvs[]
QED

Theorem lookup_scopes_dom_iff:
  ∀id sc1 sc2.
    MAP FDOM sc1 = MAP FDOM sc2 ⇒
    (IS_SOME (lookup_scopes id sc1) ⇔ IS_SOME (lookup_scopes id sc2))
Proof
  Induct_on `sc1` >>
  simp[lookup_scopes_def] >>
  Cases_on `sc2` >>
  simp[lookup_scopes_def] >>
  rpt strip_tac >>
  Cases_on `FLOOKUP h' id` >>
  Cases_on `FLOOKUP h id` >>
  gvs[finite_mapTheory.flookup_thm]
QED

(****************************************)
(* Theorems *)

Theorem var_in_scope_implies_name_target:
  ∀cx (st:evaluation_state) n.
    (cx.txn.is_creation ⇒ valid_lookups cx st) ∧
    var_in_scope st n ⇒
    lookup_name_target cx st n = SOME (BaseTargetV (ScopedVar n) [])
Proof
  rw[var_in_scope_def, valid_lookups_def, lookup_scoped_var_def, lookup_name_target_def, lookup_base_target_def] >>
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def] >>
  `IS_SOME (lookup_scopes (string_to_num n) st.scopes)`
    by metis_tac[find_containing_scope_lookup_scopes] >>
  simp[] >>
  Cases_on `cx.txn.is_creation` >-
    gvs[get_immutables_def, get_immutables_module_def,
        get_current_globals_def, bind_def, lift_option_def, return_def,
        lift_sum_def, exactly_one_option_def, immutable_target_def, raise_def] >>
  simp[return_def, lift_sum_def, exactly_one_option_def]
QED

Theorem lookup_name_target_implies_var_in_scope:
  ∀cx st n.
    lookup_name_target cx st n = SOME (BaseTargetV (ScopedVar n) []) ⇒
    var_in_scope st n
Proof
  rw[var_in_scope_def, lookup_scoped_var_def, lookup_name_target_def, lookup_base_target_def] >>
  pop_assum mp_tac >>
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def] >>
  Cases_on `IS_SOME (lookup_scopes (string_to_num n) st.scopes)` >- simp[] >>
  fs[] >>
  Cases_on `cx.txn.is_creation` >-
   (simp[get_immutables_def, get_immutables_module_def,
         get_current_globals_def, bind_def, lift_option_def,
         return_def, raise_def] >>
    Cases_on `ALOOKUP st.globals cx.txn.target` >>
    simp[return_def, immutable_target_def] >>
    Cases_on `FLOOKUP (get_module_globals NONE x).immutables (string_to_num n)` >>
    simp[exactly_one_option_def, lift_sum_def, return_def, raise_def]) >>
  simp[return_def, exactly_one_option_def, lift_sum_def, raise_def]
QED

Theorem lookup_scoped_var_implies_lookup_name:
  ∀cx st n v.
    valid_lookups cx st ∧
    lookup_scoped_var st n = SOME v ⇒
    lookup_name cx st n = SOME v
Proof
  simp[valid_lookups_def, lookup_scoped_var_def, var_in_scope_def] >>
  rpt strip_tac >>
  gvs[lookup_scopes_to_lookup_name, lookup_scopes_find_containing]
QED

Theorem var_in_scope_dom_iff:
  ∀st1 st2 n.
    MAP FDOM st1.scopes = MAP FDOM st2.scopes ⇒
    (var_in_scope st1 n ⇔ var_in_scope st2 n)
Proof
  fs[var_in_scope_def, lookup_scoped_var_def] >>
  gvs[lookup_scopes_dom_iff]
QED

Theorem var_not_in_scope_update:
  ∀st n v.
    st.scopes ≠ [] ∧ ¬ var_in_scope st n ⇒
    update_scoped_var st n v = (st with scopes := (HD st.scopes |+ (string_to_num n, v)) :: TL st.scopes)
Proof
  rw[var_in_scope_def, lookup_scoped_var_def, update_scoped_var_def] >>
  Cases_on `find_containing_scope (string_to_num n) st.scopes` >-
   (Cases_on `st.scopes` >> gvs[]) >>
  PairCases_on `x` >> drule find_containing_scope_lookup >> simp[]
QED

Theorem assign_target_scoped_var_replace:
  ∀cx st n v.
    var_in_scope st n ⇒
    ∃old_v.
      assign_target cx (BaseTargetV (ScopedVar n) []) (Replace v) st =
      (INL (Value old_v), update_scoped_var st n v)
Proof
  rw[var_in_scope_def, lookup_scoped_var_def] >>
  `IS_SOME (find_containing_scope (string_to_num n) st.scopes)`
    by metis_tac[lookup_scopes_find_containing] >>
  Cases_on `find_containing_scope (string_to_num n) st.scopes` >- gvs[] >>
  PairCases_on `x` >> gvs[] >>
  simp[Once assign_target_def, bind_def, get_scopes_def, return_def,
       lift_option_def, lift_sum_def, assign_subscripts_def,
       ignore_bind_def, set_scopes_def, update_scoped_var_def, LET_THM]
QED

Theorem assign_target_scoped_var_update:
  ∀cx st n bop v v'.
    lookup_scoped_var st n = SOME v ∧
    evaluate_binop bop v v' = INL new_v ⇒
    assign_target cx (BaseTargetV (ScopedVar n) []) (Update bop v') st =
    (INL (Value v), update_scoped_var st n new_v)
Proof
  rw[lookup_scoped_var_def] >>
  `IS_SOME (find_containing_scope (string_to_num n) st.scopes)`
    by (irule lookup_scopes_find_containing >> simp[]) >>
  Cases_on `find_containing_scope (string_to_num n) st.scopes` >- gvs[] >>
  PairCases_on `x` >> gvs[] >>
  `x2 = v` by (drule find_containing_scope_lookup >> simp[]) >> gvs[] >>
  simp[Once assign_target_def, bind_def, get_scopes_def, return_def,
       lift_option_def, lift_sum_def, assign_subscripts_def,
       ignore_bind_def, set_scopes_def, update_scoped_var_def, LET_THM]
QED

Theorem lookup_name_none_to_lookup_scoped_var:
  ∀cx st n.
    valid_lookups cx st ∧ lookup_name cx st n = NONE ⇒
    lookup_scoped_var st n = NONE
Proof
  rw[valid_lookups_def, lookup_name_def, lookup_scoped_var_def,
     var_in_scope_def] >>
  CCONTR_TAC >> gvs[] >>
  first_x_assum (qspec_then `n` mp_tac) >>
  Cases_on `lookup_scopes (string_to_num n) st.scopes` >> gvs[] >>
  qpat_x_assum `_ = NONE` mp_tac >>
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
       get_immutables_def, get_immutables_module_def, get_current_globals_def,
       lift_option_def] >>
  Cases_on `FLOOKUP (get_module_globals NONE gbs).immutables (string_to_num n)` >>
  simp[exactly_one_option_def, lift_sum_def, return_def, raise_def]
QED

Theorem lookup_name_none_to_lookup_immutable:
  ∀cx st n.
    valid_lookups cx st ∧ lookup_name cx st n = NONE ⇒
    lookup_immutable cx st n = NONE
Proof
  rw[valid_lookups_def, lookup_name_def, lookup_immutable_def,
     var_in_scope_def, lookup_scoped_var_def] >> gvs[] >>
  Cases_on `FLOOKUP (get_module_globals NONE gbs).immutables (string_to_num n)` >>
  simp[] >>
  Cases_on `lookup_scopes (string_to_num n) st.scopes` >-
   gvs[Once evaluate_def, bind_def, get_scopes_def, return_def,
       get_immutables_def, get_immutables_module_def, get_current_globals_def,
       lift_option_def, exactly_one_option_def, lift_sum_def, return_def] >>
  first_x_assum (qspec_then `n` mp_tac) >> simp[]
QED

Theorem lookup_after_update:
  ∀st n v. lookup_scoped_var (update_scoped_var st n v) n = SOME v
Proof
  rw[lookup_scoped_var_def, update_scoped_var_def, LET_THM] >>
  Cases_on `find_containing_scope (string_to_num n) st.scopes` >-
   (Cases_on `st.scopes` >> gvs[] >>
    simp[evaluation_state_accfupds, lookup_scopes_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  PairCases_on `x` >> simp[evaluation_state_accfupds] >>
  drule find_containing_scope_pre_none >> strip_tac >>
  drule lookup_scopes_update >> simp[]
QED

Theorem lookup_scopes_update_other[local]:
  ∀pre n1 n2 env v rest.
    n1 ≠ n2 ⇒
    lookup_scopes n2 (pre ⧺ env |+ (n1, v) :: rest) =
    lookup_scopes n2 (pre ⧺ env :: rest)
Proof
  Induct_on `pre` >-
   simp[lookup_scopes_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[lookup_scopes_def] >> rpt strip_tac >>
  Cases_on `FLOOKUP h n2` >> simp[]
QED

Theorem lookup_scoped_var_preserved_after_update:
  ∀st n1 n2 v.
    n1 ≠ n2 ⇒
    lookup_scoped_var (update_scoped_var st n1 v) n2 = lookup_scoped_var st n2
Proof
  rw[lookup_scoped_var_def, update_scoped_var_def, LET_THM] >>
  `string_to_num n1 ≠ string_to_num n2` by metis_tac[vyperMiscTheory.string_to_num_inj] >>
  Cases_on `find_containing_scope (string_to_num n1) st.scopes` >-
   (* Case: n1 not in scope, adds to HD *)
   (simp[evaluation_state_accfupds, lookup_scopes_def, finite_mapTheory.FLOOKUP_UPDATE] >>
    Cases_on `st.scopes` >> gvs[lookup_scopes_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  (* Case: n1 in scope, updates in place *)
  PairCases_on `x` >> simp[evaluation_state_accfupds] >>
  drule find_containing_scope_structure >> strip_tac >> gvs[] >>
  simp[lookup_scopes_update_other] >>
  AP_TERM_TAC >> simp[]
QED

Theorem globals_preserved_after_update:
  ∀st n v. (update_scoped_var st n v).globals = st.globals
Proof
  rw[update_scoped_var_def, LET_THM] >>
  Cases_on `find_containing_scope (string_to_num n) st.scopes` >-
   (Cases_on `st.scopes` >> simp[evaluation_state_accfupds]) >>
  PairCases_on `x` >> simp[evaluation_state_accfupds]
QED

Theorem lookup_name_preserved_after_update:
  ∀cx st n1 n2 v.
    n1 ≠ n2 ⇒
    lookup_name cx (update_scoped_var st n1 v) n2 = lookup_name cx st n2
Proof
  rpt strip_tac >>
  simp[lookup_name_def] >>
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
       get_immutables_def, get_immutables_module_def, get_current_globals_def,
       lift_option_def, lift_sum_def,
       globals_preserved_after_update,
       lookup_scoped_var_preserved_after_update, GSYM lookup_scoped_var_def] >>
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
       get_immutables_def, get_immutables_module_def, get_current_globals_def,
       lift_option_def, lift_sum_def,
       GSYM lookup_scoped_var_def] >>
  Cases_on `ALOOKUP st.globals cx.txn.target` >> simp[raise_def, return_def] >>
  Cases_on `exactly_one_option (lookup_scoped_var st n2)
              (FLOOKUP (get_module_globals NONE x).immutables (string_to_num n2))` >>
  simp[return_def, raise_def]
QED

Theorem valid_lookups_preserved_after_update:
  ∀cx st n v.
    valid_lookups cx st ∧ lookup_name cx st n = NONE ⇒
    valid_lookups cx (update_scoped_var st n v)
Proof
  rw[valid_lookups_def] >>
  qexists_tac `gbs` >>
  simp[globals_preserved_after_update] >>
  rpt strip_tac >>
  Cases_on `string_to_num n' = string_to_num n` >-
   ((* n' = n: use lookup_name_none_to_lookup_immutable *)
    `lookup_immutable cx st n = NONE`
      by (irule lookup_name_none_to_lookup_immutable >>
          simp[valid_lookups_def] >> metis_tac[]) >>
    gvs[lookup_immutable_def]) >>
  (* n' ≠ n: n' was already in scope before update, use valid_lookups *)
  `lookup_scoped_var st n = NONE`
    by (irule lookup_name_none_to_lookup_scoped_var >>
        simp[valid_lookups_def] >> metis_tac[]) >>
  `n ≠ n'` by metis_tac[vyperMiscTheory.string_to_num_inj] >>
  `lookup_scoped_var (update_scoped_var st n v) n' = lookup_scoped_var st n'`
    by (irule lookup_scoped_var_preserved_after_update >> simp[]) >>
  `var_in_scope st n'` by gvs[var_in_scope_def, lookup_scoped_var_def] >>
  first_x_assum irule >> simp[]
QED

Theorem scopes_nonempty_after_update:
  ∀st n v. (update_scoped_var st n v).scopes ≠ []
Proof
  rw[update_scoped_var_def, LET_THM] >>
  Cases_on `find_containing_scope (string_to_num n) st.scopes` >-
   (Cases_on `st.scopes` >> gvs[evaluation_state_accfupds]) >>
  PairCases_on `x` >> simp[evaluation_state_accfupds] >>
  Cases_on `x0` >> simp[]
QED
