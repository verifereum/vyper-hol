Theory vyperLookup
Ancestors
  vyperMisc vyperContext vyperState vyperInterpreter vyperValue vyperValueOperation

Definition lookup_scoped_var_def:
  lookup_scoped_var st n = lookup_scopes (string_to_num n) st.scopes
End

Definition var_in_scope_def:
  var_in_scope st n ⇔ IS_SOME (lookup_scoped_var st n)
End

Definition lookup_in_current_scope_def:
  lookup_in_current_scope st n = FLOOKUP (HD st.scopes) (string_to_num n)
End

Definition tl_scopes_def:
  tl_scopes st = st with scopes := TL st.scopes
End

Definition lookup_immutable_def:
  lookup_immutable cx (st:evaluation_state) n =
  case ALOOKUP st.immutables cx.txn.target of
  | SOME imms => FLOOKUP (get_source_immutables (current_module cx) imms) (string_to_num n)
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
    ∃imms. ALOOKUP st.immutables cx.txn.target = SOME imms ∧
           ∀n. var_in_scope st n ⇒ FLOOKUP (get_source_immutables (current_module cx) imms) (string_to_num n) = NONE
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

(* ScopedVar or ImmutableVar *)
Definition lookup_name_target_def:
  lookup_name_target cx st n = lookup_base_target cx st (NameTarget n)
End

(* TopLevelVar *)
Definition lookup_toplevel_name_target_def:
  lookup_toplevel_name_target cx st n = lookup_base_target cx st (TopLevelNameTarget n)
End

Definition lookup_flag_member_def:
  lookup_flag_member cx (src_id_opt, fid) mid =
  case get_module_code cx src_id_opt
    of NONE => NONE
     | SOME ts =>
  case lookup_flag fid ts
    of NONE => NONE
     | SOME ls =>
  case INDEX_OF mid ls
    of NONE => NONE
     | SOME i => SOME $ Value $ FlagV (LENGTH ls) (2 ** i)
End

(****************************************)
(* Helpers *)

Theorem lookup_scopes_to_lookup_name[local]:
  ∀cx st n v imms.
    lookup_scopes (string_to_num n) st.scopes = SOME v ∧
    ALOOKUP st.immutables cx.txn.target = SOME imms ∧
    FLOOKUP (get_source_immutables (current_module cx) imms) (string_to_num n) = NONE ⇒
    lookup_name cx st n = SOME v
Proof
  rpt strip_tac >>
  simp[lookup_name_def, Once evaluate_def, bind_def, get_scopes_def, return_def,
       get_immutables_def, get_address_immutables_def,
       lift_option_def, lift_option_type_def, exactly_one_option_def, lift_sum_def]
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

Theorem lookup_scopes_FEMPTY_CONS[local]:
  ∀n rest. lookup_scopes n (FEMPTY::rest) = lookup_scopes n rest
Proof
  simp[Once lookup_scopes_def, finite_mapTheory.FLOOKUP_EMPTY]
QED

Theorem find_containing_scope_none_lookup_scopes_none:
  ∀id sc. find_containing_scope id sc = NONE ⇒ lookup_scopes id sc = NONE
Proof
  Induct_on `sc` >> simp[Once find_containing_scope_def, Once lookup_scopes_def] >>
  rpt strip_tac >> Cases_on `FLOOKUP h id` >> gvs[] >>
  first_x_assum irule >>
  Cases_on `find_containing_scope id sc` >> gvs[]
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

Theorem lookup_in_current_scope_push:
  lookup_in_current_scope
    (st with scopes updated_by CONS (FEMPTY |+ (string_to_num id, v))) id
  = SOME v
Proof
  simp[lookup_in_current_scope_def, evaluation_state_accfupds,
       finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem tl_scopes_push:
  tl_scopes (st with scopes updated_by CONS sc) = st
Proof
  simp[tl_scopes_def, evaluation_state_accfupds] >>
  Cases_on `st` >> simp[evaluation_state_fn_updates]
QED

Theorem pop_scope_tl_scopes:
  st.scopes ≠ [] ⇒ pop_scope st = (INL (), tl_scopes st)
Proof
  Cases_on `st.scopes` >> simp[pop_scope_def, tl_scopes_def, return_def]
QED

(****************************************)
(* Theorems *)

Theorem lookup_scoped_var_implies_var_in_scope:
  ∀st n v. lookup_scoped_var st n = SOME v ⇒ var_in_scope st n
Proof
  simp[var_in_scope_def]
QED

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
    gvs[get_immutables_def, get_address_immutables_def,
        bind_def, lift_option_def, lift_option_type_def, return_def,
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
  Cases_on `cx.txn.is_creation` >>
  simp[get_immutables_def, get_address_immutables_def,
       bind_def, lift_option_def, lift_option_type_def, return_def, raise_def,
       option_CASE_rator, sum_CASE_rator, prod_CASE_rator,
       get_module_code_def, check_def, ignore_bind_def, assert_def,
       lift_sum_def, exactly_one_option_def, immutable_target_def] >>
  rpt CASE_TAC >> gvs[exactly_one_option_def]
QED

Theorem lookup_scoped_var_implies_lookup_name:
  ∀cx st n v.
    valid_lookups cx st ∧
    lookup_scoped_var st n = SOME v ⇒
    lookup_name cx st n = SOME v
Proof
  simp[valid_lookups_def, lookup_scoped_var_def, var_in_scope_def] >>
  rpt strip_tac >>
  gvs[lookup_scopes_to_lookup_name]
QED

Theorem var_in_scope_implies_some_lookup_name:
  ∀cx st n.
    valid_lookups cx st ∧
    var_in_scope st n ⇒
    IS_SOME (lookup_name cx st n)
Proof
  rw[valid_lookups_def, lookup_scoped_var_def, var_in_scope_def] >>
  Cases_on `lookup_scopes (string_to_num n) st.scopes` >> gvs[] >>
  first_x_assum (qspec_then `n` mp_tac) >> simp[] >>
  strip_tac >> drule lookup_scopes_to_lookup_name >> simp[]
QED

Theorem lookup_immutable_implies_lookup_name:
  ∀cx st n v.
    valid_lookups cx st ∧
    lookup_immutable cx st n = SOME v ⇒
    lookup_name cx st n = SOME v
Proof
  rpt strip_tac >>
  fs[valid_lookups_def, lookup_immutable_def, lookup_name_def] >> gvs[] >>
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
       get_immutables_def, get_address_immutables_def,
       lift_option_def] >>
  `lookup_scopes (string_to_num n) st.scopes = NONE` suffices_by
    (strip_tac >> simp[exactly_one_option_def, lift_sum_def, return_def]) >>
  CCONTR_TAC >> gvs[] >>
  first_x_assum (qspec_then `n` mp_tac) >>
  simp[var_in_scope_def, lookup_scoped_var_def] >>
  Cases_on `lookup_scopes (string_to_num n) st.scopes` >> gvs[]
QED

Theorem lookup_name_to_lookup_scoped_var:
  ∀cx st n v.
    valid_lookups cx st ∧
    var_in_scope st n ∧
    lookup_name cx st n = SOME v ⇒
    lookup_scoped_var st n = SOME v
Proof
  rw[valid_lookups_def, var_in_scope_def, lookup_scoped_var_def, lookup_name_def] >>
  qpat_x_assum `_ = SOME v` mp_tac >>
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
       get_immutables_def, get_address_immutables_def, lift_option_def] >>
  `FLOOKUP (get_source_immutables (current_module cx) imms) (string_to_num n) = NONE` by simp[] >>
  Cases_on `lookup_scopes (string_to_num n) st.scopes` >> gvs[] >>
  simp[exactly_one_option_def, lift_sum_def, return_def]
QED

Theorem var_in_scope_dom_iff:
  ∀st1 st2 n.
    MAP FDOM st1.scopes = MAP FDOM st2.scopes ⇒
    (var_in_scope st1 n ⇔ var_in_scope st2 n)
Proof
  fs[var_in_scope_def, lookup_scoped_var_def] >>
  gvs[lookup_scopes_dom_iff]
QED

Theorem assign_target_scoped_var_replace:
  ∀cx st n v.
    var_in_scope st n ⇒
      assign_target cx (BaseTargetV (ScopedVar n) []) (Replace v) st =
      (INL NONE, update_scoped_var st n v)
Proof
  rw[var_in_scope_def, lookup_scoped_var_def] >>
  `IS_SOME (find_containing_scope (string_to_num n) st.scopes)`
    by metis_tac[lookup_scopes_find_containing] >>
  Cases_on `find_containing_scope (string_to_num n) st.scopes` >- gvs[] >>
  PairCases_on `x` >> gvs[] >>
  simp[Once assign_target_def, bind_def, get_scopes_def, return_def,
       lift_option_def, lift_option_type_def, lift_sum_def, assign_subscripts_def,
       ignore_bind_def, set_scopes_def, update_scoped_var_def, LET_THM,
       assign_result_def]
QED

Theorem assign_target_scoped_var_update:
  ∀cx st n bop v v'.
    lookup_scoped_var st n = SOME v ∧
    evaluate_binop bop v v' = INL new_v ⇒
    assign_target cx (BaseTargetV (ScopedVar n) []) (Update bop v') st =
    (INL NONE, update_scoped_var st n new_v)
Proof
  rw[lookup_scoped_var_def] >>
  `IS_SOME (find_containing_scope (string_to_num n) st.scopes)`
    by (irule lookup_scopes_find_containing >> simp[]) >>
  Cases_on `find_containing_scope (string_to_num n) st.scopes` >- gvs[] >>
  PairCases_on `x` >> gvs[] >>
  `x2 = v` by (drule find_containing_scope_lookup >> simp[]) >> gvs[] >>
  simp[Once assign_target_def, bind_def, get_scopes_def, return_def,
       lift_option_def, lift_option_type_def, lift_sum_def, assign_subscripts_def,
       ignore_bind_def, set_scopes_def, update_scoped_var_def, LET_THM,
       assign_result_def]
QED

Theorem assign_target_scoped_var_subscripts_state:
  ∀cx st n sbs ao a a'.
    lookup_scoped_var st n = SOME a ∧
    assign_subscripts a (REVERSE sbs) ao = INL a' ⇒
    SND (assign_target cx (BaseTargetV (ScopedVar n) sbs) ao st) =
      update_scoped_var st n a'
Proof
  rpt gen_tac >> strip_tac >>
  gvs[lookup_scoped_var_def] >>
  `IS_SOME (find_containing_scope (string_to_num n) st.scopes)`
    by (irule lookup_scopes_find_containing >> simp[]) >>
  Cases_on `find_containing_scope (string_to_num n) st.scopes` >- gvs[] >>
  PairCases_on `x` >> gvs[] >>
  `x2 = a` by (drule find_containing_scope_lookup >> simp[]) >> gvs[] >>
  simp[Once assign_target_def, bind_def, get_scopes_def, return_def,
       lift_option_def, lift_option_type_def, lift_sum_def, assign_result_def,
       ignore_bind_def, set_scopes_def, update_scoped_var_def, LET_THM] >>
  Cases_on `ao` >> simp[assign_result_def, return_def, bind_def, lift_sum_def] >>
  rpt (CASE_TAC >> gvs[return_def, raise_def])
QED

Theorem assign_subscripts_PopOp_assign_result:
  ∀a subs a'.
    assign_subscripts a subs PopOp = INL a' ⇒
    ∃v. evaluate_subscripts a subs = INL v ∧ ISL (popped_value v)
Proof
  Induct_on `subs`
  (* base case *)
  >- (rw[assign_subscripts_def, evaluate_subscripts_def] >>
      Cases_on `a` >> gvs[pop_element_def, popped_value_def] >>
      rename1 `ArrayV av` >> Cases_on `av` >> gvs[pop_element_def, popped_value_def])
  (* step case *)
  >> rpt gen_tac >>
  Cases_on `h` >> simp[assign_subscripts_def, evaluate_subscripts_def] >>
  rpt (CASE_TAC >> gvs[]) >>
  strip_tac >> res_tac >> gvs[] >>
  (* AttrSubscript: case split on the value being subscripted *)
  Cases_on `a` >>
  gvs[assign_subscripts_def, evaluate_subscripts_def] >>
  rpt (CASE_TAC >> gvs[]) >>
  qpat_x_assum `(case _ of INL _ => _ | INR _ => _) = _` mp_tac >>
  CASE_TAC >> gvs[] >> strip_tac >>
  res_tac >> gvs[]
QED

Theorem assign_target_scoped_var_subscripts_valid:
  ∀cx st n sbs ao a a'.
    lookup_scoped_var st n = SOME a ∧
    assign_subscripts a (REVERSE sbs) ao = INL a' ⇒
    ISL (FST (assign_target cx (BaseTargetV (ScopedVar n) sbs) ao st))
Proof
  rpt gen_tac >> strip_tac >>
  gvs[lookup_scoped_var_def] >>
  `IS_SOME (find_containing_scope (string_to_num n) st.scopes)`
    by (irule lookup_scopes_find_containing >> simp[]) >>
  Cases_on `find_containing_scope (string_to_num n) st.scopes` >- gvs[] >>
  PairCases_on `x` >> gvs[] >>
  `x2 = a` by (drule find_containing_scope_lookup >> simp[]) >> gvs[] >>
  simp[Once assign_target_def, bind_def, get_scopes_def, return_def,
       lift_option_def, lift_option_type_def, lift_sum_def,
       ignore_bind_def, set_scopes_def, update_scoped_var_def, LET_THM] >>
  Cases_on `ao` >> simp[assign_result_def, return_def, bind_def, lift_sum_def]
  >- (drule assign_subscripts_PopOp_assign_result >> strip_tac >>
      gvs[return_def, raise_def] >>
      Cases_on `popped_value v` >> gvs[return_def])
  >> rpt (CASE_TAC >> gvs[return_def, raise_def])
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
       get_immutables_def, get_address_immutables_def,
       lift_option_def] >>
  Cases_on `FLOOKUP (get_source_immutables (current_module cx) imms) (string_to_num n)` >>
  simp[exactly_one_option_def, lift_sum_def, return_def, raise_def]
QED

Theorem lookup_name_none_to_lookup_immutable:
  ∀cx st n.
    valid_lookups cx st ∧ lookup_name cx st n = NONE ⇒
    lookup_immutable cx st n = NONE
Proof
  rw[valid_lookups_def, lookup_name_def, lookup_immutable_def,
     var_in_scope_def, lookup_scoped_var_def] >> gvs[] >>
  Cases_on `FLOOKUP (get_source_immutables (current_module cx) imms) (string_to_num n)` >>
  simp[] >>
  Cases_on `lookup_scopes (string_to_num n) st.scopes` >-
   gvs[Once evaluate_def, bind_def, get_scopes_def, return_def,
       get_immutables_def, get_address_immutables_def,
       lift_option_def, lift_option_type_def, exactly_one_option_def, lift_sum_def, return_def] >>
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

Theorem var_in_scope_after_update:
  ∀st n v. var_in_scope (update_scoped_var st n v) n
Proof
  simp[var_in_scope_def, lookup_after_update]
QED

Theorem var_in_scope_preserved_after_update:
  ∀st n1 n2 v. var_in_scope st n2 ⇒ var_in_scope (update_scoped_var st n1 v) n2
Proof
  rpt strip_tac >>
  Cases_on ‘n1 = n2’ >>
  fs[var_in_scope_def, lookup_scoped_var_preserved_after_update] >-
   simp[lookup_after_update]
QED

Theorem immutables_preserved_after_update:
  ∀st n v. (update_scoped_var st n v).immutables = st.immutables
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
       get_immutables_def, get_address_immutables_def,
       lift_option_def, lift_option_type_def, lift_sum_def,
       immutables_preserved_after_update,
       lookup_scoped_var_preserved_after_update, GSYM lookup_scoped_var_def] >>
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
       get_immutables_def, get_address_immutables_def,
       lift_option_def, lift_option_type_def, lift_sum_def,
       GSYM lookup_scoped_var_def] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >> simp[raise_def, return_def] >>
  Cases_on `exactly_one_option (lookup_scoped_var st n2)
              (FLOOKUP (get_source_immutables (current_module cx) x) (string_to_num n2))` >>
  simp[return_def, raise_def]
QED

Theorem valid_lookups_preserved_after_update_no_name:
  ∀cx st n v.
    valid_lookups cx st ∧ lookup_name cx st n = NONE ⇒
    valid_lookups cx (update_scoped_var st n v)
Proof
  rw[valid_lookups_def] >>
  qexists_tac `imms` >>
  simp[immutables_preserved_after_update] >>
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

Theorem valid_lookups_preserved_after_update_var_in_scope:
  ∀cx st n v.
    valid_lookups cx st ∧ var_in_scope st n ⇒
    valid_lookups cx (update_scoped_var st n v)
Proof
  rw[valid_lookups_def] >>
  qexists_tac `imms` >>
  simp[immutables_preserved_after_update] >>
  rpt strip_tac >>
  (* The key: var_in_scope after update implies var_in_scope before *)
  `var_in_scope st n'` by (
    gvs[var_in_scope_def, lookup_scoped_var_def] >>
    Cases_on `string_to_num n' = string_to_num n` >-
     (gvs[lookup_after_update, lookup_scoped_var_def]) >>
    `lookup_scoped_var (update_scoped_var st n v) n' = lookup_scoped_var st n'`
      by (irule lookup_scoped_var_preserved_after_update >>
          metis_tac[vyperMiscTheory.string_to_num_inj]) >>
    gvs[lookup_scoped_var_def]) >>
  first_x_assum irule >> simp[]
QED

Theorem valid_lookups_preserved_after_update_no_immutable:
  ∀cx st n v.
    valid_lookups cx st ∧ lookup_immutable cx st n = NONE ⇒
    valid_lookups cx (update_scoped_var st n v)
Proof
  rpt strip_tac >>
  Cases_on `var_in_scope st n` >-
   metis_tac[valid_lookups_preserved_after_update_var_in_scope] >>
  (* ¬var_in_scope st n: need to show lookup_name cx st n = NONE *)
  irule valid_lookups_preserved_after_update_no_name >> simp[] >>
  (* Need: lookup_name cx st n = NONE *)
  gvs[var_in_scope_def, lookup_scoped_var_def, lookup_immutable_def, valid_lookups_def] >>
  simp[lookup_name_def, Once evaluate_def, bind_def, get_scopes_def, return_def,
       get_immutables_def, get_address_immutables_def, lift_option_def, lift_option_type_def,
       exactly_one_option_def, raise_def, lift_sum_def]
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

Theorem lookup_immutable_after_set_immutable:
  ∀cx n v st st'.
    set_immutable cx (current_module cx) (string_to_num n) v st = (INL (), st') ⇒
    lookup_immutable cx st' n = SOME v
Proof
  rw[set_immutable_def, lookup_immutable_def,
     bind_def, LET_THM, get_address_immutables_def,
     set_address_immutables_def, lift_option_def] >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >> gvs[return_def, raise_def] >>
  simp[get_source_immutables_def, set_source_immutables_def,
       alistTheory.ALOOKUP_ADELKEY,
       finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem lookup_in_current_scope_to_lookup_scoped_var:
  ∀st n v.
    st.scopes ≠ [] ∧
    lookup_in_current_scope st n = SOME v ⇒
    lookup_scoped_var st n = SOME v
Proof
  rw[lookup_in_current_scope_def, lookup_scoped_var_def] >>
  Cases_on `st.scopes` >> gvs[lookup_scopes_def]
QED

Theorem lookup_in_current_scope_hd:
  ∀st n. HD st.scopes = FEMPTY ⇒ lookup_in_current_scope st n = NONE
Proof
  simp[lookup_in_current_scope_def, finite_mapTheory.FLOOKUP_EMPTY]
QED

Theorem lookup_in_current_scope_singleton_same:
  ∀st id v.
    HD st.scopes = FEMPTY |+ (string_to_num id, v) ⇒
    lookup_in_current_scope st id = SOME v
Proof
  simp[lookup_in_current_scope_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem lookup_in_current_scope_singleton_other:
  ∀st id v n.
    HD st.scopes = FEMPTY |+ (string_to_num id, v) ∧ n ≠ id ⇒
    lookup_in_current_scope st n = NONE
Proof
  simp[lookup_in_current_scope_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[finite_mapTheory.FLOOKUP_EMPTY] >>
  metis_tac[vyperMiscTheory.string_to_num_inj]
QED

Theorem lookup_in_tl_scopes:
  ∀st n.
    lookup_in_current_scope st n = NONE ⇒
    (lookup_scoped_var (tl_scopes st) n = lookup_scoped_var st n)
Proof
  rw[lookup_in_current_scope_def, lookup_scoped_var_def, tl_scopes_def] >>
  Cases_on `st.scopes` >> gvs[lookup_scopes_def]
QED

Theorem var_in_tl_scopes:
  ∀st n.
    lookup_in_current_scope st n = NONE ⇒
    (var_in_scope (tl_scopes st) n ⇔ var_in_scope st n)
Proof
  simp[var_in_scope_def, lookup_in_tl_scopes]
QED

Theorem valid_lookups_tl_scopes:
  ∀cx st. valid_lookups cx st ⇒ valid_lookups cx (tl_scopes st)
Proof
  rw[valid_lookups_def, tl_scopes_def] >>
  qexists_tac `imms` >> simp[] >>
  rpt strip_tac >> first_x_assum irule >>
  gvs[var_in_scope_def, lookup_scoped_var_def] >>
  Cases_on `st.scopes` >> gvs[lookup_scopes_def] >>
  Cases_on `FLOOKUP h (string_to_num n)` >> gvs[]
QED

Theorem valid_lookups_tl_scopes_rev:
  ∀cx st.
    HD st.scopes = FEMPTY ∧
    valid_lookups cx (tl_scopes st) ⇒
    valid_lookups cx st
Proof
  rw[valid_lookups_def, tl_scopes_def] >>
  qexists_tac `imms` >> simp[] >> rpt strip_tac >> first_x_assum irule >>
  gvs[var_in_scope_def, lookup_scoped_var_def] >>
  Cases_on `st.scopes` >> gvs[lookup_scopes_def, finite_mapTheory.FLOOKUP_EMPTY]
QED

(* Helper for if-statement: lookup_name is preserved when entering a new scope *)
Theorem lookup_name_tl_scopes:
  ∀cx st n.
    st.scopes ≠ [] ∧ HD st.scopes = FEMPTY ⇒
    lookup_name cx st n = lookup_name cx (tl_scopes st) n
Proof
  rpt strip_tac >>
  simp[lookup_name_def, tl_scopes_def] >>
  (* First, prove lookup_scoped_var equality *)
  `lookup_scoped_var st n = lookup_scoped_var (st with scopes := TL st.scopes) n` by (
    simp[lookup_scoped_var_def] >>
    Cases_on `st.scopes` >> gvs[lookup_scopes_def, finite_mapTheory.FLOOKUP_EMPTY]) >>
  (* Expand both eval_expr calls *)
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
       get_immutables_def, get_address_immutables_def,
       lift_option_def, lift_option_type_def, lift_sum_def, GSYM lookup_scoped_var_def,
       exactly_one_option_def, raise_def] >>
  CONV_TAC (RHS_CONV (SIMP_CONV (srw_ss()) [Once evaluate_def, bind_def, get_scopes_def, return_def,
       get_immutables_def, get_address_immutables_def,
       lift_option_def, lift_option_type_def, lift_sum_def, GSYM lookup_scoped_var_def,
       exactly_one_option_def, raise_def])) >>
  Cases_on `ALOOKUP st.immutables cx.txn.target` >> simp[raise_def, return_def] >>
  simp[GSYM lookup_scoped_var_def, exactly_one_option_def] >>
  `lookup_scoped_var (st with scopes := TL st.scopes) n = lookup_scopes (string_to_num n) (TL st.scopes)`
    by simp[lookup_scoped_var_def] >>
  gvs[] >>
  Cases_on `exactly_one_option (lookup_scopes (string_to_num n) (TL st.scopes))
              (FLOOKUP (get_source_immutables (current_module cx) x) (string_to_num n))` >>
  simp[return_def, raise_def, bind_def]
QED

Theorem update_scoped_var_in_tl_scopes:
  ∀st n v.
    lookup_in_current_scope st n = NONE ∧
    var_in_scope (tl_scopes st) n ⇒
    (tl_scopes (update_scoped_var st n v)).scopes =
    (update_scoped_var (tl_scopes st) n v).scopes
Proof
  rw[lookup_in_current_scope_def, var_in_scope_def, lookup_scoped_var_def,
     tl_scopes_def, update_scoped_var_def, LET_THM] >>
  Cases_on `st.scopes` >> gvs[lookup_scopes_def] >>
  simp[Once find_containing_scope_def] >> gvs[] >>
  `IS_SOME (find_containing_scope (string_to_num n) t)`
    by metis_tac[lookup_scopes_find_containing] >>
  Cases_on `find_containing_scope (string_to_num n) t` >> gvs[] >>
  PairCases_on `x` >> gvs[evaluation_state_accfupds]
QED

Theorem lookup_scoped_var_update_in_tl_scopes:
  ∀st n v.
    lookup_in_current_scope st n = NONE ∧
    var_in_scope (tl_scopes st) n ⇒
    lookup_scoped_var (tl_scopes (update_scoped_var st n v)) n = SOME v
Proof
  rpt strip_tac >>
  simp[lookup_scoped_var_def, tl_scopes_def] >>
  `(tl_scopes (update_scoped_var st n v)).scopes =
   (update_scoped_var (tl_scopes st) n v).scopes`
    by simp[update_scoped_var_in_tl_scopes] >>
  gvs[tl_scopes_def] >>
  simp[GSYM lookup_scoped_var_def, lookup_after_update]
QED

Theorem lookup_scoped_var_preserved_after_update_in_tl_scopes:
  ∀st n1 n2 v w.
    n1 ≠ n2 ∧
    lookup_in_current_scope st n1 = NONE ∧
    lookup_in_current_scope st n2 = NONE ∧
    var_in_scope (tl_scopes st) n1 ∧
    lookup_scoped_var (tl_scopes st) n2 = SOME w ⇒
    lookup_scoped_var (tl_scopes (update_scoped_var st n1 v)) n2 = SOME w
Proof
  rpt strip_tac >>
  `(tl_scopes (update_scoped_var st n1 v)).scopes =
   (update_scoped_var (tl_scopes st) n1 v).scopes`
    by simp[update_scoped_var_in_tl_scopes] >>
  gvs[lookup_scoped_var_def, tl_scopes_def] >>
  simp[GSYM lookup_scoped_var_def, lookup_scoped_var_preserved_after_update] >>
  simp[lookup_scoped_var_def]
QED

Theorem scopes_nonempty_preserved_after_update_in_tl_scopes:
  ∀st n v.
    st.scopes ≠ [] ∧
    lookup_in_current_scope st n = NONE ∧
    var_in_scope (tl_scopes st) n ⇒
    (tl_scopes (update_scoped_var st n v)).scopes ≠ []
Proof
  rpt strip_tac >>
  `(tl_scopes (update_scoped_var st n v)).scopes =
   (update_scoped_var (tl_scopes st) n v).scopes`
    by metis_tac[update_scoped_var_in_tl_scopes] >>
  gvs[tl_scopes_def, scopes_nonempty_after_update]
QED

Theorem valid_lookups_preserved_after_update_in_tl_scopes:
  ∀cx st n v.
    lookup_in_current_scope st n = NONE ∧
    var_in_scope (tl_scopes st) n ∧
    valid_lookups cx (tl_scopes st) ⇒
    valid_lookups cx (tl_scopes (update_scoped_var st n v))
Proof
  rpt strip_tac >> gvs[valid_lookups_def, tl_scopes_def] >>
  qexists_tac `imms` >> simp[immutables_preserved_after_update] >>
  rpt strip_tac >> first_x_assum irule >>
  gvs[var_in_scope_def, lookup_scoped_var_def] >>
  `(tl_scopes (update_scoped_var st n v)).scopes =
   (update_scoped_var (tl_scopes st) n v).scopes`
    by (irule update_scoped_var_in_tl_scopes >>
        gvs[var_in_scope_def, lookup_scoped_var_def, tl_scopes_def]) >>
  gvs[tl_scopes_def] >>
  Cases_on `n' = n` >> gvs[] >>
  `lookup_scoped_var (update_scoped_var (st with scopes := TL st.scopes) n v) n' =
   lookup_scoped_var (st with scopes := TL st.scopes) n'`
    by simp[lookup_scoped_var_preserved_after_update] >>
  gvs[lookup_scoped_var_def]
QED

Theorem hd_scopes_preserved_after_update_in_tl_scopes:
  ∀st n v.
    st.scopes ≠ [] ∧
    lookup_in_current_scope st n = NONE ∧
    var_in_scope (tl_scopes st) n ⇒
    HD (update_scoped_var st n v).scopes = HD st.scopes
Proof
  rw[lookup_in_current_scope_def, var_in_scope_def, lookup_scoped_var_def,
     tl_scopes_def, update_scoped_var_def, LET_THM] >>
  Cases_on `st.scopes` >> gvs[lookup_scopes_def] >>
  simp[Once find_containing_scope_def] >> gvs[] >>
  `IS_SOME (find_containing_scope (string_to_num n) t)`
    by metis_tac[lookup_scopes_find_containing] >>
  Cases_on `find_containing_scope (string_to_num n) t` >> gvs[] >>
  PairCases_on `x` >> gvs[]
QED

Theorem tl_scopes_update_eq_update_tl_scopes:
  ∀st n v.
    lookup_in_current_scope st n = NONE ∧
    var_in_scope (tl_scopes st) n ⇒
    tl_scopes (update_scoped_var st n v) = update_scoped_var (tl_scopes st) n v
Proof
  rpt strip_tac >> simp[tl_scopes_def, evaluation_state_component_equality] >>
  gvs[lookup_in_current_scope_def, var_in_scope_def, lookup_scoped_var_def, tl_scopes_def,
      update_scoped_var_def, LET_THM] >>
  Cases_on `st.scopes` >> gvs[lookup_scopes_def] >>
  simp[Once find_containing_scope_def] >> gvs[] >>
  `IS_SOME (find_containing_scope (string_to_num n) t)` by metis_tac[lookup_scopes_find_containing] >>
  Cases_on `find_containing_scope (string_to_num n) t` >> gvs[] >>
  PairCases_on `x` >> gvs[] >>
  rpt (simp[Once find_containing_scope_def] >>
       Cases_on `find_containing_scope (string_to_num n) t` >> gvs[] >>
       TRY (PairCases_on `x'` >> gvs[]))
QED

Theorem lookup_name_preserved_after_update_in_tl_scopes:
  ∀cx st n1 n2 v.
    n1 ≠ n2 ∧
    lookup_in_current_scope st n1 = NONE ∧
    var_in_scope (tl_scopes st) n1 ⇒
    lookup_name cx (tl_scopes (update_scoped_var st n1 v)) n2 =
    lookup_name cx (tl_scopes st) n2
Proof
  rpt strip_tac >>
  `tl_scopes (update_scoped_var st n1 v) = update_scoped_var (tl_scopes st) n1 v`
    by simp[tl_scopes_update_eq_update_tl_scopes] >>
  simp[lookup_name_preserved_after_update]
QED

Theorem lookup_immutable_tl_scopes:
  ∀cx st n. lookup_immutable cx (tl_scopes st) n = lookup_immutable cx st n
Proof
  rw[lookup_immutable_def, tl_scopes_def]
QED

Theorem lookup_immutable_preserved_after_update:
  ∀cx st n v k.
    lookup_immutable cx (update_scoped_var st n v) k =
    lookup_immutable cx st k
Proof
  rw[lookup_immutable_def, immutables_preserved_after_update]
QED

Theorem valid_lookups_push_non_immutable:
  ∀cx st id v.
    valid_lookups cx (tl_scopes st) ∧
    HD st.scopes = FEMPTY |+ (string_to_num id, v) ∧
    lookup_immutable cx st id = NONE ⇒
    (cx.txn.is_creation ⇒ valid_lookups cx st)
Proof
  rw[valid_lookups_def, tl_scopes_def, lookup_immutable_def,
     var_in_scope_def, lookup_scoped_var_def] >>
  qexists_tac `imms` >> simp[] >> rpt strip_tac >>
  Cases_on `st.scopes` >> gvs[lookup_scopes_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `string_to_num id = string_to_num n` >> gvs[]
QED

Theorem valid_lookups_push_singleton:
  ∀cx st id v.
    valid_lookups cx (tl_scopes st) ∧
    HD st.scopes = FEMPTY |+ (string_to_num id, v) ∧
    lookup_immutable cx st id = NONE ⇒
    valid_lookups cx st
Proof
  rw[valid_lookups_def, tl_scopes_def, lookup_immutable_def,
     var_in_scope_def, lookup_scoped_var_def] >>
  qexists_tac `imms` >> simp[] >> rpt strip_tac >>
  Cases_on `st.scopes` >> gvs[lookup_scopes_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `string_to_num id = string_to_num n` >> gvs[]
QED

(* ===== update_scoped_var frame: other variables preserved ===== *)

Theorem update_scoped_var_frame:
  ∀cx st n1 n2 v w.
    n1 ≠ n2 ∧ var_in_scope st n1 ∧ valid_lookups cx st ∧
    lookup_scoped_var st n2 = SOME w ⇒
    lookup_scoped_var (update_scoped_var st n1 v) n2 = SOME w ∧
    valid_lookups cx (update_scoped_var st n1 v) ∧
    (update_scoped_var st n1 v).scopes ≠ [] ∧
    var_in_scope (update_scoped_var st n1 v) n2
Proof
  rpt strip_tac >>
  gvs[lookup_scoped_var_preserved_after_update, scopes_nonempty_after_update] >>
  metis_tac[valid_lookups_preserved_after_update_var_in_scope,
            var_in_scope_preserved_after_update,
            var_in_scope_def, optionTheory.IS_SOME_DEF]
QED

Theorem lookup_flag_member_to_lookup_flag_mem:
  ∀cx st nsid mid v.
    lookup_flag_member cx nsid mid = SOME v ⇒
    lookup_flag_mem cx nsid mid st = (INL v, st)
Proof
  rpt gen_tac
  >> PairCases_on `nsid`
  >> simp[lookup_flag_member_def, lookup_flag_mem_def]
  >> rpt CASE_TAC >> gvs[return_def, raise_def]
QED

Theorem lookup_flag_mem_to_lookup_flag_member_some:
  ∀cx st st' nsid mid v.
    lookup_flag_mem cx nsid mid st = (INL v, st') ⇒
    lookup_flag_member cx nsid mid = SOME v
Proof
  rpt gen_tac
  >> PairCases_on `nsid`
  >> simp[lookup_flag_member_def, lookup_flag_mem_def]
  >> rpt CASE_TAC >> gvs[return_def, raise_def]
QED

Theorem lookup_flag_mem_to_lookup_flag_member_none:
  ∀cx st st' nsid mid e.
    lookup_flag_mem cx nsid mid st = (INR e, st') ⇒
    lookup_flag_member cx nsid mid = NONE
Proof
  rpt gen_tac
  >> PairCases_on `nsid`
  >> simp[lookup_flag_member_def, lookup_flag_mem_def]
  >> rpt CASE_TAC >> gvs[return_def, raise_def]
QED

(* ===== FEMPTY prepend: lookup/var/valid pass through FEMPTY :: scopes ===== *)

Theorem lookup_scoped_var_fempty_prepend:
  ∀st n.
    lookup_scoped_var (st with scopes := FEMPTY :: st.scopes) n =
    lookup_scoped_var st n
Proof
  simp[lookup_scoped_var_def, lookup_scopes_def, finite_mapTheory.FLOOKUP_DEF]
QED

Theorem var_in_scope_fempty_prepend:
  ∀st n.
    var_in_scope (st with scopes := FEMPTY :: st.scopes) n ⇔
    var_in_scope st n
Proof
  simp[var_in_scope_def, lookup_scoped_var_fempty_prepend]
QED

Theorem valid_lookups_fempty_prepend:
  ∀cx st.
    valid_lookups cx (st with scopes := FEMPTY :: st.scopes) ⇔
    valid_lookups cx st
Proof
  rpt gen_tac >> EQ_TAC >>
  simp[valid_lookups_def, var_in_scope_fempty_prepend]
QED

Theorem fcs_fempty[local]:
  ∀ni rest.
    find_containing_scope ni (FEMPTY :: rest) =
    OPTION_MAP (λ(pre,env,a,post). (FEMPTY::pre,env,a,post))
               (find_containing_scope ni rest)
Proof
  simp[find_containing_scope_def, finite_mapTheory.FLOOKUP_DEF] >>
  rpt gen_tac >>
  Cases_on `find_containing_scope ni rest` >> simp[] >>
  PairCases_on `x` >> simp[]
QED

Theorem update_scoped_var_fempty:
  ∀st n v.
    var_in_scope st n ⇒
    update_scoped_var (st with scopes := FEMPTY :: st.scopes) n v =
    (update_scoped_var st n v) with scopes :=
      FEMPTY :: (update_scoped_var st n v).scopes
Proof
  simp[update_scoped_var_def, var_in_scope_def, lookup_scoped_var_def] >>
  rpt strip_tac >>
  `find_containing_scope (string_to_num n) st.scopes ≠ NONE` by
    (strip_tac >> imp_res_tac find_containing_scope_none_lookup_scopes_none >>
     fs[]) >>
  Cases_on `find_containing_scope (string_to_num n) st.scopes` >> fs[] >>
  PairCases_on `x` >>
  simp[find_containing_scope_def, evaluation_state_component_equality]
QED

(* ===== new_variable = update when var doesn't exist ===== *)

Theorem lookup_scopes_none_fcs_none[local]:
  ∀id sc. lookup_scopes id sc = NONE ⇒ find_containing_scope id sc = NONE
Proof
  Induct_on `sc` >> simp[lookup_scopes_def, find_containing_scope_def] >>
  rpt strip_tac >> Cases_on `FLOOKUP h id` >> fs[]
QED

Theorem new_variable_eq_update:
  lookup_scoped_var st id = NONE ∧ st.scopes ≠ [] ⇒
  new_variable id v st = (INL (), update_scoped_var st id v)
Proof
  strip_tac >>
  `lookup_scopes (string_to_num id) st.scopes = NONE`
    by fs[lookup_scoped_var_def] >>
  simp[new_variable_def, LET_THM, get_scopes_def, return_def, bind_def,
       check_def, type_check_def] >>
  ASM_REWRITE_TAC[] >> simp[assert_def, ignore_bind_def, bind_def] >>
  Cases_on `st.scopes` >> fs[] >>
  simp[set_scopes_def, return_def] >>
  simp[update_scoped_var_def, LET_THM] >>
  `find_containing_scope (string_to_num id) (h::t) = NONE` by
    (irule lookup_scopes_none_fcs_none >> ASM_REWRITE_TAC[]) >>
  ASM_REWRITE_TAC[] >>
  simp[evaluation_state_component_equality]
QED
