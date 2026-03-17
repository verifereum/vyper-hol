Theory vyperLookup
Ancestors
  vyperMisc vyperContext vyperState vyperStorage vyperInterpreter vyperValue vyperValueOperation
  vyperTyping vyperEncodeDecode
Libs
  wordsLib

Definition lookup_name_def:
  lookup_name st n = lookup_scopes_val (string_to_num n) st.scopes
End

Definition lookup_name_typed_def:
  lookup_name_typed st n = lookup_scopes (string_to_num n) st.scopes
End

Definition var_in_scope_def:
  var_in_scope st n ⇔ IS_SOME (lookup_name st n)
End

Definition lookup_in_current_scope_def:
  lookup_in_current_scope st n = FLOOKUP (HD st.scopes) (string_to_num n)
End

Definition open_scope_def:
  open_scope st = st with scopes updated_by CONS FEMPTY
End

Definition tl_scopes_def:
  tl_scopes st = st with scopes := TL st.scopes
End

Definition lookup_immutable_def:
  lookup_immutable cx (st:evaluation_state) mid n =
  case ALOOKUP st.immutables cx.txn.target of
  | SOME imms => FLOOKUP (get_source_immutables mid imms) (string_to_num n)
  | NONE => NONE
End

Definition lookup_bare_global_name_def:
  lookup_bare_global_name cx st n = lookup_immutable cx st (current_module cx) n
End

(* For convenience, we define the case st.scopes = [] in such a way
   that looking up after update returns the updated variable value. *)
(* update_name: update the value of a scoped variable, preserving its type.
   The NONE branch (variable not found) is dead code when var_in_scope holds;
   it uses ARB for the type_value. *)
Definition update_name_def:
  update_name st id v =
    let n = string_to_num id in
    case find_containing_scope n st.scopes of
    | SOME (pre, env, tv, _, rest) =>
        st with scopes := (pre ++ (env |+ (n, (tv, v)))::rest)
    | NONE =>
        case st.scopes of
        | [] => st with scopes := [FEMPTY |+ (n, (ARB, v))]
        | h :: t => st with scopes := (h |+ (n, (ARB, v))) :: t
End

(* declare_name: like update_name but for creating new variables with an
   explicit type_value. *)
Definition declare_name_def:
  declare_name st id ty v =
    let n = string_to_num id in
    case st.scopes of
    | [] => st with scopes := [FEMPTY |+ (n, (ty, v))]
    | h :: t => st with scopes := (h |+ (n, (ty, v))) :: t
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
     | SOME i => SOME $ Value $ FlagV (2 ** i)
End

(****************************************)
(* Helpers *)

Theorem lookup_scopes_update_other[local]:
  ∀pre n1 n2 env v rest.
    n1 ≠ n2 ⇒
    lookup_scopes n2 (pre ⧺ env |+ (n1, v) :: rest) =
    lookup_scopes n2 (pre ⧺ env :: rest)
Proof
  Induct_on `pre` >-
   simp[lookup_scopes_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[lookup_scopes_def]
QED

Theorem lookup_scopes_val_update_other[local]:
  ∀pre n1 n2 env v rest.
    n1 ≠ n2 ⇒
    lookup_scopes_val n2 (pre ⧺ env |+ (n1, v) :: rest) =
    lookup_scopes_val n2 (pre ⧺ env :: rest)
Proof
  Induct_on `pre` >-
   simp[lookup_scopes_val_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  simp[lookup_scopes_val_def]
QED

Theorem lookup_scopes_FEMPTY_CONS[local]:
  ∀n rest. lookup_scopes n (FEMPTY::rest) = lookup_scopes n rest
Proof
  simp[Once lookup_scopes_def, finite_mapTheory.FLOOKUP_EMPTY]
QED

Theorem IS_SOME_lookup_scopes_val[simp]:
  ∀id sc. IS_SOME (lookup_scopes_val id sc) ⇔ IS_SOME (lookup_scopes id sc)
Proof
  Induct_on `sc` >> simp[lookup_scopes_val_def, lookup_scopes_def] >>
  rpt gen_tac >> Cases_on `FLOOKUP h id` >> simp[]
QED

Theorem lookup_scopes_val_SOME[local]:
  ∀id sc v.
    lookup_scopes_val id sc = SOME v ⇔
    ∃tv. lookup_scopes id sc = SOME (tv, v)
Proof
  Induct_on `sc` >> simp[lookup_scopes_val_def, lookup_scopes_def] >>
  rpt gen_tac >> Cases_on `FLOOKUP h id` >> simp[] >>
  Cases_on `x` >> simp[]
QED

Theorem lookup_scopes_val_NONE[local]:
  ∀id sc. lookup_scopes_val id sc = NONE ⇔ lookup_scopes id sc = NONE
Proof
  Induct_on `sc` >> simp[lookup_scopes_val_def, lookup_scopes_def] >>
  rpt gen_tac >> Cases_on `FLOOKUP h id` >> simp[]
QED

Theorem find_containing_scope_none_lookup_scopes_none[local]:
  ∀id sc. find_containing_scope id sc = NONE ⇒ lookup_scopes id sc = NONE
Proof
  Induct_on `sc` >> simp[Once find_containing_scope_def, Once lookup_scopes_def] >>
  rpt strip_tac >> Cases_on `FLOOKUP h id` >> gvs[] >>
  Cases_on `x` >> gvs[]
QED

Theorem lookup_scopes_find_containing[local]:
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
  Cases_on `x` >> simp[]
QED

Theorem find_containing_scope_pre_none[local]:
  ∀id sc pre env tv v rest.
    find_containing_scope id sc = SOME (pre,env,tv,v,rest) ⇒
    lookup_scopes id pre = NONE
Proof
  Induct_on `sc` >- rw[find_containing_scope_def] >>
  simp[find_containing_scope_def] >>
  rpt gen_tac >> Cases_on `FLOOKUP h id` >> gvs[] >-
   (strip_tac >> PairCases_on `z` >> gvs[] >> simp[lookup_scopes_def]) >>
  Cases_on `x` >> simp[lookup_scopes_def]
QED

Theorem lookup_scopes_update[local]:
  ∀id pre env v rest.
    lookup_scopes id pre = NONE ⇒
    lookup_scopes id (pre ++ env |+ (id,v) :: rest) = SOME v
Proof
  Induct_on `pre` >-
   simp[lookup_scopes_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[lookup_scopes_def, AllCaseEqs()]
QED

Theorem find_containing_scope_structure[local]:
  ∀id sc pre env tv v rest.
    find_containing_scope id sc = SOME (pre, env, tv, v, rest) ⇒
    sc = pre ++ env :: rest ∧ FLOOKUP env id = SOME (tv, v)
Proof
  Induct_on `sc` >- rw[find_containing_scope_def] >>
  rpt gen_tac >> strip_tac >> qpat_x_assum `_ = SOME _` mp_tac >>
  simp[find_containing_scope_def] >>
  Cases_on `FLOOKUP h id` >> simp[] >-
  (strip_tac >> PairCases_on `z` >> gvs[] >> first_x_assum drule >> simp[]) >>
  Cases_on `x` >> strip_tac >> gvs[]
QED

Theorem find_containing_scope_lookup[local]:
  ∀id sc pre env tv v rest.
    find_containing_scope id sc = SOME (pre, env, tv, v, rest) ⇒
    lookup_scopes id sc = SOME (tv, v)
Proof
  Induct_on `sc` >- rw[find_containing_scope_def] >>
  rw[find_containing_scope_def, lookup_scopes_def] >>
  Cases_on `FLOOKUP h id` >> gvs[] >-
  (PairCases_on `z` >> gvs[]) >>
  Cases_on `x` >> gvs[]
QED

Theorem find_containing_scope_lookup_scopes[local]:
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

Theorem lookup_scopes_dom_iff[local]:
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

Theorem tl_scopes_push[local]:
  tl_scopes (st with scopes updated_by CONS sc) = st
Proof
  simp[tl_scopes_def, evaluation_state_accfupds] >>
  Cases_on `st` >> simp[evaluation_state_fn_updates]
QED

Theorem tl_scopes_cons_id[local]:
  ∀st:evaluation_state.
    st.scopes ≠ [] ∧ HD st.scopes = FEMPTY ⇒
    tl_scopes st with scopes updated_by CONS FEMPTY = st
Proof
  rpt strip_tac >> Cases_on `st.scopes` >>
  gvs[tl_scopes_def, evaluation_state_accfupds] >>
  Cases_on `st` >> simp[evaluation_state_fn_updates, evaluation_state_component_equality]
QED

Theorem lookup_in_current_scope_singleton_same[local]:
  ∀st id v.
    HD st.scopes = FEMPTY |+ (string_to_num id, v) ⇒
    lookup_in_current_scope st id = SOME v
Proof
  simp[lookup_in_current_scope_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem lookup_in_current_scope_singleton_other[local]:
  ∀st id v n.
    HD st.scopes = FEMPTY |+ (string_to_num id, v) ∧ n ≠ id ⇒
    lookup_in_current_scope st n = NONE
Proof
  simp[lookup_in_current_scope_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[finite_mapTheory.FLOOKUP_EMPTY] >>
  metis_tac[vyperMiscTheory.string_to_num_inj]
QED

(****************************************)
(* Scope lemmas *)

Theorem tl_scopes_open_scope:
  ∀st. tl_scopes (open_scope st) = st
Proof
  simp[open_scope_def, tl_scopes_push]
QED

Theorem lookup_name_typed_open_scope:
  ∀st n. lookup_name_typed (open_scope st) n = lookup_name_typed st n
Proof
  simp[open_scope_def, lookup_name_typed_def,
       evaluation_state_accfupds, lookup_scopes_FEMPTY_CONS]
QED

Theorem lookup_name_open_scope:
  ∀st n. lookup_name (open_scope st) n = lookup_name st n
Proof
  simp[open_scope_def, lookup_name_def, evaluation_state_accfupds] >>
  simp[Once lookup_scopes_val_def, finite_mapTheory.FLOOKUP_EMPTY]
QED

Theorem var_in_scope_open_scope:
  ∀st n. var_in_scope (open_scope st) n ⇔ var_in_scope st n
Proof
  simp[var_in_scope_def, lookup_name_open_scope]
QED

Theorem scopes_nonempty_open_scope:
  ∀st. (open_scope st).scopes ≠ []
Proof
  simp[open_scope_def, evaluation_state_accfupds]
QED

Theorem tl_scopes_update_open_scope:
  ∀st n v. var_in_scope st n ⇒
    tl_scopes (update_name (open_scope st) n v) = update_name st n v
Proof
  rpt strip_tac >>
  gvs[var_in_scope_def, lookup_name_def] >>
  `IS_SOME (find_containing_scope (string_to_num n) st.scopes)` by
    (irule lookup_scopes_find_containing >> simp[]) >>
  Cases_on `find_containing_scope (string_to_num n) st.scopes` >> gvs[] >>
  PairCases_on `x` >> gvs[] >>
  simp[open_scope_def, tl_scopes_def, update_name_def, LET_THM,
       evaluation_state_accfupds, evaluation_state_component_equality,
       find_containing_scope_def, finite_mapTheory.FLOOKUP_EMPTY]
QED

Theorem tl_scopes_update_declare_open_scope:
  ∀st id1 id2 tyv v v'.
    id1 ≠ id2 ∧ var_in_scope st id2 ⇒
    tl_scopes (update_name (declare_name (open_scope st) id1 tyv v) id2 v') =
    update_name st id2 v'
Proof
  rpt strip_tac >>
  gvs[var_in_scope_def, lookup_name_def] >>
  `string_to_num id1 ≠ string_to_num id2` by
    metis_tac[vyperMiscTheory.string_to_num_inj] >>
  `IS_SOME (find_containing_scope (string_to_num id2) st.scopes)` by
    (irule lookup_scopes_find_containing >> simp[]) >>
  Cases_on `find_containing_scope (string_to_num id2) st.scopes` >> gvs[] >>
  PairCases_on `x` >> gvs[] >>
  simp[open_scope_def, declare_name_def, tl_scopes_def, update_name_def, LET_THM,
       evaluation_state_accfupds, evaluation_state_component_equality,
       find_containing_scope_def, finite_mapTheory.FLOOKUP_UPDATE,
       finite_mapTheory.FLOOKUP_EMPTY]
QED

Theorem tl_scopes_declare_name_open_scope:
  ∀st id tyv v. tl_scopes (declare_name (open_scope st) id tyv v) = st
Proof
  simp[open_scope_def, declare_name_def,
       tl_scopes_def, evaluation_state_component_equality]
QED

Theorem open_scope_tl_scopes_id:
  ∀st:evaluation_state.
    st.scopes ≠ [] ∧ HD st.scopes = FEMPTY ⇒
    open_scope (tl_scopes st) = st
Proof
  simp[open_scope_def, tl_scopes_cons_id]
QED

(****************************************)
(* Bridge lemmas *)

Theorem lookup_name_typed_to_lookup_name:
  ∀st n.
    lookup_name st n = OPTION_MAP SND (lookup_name_typed st n)
Proof
  rw[lookup_name_def, lookup_name_typed_def] >>
  Cases_on `lookup_scopes (string_to_num n) st.scopes` >>
  simp[lookup_scopes_val_NONE] >>
  Cases_on `x` >> simp[lookup_scopes_val_SOME]
QED

Theorem lookup_name_SOME:
  ∀id sc v.
    lookup_name id sc = SOME v ⇔
    ∃tv. lookup_name_typed id sc = SOME (tv, v)
Proof
  simp[lookup_name_def, lookup_name_typed_def, lookup_scopes_val_SOME]
QED

Theorem lookup_name_NONE:
  ∀id sc. lookup_name id sc = NONE ⇔ lookup_name_typed id sc = NONE
Proof
  simp[lookup_name_def, lookup_name_typed_def, lookup_scopes_val_NONE]
QED

Theorem var_in_scope_lookup_name_typed[local]:
  ∀st n. var_in_scope st n ⇔ IS_SOME (lookup_name_typed st n)
Proof
  simp[var_in_scope_def, lookup_name_def, lookup_name_typed_def]
QED

Theorem lookup_name_implies_var_in_scope:
  ∀st n v. lookup_name st n = SOME v ⇒ var_in_scope st n
Proof
  simp[var_in_scope_def]
QED

(* ===== lookup_name_typed with_scopes ===== *)

Theorem lookup_name_typed_with_scopes:
  ∀st1 st2 n. lookup_name_typed (st1 with scopes := st2.scopes) n = lookup_name_typed st2 n
Proof
  rw[lookup_name_typed_def]
QED

Theorem lookup_name_with_scopes:
  ∀st1 st2 n. lookup_name (st1 with scopes := st2.scopes) n = lookup_name st2 n
Proof
  simp[lookup_name_typed_to_lookup_name, lookup_name_typed_with_scopes]
QED

Theorem lookup_name_typed_with_scopes_list:
  ∀st1 st2 n sc.
    lookup_name_typed (st1 with scopes := sc) n = lookup_name_typed (st2 with scopes := sc) n
Proof
  rw[lookup_name_typed_def]
QED

Theorem lookup_name_with_scopes_list:
  ∀st1 st2 n sc.
    lookup_name (st1 with scopes := sc) n = lookup_name (st2 with scopes := sc) n
Proof
  rpt gen_tac >>
  simp[lookup_name_typed_to_lookup_name] >>
  AP_TERM_TAC >>
  simp[lookup_name_typed_with_scopes_list]
QED

Theorem var_in_scope_implies_name_target:
  ∀cx (st:evaluation_state) n.
    var_in_scope st n ⇒
    lookup_name_target cx st n = SOME (BaseTargetV (ScopedVar n) [])
Proof
  rw[var_in_scope_def, lookup_name_def, lookup_name_target_def, lookup_base_target_def] >>
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
       check_def, type_check_def, assert_def, ignore_bind_def]
QED

Theorem lookup_name_target_implies_var_in_scope:
  ∀cx st n.
    lookup_name_target cx st n = SOME (BaseTargetV (ScopedVar n) []) ⇒
    var_in_scope st n
Proof
  rw[var_in_scope_def, lookup_name_def, lookup_name_target_def, lookup_base_target_def] >>
  pop_assum mp_tac >>
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
       check_def, type_check_def, assert_def, ignore_bind_def, raise_def] >>
  Cases_on `IS_SOME (lookup_scopes (string_to_num n) st.scopes)` >> simp[]
QED

Theorem var_in_scope_dom_iff:
  ∀st1 st2 n.
    MAP FDOM st1.scopes = MAP FDOM st2.scopes ⇒
    (var_in_scope st1 n ⇔ var_in_scope st2 n)
Proof
  fs[var_in_scope_def, lookup_name_def] >>
  gvs[lookup_scopes_dom_iff]
QED

Theorem var_in_scope_iff_lookup_scopes:
  ∀st n. var_in_scope st n ⇔ IS_SOME (lookup_scopes (string_to_num n) st.scopes)
Proof
  simp[var_in_scope_def, lookup_name_def]
QED

Theorem var_in_scope_scopes_subset:
  ∀st st' n.
    st.scopes ≠ [] ∧ st'.scopes ≠ [] ∧
    FDOM (HD st.scopes) ⊆ FDOM (HD st'.scopes) ∧
    MAP FDOM (TL st.scopes) = MAP FDOM (TL st'.scopes) ∧
    var_in_scope st n ⇒
    var_in_scope st' n
Proof
  rpt strip_tac >>
  gvs[var_in_scope_def, lookup_name_def] >>
  Cases_on `st.scopes` >> Cases_on `st'.scopes` >> gvs[] >>
  fs[lookup_scopes_def, AllCaseEqs()] >>
  Cases_on `FLOOKUP h (string_to_num n)` >> gvs[] >-
  (Cases_on `FLOOKUP h' (string_to_num n)` >> gvs[] >> metis_tac[lookup_scopes_dom_iff]) >>
  `FLOOKUP h' (string_to_num n) ≠ NONE`
    by fs[finite_mapTheory.flookup_thm, pred_setTheory.SUBSET_DEF] >>
  Cases_on `FLOOKUP h' (string_to_num n)` >> gvs[]
QED

Theorem assign_target_scoped_var_implies_var_in_scope:
  ∀cx st n sbs ao.
    ISL (FST (assign_target cx (BaseTargetV (ScopedVar n) sbs) ao st)) ⇒
    var_in_scope st n
Proof
  rw[var_in_scope_def, lookup_name_def] >>
  gvs[Once assign_target_def, bind_def, get_scopes_def, return_def,
      lift_option_def, lift_option_type_def, LET_THM] >>
  Cases_on `find_containing_scope (string_to_num n) st.scopes` >>
  gvs[raise_def] >>
  irule find_containing_scope_lookup_scopes >> simp[]
QED

Theorem assign_target_name_replace:
  ∀cx st n v.
    var_in_scope st n ⇒
      assign_target cx (BaseTargetV (ScopedVar n) []) (Replace v) st =
      (INL NONE, update_name st n v)
Proof
  rw[var_in_scope_def, lookup_name_def] >>
  `IS_SOME (find_containing_scope (string_to_num n) st.scopes)`
    by metis_tac[lookup_scopes_find_containing] >>
  Cases_on `find_containing_scope (string_to_num n) st.scopes` >- gvs[] >>
  PairCases_on `x` >> gvs[] >>
  simp[Once assign_target_def, bind_def, get_scopes_def, return_def,
       lift_option_def, lift_option_type_def, lift_sum_def, assign_subscripts_def,
       ignore_bind_def, set_scopes_def, update_name_def, LET_THM,
       assign_result_def]
QED

Theorem assign_target_name_update:
  ∀cx st n ty bop v v'.
    lookup_name st n = SOME v ∧
    evaluate_binop (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
                   NoneTV bop v v' = INL new_v ⇒
    assign_target cx (BaseTargetV (ScopedVar n) []) (Update ty bop v') st =
    (INL NONE, update_name st n new_v)
Proof
  rw[lookup_name_def, lookup_scopes_val_SOME] >>
  `IS_SOME (find_containing_scope (string_to_num n) st.scopes)`
    by (irule lookup_scopes_find_containing >> simp[]) >>
  Cases_on `find_containing_scope (string_to_num n) st.scopes` >- gvs[] >>
  PairCases_on `x` >> gvs[] >>
  drule find_containing_scope_lookup >> strip_tac >> gvs[] >>
  simp[Once assign_target_def, bind_def, get_scopes_def, return_def,
       lift_option_def, lift_option_type_def, lift_sum_def, assign_subscripts_def,
       ignore_bind_def, set_scopes_def, update_name_def, LET_THM,
       assign_result_def]
QED

Theorem assign_target_name_subscripts_state:
  ∀cx st n sbs ao tv a a'.
    lookup_name_typed st n = SOME (tv, a) ∧
    assign_subscripts tv a (REVERSE sbs) ao = INL a' ⇒
    SND (assign_target cx (BaseTargetV (ScopedVar n) sbs) ao st) =
      update_name st n a'
Proof
  rpt gen_tac >> strip_tac >>
  gvs[lookup_name_typed_def] >>
  `IS_SOME (find_containing_scope (string_to_num n) st.scopes)`
    by (irule lookup_scopes_find_containing >> simp[]) >>
  Cases_on `find_containing_scope (string_to_num n) st.scopes` >- gvs[] >>
  PairCases_on `x` >> gvs[] >>
  drule find_containing_scope_lookup >> strip_tac >> gvs[] >>
  simp[Once assign_target_def, bind_def, get_scopes_def, return_def,
       lift_option_def, lift_option_type_def, lift_sum_def, assign_result_def,
       ignore_bind_def, set_scopes_def, update_name_def, LET_THM] >>
  Cases_on `ao` >> simp[assign_result_def, return_def, bind_def, lift_sum_def] >>
  rpt (CASE_TAC >> gvs[return_def, raise_def])
QED

Theorem assign_subscripts_PopOp_assign_result:
  ∀tv a subs a'.
    assign_subscripts tv a subs PopOp = INL a' ⇒
    ∃v. evaluate_subscripts tv a subs = INL v ∧ ISL (popped_value v)
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

Theorem assign_target_name_subscripts_valid:
  ∀cx st n sbs ao tv a a'.
    lookup_name_typed st n = SOME (tv, a) ∧
    assign_subscripts tv a (REVERSE sbs) ao = INL a' ⇒
    ISL (FST (assign_target cx (BaseTargetV (ScopedVar n) sbs) ao st))
Proof
  rpt gen_tac >> strip_tac >>
  gvs[lookup_name_typed_def] >>
  `IS_SOME (find_containing_scope (string_to_num n) st.scopes)`
    by (irule lookup_scopes_find_containing >> simp[]) >>
  Cases_on `find_containing_scope (string_to_num n) st.scopes` >- gvs[] >>
  PairCases_on `x` >> gvs[] >>
  drule find_containing_scope_lookup >> strip_tac >> gvs[] >>
  simp[Once assign_target_def, bind_def, get_scopes_def, return_def,
       lift_option_def, lift_option_type_def, lift_sum_def,
       ignore_bind_def, set_scopes_def, update_name_def, LET_THM] >>
  Cases_on `ao` >> simp[assign_result_def, return_def, bind_def, lift_sum_def]
  >> drule assign_subscripts_PopOp_assign_result >> strip_tac >>
     gvs[return_def, raise_def] >>
     Cases_on `popped_value v` >> gvs[return_def]
QED

(* ===== lookup_name_typed after update_name ===== *)

(* Type-preserving: when the variable exists, its type is preserved *)
Theorem lookup_name_typed_after_update_some:
  ∀st n tv v0 v.
    lookup_name_typed st n = SOME (tv, v0) ⇒
    lookup_name_typed (update_name st n v) n = SOME (tv, v)
Proof
  rw[lookup_name_typed_def, update_name_def, LET_THM] >>
  `IS_SOME (find_containing_scope (string_to_num n) st.scopes)`
    by (irule lookup_scopes_find_containing >> simp[]) >>
  Cases_on `find_containing_scope (string_to_num n) st.scopes` >- gvs[] >>
  PairCases_on `x` >> gvs[evaluation_state_accfupds] >>
  imp_res_tac find_containing_scope_lookup >> gvs[] >>
  imp_res_tac find_containing_scope_pre_none >>
  irule lookup_scopes_update >> simp[]
QED

(* When the variable does not exist, update_name still succeeds *)
Theorem lookup_name_typed_after_update_none:
  ∀st n v.
    lookup_name_typed st n = NONE ⇒
    ∃tv. lookup_name_typed (update_name st n v) n = SOME (tv, v)
Proof
  rw[lookup_name_typed_def, update_name_def, LET_THM] >>
  `find_containing_scope (string_to_num n) st.scopes = NONE` by
    (Cases_on `find_containing_scope (string_to_num n) st.scopes` >> gvs[] >>
     PairCases_on `x` >> imp_res_tac find_containing_scope_lookup >> gvs[]) >>
  simp[] >> Cases_on `st.scopes` >> gvs[evaluation_state_accfupds] >>
  simp[lookup_scopes_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem lookup_name_typed_after_update:
  ∀st n v. ∃ty. lookup_name_typed (update_name st n v) n = SOME (ty, v)
Proof
  rpt gen_tac >>
  Cases_on `lookup_name_typed st n` >-
    metis_tac[lookup_name_typed_after_update_none] >>
  PairCases_on `x` >> metis_tac[lookup_name_typed_after_update_some]
QED

Theorem lookup_after_update:
  ∀st n v. lookup_name (update_name st n v) n = SOME v
Proof
  simp[lookup_name_SOME] >> metis_tac[lookup_name_typed_after_update]
QED

(* ===== lookup_name_typed preserved after update_name ===== *)

Theorem lookup_name_typed_preserved_after_update:
  ∀st n1 n2 v.
    n1 ≠ n2 ⇒
    lookup_name_typed (update_name st n1 v) n2 = lookup_name_typed st n2
Proof
  rw[lookup_name_typed_def, update_name_def, LET_THM] >>
  `string_to_num n1 ≠ string_to_num n2` by metis_tac[vyperMiscTheory.string_to_num_inj] >>
  Cases_on `find_containing_scope (string_to_num n1) st.scopes` >-
   (simp[evaluation_state_accfupds, lookup_scopes_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
    Cases_on `st.scopes` >>
    gvs[lookup_scopes_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  PairCases_on `x` >> simp[evaluation_state_accfupds] >>
  drule find_containing_scope_structure >> strip_tac >> gvs[] >>
  `x0 ⧺ [x1] ⧺ x4 = x0 ⧺ x1::x4` by simp[] >>
  pop_assum SUBST1_TAC >>
  simp[lookup_scopes_update_other]
QED

Theorem lookup_name_preserved_after_update:
  ∀st n1 n2 v.
    n1 ≠ n2 ⇒
    lookup_name (update_name st n1 v) n2 = lookup_name st n2
Proof
  simp[lookup_name_typed_to_lookup_name, lookup_name_typed_preserved_after_update]
QED

Theorem var_in_scope_after_update:
  ∀st n v. var_in_scope (update_name st n v) n
Proof
  simp[var_in_scope_def, lookup_after_update]
QED

Theorem var_in_scope_preserved_after_update:
  ∀st n1 n2 v. var_in_scope st n2 ⇒ var_in_scope (update_name st n1 v) n2
Proof
  rpt strip_tac >>
  Cases_on `n1 = n2` >>
  fs[var_in_scope_def, lookup_name_preserved_after_update] >-
   simp[lookup_after_update]
QED

Theorem immutables_preserved_after_update:
  ∀st n v. (update_name st n v).immutables = st.immutables
Proof
  rw[update_name_def, LET_THM] >>
  Cases_on `find_containing_scope (string_to_num n) st.scopes` >-
   (Cases_on `st.scopes` >> simp[evaluation_state_accfupds]) >>
  PairCases_on `x` >> simp[evaluation_state_accfupds]
QED

Theorem scopes_nonempty_after_update:
  ∀st n v. (update_name st n v).scopes ≠ []
Proof
  rw[update_name_def, LET_THM] >>
  Cases_on `find_containing_scope (string_to_num n) st.scopes` >-
   (Cases_on `st.scopes` >> gvs[evaluation_state_accfupds]) >>
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

(* ===== lookup_in_current_scope to lookup_name_typed ===== *)

Theorem lookup_in_current_scope_to_lookup_name_typed:
  ∀st n tv v.
    st.scopes ≠ [] ∧
    lookup_in_current_scope st n = SOME (tv, v) ⇒
    lookup_name_typed st n = SOME (tv, v)
Proof
  rw[lookup_in_current_scope_def, lookup_name_typed_def] >>
  Cases_on `st.scopes` >> gvs[lookup_scopes_def]
QED

Theorem lookup_in_current_scope_to_lookup_name:
  ∀st n tv v.
    st.scopes ≠ [] ∧
    lookup_in_current_scope st n = SOME (tv, v) ⇒
    lookup_name st n = SOME v
Proof
  simp[lookup_name_SOME] >> metis_tac[lookup_in_current_scope_to_lookup_name_typed]
QED

Theorem lookup_in_current_scope_hd:
  ∀st n. HD st.scopes = FEMPTY ⇒ lookup_in_current_scope st n = NONE
Proof
  simp[lookup_in_current_scope_def, finite_mapTheory.FLOOKUP_EMPTY]
QED

Theorem lookup_in_current_scope_push_same:
  ∀st id tyv v.
    lookup_in_current_scope (declare_name (open_scope st) id tyv v) id = SOME (tyv, v)
Proof
  rpt gen_tac >>
  `(declare_name (open_scope st) id tyv v).scopes =
   (FEMPTY |+ (string_to_num id, (tyv, v))) :: st.scopes` by
    simp[open_scope_def, declare_name_def, evaluation_state_accfupds] >>
  simp[lookup_in_current_scope_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem lookup_in_current_scope_push_other:
  ∀st id n tyv v.
    n ≠ id ⇒
    lookup_in_current_scope (declare_name (open_scope st) id tyv v) n = NONE
Proof
  rpt strip_tac >>
  `(declare_name (open_scope st) id tyv v).scopes =
   (FEMPTY |+ (string_to_num id, (tyv, v))) :: st.scopes` by
    simp[open_scope_def, declare_name_def, evaluation_state_accfupds] >>
  simp[lookup_in_current_scope_def, finite_mapTheory.FLOOKUP_UPDATE,
       finite_mapTheory.FLOOKUP_EMPTY] >>
  metis_tac[vyperMiscTheory.string_to_num_inj]
QED

(* ===== lookup_name_typed in tl_scopes ===== *)

Theorem lookup_name_typed_in_tl_scopes:
  ∀st n.
    lookup_in_current_scope st n = NONE ⇒
    (lookup_name_typed (tl_scopes st) n = lookup_name_typed st n)
Proof
  rw[lookup_in_current_scope_def, lookup_name_typed_def, tl_scopes_def] >>
  Cases_on `st.scopes` >> gvs[lookup_scopes_def]
QED

Theorem lookup_in_tl_scopes:
  ∀st n.
    lookup_in_current_scope st n = NONE ⇒
    (lookup_name (tl_scopes st) n = lookup_name st n)
Proof
  simp[lookup_name_typed_to_lookup_name, lookup_name_typed_in_tl_scopes]
QED

Theorem var_in_tl_scopes:
  ∀st n.
    lookup_in_current_scope st n = NONE ⇒
    (var_in_scope (tl_scopes st) n ⇔ var_in_scope st n)
Proof
  simp[var_in_scope_def, lookup_in_tl_scopes]
QED

Theorem update_name_in_tl_scopes:
  ∀st n v.
    lookup_in_current_scope st n = NONE ∧
    var_in_scope (tl_scopes st) n ⇒
    (tl_scopes (update_name st n v)).scopes =
    (update_name (tl_scopes st) n v).scopes
Proof
  rw[lookup_in_current_scope_def, var_in_scope_def, lookup_name_def,
     tl_scopes_def, update_name_def, LET_THM] >>
  Cases_on `st.scopes` >> gvs[lookup_scopes_val_def] >>
  simp[Once find_containing_scope_def] >> gvs[] >-
  gvs[lookup_scopes_def] >>
  `IS_SOME (find_containing_scope (string_to_num n) t)`
    by metis_tac[lookup_scopes_find_containing] >>
  Cases_on `find_containing_scope (string_to_num n) t` >> gvs[] >>
  PairCases_on `x` >> gvs[evaluation_state_accfupds]
QED

(* ===== lookup_name_typed update in tl_scopes ===== *)

Theorem lookup_name_typed_update_in_tl_scopes:
  ∀st n tv v0 v.
    lookup_in_current_scope st n = NONE ∧
    lookup_name_typed (tl_scopes st) n = SOME (tv, v0) ⇒
    lookup_name_typed (tl_scopes (update_name st n v)) n = SOME (tv, v)
Proof
  rpt strip_tac >>
  `var_in_scope (tl_scopes st) n` by
    simp[var_in_scope_lookup_name_typed] >>
  `(tl_scopes (update_name st n v)).scopes =
   (update_name (tl_scopes st) n v).scopes`
    by metis_tac[update_name_in_tl_scopes] >>
  `lookup_name_typed (update_name (tl_scopes st) n v) n = SOME (tv, v)` by
    (irule lookup_name_typed_after_update_some >> qexists_tac `v0` >> simp[]) >>
  gvs[lookup_name_typed_def]
QED

Theorem lookup_name_update_in_tl_scopes:
  ∀st n v.
    lookup_in_current_scope st n = NONE ∧
    var_in_scope (tl_scopes st) n ⇒
    lookup_name (tl_scopes (update_name st n v)) n = SOME v
Proof
  rpt strip_tac >>
  simp[lookup_name_SOME] >>
  `∃tv v0. lookup_name_typed (tl_scopes st) n = SOME (tv, v0)` by
    (Cases_on `lookup_name_typed (tl_scopes st) n` >>
     gvs[var_in_scope_lookup_name_typed] >>
     PairCases_on `x` >> metis_tac[]) >>
  metis_tac[lookup_name_typed_update_in_tl_scopes]
QED

(* ===== lookup_name_typed preserved after update in tl_scopes ===== *)

Theorem lookup_name_typed_preserved_after_update_in_tl_scopes:
  ∀st n1 n2 v tv w.
    n1 ≠ n2 ∧
    lookup_in_current_scope st n1 = NONE ∧
    lookup_in_current_scope st n2 = NONE ∧
    var_in_scope (tl_scopes st) n1 ∧
    lookup_name_typed (tl_scopes st) n2 = SOME (tv, w) ⇒
    lookup_name_typed (tl_scopes (update_name st n1 v)) n2 = SOME (tv, w)
Proof
  rpt strip_tac >>
  `(tl_scopes (update_name st n1 v)).scopes =
   (update_name (tl_scopes st) n1 v).scopes`
    by simp[update_name_in_tl_scopes] >>
  `lookup_name_typed (update_name (tl_scopes st) n1 v) n2 = SOME (tv, w)` by
    simp[lookup_name_typed_preserved_after_update] >>
  gvs[lookup_name_typed_def]
QED

Theorem lookup_name_preserved_after_update_in_tl_scopes:
  ∀st n1 n2 v w.
    n1 ≠ n2 ∧
    lookup_in_current_scope st n1 = NONE ∧
    lookup_in_current_scope st n2 = NONE ∧
    var_in_scope (tl_scopes st) n1 ∧
    lookup_name (tl_scopes st) n2 = SOME w ⇒
    lookup_name (tl_scopes (update_name st n1 v)) n2 = SOME w
Proof
  rpt strip_tac >>
  gvs[lookup_name_SOME] >>
  simp[lookup_name_SOME] >>
  metis_tac[lookup_name_typed_preserved_after_update_in_tl_scopes]
QED

Theorem scopes_nonempty_preserved_after_update_in_tl_scopes:
  ∀st n v.
    st.scopes ≠ [] ∧
    lookup_in_current_scope st n = NONE ∧
    var_in_scope (tl_scopes st) n ⇒
    (tl_scopes (update_name st n v)).scopes ≠ []
Proof
  rpt strip_tac >>
  `(tl_scopes (update_name st n v)).scopes =
   (update_name (tl_scopes st) n v).scopes`
    by metis_tac[update_name_in_tl_scopes] >>
  gvs[tl_scopes_def, scopes_nonempty_after_update]
QED

Theorem hd_scopes_preserved_after_update_in_tl_scopes:
  ∀st n v.
    st.scopes ≠ [] ∧
    lookup_in_current_scope st n = NONE ∧
    var_in_scope (tl_scopes st) n ⇒
    HD (update_name st n v).scopes = HD st.scopes
Proof
  rw[lookup_in_current_scope_def, var_in_scope_def, lookup_name_def,
     tl_scopes_def, update_name_def, LET_THM] >>
  Cases_on `st.scopes` >> gvs[lookup_scopes_val_def, lookup_scopes_def] >>
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
    tl_scopes (update_name st n v) = update_name (tl_scopes st) n v
Proof
  rpt strip_tac >> simp[tl_scopes_def, evaluation_state_component_equality] >>
  gvs[lookup_in_current_scope_def, var_in_scope_def, lookup_name_def, tl_scopes_def,
      update_name_def, LET_THM] >>
  Cases_on `st.scopes` >> gvs[lookup_scopes_val_def] >>
  simp[Once find_containing_scope_def] >> gvs[] >-
  gvs[lookup_scopes_def] >>
  `IS_SOME (find_containing_scope (string_to_num n) t)` by metis_tac[lookup_scopes_find_containing] >>
  Cases_on `find_containing_scope (string_to_num n) t` >> gvs[] >>
  PairCases_on `x` >> gvs[] >>
  rpt (simp[Once find_containing_scope_def] >>
       Cases_on `find_containing_scope (string_to_num n) t` >> gvs[] >>
       TRY (PairCases_on `x'` >> gvs[]))
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

(* ===== update_name frame: other variables preserved ===== *)

Theorem update_name_typed_frame:
  ∀st n1 n2 v tv w.
    n1 ≠ n2 ∧
    lookup_name_typed st n2 = SOME (tv, w) ⇒
    lookup_name_typed (update_name st n1 v) n2 = SOME (tv, w) ∧
    (update_name st n1 v).scopes ≠ [] ∧
    var_in_scope (update_name st n1 v) n2
Proof
  rpt gen_tac >> strip_tac >>
  gvs[lookup_name_typed_preserved_after_update, scopes_nonempty_after_update,
      var_in_scope_lookup_name_typed, lookup_name_typed_preserved_after_update]
QED

Theorem update_name_frame:
  ∀st n1 n2 v w.
    n1 ≠ n2 ∧
    lookup_name st n2 = SOME w ⇒
    lookup_name (update_name st n1 v) n2 = SOME w ∧
    (update_name st n1 v).scopes ≠ [] ∧
    var_in_scope (update_name st n1 v) n2
Proof
  rpt gen_tac >> strip_tac >>
  `∃tv. lookup_name_typed st n2 = SOME (tv, w)` by
    metis_tac[lookup_name_SOME] >>
  imp_res_tac update_name_typed_frame >>
  gvs[lookup_name_typed_to_lookup_name]
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

(* TODO: this should be encapsulated more, with declare_name probably *)

Theorem lookup_name_typed_fempty_prepend:
  ∀st n.
    lookup_name_typed (st with scopes := FEMPTY :: st.scopes) n =
    lookup_name_typed st n
Proof
  simp[lookup_name_typed_def, lookup_scopes_def, finite_mapTheory.FLOOKUP_DEF]
QED

Theorem lookup_name_fempty_prepend:
  ∀st n.
    lookup_name (st with scopes := FEMPTY :: st.scopes) n =
    lookup_name st n
Proof
  simp[lookup_name_typed_to_lookup_name, lookup_name_typed_fempty_prepend]
QED

Theorem var_in_scope_fempty_prepend:
  ∀st n.
    var_in_scope (st with scopes := FEMPTY :: st.scopes) n ⇔
    var_in_scope st n
Proof
  simp[var_in_scope_def, lookup_name_fempty_prepend]
QED

Theorem fcs_fempty[local]:
  ∀ni rest.
    find_containing_scope ni (FEMPTY :: rest) =
    OPTION_MAP (λ(pre,env,tv,v,post). (FEMPTY::pre,env,tv,v,post))
               (find_containing_scope ni rest)
Proof
  simp[find_containing_scope_def, finite_mapTheory.FLOOKUP_DEF] >>
  rpt gen_tac >>
  Cases_on `find_containing_scope ni rest` >> simp[] >>
  PairCases_on `x` >> simp[]
QED

Theorem update_name_fempty:
  ∀st n v.
    var_in_scope st n ⇒
    update_name (st with scopes := FEMPTY :: st.scopes) n v =
    (update_name st n v) with scopes :=
      FEMPTY :: (update_name st n v).scopes
Proof
  simp[update_name_def, var_in_scope_def, lookup_name_def] >>
  rpt strip_tac >>
  `IS_SOME (find_containing_scope (string_to_num n) st.scopes)` by
    (irule lookup_scopes_find_containing >> simp[]) >>
  Cases_on `find_containing_scope (string_to_num n) st.scopes` >> gvs[] >>
  PairCases_on `x` >>
  simp[find_containing_scope_def, evaluation_state_component_equality]
QED

(* ============================================================ *)
(* declare_name lemmas *)

Theorem declare_name_preserves_length:
  ∀st n tyv v.
    st.scopes ≠ [] ⇒
    LENGTH (declare_name st n tyv v).scopes = LENGTH st.scopes
Proof
  rw[declare_name_def] >> Cases_on `st.scopes` >> fs[]
QED

(* ===== lookup_name_typed after declare_name ===== *)

Theorem lookup_name_typed_after_declare:
  ∀st n tyv v.
    lookup_name_typed (declare_name st n tyv v) n = SOME (tyv, v)
Proof
  rpt strip_tac >>
  simp[lookup_name_typed_def, declare_name_def] >>
  Cases_on `st.scopes` >> gvs[] >>
  simp[lookup_scopes_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem lookup_after_declare:
  ∀st n tyv v.
    lookup_name (declare_name st n tyv v) n = SOME v
Proof
  simp[lookup_name_SOME] >> metis_tac[lookup_name_typed_after_declare]
QED

Theorem lookup_name_typed_preserved_after_declare:
  ∀st n1 n2 tyv v.
    n1 ≠ n2 ⇒
    lookup_name_typed (declare_name st n1 tyv v) n2 = lookup_name_typed st n2
Proof
  rpt strip_tac >>
  simp[lookup_name_typed_def, declare_name_def] >>
  Cases_on `st.scopes` >> gvs[] >>
  simp[lookup_scopes_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  gvs[vyperMiscTheory.string_to_num_inj]
QED

Theorem lookup_name_preserved_after_declare:
  ∀st n1 n2 tyv v.
    n1 ≠ n2 ⇒
    lookup_name (declare_name st n1 tyv v) n2 = lookup_name st n2
Proof
  simp[lookup_name_typed_to_lookup_name, lookup_name_typed_preserved_after_declare]
QED

Theorem scopes_nonempty_after_declare:
  ∀st n tyv v.
    (declare_name st n tyv v).scopes ≠ []
Proof
  rw[declare_name_def] >> Cases_on `st.scopes` >> fs[]
QED

Theorem var_in_scope_after_declare:
  ∀st n tyv v.
    var_in_scope (declare_name st n tyv v) n
Proof
  rw[var_in_scope_def, lookup_after_declare]
QED

Theorem var_in_scope_preserved_after_declare:
  ∀st n1 n2 tyv v.
    var_in_scope st n2 ⇒
    var_in_scope (declare_name st n1 tyv v) n2
Proof
  rw[var_in_scope_def] >>
  Cases_on `n1 = n2` >- (rw[lookup_after_declare]) >>
  rw[lookup_name_preserved_after_declare]
QED

Theorem update_name_declare_name_comm:
  ∀st n1 n2 tyv v v'.
    n1 ≠ n2 ∧ st.scopes ≠ [] ⇒
    update_name (declare_name st n1 tyv v) n2 v' =
    declare_name (update_name st n2 v') n1 tyv v
Proof
  rw[declare_name_def, update_name_def] >>
  Cases_on `st.scopes` >> fs[] >>
  rename1 `h :: t` >>
  `string_to_num n1 ≠ string_to_num n2` by
    metis_tac[vyperMiscTheory.string_to_num_inj] >>
  simp[Once find_containing_scope_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  Cases_on `FLOOKUP h (string_to_num n2)` >> simp[]
  >| [
    (* n2 not in head scope — recurse into tail *)
    simp[SimpR ``$=``, Once find_containing_scope_def] >>
    Cases_on `find_containing_scope (string_to_num n2) t` >> simp[]
    >- simp[Once find_containing_scope_def,
            evaluation_state_component_equality,
            finite_mapTheory.FUPDATE_COMMUTES,
            find_containing_scope_def]
    >> PairCases_on `x` >> simp[] >>
       simp[find_containing_scope_def, evaluation_state_component_equality],
    (* n2 in head scope *)
    PairCases_on `x` >> simp[] >>
    simp[Once find_containing_scope_def, finite_mapTheory.FLOOKUP_DEF,
         evaluation_state_component_equality,
         finite_mapTheory.FUPDATE_COMMUTES,
         find_containing_scope_def]
  ]
QED

Theorem lookup_name_typed_empty_scopes:
  ∀st n. st.scopes = [] ⇒ lookup_name_typed st n = NONE
Proof
  rpt strip_tac >>
  simp[lookup_name_typed_def, lookup_scopes_def]
QED

Theorem lookup_name_empty_scopes:
  ∀st n. st.scopes = [] ⇒ lookup_name st n = NONE
Proof
  simp[lookup_name_typed_to_lookup_name, lookup_name_typed_empty_scopes]
QED
