Theory vyperAssignTargetSpec

Ancestors
  vyperInterpreter

Definition assign_target_spec_def:
  assign_target_spec cx st (av : assignment_value) (ao : assign_operation) Q ⇔
    case assign_target cx av ao st of
    | (INL _, st') => Q st'
    | (INR _, _) => F
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

Definition is_valid_lookup_name_def:
  is_valid_lookup_name cx st n <=>
    IS_SOME (ALOOKUP st.globals cx.txn.target) ∧
    IS_SOME (lookup_name cx st n)
End

Definition lookup_toplevel_name_target_def:
  lookup_toplevel_name_target cx st n = lookup_base_target cx st (TopLevelNameTarget n)
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

(**********************************************************************)
(* Helper lemmas *)

Theorem lookup_scopes_to_lookup_name:
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

Theorem lookup_scopes_update_preserves:
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

Theorem ALOOKUP_set_module_globals_preserves:
  ∀al k v tgt. IS_SOME (ALOOKUP al tgt) ⇒ IS_SOME (ALOOKUP ((k, v) :: ADELKEY k al) tgt)
Proof
  rpt strip_tac >> Cases_on `k = tgt` >> simp[alistTheory.ALOOKUP_ADELKEY]
QED

Theorem assign_target_preserves_scopes:
  (∀cx av ao st res st'.
     assign_target cx av ao st = (INL res, st') ⇒
     (∀n. IS_SOME (lookup_scopes n st.scopes) ⇔ IS_SOME (lookup_scopes n st'.scopes))) ∧
  (∀cx gvs vs st res st'.
     assign_targets cx gvs vs st = (INL res, st') ⇒
     (∀n. IS_SOME (lookup_scopes n st.scopes) ⇔ IS_SOME (lookup_scopes n st'.scopes)))
Proof
  ho_match_mp_tac assign_target_ind >> rpt conj_tac >> rpt gen_tac >>
  simp[Once assign_target_def, bind_def, get_scopes_def, return_def,
       lift_option_def, lift_sum_def, AllCaseEqs(), raise_def, LET_THM,
       ignore_bind_def, set_scopes_def] >-
  ((* ScopedVar case *)
   simp[AllCaseEqs(), return_def, raise_def, bind_def, set_scopes_def] >>
   strip_tac >> gvs[] >>
   rpt (qpat_x_assum `(case _ of NONE => _ | SOME v => _) _ = _` mp_tac) >>
   simp[AllCaseEqs(), return_def, raise_def] >> rpt strip_tac >> gvs[] >>
   qpat_x_assum `(case find_containing_scope _ _ of _ => _ | _ => _) _ = _` mp_tac >>
   simp[AllCaseEqs(), return_def, raise_def] >> strip_tac >> gvs[] >>
   Cases_on `find_containing_scope (string_to_num id) st.scopes` >> gvs[return_def, raise_def] >>
   PairCases_on `x` >> gvs[bind_def, AllCaseEqs(), return_def, raise_def, set_scopes_def] >>
   `s''.scopes = x0 ++ [x1] ++ x3 ∧ FLOOKUP x1 (string_to_num id) = SOME x2`
     by (drule find_containing_scope_structure >> simp[]) >>
   metis_tac[lookup_scopes_update_preserves]) >-
  ((* TopLevelVar case *)
   strip_tac >> gvs[AllCaseEqs(), return_def, raise_def, lookup_global_def,
                    bind_def, get_current_globals_def, lift_option_def, LET_THM,
                    set_global_def, set_current_globals_def] >>
   rpt (qpat_x_assum `(case _ of _ => _ | _ => _) _ = _` mp_tac) >>
   simp[AllCaseEqs(), return_def, raise_def] >> rpt strip_tac >> gvs[] >>
   qpat_x_assum `(case ALOOKUP _ _ of _ => _ | _ => _) _ = _` mp_tac >>
   simp[AllCaseEqs(), return_def, raise_def] >> strip_tac >> gvs[] >>
   rpt (FIRST [qpat_x_assum `(case ALOOKUP _ _ of _ => _ | _ => _) _ = _` mp_tac,
               qpat_x_assum `(case assign_toplevel _ _ _ _ of _ => _ | _ => _) _ = _` mp_tac,
               qpat_x_assum `(case get_module_code _ _ of _ => _ | _ => _) _ = _` mp_tac,
               qpat_x_assum `(case FLOOKUP _ _ of _ => _ | _ => _) _ = _` mp_tac]) >>
   simp[AllCaseEqs(), return_def, raise_def] >> rpt strip_tac >> gvs[] >>
   gvs[AllCaseEqs(), return_def, raise_def] >>
   `st.scopes = s'⁵'.scopes` by (Cases_on `ALOOKUP st.globals cx.txn.target` >> gvs[return_def, raise_def]) >>
   `s'⁵'.scopes = s''.scopes` by (Cases_on `FLOOKUP (get_module_globals src_id_opt gbs).mutables (string_to_num id)` >> gvs[return_def, raise_def]) >>
   `s''.scopes = s'³'.scopes` by (Cases_on `get_module_code cx src_id_opt` >> gvs[return_def, raise_def]) >>
   `s'³'.scopes = s'⁴'.scopes` by (Cases_on `assign_toplevel (type_env ts) res (REVERSE is) ao` >> gvs[return_def, raise_def]) >>
   `s'⁴'.scopes = s'⁶'.scopes` by (Cases_on `ALOOKUP s'⁴'.globals cx.txn.target` >> gvs[return_def, raise_def]) >>
   gvs[]) >-
  ((* ImmutableVar case *)
   strip_tac >> gvs[get_immutables_def, get_immutables_module_def, bind_def,
                    get_current_globals_def, lift_option_def, AllCaseEqs(), return_def,
                    raise_def, LET_THM, set_immutable_def, set_current_globals_def] >>
   `st.scopes = s''.scopes` by (Cases_on `ALOOKUP st.globals cx.txn.target` >> gvs[return_def, raise_def]) >>
   `s''.scopes = s'³'.scopes` by (Cases_on `FLOOKUP (get_module_globals NONE gbs).immutables (string_to_num id)` >> gvs[return_def, raise_def]) >>
   `s'³'.scopes = s'⁴'.scopes` by (Cases_on `assign_subscripts a (REVERSE is) ao` >> gvs[return_def, raise_def]) >>
   `s'⁴'.scopes = s'⁶'.scopes` by (Cases_on `ALOOKUP s'⁴'.globals cx.txn.target` >> gvs[return_def, raise_def]) >>
   gvs[]) >-
  ((* TupleTargetV case *)
   rpt strip_tac >> gvs[check_def, AllCaseEqs(), return_def, raise_def] >>
   first_x_assum drule >> simp[] >>
   strip_tac >> gvs[assert_def, AllCaseEqs(), return_def, raise_def]) >-
  ((* assign_targets cons case *)
   rpt strip_tac >> gvs[get_Value_def, AllCaseEqs(), return_def, raise_def] >>
   Cases_on `tw` >> gvs[get_Value_def, return_def, raise_def] >>
   first_x_assum (qspec_then `s''` mp_tac) >> simp[] >>
   first_x_assum drule >> simp[])
QED

(* Combined theorem proving both globals and immutables preservation.
   These must be proven together to avoid circular dependency in the
   assign_targets cons case.
   
   NOTE: The proof was developed interactively (see PLAN.md for the full proof
   script). The >~ pattern matching syntax doesn't work correctly with the
   many cases generated by assign_target_ind, so we use positional >- tactics. *)
Theorem assign_target_preserves_globals_and_immutables:
  (∀cx av ao st res st'.
     assign_target cx av ao st = (INL res, st') ⇒
     (∀tgt. IS_SOME (ALOOKUP st.globals tgt) ⇒ IS_SOME (ALOOKUP st'.globals tgt)) ∧
     (∀n gbs gbs'.
        ALOOKUP st.globals cx.txn.target = SOME gbs ∧
        ALOOKUP st'.globals cx.txn.target = SOME gbs' ⇒
        IS_SOME (FLOOKUP (get_module_globals NONE gbs).immutables n) =
        IS_SOME (FLOOKUP (get_module_globals NONE gbs').immutables n))) ∧
  (∀cx gvs vs st res st'.
     assign_targets cx gvs vs st = (INL res, st') ⇒
     (∀tgt. IS_SOME (ALOOKUP st.globals tgt) ⇒ IS_SOME (ALOOKUP st'.globals tgt)) ∧
     (∀n gbs gbs'.
        ALOOKUP st.globals cx.txn.target = SOME gbs ∧
        ALOOKUP st'.globals cx.txn.target = SOME gbs' ⇒
        IS_SOME (FLOOKUP (get_module_globals NONE gbs).immutables n) =
        IS_SOME (FLOOKUP (get_module_globals NONE gbs').immutables n)))
Proof
  cheat (* TODO: See PLAN.md for the full proof script *)
QED

(* Derived: assign_target preserves immutables *)
Theorem assign_target_preserves_immutables:
  (∀cx av ao st res st'.
     assign_target cx av ao st = (INL res, st') ⇒
     ∀n gbs gbs'.
       ALOOKUP st.globals cx.txn.target = SOME gbs ∧
       ALOOKUP st'.globals cx.txn.target = SOME gbs' ⇒
       IS_SOME (FLOOKUP (get_module_globals NONE gbs).immutables n) =
       IS_SOME (FLOOKUP (get_module_globals NONE gbs').immutables n)) ∧
  (∀cx gvs vs st res st'.
     assign_targets cx gvs vs st = (INL res, st') ⇒
     ∀n gbs gbs'.
       ALOOKUP st.globals cx.txn.target = SOME gbs ∧
       ALOOKUP st'.globals cx.txn.target = SOME gbs' ⇒
       IS_SOME (FLOOKUP (get_module_globals NONE gbs).immutables n) =
       IS_SOME (FLOOKUP (get_module_globals NONE gbs').immutables n))
Proof
  metis_tac[assign_target_preserves_globals_and_immutables]
QED

(* Derived: assign_target preserves globals existence *)
Theorem assign_target_preserves_globals:
  (∀cx av ao st res st'.
     assign_target cx av ao st = (INL res, st') ⇒
     IS_SOME (ALOOKUP st.globals cx.txn.target) ⇒
     IS_SOME (ALOOKUP st'.globals cx.txn.target)) ∧
  (∀cx gvs vs st res st'.
     assign_targets cx gvs vs st = (INL res, st') ⇒
     IS_SOME (ALOOKUP st.globals cx.txn.target) ⇒
     IS_SOME (ALOOKUP st'.globals cx.txn.target))
Proof
  metis_tac[assign_target_preserves_globals_and_immutables]
QED

(**********************************************************************)

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

Theorem assign_target_spec_preserves_name_targets:
  ∀P cx st av ao n.
    IS_SOME (ALOOKUP st.globals cx.txn.target) ∧
    lookup_name_target cx st n = SOME av' ∧
    assign_target_spec cx st av ao P ⇒
    assign_target_spec cx st av ao (λst'. P st' ∧ lookup_name_target cx st' n = SOME av')
Proof
  cheat
QED

Theorem assign_target_spec_lookup:
  ∀cx st n av v.
    is_valid_lookup_name cx st n ∧
    lookup_name_target cx st n = SOME av ⇒
    assign_target_spec cx st av (Replace v) P ⇒
    assign_target_spec cx st av (Replace v) (λst'. P st' ∧ lookup_name cx st' n = SOME v)
Proof
  simp[is_valid_lookup_name_def, lookup_name_target_def, lookup_base_target_def,
       assign_target_spec_def, lookup_name_def, AllCaseEqs()] >>
  rpt strip_tac >> Cases_on `ALOOKUP st.globals cx.txn.target` >- fs[] >>
  gvs[] >>
  Cases_on `assign_target cx (BaseTargetV loc sbs) (Replace v) st` >>
  Cases_on `q` >-
  (* assign_target succeeded *)
  (gvs[] >>
   qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
   simp[Once evaluate_def, bind_def, get_scopes_def, return_def] >>
   Cases_on `cx.txn.is_creation` >-
   (* is_creation = T *)
   (gvs[return_def, get_immutables_def, get_immutables_module_def, bind_def,
        get_current_globals_def, lift_option_def, return_def, lift_sum_def,
        immutable_target_def] >>
    Cases_on `IS_SOME (lookup_scopes (string_to_num n) st.scopes)` >>
    Cases_on `FLOOKUP (get_module_globals NONE x).immutables (string_to_num n)` >>
    gvs[exactly_one_option_def, return_def, raise_def] >-
    (* ScopedVar case *)
    (strip_tac >> gvs[] >>
     qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
     simp[Once assign_target_def, bind_def, get_scopes_def, return_def, lift_option_def] >>
     `IS_SOME (find_containing_scope (string_to_num n) st.scopes)`
       by metis_tac[lookup_scopes_find_containing] >>
     Cases_on `find_containing_scope (string_to_num n) st.scopes` >>
     gvs[return_def, raise_def] >> PairCases_on `x''` >>
     simp[bind_def, lift_sum_def, assign_subscripts_def, return_def,
          set_scopes_def, ignore_bind_def] >>
     strip_tac >> gvs[] >>
     `lookup_scopes (string_to_num n) x''0 = NONE`
       by metis_tac[find_containing_scope_pre_none] >>
     `lookup_scopes (string_to_num n) (x''0 ++ x''1 |+ (string_to_num n,v)::x''3) = SOME v`
       by metis_tac[lookup_scopes_update] >>
     simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
          get_immutables_def, get_immutables_module_def, get_current_globals_def,
          lift_option_def, lift_sum_def, exactly_one_option_def, return_def]) >>
    (* ImmutableVar case *)
    strip_tac >> gvs[] >>
    qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
    simp[Once assign_target_def, bind_def, get_scopes_def, return_def,
         lift_option_def, get_immutables_def, get_immutables_module_def,
         get_current_globals_def, lift_sum_def, assign_subscripts_def,
         return_def, ignore_bind_def, set_immutable_def,
         lift_option_def, set_current_globals_def] >>
    strip_tac >> gvs[] >>
    simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
         get_immutables_def, get_immutables_module_def, get_current_globals_def,
         lift_option_def, get_module_globals_def, set_module_globals_def,
         finite_mapTheory.FLOOKUP_UPDATE, lift_sum_def,
         exactly_one_option_def, return_def]) >>
   (* is_creation = F *)
   gvs[return_def, lift_sum_def] >>
   Cases_on `IS_SOME (lookup_scopes (string_to_num n) st.scopes)` >>
   gvs[exactly_one_option_def, return_def, raise_def] >>
   strip_tac >> gvs[] >>
   qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
   simp[Once assign_target_def, bind_def, get_scopes_def, return_def, lift_option_def] >>
   `IS_SOME (find_containing_scope (string_to_num n) st.scopes)`
     by metis_tac[lookup_scopes_find_containing] >>
   Cases_on `find_containing_scope (string_to_num n) st.scopes` >>
   gvs[return_def, raise_def] >> PairCases_on `x''` >>
   simp[bind_def, lift_sum_def, assign_subscripts_def, return_def,
        set_scopes_def, ignore_bind_def] >>
   strip_tac >> gvs[] >>
   `lookup_scopes (string_to_num n) x''0 = NONE`
     by metis_tac[find_containing_scope_pre_none] >>
   `lookup_scopes (string_to_num n) (x''0 ++ x''1 |+ (string_to_num n,v)::x''3) = SOME v`
     by metis_tac[lookup_scopes_update] >>
   simp[Once evaluate_def, bind_def, get_scopes_def, return_def] >>
   simp[get_immutables_def, get_immutables_module_def, bind_def,
        get_current_globals_def, lift_option_def, return_def, lift_sum_def] >>
   Cases_on `FLOOKUP (get_module_globals NONE x).immutables (string_to_num n)` >-
   simp[exactly_one_option_def, return_def] >>
   (* Contradiction: both scopes and immutables have the var, but original eval_expr succeeded *)
   fs[Once evaluate_def, bind_def, get_scopes_def, return_def,
      get_immutables_def, get_immutables_module_def, get_current_globals_def,
      lift_option_def, lift_sum_def, exactly_one_option_def, return_def, raise_def] >>
   Cases_on `lookup_scopes (string_to_num n) st.scopes` >> gvs[] >>
   gvs[exactly_one_option_def, return_def, raise_def]) >>
  (* assign_target failed *)
  simp[] >> fs[]
QED

Theorem assign_target_spec_update:
  ∀cx st n bop av v1 v2 v.
    lookup_name cx st n = SOME v1 ∧
    lookup_name_target cx st n = SOME av ∧
    evaluate_binop bop v1 v2 = INL v ∧
    assign_target_spec cx st av (Update bop v2) P ⇒
    assign_target_spec cx st av (Update bop v2) (λst'. P st' ∧ lookup_name cx st' n = SOME v)
Proof
  simp[assign_target_spec_def, lookup_name_target_def, lookup_base_target_def,
       lookup_name_def, AllCaseEqs()] >>
  rpt strip_tac >>
  Cases_on `assign_target cx av (Update bop v2) st` >> Cases_on `q` >> gvs[] >>
  (* Analyze eval_base_target *)
  qpat_x_assum `eval_base_target _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def] >>
  Cases_on `cx.txn.is_creation` >-
  (* is_creation = T *)
  (gvs[return_def, get_immutables_def, get_immutables_module_def, bind_def,
       get_current_globals_def, lift_option_def, return_def, lift_sum_def,
       immutable_target_def] >>
   Cases_on `ALOOKUP st.globals cx.txn.target` >> gvs[raise_def, return_def] >>
   Cases_on `IS_SOME (lookup_scopes (string_to_num n) st.scopes)` >>
   Cases_on `FLOOKUP (get_module_globals NONE x').immutables (string_to_num n)` >>
   gvs[exactly_one_option_def, return_def, raise_def] >-
   (* ScopedVar case *)
   (strip_tac >> gvs[] >>
    qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
    simp[Once assign_target_def, bind_def, get_scopes_def, return_def, lift_option_def] >>
    `IS_SOME (find_containing_scope (string_to_num n) st.scopes)`
      by metis_tac[lookup_scopes_find_containing] >>
    Cases_on `find_containing_scope (string_to_num n) st.scopes` >>
    gvs[return_def, raise_def] >> PairCases_on `x''` >>
    simp[bind_def, lift_sum_def, assign_subscripts_def, set_scopes_def,
         ignore_bind_def, return_def] >>
    `lookup_scopes (string_to_num n) st.scopes = SOME x''2`
      by metis_tac[find_containing_scope_lookup] >>
    (* Show x''2 = v1 *)
    `x''2 = v1` by (
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
           get_immutables_def, get_immutables_module_def, get_current_globals_def,
           lift_option_def, lift_sum_def, exactly_one_option_def, return_def, raise_def]) >>
    gvs[return_def, raise_def] >>
    strip_tac >> gvs[] >>
    `lookup_scopes (string_to_num n) x''0 = NONE`
      by metis_tac[find_containing_scope_pre_none] >>
    `lookup_scopes (string_to_num n) (x''0 ++ x''1 |+ (string_to_num n,v)::x''3) = SOME v`
      by metis_tac[lookup_scopes_update] >>
    simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
         get_immutables_def, get_immutables_module_def, get_current_globals_def,
         lift_option_def, lift_sum_def, exactly_one_option_def, return_def]) >>
   (* ImmutableVar case *)
   strip_tac >> gvs[] >>
   qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
   simp[Once assign_target_def, bind_def, get_scopes_def, return_def,
        lift_option_def, get_immutables_def, get_immutables_module_def,
        get_current_globals_def, lift_sum_def, assign_subscripts_def,
        return_def, ignore_bind_def, set_immutable_def, set_current_globals_def] >>
   (* Show x'' = v1 *)
   `x'' = v1` by (
     qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
     simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
          get_immutables_def, get_immutables_module_def, get_current_globals_def,
          lift_option_def, lift_sum_def, exactly_one_option_def, return_def, raise_def]) >>
   gvs[return_def, raise_def] >>
   strip_tac >> gvs[] >>
   simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
        get_immutables_def, get_immutables_module_def, get_current_globals_def,
        lift_option_def, get_module_globals_def, set_module_globals_def,
        finite_mapTheory.FLOOKUP_UPDATE, lift_sum_def,
        exactly_one_option_def, return_def]) >>
  (* is_creation = F *)
  gvs[return_def, lift_sum_def] >>
  Cases_on `IS_SOME (lookup_scopes (string_to_num n) st.scopes)` >>
  gvs[exactly_one_option_def, return_def, raise_def] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `assign_target _ _ _ _ = _` mp_tac >>
  simp[Once assign_target_def, bind_def, get_scopes_def, return_def, lift_option_def] >>
  `IS_SOME (find_containing_scope (string_to_num n) st.scopes)`
    by metis_tac[lookup_scopes_find_containing] >>
  Cases_on `find_containing_scope (string_to_num n) st.scopes` >>
  gvs[return_def, raise_def] >> PairCases_on `x'` >>
  simp[bind_def, lift_sum_def, assign_subscripts_def, set_scopes_def,
       ignore_bind_def, return_def] >>
  `lookup_scopes (string_to_num n) st.scopes = SOME x'2`
    by metis_tac[find_containing_scope_lookup] >>
  (* Show x'2 = v1 *)
  `x'2 = v1` by (
    qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
    simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
         get_immutables_def, get_immutables_module_def, get_current_globals_def,
         lift_option_def, lift_sum_def, exactly_one_option_def, return_def, raise_def] >>
    Cases_on `ALOOKUP st.globals cx.txn.target` >> gvs[return_def, raise_def] >>
    Cases_on `FLOOKUP (get_module_globals NONE x).immutables (string_to_num n)` >>
    gvs[exactly_one_option_def, return_def, raise_def]) >>
  gvs[return_def, raise_def] >>
  strip_tac >> gvs[] >>
  `lookup_scopes (string_to_num n) x'0 = NONE`
    by metis_tac[find_containing_scope_pre_none] >>
  `lookup_scopes (string_to_num n) (x'0 ++ x'1 |+ (string_to_num n,v)::x'3) = SOME v`
    by metis_tac[lookup_scopes_update] >>
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
       get_immutables_def, get_immutables_module_def, get_current_globals_def,
       lift_option_def, lift_sum_def, exactly_one_option_def, return_def] >>
  Cases_on `ALOOKUP st.globals cx.txn.target` >> gvs[raise_def, return_def] >-
  (qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
   simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
        get_immutables_def, get_immutables_module_def, get_current_globals_def,
        lift_option_def, lift_sum_def, exactly_one_option_def, return_def, raise_def]) >>
  Cases_on `FLOOKUP (get_module_globals NONE x).immutables (string_to_num n)` >-
  simp[exactly_one_option_def, return_def] >>
  (* Contradiction: both scopes and immutables have the var *)
  fs[Once evaluate_def, bind_def, get_scopes_def, return_def,
     get_immutables_def, get_immutables_module_def, get_current_globals_def,
     lift_option_def, lift_sum_def, exactly_one_option_def, return_def, raise_def]
QED
