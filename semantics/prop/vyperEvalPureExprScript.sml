Theory vyperEvalPureExpr

Ancestors
  vyperPureExpr vyperLookup vyperState vyperStatePreservation vyperPlaceFrames

(* ===== eval_pure_expr / eval_pure_exprs ===== *)
(*
  eval_pure_expr  : cx -> st -> expr -> eval_result option
  eval_pure_exprs : cx -> st -> expr list -> value list option

  eval_pure_expr evaluates a pure expression to the same result as eval_expr.
  Locations stay unresolved until an operation needs their contents.

  eval_pure_exprs evaluates a list of pure expressions, materialising
  each result to a value (reading from storage if needed).
*)

Definition eval_pure_expr_def:
  (* Base cases *)
  eval_pure_expr cx st (Name _ id) =
    (if IS_SOME (lookup_scopes id st.scopes)
     then SOME (PlaceR (MemoryPlace id [])) else NONE) ∧

  eval_pure_expr cx st (TopLevelName ty nsid) =
    (case eval_expr cx (TopLevelName ty nsid) st of
     | (INL tv, _) => SOME tv
     | _ => NONE) ∧

  eval_pure_expr cx st (FlagMember _ nsid mid) =
    lookup_flag_member cx nsid mid ∧

  eval_pure_expr cx st (Literal _ l) =
    SOME (Value (evaluate_literal l)) ∧

  (* Conditional *)
  eval_pure_expr cx st (IfExp _ cond et ef) =
    (case eval_pure_expr cx st cond of
     | SOME res =>
       (case read_result cx res st of
        | (INL (BoolV b), _) =>
          (case (if b then eval_pure_expr cx st et else eval_pure_expr cx st ef) of
           | SOME selected =>
             (case conditional_result cx selected st of
              | (INL result, _) => SOME result
              | _ => NONE)
           | NONE => NONE)
        | _ => NONE)
     | NONE => NONE) ∧

  (* Struct literal *)
  eval_pure_expr cx st (StructLit _ src kes) =
    (case eval_pure_exprs cx st (MAP SND kes) of
     | SOME vs => SOME (Value (StructV (ZIP (MAP FST kes, vs))))
     | NONE => NONE) ∧

  (* Subscript *)
  eval_pure_expr cx st (Subscript ty e1 e2) =
    (case eval_pure_expr cx st e1 of
     | SOME tv1 =>
       (case eval_pure_expr cx st e2 of
        | SOME idx =>
          (case read_result cx idx st of
           | (INL v2, _) =>
             (case select_result cx (expr_type e1) tv1 (ValueSubscript v2) st of
              | (INL result, _) => SOME result
              | _ => NONE)
           | _ => NONE)
        | _ => NONE)
     | NONE => NONE) ∧

  (* Attribute access *)
  eval_pure_expr cx st (Attribute _ e id) =
    (case eval_pure_expr cx st e of
     | SOME res =>
       (case select_result cx (expr_type e) res (AttrSubscript id) st of
        | (INL result, _) => SOME result
        | _ => NONE)
     | _ => NONE) ∧

  (* General builtins *)
  eval_pure_expr cx st (Builtin ty bt es) =
    (if bt = Len then
       (case es of
        | [e] =>
          (case eval_pure_expr cx st e of
           | SOME tv =>
             (case result_array_length cx tv st of
              | (INL len, _) => SOME (Value (IntV (&len)))
              | _ => NONE)
           | NONE => NONE)
        | _ => NONE)
     else if builtin_args_length_ok bt (LENGTH es) then
       (case eval_pure_exprs cx st es of
        | SOME vs =>
          (if bt = Bop In ∨ bt = Bop NotIn then
             if LENGTH vs = 2 then
               (case evaluate_type (get_tenv cx) (expr_type (EL 1 es)) of
                | NONE => NONE
                | SOME tv =>
                    (case evaluate_membership tv (bt = Bop NotIn) (HD vs) (EL 1 vs) of
                     | INL v => SOME (Value v)
                     | INR _ => NONE))
             else NONE
           else
             case evaluate_builtin cx st.accounts ty bt (MAP expr_type es) vs of
             | INL v => SOME (Value v)
             | INR _ => NONE)
        | NONE => NONE)
     else NONE) ∧

  (* General type builtins *)
  eval_pure_expr cx st (TypeBuiltin _ tb typ es) =
    (if type_builtin_args_length_ok tb (LENGTH es) then
       (case eval_pure_exprs cx st es of
        | SOME vs =>
          (case evaluate_type_builtin cx tb typ (MAP expr_type es) vs of
           | INL v => SOME (Value v)
           | INR _ => NONE)
        | NONE => NONE)
     else NONE) ∧

  (* Non-pure expressions *)
  eval_pure_expr cx st _ = NONE ∧

  (* eval_pure_exprs: evaluate list, materialising each result *)
  eval_pure_exprs cx st [] = SOME [] ∧

  eval_pure_exprs cx st (e::es) =
    (case eval_pure_expr cx st e of
     | SOME tv =>
       (case read_result cx tv st of
        | (INL v, _) =>
          (case eval_pure_exprs cx st es of
           | SOME vs => SOME (v::vs)
           | NONE => NONE)
        | _ => NONE)
     | NONE => NONE)
Termination
  WF_REL_TAC `measure (sum_size
    (\(cx:evaluation_context, st:evaluation_state, e). expr_size e)
    (\(cx:evaluation_context, st:evaluation_state, es).
       list_size expr_size es))` >>
  rpt gen_tac >>
  Induct_on `kes` >>
  simp[pairTheory.FORALL_PROD, basicSizeTheory.pair_size_def]
End

(* Convenience wrapper: evaluate pure expression to value *)
Definition eval_pure_value_def:
  eval_pure_value cx st e =
    (case eval_pure_expr cx st e of
     | SOME tv =>
       (case read_result cx tv st of
        | (INL v, _) => SOME v
        | _ => NONE)
     | NONE => NONE)
End

val monadic_defs =
  [vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_def,
   vyperStateTheory.return_def,
   vyperStateTheory.lift_sum_def, vyperStateTheory.get_scopes_def,
   vyperStateTheory.get_accounts_def, vyperStateTheory.type_check_def,
   vyperStateTheory.assert_def, vyperStateTheory.raise_def];

(* ===== Forward direction: eval_pure_expr/exprs SOME ⇒ eval_expr/exprs INL ===== *)

Theorem eval_pure_to_eval_mutual:
  (∀cx st e v.
    eval_pure_expr cx st e = SOME v ⇒
    eval_expr cx e st = (INL v, st)) ∧
  (∀cx st es vs.
    eval_pure_exprs cx st es = SOME vs ⇒
    eval_exprs cx es st = (INL vs, st))
Proof
  ho_match_mp_tac eval_pure_expr_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac
  (* Name *)
  >- (gvs[Once eval_pure_expr_def] >>
      simp[Once vyperInterpreterTheory.evaluate_def,
           vyperStateTheory.get_scopes_def, vyperStateTheory.type_check_def,
           vyperStateTheory.assert_def] >> simp monadic_defs)
  (* TopLevelName *)
  >- (fs[Once eval_pure_expr_def] >>
      Cases_on `eval_expr cx (TopLevelName ty nsid) st` >>
      gvs[AllCaseEqs()] >>
      drule_at Any eval_expr_preserves_state >> simp[pure_expr_def])
  (* FlagMember *)
  >- (fs[Once eval_pure_expr_def,
         Once vyperInterpreterTheory.evaluate_def] >>
      metis_tac[lookup_flag_member_to_lookup_flag_mem])
  (* Literal *)
  >- (fs[Once eval_pure_expr_def,
         Once vyperInterpreterTheory.evaluate_def] >>
      simp monadic_defs)
  (* IfExp *)
  >- (rpt gen_tac >>
      simp[Once eval_pure_expr_def] >> strip_tac >>
      simp[Once vyperInterpreterTheory.evaluate_def] >>
      simp monadic_defs >> gvs[AllCaseEqs()] >>
      imp_res_tac read_result_state >>
      imp_res_tac conditional_result_state >> gvs[] >>
      simp[vyperInterpreterTheory.switch_BoolV_def] >>
      simp monadic_defs)
  (* StructLit *)
  >- (rpt gen_tac >>
      simp[Once eval_pure_expr_def] >> strip_tac >>
      gvs[AllCaseEqs()] >>
      simp[Once vyperInterpreterTheory.evaluate_def] >>
      simp monadic_defs >>
      Cases_on `src` >> simp[LET_DEF] >>
      simp[Once vyperInterpreterTheory.evaluate_def] >>
      simp (LET_DEF :: monadic_defs))
  (* Subscript *)
  >- (rpt gen_tac >>
      simp[Once eval_pure_expr_def] >> strip_tac >>
      gvs[AllCaseEqs()] >>
      imp_res_tac read_result_state >>
      imp_res_tac select_result_state >> gvs[] >>
      simp[Once vyperInterpreterTheory.evaluate_def] >>
      simp monadic_defs)
  (* Attribute *)
  >- (rpt gen_tac >>
      simp[Once eval_pure_expr_def] >> strip_tac >>
      gvs[AllCaseEqs()] >>
      imp_res_tac select_result_state >> gvs[] >>
      simp[Once vyperInterpreterTheory.evaluate_def] >>
      simp monadic_defs)
  (* Builtin *)
  >- (rpt gen_tac >>
      simp[Once eval_pure_expr_def] >> strip_tac >>
      simp[Once vyperInterpreterTheory.evaluate_def] >>
      simp monadic_defs >>
      simp[vyperStateTheory.type_check_def, vyperStateTheory.assert_def] >>
      gvs[AllCaseEqs()] >>
      simp monadic_defs >>
      imp_res_tac result_array_length_state >>
      simp[vyperContextTheory.builtin_args_length_ok_def] >>
      simp[vyperStateTheory.get_accounts_def] >>
      simp monadic_defs >>
      simp[vyperStateTheory.assert_def, vyperStateTheory.return_def])
  (* TypeBuiltin *)
  >- (rpt gen_tac >>
      simp[Once eval_pure_expr_def] >> strip_tac >>
      gvs[AllCaseEqs()] >>
      simp[Once vyperInterpreterTheory.evaluate_def] >>
      simp monadic_defs >>
      simp[vyperStateTheory.type_check_def, vyperStateTheory.assert_def] >>
      simp monadic_defs)
  (* Pop - impossible *)
  >- fs[eval_pure_expr_def]
  (* Call - impossible *)
  >- fs[eval_pure_expr_def]
  (* [] case *)
  >- (fs[Once eval_pure_expr_def, Once vyperInterpreterTheory.evaluate_def] >>
      simp monadic_defs)
  (* e::es case *)
  >- (rpt gen_tac >>
      simp[Once eval_pure_expr_def] >> strip_tac >>
      gvs[AllCaseEqs()] >>
      simp[Once vyperInterpreterTheory.evaluate_def] >>
      simp monadic_defs >>
      drule read_result_state >> simp[])
QED

Theorem eval_pure_expr_to_eval_expr_some:
  ∀cx st e v.
    eval_pure_expr cx st e = SOME v ⇒
    eval_expr cx e st = (INL v, st)
Proof
  metis_tac[eval_pure_to_eval_mutual]
QED

Theorem eval_expr_to_eval_pure_expr_none:
  ∀cx st st' e err.
    eval_expr cx e st = (INR err, st') ⇒
    eval_pure_expr cx st e = NONE
Proof
  rpt strip_tac >>
  CCONTR_TAC >> gvs[] >>
  Cases_on `eval_pure_expr cx st e` >> gvs[] >>
  drule (eval_pure_to_eval_mutual |> CONJUNCT1) >> gvs[]
QED

(* ===== Reverse direction: eval_expr/exprs INL ⇒ eval_pure_expr/exprs SOME ===== *)

Theorem eval_to_eval_pure_mutual:
  (∀cx st e. ∀st' v.
    pure_expr e ∧ eval_expr cx e st = (INL v, st') ⇒
    eval_pure_expr cx st e = SOME v) ∧
  (∀cx st es. ∀st' vs.
    EVERY pure_expr es ∧ eval_exprs cx es st = (INL vs, st') ⇒
    eval_pure_exprs cx st es = SOME vs)
Proof
  ho_match_mp_tac eval_pure_expr_ind >>
  rpt conj_tac
  (* Name *)
  >- (rpt gen_tac >> strip_tac >>
      gvs[Once vyperInterpreterTheory.evaluate_def] >>
      gvs monadic_defs >>
      gvs[AllCaseEqs()] >> simp[Once eval_pure_expr_def])
  (* TopLevelName *)
  >- (rpt gen_tac >> strip_tac >>
      simp[Once eval_pure_expr_def] >>
      Cases_on `eval_expr cx (TopLevelName ty nsid) st` >>
      gvs[AllCaseEqs()])
  (* FlagMember *)
  >- (rpt gen_tac >> strip_tac >>
      simp[Once eval_pure_expr_def] >>
      gvs[Once vyperInterpreterTheory.evaluate_def] >>
      irule lookup_flag_mem_to_lookup_flag_member_some >>
      metis_tac[])
  (* Literal *)
  >- (rpt gen_tac >> strip_tac >>
      simp[Once eval_pure_expr_def] >>
      gvs[Once vyperInterpreterTheory.evaluate_def] >>
      gvs monadic_defs)
  (* IfExp *)
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      simp[Once eval_pure_expr_def] >>
      gvs[pure_expr_def] >>
      qpat_x_assum `eval_expr _ (IfExp _ _ _ _) _ = _` mp_tac >>
      simp[Once vyperInterpreterTheory.evaluate_def] >>
      simp monadic_defs >>
      strip_tac >> gvs[AllCaseEqs()] >>
      imp_res_tac eval_expr_preserves_state >> gvs[] >>
      gvs monadic_defs >> gvs[AllCaseEqs()] >>
      imp_res_tac read_result_state >> gvs[] >>
      gvs[vyperInterpreterTheory.switch_BoolV_def] >>
      gvs monadic_defs >> gvs[AllCaseEqs()] >>
      imp_res_tac eval_expr_preserves_state >> gvs[] >>
      imp_res_tac conditional_result_state >>
      imp_res_tac read_result_state >> gvs[] >>
      Cases_on `v'' = BoolV T` >> gvs monadic_defs >>
      Cases_on `v'' = BoolV F` >> gvs monadic_defs >>
      gvs[AllCaseEqs()] >> metis_tac[])
  (* StructLit *)
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      simp[Once eval_pure_expr_def] >>
      gvs[pure_expr_def] >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      Cases_on `src` >>
      simp[Once vyperInterpreterTheory.evaluate_def, LET_DEF] >>
      simp monadic_defs >>
      strip_tac >> gvs[AllCaseEqs()] >>
      `EVERY pure_expr (MAP SND kes)` by gvs[listTheory.EVERY_EL] >>
      gvs[])
  (* Subscript *)
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      simp[Once eval_pure_expr_def] >>
      gvs[pure_expr_def] >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once vyperInterpreterTheory.evaluate_def] >>
      simp monadic_defs >>
      strip_tac >> gvs[AllCaseEqs()] >>
      `s'' = st` by metis_tac[eval_expr_preserves_state, pure_expr_def] >>
      pop_assum SUBST_ALL_TAC >>
      `s'³' = st` by metis_tac[eval_expr_preserves_state, pure_expr_def] >>
      pop_assum SUBST_ALL_TAC >>
      imp_res_tac read_result_state >>
      imp_res_tac select_result_state >> gvs[])
  (* Attribute *)
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      simp[Once eval_pure_expr_def] >>
      gvs[pure_expr_def] >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once vyperInterpreterTheory.evaluate_def] >>
      simp monadic_defs >>
      strip_tac >> gvs[AllCaseEqs()] >>
      `s'' = st` by metis_tac[eval_expr_preserves_state, pure_expr_def] >>
      pop_assum SUBST_ALL_TAC >>
      imp_res_tac select_result_state >> gvs[])
  (* Builtin *)
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      simp[Once eval_pure_expr_def] >>
      gvs[pure_expr_def] >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once vyperInterpreterTheory.evaluate_def] >>
      simp monadic_defs >>
      simp[vyperStateTheory.type_check_def, vyperStateTheory.assert_def] >>
      strip_tac >> gvs[AllCaseEqs()] >>
      Cases_on `bt = Len` >> gvs[]
      >- (* Len case *)
         (`LENGTH es = 1` by
            gvs[vyperContextTheory.builtin_args_length_ok_def] >>
          Cases_on `es` >> gvs[] >>
          fs[vyperStateTheory.bind_def] >>
          gvs[AllCaseEqs()] >>
          rename1 `eval_expr cx h st = (INL tv, s1)` >>
          rename1 `result_array_length cx tv s1 = (INL len, s2)` >>
          `s1 = st` by metis_tac[eval_expr_preserves_state, pure_expr_def] >>
          pop_assum SUBST_ALL_TAC >>
          drule vyperStatePreservationTheory.result_array_length_state >>
          strip_tac >> gvs[vyperStateTheory.return_def] >> metis_tac[])
      >- (* non-Len case *)
         (`EVERY pure_expr es` by gvs[listTheory.EVERY_EL] >>
          Cases_on `bt = Bop In ∨ bt = Bop NotIn` >> gvs[] >>
          fs[vyperStateTheory.bind_def] >>
          gvs[AllCaseEqs()] >>
          rename1 `eval_exprs cx es st = (INL vs, s1)` >>
          `eval_pure_exprs cx st es = SOME vs` by metis_tac[] >>
          simp[] >>
          `s1 = st` by metis_tac[eval_exprs_preserves_state] >>
          pop_assum SUBST_ALL_TAC >>
          gvs[vyperStateTheory.get_accounts_def, vyperStateTheory.return_def,
              vyperStateTheory.raise_def, vyperStateTheory.bind_def,
              vyperStateTheory.ignore_bind_def, vyperStateTheory.assert_def,
              vyperStateTheory.lift_sum_def, vyperStateTheory.lift_option_type_def,
              vyperMiscTheory.option_CASE_rator, vyperMiscTheory.sum_CASE_rator,
              AllCaseEqs()]))
  (* TypeBuiltin *)
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      simp[Once eval_pure_expr_def] >>
      gvs[pure_expr_def] >>
      qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
      simp[Once vyperInterpreterTheory.evaluate_def] >>
      simp monadic_defs >>
      simp[vyperStateTheory.type_check_def, vyperStateTheory.assert_def] >>
      simp[vyperStateTheory.bind_def] >>
      strip_tac >> gvs[AllCaseEqs()] >>
      `EVERY pure_expr es` by gvs[listTheory.EVERY_EL] >>
      rename1 `eval_exprs cx es st = (INL vs, s1)` >>
      `eval_pure_exprs cx st es = SOME vs` by metis_tac[] >>
      simp[] >>
      Cases_on `evaluate_type_builtin cx tb typ (MAP expr_type es) vs` >>
      gvs[vyperStateTheory.lift_sum_def, vyperStateTheory.return_def,
          vyperStateTheory.raise_def])
  (* Pop - impossible *)
  >- simp[pure_expr_def]
  (* Call - impossible *)
  >- simp[pure_expr_def]
  (* [] case *)
  >- (simp[Once eval_pure_expr_def, Once vyperInterpreterTheory.evaluate_def] >>
      simp monadic_defs)
  (* e::es case *)
  >- (rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
      simp[Once eval_pure_expr_def] >>
      gvs[listTheory.EVERY_DEF] >>
      qpat_x_assum `eval_exprs _ _ _ = _` mp_tac >>
      simp[Once vyperInterpreterTheory.evaluate_def] >>
      simp monadic_defs >>
      strip_tac >> gvs[AllCaseEqs()] >>
      rename1 `eval_expr cx e st = (INL tv, s1)` >>
      rename1 `read_result cx tv s1 = (INL v, s2)` >>
      `s1 = st` by metis_tac[eval_expr_preserves_state] >>
      pop_assum SUBST_ALL_TAC >>
      `s2 = st` by
        metis_tac[vyperStateTheory.read_result_state] >>
      pop_assum SUBST_ALL_TAC >>
      gvs[])
QED

Theorem eval_expr_to_eval_pure_expr_some:
  ∀cx st st' e v.
    pure_expr e ∧ eval_expr cx e st = (INL v, st') ⇒
    eval_pure_expr cx st e = SOME v
Proof
  metis_tac[eval_to_eval_pure_mutual]
QED

Theorem eval_pure_expr_to_eval_expr_none:
  ∀cx st e.
    pure_expr e ∧ eval_pure_expr cx st e = NONE ⇒
    ∃err. eval_expr cx e st = (INR err, st)
Proof
  rpt strip_tac >>
  Cases_on `eval_expr cx e st` >> rename1 `(res, st')` >>
  Cases_on `res`
  >- (drule_all (eval_to_eval_pure_mutual |> CONJUNCT1) >> gvs[])
  >- (`st' = st` by metis_tac[eval_expr_preserves_state] >> gvs[])
QED

(* Pure correspondence exports must not depend on admissions. *)
val () = List.app
  (fn (name,th) =>
    let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
      if null (Thm.hyp th) andalso null axioms andalso
         List.all (fn oracle => oracle = "DISK_THM") oracles then ()
      else raise Fail ("pure correspondence proof is not closed: " ^ name)
    end)
  (DB.thms "vyperEvalPureExpr");
