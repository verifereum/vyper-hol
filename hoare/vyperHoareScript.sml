Theory vyperHoare

Ancestors
  vyperInterpreter vyperAssignTargetSpec vyperLookup vyperEvalExprPreservesScopesDom vyperEvalPreservesScopes vyperEvalMisc

(**********************************************************************)
(* Definitions *)

Definition stmts_spec_def:
  stmts_spec cx (P : evaluation_state -> bool) (ss : stmt list) (Q_ok : evaluation_state -> bool) (Q_ret : value -> evaluation_state -> bool) <=>
    !st. P st ==>
      case eval_stmts cx ss st of
      | (INL (), st') => Q_ok st'
      | (INR (ReturnException v), st') => Q_ret v st'
      | (INR (AssertException s), st') => F (* assertions not allowed to fail *)
      | (INR BreakException, st') => F  (* TODO: break not yet supported *)
      | (INR ContinueException, st') => F (* TODO: continue not yet supported *)
      | (INR (Error s), st') => F
End

Definition expr_spec_def:
  expr_spec cx (P : evaluation_state -> bool) (e : expr) (tv : toplevel_value) (Q : evaluation_state -> bool) <=>
    !st. P st ==>
      case eval_expr cx e st of
      | (INL tv', st') =>
             if tv' = tv then Q st' else F
      | (INR _, st') => F (* ignore exceptions in expressions for now *)
End

Definition target_spec_def:
  target_spec cx (P : evaluation_state -> bool) (tgt : assignment_target) (v : assignment_value) (Q : evaluation_state -> bool) <=>
    !st. P st ==>
      case eval_target cx tgt st of
      | (INL val, st') =>
             if val = v then Q st' else F
      | (INR _, st') => F (* ignore exceptions in target expressions for now *)
End

val _ =
  add_rule
    { term_name   = "stmts_spec",
      fixity      = Closefix,
      pp_elements =
      [ TOK "⟦",
        TM,
        TOK "⟧",
        BreakSpace(1,0),
        TOK "⦃",
        TM,
        TOK "⦄",
        BreakSpace(1,0),
        TM,
        BreakSpace(1,0),
        TOK "⦃",
        TM,
        TOK "∥",
        TM,
        TOK "⦄" ],
      paren_style = OnlyIfNecessary,
      block_style = (AroundEachPhrase, (PP.INCONSISTENT, 0)) };

val _ =
  add_rule
    { term_name   = "expr_spec",
      fixity      = Closefix,
      pp_elements =
      [ TOK "⟦",
        TM,
        TOK "⟧",
        BreakSpace(1,0),
        TOK "⦃",
        TM,
        TOK "⦄",
        BreakSpace(1,0),
        TM,
        BreakSpace(1,0),
        TOK "⇓",
        BreakSpace(1,0),
        TM,
        BreakSpace(1,0),
        TOK "⦃",
        TM,
        TOK "⦄" ],
      paren_style = OnlyIfNecessary,
      block_style = (AroundEachPhrase, (PP.INCONSISTENT, 0)) };

val _ =
  add_rule
    { term_name   = "target_spec",
      fixity      = Closefix,
      pp_elements =
      [ TOK "⟦",
        TM,
        TOK "⟧",
        BreakSpace(1,0),
        TOK "⦃",
        TM,
        TOK "⦄",
        BreakSpace(1,0),
        TM,
        BreakSpace(1,0),
        TOK "⇓ᵗ",
        BreakSpace(1,0),
        TM,
        BreakSpace(1,0),
        TOK "⦃",
        TM,
        TOK "⦄" ],
      paren_style = OnlyIfNecessary,
      block_style = (AroundEachPhrase, (PP.INCONSISTENT, 0)) };

(**********************************************************************)
(* Helper lemmas *)

Theorem with_scopes_id[local]:
  (r:evaluation_state) with scopes := r.scopes = r
Proof
  Cases_on `r` >> simp[evaluation_state_fn_updates]
QED

Theorem scopes_cons_lemma[local]:
  (r:evaluation_state) with scopes := FEMPTY::r.scopes =
  r with scopes updated_by CONS FEMPTY
Proof
  Cases_on `r` >> simp[evaluation_state_fn_updates]
QED

(**********************************************************************)
(* Rules *)

Theorem expr_spec_consequence:
  ∀P P' Q Q' cx e v.
    (∀st. P' st ⇒ P st) ∧
    (∀st. Q st ⇒ Q' st) ∧
    (⟦cx⟧ ⦃P⦄ e ⇓ v ⦃Q⦄) ⇒
    ⟦cx⟧ ⦃P'⦄ e ⇓ v ⦃Q'⦄
Proof
  rw[expr_spec_def] >>
  first_x_assum (qspec_then `st` mp_tac) >> simp[] >>
  Cases_on `eval_expr cx e st` >>
  Cases_on `q` >> gvs[]
QED

Theorem expr_spec_literal:
  ∀P P' cx l. ⟦cx⟧ ⦃P⦄ (Literal l) ⇓ Value (evaluate_literal l) ⦃P⦄
Proof
  rw[expr_spec_def, evaluate_def, return_def]
QED

Theorem expr_spec_name:
  ∀P cx n v. ⟦cx⟧ ⦃λst. P st ∧ lookup_name cx st n = SOME v⦄ (Name n) ⇓ Value v ⦃λst. P st ∧ lookup_name cx st n = SOME v⦄
Proof
  rw[expr_spec_def, lookup_name_def] >> rpt strip_tac >>
  Cases_on `eval_expr cx (Name n) st` >>
  Cases_on `q` >> gvs[] >>
  Cases_on `x` >> gvs[] >>
  drule eval_expr_Name_preserves_state >> simp[]
QED

Theorem expr_spec_scoped_var:
  ∀P cx n v. ⟦cx⟧ ⦃λst. P st ∧ valid_lookups cx st ∧ lookup_scoped_var st n = SOME v⦄ (Name n) ⇓ Value v ⦃λst. P st ∧ valid_lookups cx st ∧ lookup_scoped_var st n = SOME v⦄
Proof
  rw[expr_spec_def] >>
  (subgoal ‘lookup_name cx st n = SOME v’ >- gvs[lookup_scoped_var_implies_lookup_name]) >>
  fs[lookup_name_def] >> rpt strip_tac >>
  Cases_on `eval_expr cx (Name n) st` >>
  Cases_on `q` >> gvs[] >>
  Cases_on `x` >> gvs[] >>
  drule eval_expr_Name_preserves_state >> simp[]
QED

Theorem expr_spec_if:
  ∀P P' Q cx e1 e2 e3 v1 v2 v3.
    (v1 = BoolV T ∨ v1 = BoolV F) ∧
    (⟦cx⟧ ⦃P⦄ e1 ⇓ Value v1 ⦃P'⦄) ∧
    (⟦cx⟧ ⦃λst. P' st ∧ v1 = BoolV T⦄ e2 ⇓ v2 ⦃Q⦄) ∧
    (⟦cx⟧ ⦃λst. P' st ∧ v1 = BoolV F⦄ e3 ⇓ v3 ⦃Q⦄) ⇒
          ⟦cx⟧ ⦃P⦄ (IfExp e1 e2 e3) ⇓ (if v1 = BoolV T then v2 else v3) ⦃Q⦄
Proof
  rw[expr_spec_def] >>
  simp[Once evaluate_def, bind_def] >>
  qpat_x_assum `!s. P s ==> _` (qspec_then `st` mp_tac) >>
  simp[] >>
  Cases_on `eval_expr cx e1 st` >>
  Cases_on `q` >>
  simp[switch_BoolV_def]
QED

Theorem expr_spec_builtin_bop:
  ∀P P' Q cx e1 e2 v1 v2 bop v_result.
    evaluate_binop bop v1 v2 = INL v_result ∧
    (⟦cx⟧ ⦃P⦄ e1 ⇓ Value v1 ⦃P'⦄) ∧
    (⟦cx⟧ ⦃P'⦄ e2 ⇓ Value v2 ⦃Q⦄) ⇒
    ⟦cx⟧ ⦃P⦄ (Builtin (Bop bop) [e1; e2]) ⇓ Value v_result ⦃Q⦄
Proof
  rw[expr_spec_def] >>
  simp[Once evaluate_def, bind_def, check_def, assert_def,
       builtin_args_length_ok_def] >>
  simp[assert_def, ignore_bind_def, bind_def, Once evaluate_def] >>
  qpat_x_assum `!st. P st ==> _` (qspec_then `st` mp_tac) >> simp[] >>
  Cases_on `eval_expr cx e1 st` >> Cases_on `q` >> simp[] >>
  simp[return_def, bind_def, Once evaluate_def] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `!st. P' st ==> _` (qspec_then `r` mp_tac) >> simp[] >>
  Cases_on `eval_expr cx e2 r` >> Cases_on `q` >> simp[] >>
  simp[return_def, Once evaluate_def, get_accounts_def,
       lift_sum_def, evaluate_builtin_def]
QED

Theorem expr_spec_builtin_env_sender:
  ∀P cx. ⟦cx⟧ ⦃P⦄ (Builtin (Env Sender) []) ⇓ Value (AddressV cx.txn.sender) ⦃P⦄
Proof
  rw[expr_spec_def, evaluate_def, return_def] >>
  simp[check_def, assert_def, builtin_args_length_ok_def, bind_def,
       return_def, get_accounts_def] >>
  simp[assert_def, ignore_bind_def, bind_def, return_def,
       get_accounts_def] >>
  simp[lift_sum_def, evaluate_builtin_def, return_def]
QED

Theorem expr_spec_subscript_array:
  ∀P P' Q cx e1 e2 av sign i v.
    IS_SOME (get_self_code cx) ∧
    array_index av i = SOME v ∧
    (⟦cx⟧ ⦃P⦄ e1 ⇓ (Value (ArrayV av)) ⦃P'⦄) ∧
    (⟦cx⟧ ⦃P'⦄ e2 ⇓ (Value (IntV sign i)) ⦃Q⦄) ⇒
    ⟦cx⟧ ⦃P⦄ (Subscript e1 e2) ⇓ (Value v) ⦃Q⦄
Proof
  rw[expr_spec_def] >>
  simp[Once evaluate_def, bind_def] >>
  qpat_x_assum `!st. P st ==> _` (qspec_then `st` mp_tac) >> simp[] >>
  Cases_on `eval_expr cx e1 st` >> Cases_on `q` >> simp[] >>
  strip_tac >> gvs[] >>
  simp[bind_def] >>
  qpat_x_assum `!st. P' st ==> _` (qspec_then `r` mp_tac) >> simp[] >>
  Cases_on `eval_expr cx e2 r` >> Cases_on `q` >> simp[] >>
  strip_tac >> gvs[] >>
  simp[get_Value_def, return_def, bind_def, lift_option_def] >>
  Cases_on `get_self_code cx` >> gvs[return_def, raise_def] >>
  simp[lift_sum_def, evaluate_subscript_def, return_def]
QED

Theorem expr_spec_preserves_var_in_scope:
  ∀P Q cx n e v.
    (⟦cx⟧ ⦃λst. P st ∧ var_in_scope st n⦄ e ⇓ v ⦃Q⦄) ⇒
    ⟦cx⟧ ⦃λst. P st ∧ var_in_scope st n⦄ e ⇓ v ⦃λst. Q st ∧ var_in_scope st n⦄
Proof
  rw[expr_spec_def] >>
  Cases_on `eval_expr cx e st` >> Cases_on `q` >> gvs[] >-
  (drule eval_expr_preserves_var_in_scope >> strip_tac >>
   last_x_assum (qspec_then `st` mp_tac) >> gvs[]) >>
  first_x_assum (qspec_then `st` mp_tac) >> gvs[]
QED

Theorem target_spec_consequence:
  ∀P P' Q Q' cx tgt av.
    (∀st. P' st ⇒ P st) ∧
    (∀st. Q st ⇒ Q' st) ∧
    (⟦cx⟧ ⦃P⦄ tgt ⇓ᵗ av ⦃Q⦄) ⇒
    ⟦cx⟧ ⦃P'⦄ tgt ⇓ᵗ av ⦃Q'⦄
Proof
  rw[target_spec_def] >>
  first_x_assum (qspec_then `st` mp_tac) >> simp[] >>
  Cases_on `eval_target cx tgt st` >>
  Cases_on `q` >> gvs[]
QED

Theorem target_spec_name:
  ∀P cx n av.
     ⟦cx⟧ ⦃λst. P st ∧ lookup_name_target cx st n = SOME av⦄ (BaseTarget (NameTarget n)) ⇓ᵗ av ⦃λst. P st ∧ lookup_name_target cx st n = SOME av⦄
Proof
  rw[target_spec_def, lookup_name_target_def] >> rpt strip_tac >>
  simp[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_base_target cx (NameTarget n) st` >> gvs[return_def] >>
  Cases_on `q` >> gvs[return_def] >-
  (PairCases_on `x` >> gvs[return_def] >>
   drule eval_base_target_NameTarget_preserves_state >> simp[] >>
   strip_tac >> gvs[lookup_base_target_def]) >>
  gvs[lookup_base_target_def]
QED

Theorem target_spec_scoped_var:
  ∀P cx n.
     ⟦cx⟧ ⦃λst. P st ∧ (cx.txn.is_creation ⇒ valid_lookups cx st) ∧ var_in_scope st n⦄ (BaseTarget (NameTarget n)) ⇓ᵗ (BaseTargetV (ScopedVar n) []) ⦃λst. P st ∧ (cx.txn.is_creation ⇒ valid_lookups cx st) ∧ var_in_scope st n⦄
Proof
  rw[target_spec_def] >> rpt strip_tac >>
  simp[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_base_target cx (NameTarget n) st` >> gvs[return_def] >>
  Cases_on `q` >> gvs[return_def] >-
  (PairCases_on `x` >> gvs[return_def] >>
   drule eval_base_target_NameTarget_preserves_state >> strip_tac >> gvs[] >>
   `lookup_name_target cx r n = SOME (BaseTargetV (ScopedVar n) [])` by
     (irule var_in_scope_implies_name_target >> simp[]) >>
   gvs[lookup_name_target_def, lookup_base_target_def]) >>
  `lookup_name_target cx st n = SOME (BaseTargetV (ScopedVar n) [])` by
    (irule var_in_scope_implies_name_target >> simp[]) >>
  gvs[lookup_name_target_def, lookup_base_target_def]
QED

Theorem target_spec_toplevelname_target:
  ∀P cx src_id_opt id.
    ⟦cx⟧ ⦃P⦄ (BaseTarget (TopLevelNameTarget (src_id_opt, id))) ⇓ᵗ
         (BaseTargetV (TopLevelVar src_id_opt id) []) ⦃P⦄
Proof
  rw[target_spec_def] >>
  simp[Once evaluate_def, bind_def, return_def] >>
  simp[Once evaluate_def, return_def]
QED

Theorem target_spec_subscript_target:
  ∀P P' Q cx bt e loc sbs v k.
    value_to_key v = SOME k ∧
    (⟦cx⟧ ⦃P⦄ (BaseTarget bt) ⇓ᵗ (BaseTargetV loc sbs) ⦃P'⦄) ∧
    (⟦cx⟧ ⦃P'⦄ e ⇓ Value v ⦃Q⦄) ⇒
    ⟦cx⟧ ⦃P⦄ (BaseTarget (SubscriptTarget bt e)) ⇓ᵗ (BaseTargetV loc (k::sbs)) ⦃Q⦄
Proof
  rw[target_spec_def, expr_spec_def] >>
  simp[Once evaluate_def, bind_def, return_def] >>
  simp[Once evaluate_def, bind_def] >>
  qpat_x_assum `!st. P st ==> _` (qspec_then `st` mp_tac) >>
  simp[] >>
  simp[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_base_target cx bt st` >>
  Cases_on `q` >> simp[return_def] >>
  Cases_on `x` >> simp[return_def] >>
  strip_tac >> gvs[] >>
  qpat_x_assum `!st. P' st ==> _` (qspec_then `r` mp_tac) >>
  simp[] >> simp[bind_def] >>
  Cases_on `eval_expr cx e r` >> simp[] >>
  Cases_on `q` >> simp[] >> simp[return_def, lift_option_def]
QED

Theorem stmts_spec_consequence:
  !P P' Q Q' R R' cx ss.
    (!st. P' st ==> P st) /\
    (!st. Q st ==> Q' st) /\
    (!v st. R v st ==> R' v st) /\
    (⟦cx⟧ ⦃P⦄ ss ⦃Q ∥ R⦄) ==>
    ⟦cx⟧ ⦃P'⦄ ss ⦃Q' ∥ R'⦄
Proof
  rw[stmts_spec_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `st` mp_tac) >> simp[] >>
  Cases_on `eval_stmts cx ss st` >>
  Cases_on `q` >> gvs[] >>
  Cases_on `y` >> gvs[]
QED

Theorem stmts_spec_nil:
  ∀P Q_ret cx. ⟦cx⟧ ⦃P⦄ [] ⦃P ∥ Q_ret⦄
Proof
  rw[stmts_spec_def] >> simp[Once evaluate_def, return_def]
QED

Theorem stmts_spec_pass:
  ∀P Q_ret cx. ⟦cx⟧ ⦃P⦄ [Pass] ⦃P ∥ Q_ret⦄
Proof
  rw[stmts_spec_def] >>
  simp[Once evaluate_def, return_def] >>
  simp[Once evaluate_def, ignore_bind_def, bind_def, return_def] >>
  simp[Once evaluate_def, return_def]
QED

Theorem stmts_spec_if:
  ∀P P' Q R cx e ss1 ss2 v1.
    (v1 = BoolV T ∨ v1 = BoolV F) ∧
    (⟦cx⟧ ⦃P⦄ e ⇓ Value v1 ⦃P'⦄) ∧
    (⟦cx⟧ ⦃λst.
            st.scopes ≠ [] ∧ HD st.scopes = FEMPTY ∧
            P' (st with scopes := TL st.scopes) ∧
            v1 = BoolV T⦄
          ss1
          ⦃λst. Q (st with scopes := TL st.scopes) ∥
            λv st. R v (st with scopes := TL st.scopes)⦄) ∧
    (⟦cx⟧ ⦃λst.
            st.scopes ≠ [] ∧ HD st.scopes = FEMPTY ∧
            P' (st with scopes := TL st.scopes) ∧
            v1 = BoolV F⦄
          ss2
          ⦃λst. Q (st with scopes := TL st.scopes) ∥
            λv st. R v (st with scopes := TL st.scopes)⦄) ⇒
          ⟦cx⟧ ⦃P⦄ [If e ss1 ss2] ⦃Q ∥ R⦄
Proof
  rw[stmts_spec_def, expr_spec_def] >>
  simp[Once evaluate_def, bind_def, ignore_bind_def] >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, finally_def,
       push_scope_def, return_def] >>
  qpat_x_assum `!st. P st ==> _` (qspec_then `st` mp_tac) >> simp[] >>
  Cases_on `eval_expr cx e st` >> Cases_on `q` >> simp[] >>
  simp[switch_BoolV_def] >> strip_tac >-
  ((* v1 = Value (BoolV T) case *)
   rename [`eval_expr _ _ _ = (INL _, r_after_expr)`] >>
   first_x_assum (qspec_then `r_after_expr with scopes := FEMPTY :: r_after_expr.scopes` mp_tac) >>
   simp[with_scopes_id, scopes_cons_lemma] >>
   Cases_on `eval_stmts cx ss1 (r_after_expr with scopes updated_by CONS FEMPTY)` >>
   Cases_on `q` >> simp[] >-
   ((* Normal completion *)
    rename [`eval_stmts _ _ _ = (INL _, r_after_ss)`] >>
    strip_tac >>
    `r_after_ss.scopes <> []` by
      (drule eval_stmts_preserves_scopes_len >> REWRITE_TAC[evaluation_state_accfupds] >>
       simp[] >> Cases_on `r_after_ss.scopes` >> fs[]) >>
    simp[pop_scope_def] >>
    Cases_on `r_after_ss.scopes` >> gvs[return_def] >>
    simp[Once evaluate_def, return_def]) >>
   (* Exception cases *)
   rename [`eval_stmts _ _ _ = (INR _, r_after_ss)`] >>
   Cases_on `y` >> simp[] >>
   strip_tac >>
   `r_after_ss.scopes <> []` by
     (drule eval_stmts_preserves_scopes_len >> REWRITE_TAC[evaluation_state_accfupds] >>
      simp[] >> Cases_on `r_after_ss.scopes` >> fs[]) >>
   simp[pop_scope_def] >>
   Cases_on `r_after_ss.scopes` >> gvs[return_def, raise_def]) >>
  (* v1 = Value (BoolV F) case *)
  rename [`eval_expr _ _ _ = (INL _, r_after_expr)`] >>
  first_x_assum (qspec_then `r_after_expr with scopes := FEMPTY :: r_after_expr.scopes` mp_tac) >>
  simp[with_scopes_id, scopes_cons_lemma] >>
  Cases_on `eval_stmts cx ss2 (r_after_expr with scopes updated_by CONS FEMPTY)` >>
  Cases_on `q` >> simp[] >-
  ((* Normal completion *)
   rename [`eval_stmts _ _ _ = (INL _, r_after_ss)`] >>
   strip_tac >>
   `r_after_ss.scopes <> []` by
     (drule eval_stmts_preserves_scopes_len >> REWRITE_TAC[evaluation_state_accfupds] >>
      simp[] >> Cases_on `r_after_ss.scopes` >> fs[]) >>
   simp[pop_scope_def] >>
   Cases_on `r_after_ss.scopes` >> gvs[return_def] >>
   simp[Once evaluate_def, return_def]) >>
  (* Exception cases *)
  rename [`eval_stmts _ _ _ = (INR _, r_after_ss)`] >>
  Cases_on `y` >> simp[] >>
  strip_tac >>
  `r_after_ss.scopes <> []` by
    (drule eval_stmts_preserves_scopes_len >> REWRITE_TAC[evaluation_state_accfupds] >>
     simp[] >> Cases_on `r_after_ss.scopes` >> fs[]) >>
  simp[pop_scope_def] >>
  Cases_on `r_after_ss.scopes` >> gvs[return_def, raise_def]
QED

Theorem stmts_spec_assign:
  ∀P P' Q cx tgt av e v.
     (⟦cx⟧ ⦃P⦄ tgt ⇓ᵗ av ⦃P'⦄) ⇒
     (⟦cx⟧ ⦃P'⦄ e ⇓ Value v ⦃λst. assign_target_spec cx st av (Replace v) Q⦄) ⇒
     ⟦cx⟧ ⦃P⦄ [Assign tgt e] ⦃Q ∥ λ_ _. F⦄
Proof
  rw[stmts_spec_def, target_spec_def, expr_spec_def, assign_target_spec_def]
   >> rpt strip_tac >>
   simp[Once evaluate_def, bind_def, ignore_bind_def] >> simp[Once
    evaluate_def, bind_def] >>
   qpat_x_assum `!st. P st ==> _` (qspec_then `st` mp_tac) >> simp[] >>
   Cases_on `eval_target cx tgt st` >> Cases_on `q` >> simp[] >>
   strip_tac >> gvs[] >>
   rename [`eval_target _ _ _ = (INL _, st')`] >>
   first_x_assum (qspec_then `st'` mp_tac) >> simp[] >>
   Cases_on `eval_expr cx e st'` >> Cases_on `q` >> simp[] >>
   strip_tac >> gvs[return_def, bind_def] >>
   simp[bind_def, ignore_bind_def] >>
   rename [`eval_expr _ _ _ = (INL _, st'')`] >>
   Cases_on `assign_target cx av (Replace v) st''` >> Cases_on `q`
    >> gvs[return_def] >>
   simp[Once evaluate_def, return_def]
QED

Theorem stmts_spec_assign_name:
  ∀P Q cx n av e v.
    (⟦cx⟧ ⦃λst. P st ∧ lookup_name_target cx st n = SOME av⦄ e ⇓ Value v ⦃λst. assign_target_spec cx st av (Replace v) Q⦄) ⇒
    ⟦cx⟧ ⦃λst. P st ∧ lookup_name_target cx st n = SOME av⦄ [Assign (BaseTarget (NameTarget n)) e] ⦃Q ∥ λ_ _. F⦄
Proof
  rpt strip_tac >>
  irule stmts_spec_assign >>
  qexistsl_tac [`λst. P st ∧ lookup_name_target cx st n = SOME av`, `av`, `v`] >>
  conj_tac >- simp[] >>
  rw[target_spec_def, lookup_name_target_def] >>
  simp[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_base_target cx (NameTarget n) st` >>
  Cases_on `q` >> gvs[] >-
  (PairCases_on `x` >> gvs[return_def] >>
   drule eval_base_target_NameTarget_preserves_state >> strip_tac >>
   gvs[lookup_base_target_def]) >>
  gvs[lookup_base_target_def]
QED

Theorem stmts_spec_assign_scoped_var:
  ∀P Q cx n e v.
    (⟦cx⟧ ⦃λst. P st ∧ var_in_scope st n⦄ e ⇓ Value v ⦃λst. Q (update_scoped_var st n v)⦄) ⇒
    ⟦cx⟧ ⦃λst. P st ∧ (cx.txn.is_creation ⇒ valid_lookups cx st) ∧ var_in_scope st n⦄ [Assign (BaseTarget (NameTarget n)) e] ⦃Q ∥ λ_ _. F⦄
Proof
  rpt strip_tac >>
  (* Step 1: Use expr_spec_preserves_var_in_scope *)
  `⟦cx⟧ ⦃λst. P st ∧ var_in_scope st n⦄ e ⇓ Value v ⦃λst. var_in_scope st n ∧ Q (update_scoped_var st n v)⦄` by
    (drule expr_spec_preserves_var_in_scope >> strip_tac >>
     irule expr_spec_consequence >>
     qexistsl_tac [`λst. P st ∧ var_in_scope st n`,
                   `(λst. (λst. Q (update_scoped_var st n v)) st ∧ var_in_scope st n)`] >> simp[]) >>
  (* Step 2: Use assign_target_spec_scoped_var_replace_intro *)
  `⟦cx⟧ ⦃λst. P st ∧ var_in_scope st n⦄ e ⇓ Value v ⦃λst. assign_target_spec cx st (BaseTargetV (ScopedVar n) []) (Replace v) Q⦄` by
    (irule expr_spec_consequence >>
     qexistsl_tac [`λst. P st ∧ var_in_scope st n`,
                   `λst. var_in_scope st n ∧ Q (update_scoped_var st n v)`] >>
     simp[assign_target_spec_scoped_var_replace_intro]) >>
  (* Step 3: Use lookup_name_target_implies_var_in_scope *)
  sg `⟦cx⟧ ⦃λst. P st ∧ lookup_name_target cx st n = SOME (BaseTargetV (ScopedVar n) [])⦄ e ⇓ Value v ⦃λst. assign_target_spec cx st (BaseTargetV (ScopedVar n) []) (Replace v) Q⦄` >-
    (irule expr_spec_consequence >>
     qexistsl_tac [`λst. P st ∧ var_in_scope st n`,
                   `λst. assign_target_spec cx st (BaseTargetV (ScopedVar n) []) (Replace v) Q`] >>
     simp[] >>
     rpt strip_tac >> drule lookup_name_target_implies_var_in_scope >> simp[]) >>
  (* Step 4: Use stmts_spec_assign_name *)
  `⟦cx⟧ ⦃λst. P st ∧ lookup_name_target cx st n = SOME (BaseTargetV (ScopedVar n) [])⦄ [Assign (BaseTarget (NameTarget n)) e] ⦃Q ∥ λ_0 _1. F⦄` by
    (irule stmts_spec_assign_name >> simp[] >>
     qexists_tac `v` >> simp[]) >>
  (* Step 5: Use var_in_scope_implies_name_target *)
  irule stmts_spec_consequence >>
  qexistsl_tac [`λst. P st ∧ lookup_name_target cx st n = SOME (BaseTargetV (ScopedVar n) [])`,
                `Q`, `λ_0 _1. F`] >> simp[] >>
  rpt strip_tac >> irule var_in_scope_implies_name_target >> simp[]
QED

Theorem stmts_spec_ann_assign:
  ∀P Q cx n ty e v.
    (⟦cx⟧ ⦃P⦄ e ⇓ Value v ⦃λst. st.scopes ≠ [] ∧
                                lookup_scoped_var st n = NONE ∧
                                Q (update_scoped_var st n v)⦄) ⇒
    ⟦cx⟧ ⦃P⦄ [AnnAssign n ty e] ⦃Q ∥ λ_ _. F⦄
Proof
  rw[stmts_spec_def, expr_spec_def] >>
  simp[Once evaluate_def, bind_def, ignore_bind_def] >>
  simp[Once evaluate_def, bind_def] >>
  first_x_assum (qspec_then `st` mp_tac) >> simp[] >>
  Cases_on `eval_expr cx e st` >> Cases_on `q` >> simp[] >>
  strip_tac >> gvs[return_def] >>
  simp[new_variable_def, bind_def, ignore_bind_def, get_scopes_def,
       return_def, check_def, assert_def] >>
  Cases_on `r.scopes` >> gvs[lookup_scoped_var_def] >>
  simp[set_scopes_def, return_def] >>
  simp[Once evaluate_def, return_def] >>
  gvs[update_scoped_var_def, LET_THM] >>
  sg `~IS_SOME (find_containing_scope (string_to_num n) (h::t))` >-
    (CCONTR_TAC >> gvs[] >> drule find_containing_scope_lookup_scopes >> gvs[]) >>
  Cases_on `find_containing_scope (string_to_num n) (h::t)` >> gvs[]
QED

Theorem stmts_spec_aug_assign:
  ∀P P' Q cx (tgt:base_assignment_target) av bop e v.
     (⟦cx⟧ ⦃P⦄ (BaseTarget tgt) ⇓ᵗ av ⦃P'⦄) ∧
     (⟦cx⟧ ⦃P'⦄ e ⇓ Value v ⦃λst. assign_target_spec cx st av (Update bop v) Q⦄) ⇒
     ⟦cx⟧ ⦃P⦄ [AugAssign tgt bop e] ⦃Q ∥ λ_ _. F⦄
Proof
  rw[stmts_spec_def, target_spec_def, expr_spec_def, assign_target_spec_def] >>
  simp[Once evaluate_def, bind_def, ignore_bind_def] >>
  simp[Once evaluate_def, bind_def] >>
  last_x_assum (qspec_then `st` mp_tac) >>
  simp[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_base_target cx tgt st` >> Cases_on `q` >> simp[] >-
  (Cases_on `x` >> simp[return_def] >> strip_tac >>
   first_x_assum (qspec_then `r` mp_tac) >>
   simp[bind_def, return_def] >>
   Cases_on `eval_expr cx e r` >> Cases_on `q'` >> simp[] >-
   (simp[return_def, bind_def, ignore_bind_def] >>
    strip_tac >>
    Cases_on `assign_target cx av (Update bop v) r''` >>
    Cases_on `q'` >> simp[] >-
    (simp[Once evaluate_def, return_def] >> fs[]) >>
    gvs[AllCaseEqs()]) >>
   simp[])
QED

Theorem stmts_spec_aug_assign_name:
  ∀P Q cx n av bop e v.
    (⟦cx⟧ ⦃λst. P st ∧ lookup_name_target cx st n = SOME av⦄ e ⇓ Value v ⦃λst. assign_target_spec cx st av (Update bop v) Q⦄) ⇒
    ⟦cx⟧ ⦃λst. P st ∧ lookup_name_target cx st n = SOME av⦄ [AugAssign (NameTarget n) bop e] ⦃Q ∥ λ_ _. F⦄
Proof
  rpt strip_tac >>
  irule stmts_spec_aug_assign >>
  qexistsl_tac [`λst. P st ∧ lookup_name_target cx st n = SOME av`, `av`, `v`] >>
  conj_tac >- simp[] >>
  rw[target_spec_def, lookup_name_target_def] >>
  simp[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_base_target cx (NameTarget n) st` >>
  Cases_on `q` >> gvs[] >-
  (PairCases_on `x` >> gvs[return_def] >>
   drule eval_base_target_NameTarget_preserves_state >> strip_tac >>
   gvs[lookup_base_target_def]) >>
  gvs[lookup_base_target_def]
QED

Theorem stmts_spec_aug_assign_scoped_var:
  ∀P Q cx n bop e v1 v2 v.
     evaluate_binop bop v1 v2 = INL v ∧
    (⟦cx⟧ ⦃P⦄ e ⇓ Value v2 ⦃λst. lookup_scoped_var st n = SOME v1 ∧ Q (update_scoped_var st n v)⦄) ⇒
    ⟦cx⟧ ⦃λst. P st ∧ (cx.txn.is_creation ⇒ valid_lookups cx st) ∧ var_in_scope st n⦄ [AugAssign (NameTarget n) bop e] ⦃Q ∥ λ_ _. F⦄
Proof
  (* Proof sketch:
     1. Use assign_target_spec_scoped_var_update_intro and stmts_spec_consequence to obtain:
         ⟦cx⟧ ⦃P⦄ e ⇓ Value v2 ⦃λst. assign_target_spec cx st (BaseTargetV (ScopedVar n) []) (Update bop v) Q⦄
     2. Use target_spec_scoped_var to obtain:
        ⟦cx⟧ ⦃λst. P st ∧ (cx.txn.is_creation ⇒ valid_lookups cx st) ∧ var_in_scope st n⦄ (BaseTarget (NameTarget n)) ⇓ᵗ (BaseTargetV (ScopedVar n) []) ⦃P⦄
     3. Use stmts_spec_aug_assign to obtain:
         ⟦cx⟧ ⦃λst. P st ∧ (cx.txn.is_creation ⇒ valid_lookups cx st) ∧ var_in_scope st n⦄ [AugAssign (NameTarget n) bop e] ⦃Q ∥ λ_ _. F⦄
   *)
  rpt strip_tac >>
  irule stmts_spec_aug_assign >>
  qexistsl_tac [`(λst. P st ∧ (cx.txn.is_creation ⇒ valid_lookups cx st) ∧ var_in_scope st n)`, `BaseTargetV (ScopedVar n) []`, `v2`] >>
  reverse conj_tac >-
  simp[target_spec_scoped_var] >>
  irule expr_spec_consequence >>
  qexistsl_tac [`P`, `(λst. lookup_scoped_var st n = SOME v1 ∧ Q (update_scoped_var st n v))`] >>
  simp[assign_target_spec_scoped_var_update_intro]
QED

Theorem stmts_spec_append:
  ∀P1 P2 P3 R cx ss1 ss2.
    (⟦cx⟧ ⦃P1⦄ ss1 ⦃P2 ∥ R⦄) ∧
    (⟦cx⟧ ⦃P2⦄ ss2 ⦃P3 ∥ R⦄) ⇒
    ⟦cx⟧ ⦃P1⦄ (ss1 ++ ss2) ⦃P3 ∥ R⦄
Proof
  rw[stmts_spec_def, eval_stmts_append] >>
  simp[ignore_bind_def, bind_def] >>
  Cases_on `eval_stmts cx ss1 st` >>
  Cases_on `q` >> gvs[] >-
  (`P2 r` by (last_x_assum (qspec_then `st` mp_tac) >> simp[]) >>
   first_x_assum (qspec_then `r` mp_tac) >> simp[] >>
   Cases_on `eval_stmts cx ss2 r` >> Cases_on `q` >> gvs[] >>
   Cases_on `y` >> simp[]) >>
  last_x_assum (qspec_then `st` mp_tac) >> simp[] >>
  Cases_on `y` >> simp[]
QED

Theorem stmts_spec_cons:
  ∀P1 P2 P3 R cx s ss.
    (⟦cx⟧ ⦃P1⦄ [s] ⦃P2 ∥ R⦄) ∧
    (⟦cx⟧ ⦃P2⦄ ss ⦃P3 ∥ R⦄) ⇒
    ⟦cx⟧ ⦃P1⦄ (s :: ss) ⦃P3 ∥ R⦄
Proof
  rpt strip_tac >>
  ONCE_REWRITE_TAC [GSYM (EVAL ``[h:'a] ++ t``)] >>
  irule stmts_spec_append >>
  qexists_tac `P2` >> simp[]
QED

Theorem stmts_spec_return_none:
  ∀P cx.
     ⟦cx⟧ ⦃P NoneV⦄ [Return NONE] ⦃λ_. F ∥ P⦄
Proof
  rw[stmts_spec_def] >>
  simp[Once evaluate_def, ignore_bind_def, bind_def] >>
  simp[Once evaluate_def, raise_def]
QED

Theorem stmts_spec_return_some:
  ∀P Q cx e v.
     (⟦cx⟧ ⦃P⦄ e ⇓ Value v ⦃Q v⦄) ⇒
     ⟦cx⟧ ⦃P⦄ [Return (SOME e)] ⦃λ_. F ∥ Q⦄
Proof
  rw[stmts_spec_def, expr_spec_def] >>
  simp[Once evaluate_def, ignore_bind_def, bind_def] >>
  simp[Once evaluate_def, bind_def] >>
  first_x_assum (qspec_then `st` mp_tac) >> simp[] >>
  Cases_on `eval_expr cx e st` >>
  Cases_on `q` >> simp[return_def, raise_def]
QED

Theorem stmts_spec_assert_true:
  ∀P Q cx e se.
    (⟦cx⟧ ⦃P⦄ e ⇓ Value (BoolV T) ⦃Q⦄) ⇒
    ⟦cx⟧ ⦃P⦄ [Assert e se] ⦃Q ∥ λ_ _. F⦄
Proof
  rw[stmts_spec_def, expr_spec_def] >>
  simp[Once evaluate_def, bind_def, ignore_bind_def] >>
  simp[Once evaluate_def, bind_def] >>
  Cases_on `eval_expr cx e st` >> gvs[] >>
  first_x_assum (qspec_then `st` mp_tac) >> simp[] >>
  Cases_on `q` >> gvs[] >>
  strip_tac >> gvs[switch_BoolV_def, return_def] >>
  simp[Once evaluate_def, return_def]
QED
