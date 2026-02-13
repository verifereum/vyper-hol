Theory vyperHoare

Ancestors
  vyperInterpreter vyperUpdateTarget vyperLookup vyperEvalExprPreservesScopesDom vyperEvalPreservesScopes vyperEvalMisc vyperEvalPreservesNameTarget vyperTypeValue

(**********************************************************************)
(* Definitions *)

Definition stmts_spec_def:
  stmts_spec cx (P : evaluation_state -> bool) (ss : stmt list) (Q_ok : evaluation_state -> bool) (Q_ret : value -> evaluation_state -> bool) <=>
    !st. P st ==>
      case eval_stmts cx ss st of
      | (INL (), st') => Q_ok st'
      | (INR (ReturnException v), st') => Q_ret v st'
      | (INR (AssertException str), st') => F (* assertions not allowed to fail *)
      | (INR BreakException, st') => F  (* TODO: break not yet supported *)
      | (INR ContinueException, st') => F (* TODO: continue not yet supported *)
      | (INR (Error str'), st') => F
End

Definition expr_spec_def:
  expr_spec cx (P : evaluation_state -> bool) (e : expr) (Q : toplevel_value -> evaluation_state -> bool) <=>
    !st. P st ==>
      case eval_expr cx e st of
      | (INL tv, st') => Q tv st'
      | (INR _, st') => F
End

Definition target_spec_def:
  target_spec cx (P : evaluation_state -> bool) (tgt : assignment_target) (Q : assignment_value -> evaluation_state -> bool) <=>
    !st. P st ==>
      case eval_target cx tgt st of
      | (INL av, st') => Q av st'
      | (INR _, st') => F (* ignore exceptions in target expressions for now *)
End

Definition get_value_def[simp]:
  get_value (Value v) = SOME v ∧
  get_value _ = NONE
End

Definition get_value_to_key_def[simp]:
  get_value_to_key (Value v) = value_to_key v ∧
  get_value_to_key _ = NONE
End

(**********************************************************************)
(* Syntax *)

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
        BreakSpace(1,0),
        TOK "∥",
        BreakSpace(1,0),
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

Theorem scopes_nonempty_after_eval_stmts_push[local]:
  eval_stmts cx bdy (st with scopes updated_by CONS sc) = (res, st') ⇒
  st'.scopes ≠ []
Proof
  strip_tac >> drule eval_stmts_preserves_scopes_len >>
  simp[evaluation_state_accfupds] >>
  Cases_on `st'.scopes` >> simp[]
QED

(**********************************************************************)
(* Rules *)

Theorem expr_spec_consequence:
  ∀P P' Q Q' cx e.
    (∀st. P' st ⇒ P st) ∧
    (∀tv st. Q tv st ⇒ Q' tv st) ∧
    (⟦cx⟧ ⦃P⦄ e ⇓⦃Q⦄) ⇒
    ⟦cx⟧ ⦃P'⦄ e ⇓⦃Q'⦄
Proof
  rw[expr_spec_def] >>
  first_x_assum (qspec_then `st` mp_tac) >> simp[] >>
  Cases_on `eval_expr cx e st` >>
  Cases_on `q` >> gvs[]
QED

Theorem expr_spec_exists:
  ∀P Q cx e.
    (∀x. ⟦cx⟧ ⦃P x⦄ e ⇓⦃Q x⦄) ⇒
    ⟦cx⟧ ⦃λst. ∃x. P x st⦄ e ⇓⦃λtv st. ∃x. Q x tv st⦄
Proof
  rw[expr_spec_def] >>
  first_x_assum (qspecl_then [`x`, `st`] mp_tac) >> simp[] >>
  Cases_on `eval_expr cx e st` >> Cases_on `q` >> simp[] >>
  metis_tac[]
QED

Theorem expr_spec_literal:
  ∀P P' cx l. ⟦cx⟧ ⦃P⦄ Literal l ⇓⦃λtv st. P st ∧ tv = Value (evaluate_literal l)⦄
Proof
  rw[expr_spec_def, evaluate_def, return_def]
QED

Theorem expr_spec_name:
  ∀P cx n. ⟦cx⟧ ⦃λst. P st ∧ IS_SOME (lookup_name cx st n)⦄ Name n ⇓⦃λtv st. P st ∧ lookup_name cx st n = get_value tv⦄
Proof
  rw[expr_spec_def, lookup_name_def] >> rpt strip_tac >>
  Cases_on `eval_expr cx (Name n) st` >>
  Cases_on `q` >> gvs[] >>
  Cases_on `x` >> gvs[] >>
  drule eval_expr_Name_preserves_state >> simp[]
QED

Theorem expr_spec_scoped_var:
  ∀P cx n. ⟦cx⟧ ⦃λst. P st ∧ valid_lookups cx st ∧ var_in_scope st n⦄ Name n ⇓⦃λtv st. P st ∧ valid_lookups cx st ∧ lookup_scoped_var st n = get_value tv⦄
Proof
  rw[expr_spec_def] >>
  Cases_on `eval_expr cx (Name n) st` >> Cases_on `q` >> gvs[] >-
  ((* INL case *)
   Cases_on `x` >> gvs[] >-
   ((* Value v case *)
    drule eval_expr_Name_preserves_state >> simp[] >> strip_tac >> gvs[] >>
    `lookup_name cx r n = SOME v` by simp[lookup_name_def] >>
    drule_all lookup_name_to_lookup_scoped_var >> simp[]) >>
   (* HashMapRef case - contradictory *)
   `lookup_name cx st n = NONE` by simp[lookup_name_def] >>
   `IS_SOME (lookup_name cx st n)` by metis_tac[var_in_scope_implies_some_lookup_name] >>
   gvs[]) >>
  (* INR case - contradictory *)
  `lookup_name cx st n = NONE` by simp[lookup_name_def] >>
  `IS_SOME (lookup_name cx st n)` by metis_tac[var_in_scope_implies_some_lookup_name] >>
  gvs[]
QED

Theorem expr_spec_name_eq:
  ∀P cx n v. ⟦cx⟧ ⦃λst. P st ∧ lookup_name cx st n = SOME v⦄ Name n ⇓⦃λtv st. P st ∧ lookup_name cx st n = SOME v ∧ tv = Value v⦄
Proof
  rw[expr_spec_def, lookup_name_def] >> rpt strip_tac >>
  Cases_on `eval_expr cx (Name n) st` >>
  Cases_on `q` >> gvs[] >>
  Cases_on `x` >> gvs[] >>
  drule eval_expr_Name_preserves_state >> simp[]
QED

Theorem expr_spec_scoped_var_eq:
  ∀P cx n v. ⟦cx⟧ ⦃λst. P st ∧ valid_lookups cx st ∧ lookup_scoped_var st n = SOME v⦄ Name n ⇓⦃λtv st. P st ∧ valid_lookups cx st ∧ lookup_scoped_var st n = SOME v ∧ tv = Value v⦄
Proof
  rw[expr_spec_def] >>
  `lookup_name cx st n = SOME v` by metis_tac[lookup_scoped_var_implies_lookup_name] >>
  gvs[lookup_name_def, AllCaseEqs()] >>
  drule eval_expr_Name_preserves_state >> simp[]
QED

Theorem expr_spec_if:
  ∀P P' Q cx e1 e2 e3 v1 v2 v3.
    (v1 = BoolV T ∨ v1 = BoolV F) ∧
    (⟦cx⟧ ⦃P⦄ e1 ⇓⦃λtv st. tv = Value v1 ∧ P' st⦄) ∧
    (⟦cx⟧ ⦃λst. P' st ∧ v1 = BoolV T⦄ e2 ⇓⦃λtv st. tv = v2 ∧ Q st⦄) ∧
    (⟦cx⟧ ⦃λst. P' st ∧ v1 = BoolV F⦄ e3 ⇓⦃λtv st. tv = v3 ∧ Q st⦄) ⇒
          ⟦cx⟧ ⦃P⦄ (IfExp e1 e2 e3) ⇓⦃λtv st. tv = (if v1 = BoolV T then v2 else v3) ∧ Q st⦄
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
    (⟦cx⟧ ⦃P⦄ e1 ⇓⦃λtv st. tv = Value v1 ∧ P' st⦄) ∧
    (⟦cx⟧ ⦃P'⦄ e2 ⇓⦃λtv st. tv = Value v2 ∧ Q st⦄) ⇒
    ⟦cx⟧ ⦃P⦄ (Builtin (Bop bop) [e1; e2]) ⇓⦃λtv st. tv = Value v_result ∧ Q st⦄
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
  ∀P cx. ⟦cx⟧ ⦃P⦄ (Builtin (Env Sender) []) ⇓⦃λtv st. tv = Value (AddressV cx.txn.sender) ∧ P st⦄
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
    (⟦cx⟧ ⦃P⦄ e1 ⇓⦃λtv st. tv = Value (ArrayV av) ∧ P' st⦄) ∧
    (⟦cx⟧ ⦃P'⦄ e2 ⇓⦃λtv st. tv = Value (IntV sign i) ∧ Q st⦄) ⇒
    ⟦cx⟧ ⦃P⦄ (Subscript e1 e2) ⇓⦃λtv st. tv = Value v ∧ Q st⦄
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

Theorem expr_spec_preserves_var_in_scope[local]:
  ∀P Q cx n e.
    (⟦cx⟧ ⦃λst. P st ∧ var_in_scope st n⦄ e ⇓⦃Q⦄) ⇒
    ⟦cx⟧ ⦃λst. P st ∧ var_in_scope st n⦄ e ⇓⦃λv st. Q v st ∧ var_in_scope st n⦄
Proof
  rw[expr_spec_def] >>
  Cases_on `eval_expr cx e st` >> Cases_on `q` >> gvs[] >-
  (drule eval_expr_preserves_var_in_scope >> strip_tac >>
   last_x_assum (qspec_then `st` mp_tac) >> gvs[]) >>
  first_x_assum (qspec_then `st` mp_tac) >> gvs[]
QED

Theorem target_spec_consequence:
  ∀P P' Q Q' cx (tgt:assignment_target).
    (∀st. P' st ⇒ P st) ∧
    (∀av st. Q av st ⇒ Q' av st) ∧
    (⟦cx⟧ ⦃P⦄ tgt ⇓ᵗ⦃Q⦄) ⇒
    ⟦cx⟧ ⦃P'⦄ tgt ⇓ᵗ⦃Q'⦄
Proof
  rw[target_spec_def] >>
  first_x_assum (qspec_then `st` mp_tac) >> simp[] >>
  Cases_on `eval_target cx tgt st` >>
  Cases_on `q` >> gvs[]
QED

Theorem target_spec_exists:
  ∀P Q cx (tgt:assignment_target).
    (∀x. ⟦cx⟧ ⦃P x⦄ tgt ⇓ᵗ⦃Q x⦄) ⇒
    ⟦cx⟧ ⦃λst. ∃x. P x st⦄ tgt ⇓ᵗ⦃λav st. ∃x. Q x av st⦄
Proof
  rw[target_spec_def] >>
  first_x_assum (qspecl_then [`x`, `st`] mp_tac) >> simp[] >>
  Cases_on `eval_target cx tgt st` >> Cases_on `q` >> simp[] >>
  metis_tac[]
QED

Theorem target_spec_name:
  ∀P cx n.
    ⟦cx⟧ ⦃λst. P st ∧ IS_SOME (lookup_name_target cx st n)⦄ (BaseTarget (NameTarget n)) ⇓ᵗ⦃λav st. P st ∧ lookup_name_target cx st n = SOME av⦄
Proof
  rw[target_spec_def, lookup_name_target_def] >> rpt strip_tac >>
  simp[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_base_target cx (NameTarget n) st` >> Cases_on `q` >> gvs[] >-
  (PairCases_on `x` >> simp[return_def] >>
   drule eval_base_target_NameTarget_preserves_state >> strip_tac >> gvs[lookup_base_target_def]) >>
  gvs[lookup_base_target_def]
QED

Theorem target_spec_name_eq:
  ∀P cx n av.
    ⟦cx⟧ ⦃λst. P st ∧ lookup_name_target cx st n = SOME av⦄ (BaseTarget (NameTarget n)) ⇓ᵗ⦃λav' st. av' = av ∧ P st ∧ lookup_name_target cx st n = SOME av⦄
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
   ⟦cx⟧ ⦃λst. P st ∧ (cx.txn.is_creation ⇒ valid_lookups cx st) ∧ var_in_scope st n⦄ (BaseTarget (NameTarget n)) ⇓ᵗ⦃λav st. av = (BaseTargetV (ScopedVar n) []) ∧ P st ∧ (cx.txn.is_creation ⇒ valid_lookups cx st) ∧ var_in_scope st n⦄
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

Theorem target_spec_toplevel_name_target:
  ∀P cx src_id_opt id.
   ⟦cx⟧ ⦃P⦄ BaseTarget (TopLevelNameTarget (src_id_opt, id)) ⇓ᵗ⦃λav st. av = (BaseTargetV (TopLevelVar src_id_opt id) []) ∧ P st⦄
Proof
  rw[target_spec_def] >>
  simp[Once evaluate_def, bind_def, return_def] >>
  simp[Once evaluate_def, return_def]
QED

Theorem target_spec_subscript_target:
  ∀P P' Q cx bt e loc sbs k.
    (⟦cx⟧ ⦃P⦄ BaseTarget bt ⇓ᵗ⦃λav st. av = (BaseTargetV loc sbs) ∧ P' st⦄) ∧
    (⟦cx⟧ ⦃P'⦄ e ⇓⦃λtv st. get_value_to_key tv = SOME k ∧ Q st⦄) ⇒
    ⟦cx⟧ ⦃P⦄ BaseTarget (SubscriptTarget bt e) ⇓ᵗ⦃λav st. av = (BaseTargetV loc (k::sbs)) ∧ Q st⦄
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
  Cases_on `q` >> simp[] >> simp[return_def, lift_option_def] >>
  strip_tac >> Cases_on `x` >> simp[get_Value_def, return_def, lift_option_def] >>
  gvs[get_value_to_key_def] >> simp[return_def]
QED

Theorem stmts_spec_consequence:
  ∀P P' Q Q' R R' cx ss.
    (∀st. P' st ⇒ P st) ∧
    (∀st. Q st ⇒ Q' st) ∧
    (∀v st. R v st ⇒ R' v st) ∧
    (⟦cx⟧ ⦃P⦄ ss ⦃Q ∥ R⦄) ⇒
    ⟦cx⟧ ⦃P'⦄ ss ⦃Q' ∥ R'⦄
Proof
  rw[stmts_spec_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `st` mp_tac) >> simp[] >>
  Cases_on `eval_stmts cx ss st` >>
  Cases_on `q` >> gvs[] >>
  Cases_on `y` >> gvs[]
QED

Theorem stmts_spec_false_pre:
  ∀Q R cx ss. ⟦cx⟧ ⦃λst. F⦄ ss ⦃Q ∥ R⦄
Proof
  rw[stmts_spec_def]
QED

Theorem stmts_spec_precond:
  ∀P Q R cx ss cond.
    (cond ⇒ ⟦cx⟧ ⦃P⦄ ss ⦃Q ∥ R⦄) ⇔
    ⟦cx⟧ ⦃λst. cond ∧ P st⦄ ss ⦃Q ∥ R⦄
Proof
  rw[stmts_spec_def] >> metis_tac[]
QED

Theorem stmts_spec_exists:
  ∀P Q R cx ss.
    (∀x . ⟦cx⟧ ⦃P x⦄ ss ⦃Q x ∥ R x⦄) ⇒
    ⟦cx⟧ ⦃λst. ∃x. P x st⦄ ss ⦃λst. ∃x. Q x st ∥ λv st. ∃x. R x v st⦄
Proof
  rw[stmts_spec_def] >>
  first_x_assum (qspecl_then [`x`, `st`] mp_tac) >> simp[] >>
  Cases_on `eval_stmts cx ss st` >> Cases_on `q` >> simp[] >-
  metis_tac[] >>
  Cases_on `y` >> simp[] >>
  metis_tac[]
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
    (⟦cx⟧ ⦃P⦄ e ⇓⦃λtv st. tv = Value v1 ∧ P' st⦄) ∧
    (⟦cx⟧ ⦃λst.
            st.scopes ≠ [] ∧ HD st.scopes = FEMPTY ∧
            P' (tl_scopes st) ∧
            v1 = BoolV T⦄
          ss1
          ⦃λst. Q (tl_scopes st) ∥
            λv st. R v (tl_scopes st)⦄) ∧
    (⟦cx⟧ ⦃λst.
            st.scopes ≠ [] ∧ HD st.scopes = FEMPTY ∧
            P' (tl_scopes st) ∧
            v1 = BoolV F⦄
          ss2
          ⦃λst. Q (tl_scopes st) ∥
            λv st. R v (tl_scopes st)⦄) ⇒
          ⟦cx⟧ ⦃P⦄ [If e ss1 ss2] ⦃Q ∥ R⦄
Proof
  rw[stmts_spec_def, expr_spec_def, tl_scopes_def] >>
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

(* ===================================================================== *)
(* Helper for stmts_spec_for_range: eval_for on GENLIST by induction on m.
   WHY THIS IS TRUE:
   Base (m=0): GENLIST f 0 = [], eval_for [] = return (), I(n+0) = I n.
   Step (SUC m'): GENLIST gives (IntV ib n)::tail. eval_for unfolds:
     push scope, try body, pop scope. Body hyp at k=n gives:
     INL: I(n+1), continue with IH.  INR Return: R v, propagates.
     Others: F, contradiction.
   pop_scope_tl_scopes + scopes_nonempty justify pop_scope succeeds. *)
Theorem eval_for_spec[local]:
  ∀m n ib nm bdy cx (I: int -> evaluation_state -> bool) R st.
    (∀k:int. n ≤ k ∧ k < n + &m ⇒
      ∀st0. I k st0 ⇒
        case eval_stmts cx bdy
               (st0 with scopes updated_by CONS (FEMPTY |+ (nm, IntV ib k))) of
        | (INL (), st1) => I (k + 1) (tl_scopes st1)
        | (INR (ReturnException v), st1) => R v (tl_scopes st1)
        | _ => F) ∧
    I n st ⇒
    case eval_for cx nm bdy (GENLIST (λi. IntV ib (n + &i)) m) st of
    | (INL (), st') => I (n + &m) st'
    | (INR (ReturnException v), st') => R v st'
    | _ => F
Proof
  Induct_on `m`
  >- simp[Once evaluate_def, return_def]
  >> rpt strip_tac
  >> simp[listTheory.GENLIST_CONS, combinTheory.o_DEF]
  >> simp[Once evaluate_def, bind_def, push_scope_with_var_def,
          return_def, ignore_bind_def, finally_def, try_def]
  >> Cases_on `eval_stmts cx bdy
        (st with scopes updated_by CONS (FEMPTY |+ (nm, IntV ib n)))`
  >> rename1 `_ = (res, st1)`
  >> `st1.scopes ≠ []` by metis_tac[scopes_nonempty_after_eval_stmts_push]
  >> Cases_on `res`
  >> simp[pop_scope_tl_scopes, return_def, handle_loop_exception_def, raise_def]
  >- (
    (* INL case: apply IH with n+1 *)
    first_x_assum (qspecl_then
      [`n + 1`, `ib`, `nm`, `bdy`, `cx`, `I'`, `R`, `tl_scopes st1`] mp_tac) >>
    simp[integerTheory.INT_ADD_ASSOC] >>
    impl_tac >- (
      conj_tac >- (
        rpt strip_tac >>
        qpat_assum `∀k. n ≤ k ∧ _ ⇒ _` (qspec_then `k` mp_tac) >>
        impl_tac >- intLib.ARITH_TAC >>
        disch_then (qspec_then `st0` mp_tac) >> simp[]
      ) >>
      qpat_x_assum `∀k. n ≤ k ∧ _ ⇒ _` (qspec_then `n` mp_tac) >>
      impl_tac >- intLib.ARITH_TAC >>
      disch_then (qspec_then `st` mp_tac) >>
      impl_tac >- simp[] >>
      asm_rewrite_tac[] >> simp[]
    ) >>
    `(λi. IntV ib (n + 1 + &i)) = (λx. IntV ib (n + &SUC x))` by (
      simp[FUN_EQ_THM] >> intLib.ARITH_TAC
    ) >>
    `n + 1 + &m = n + &SUC m` by intLib.ARITH_TAC >>
    simp[]
  )
  >> (
    (* INR case: use body hypothesis at k=n *)
    rename1 `_ = (INR exc, _)` >>
    qpat_x_assum `∀k. n ≤ k ∧ _ ⇒ _` (qspec_then `n` mp_tac) >>
    impl_tac >- intLib.ARITH_TAC >>
    disch_then (qspec_then `st` mp_tac) >>
    impl_tac >- simp[] >>
    disch_then assume_tac >>
    Cases_on `exc` >>
    simp[return_def, raise_def, pop_scope_tl_scopes] >>
    pop_assum mp_tac >>
    pop_assum mp_tac >>
    pop_assum (fn th => REWRITE_TAC[th]) >>
    simp[]
  )
QED

Theorem stmts_spec_for_range:
  ∀P P' I cx id typ ib e1 e2 b body v1 v2 n m.
    m ≤ b ∧
    get_range_limits v1 v2 = INL (ib, n, m) ∧
    (⟦cx⟧ ⦃P⦄ e1 ⇓⦃λtv st. tv = Value v1 ∧ P' st⦄) ∧
    (⟦cx⟧ ⦃P'⦄ e2 ⇓⦃λtv st. tv = Value v2 ∧ I n st⦄) ∧
    (∀k:int. n ≤ k ∧ k < n + &m ⇒
         ⟦cx⟧
         ⦃λst. st.scopes ≠ [] ∧
               HD st.scopes = FEMPTY |+ (string_to_num id, IntV ib k) ∧
               I k (tl_scopes st)⦄
         body
         ⦃λst. I (k + 1) (tl_scopes st) ∥ λv st. R v (tl_scopes st)⦄) ⇒
    ⟦cx⟧ ⦃P⦄ [For id typ (Range e1 e2) b body] ⦃I (n + &m) ∥ R⦄
Proof
  rw[stmts_spec_def, expr_spec_def] >> rpt strip_tac >>
  (* Phase 1: Unfold eval_stmts [For ...] → eval_stmt *)
  simp[Once evaluate_def, bind_def, ignore_bind_def] >>
  (* Phase 2: Unfold eval_stmt (For ...) → eval_iterator + check + eval_for *)
  simp[Once evaluate_def, bind_def] >>
  (* Phase 3: Unfold eval_iterator (Range ...) *)
  simp[Once evaluate_def, bind_def] >>
  (* Phase 4: Evaluate e1 using expr_spec hypothesis *)
  qpat_x_assum `∀st. P st ⇒ _` (qspec_then `st` mp_tac) >> simp[] >>
  Cases_on `eval_expr cx e1 st` >> Cases_on `q` >> simp[] >>
  strip_tac >> gvs[] >>
  (* get_Value for e1 result, then evaluate e2 *)
  simp[bind_def, get_Value_def, return_def] >>
  qpat_x_assum `∀st. P' st ⇒ _` (qspec_then `r` mp_tac) >> simp[] >>
  Cases_on `eval_expr cx e2 r` >> Cases_on `q` >> simp[] >>
  strip_tac >> gvs[] >>
  (* Phase 5: get_Value, get_range_limits, lift_sum, compatible_bound *)
  simp[get_Value_def, return_def, bind_def, lift_sum_def,
       check_def, assert_def, ignore_bind_def, compatible_bound_def] >>
  (* Phase 6: Apply eval_for_spec *)
  `∀k:int. n ≤ k ∧ k < n + &m ⇒
     ∀st0. I' k st0 ⇒
       case eval_stmts cx body
              (st0 with scopes updated_by CONS
                 (FEMPTY |+ (string_to_num id, IntV ib k))) of
       | (INL (),st1) => I' (k + 1) (tl_scopes st1)
       | (INR (ReturnException v),st1) => R v (tl_scopes st1)
       | _ => F` by (
    rpt strip_tac >>
    qpat_x_assum `∀k. _ ⇒ ∀st. _ ⇒ _` (qspec_then `k` mp_tac) >>
    simp[] >>
    disch_then (qspec_then
      `st0 with scopes updated_by CONS
         (FEMPTY |+ (string_to_num id, IntV ib k))` mp_tac) >>
    simp[tl_scopes_push]
  ) >>
  drule_all eval_for_spec >> strip_tac >>
  Cases_on `eval_for cx (string_to_num id) body
              (GENLIST (λn'. IntV ib (n + &n')) m) r''` >>
  Cases_on `q` >> gvs[Once evaluate_def, return_def] >>
  Cases_on `y` >> gvs[]
QED

Theorem stmts_spec_assign:
  ∀P P' Q cx tgt e.
     (⟦cx⟧ ⦃P⦄ tgt ⇓ᵗ⦃λav st. P' av st⦄) ∧
     (∀av. ⟦cx⟧ ⦃P' av⦄ e ⇓⦃λtv st. ∃v. tv = Value v ∧ valid_target cx st av (Replace v) ∧ Q (update_target cx st av (Replace v))⦄) ⇒
     ⟦cx⟧ ⦃P⦄ [Assign tgt e] ⦃Q ∥ λ_ _. F⦄
Proof
  rw[stmts_spec_def, target_spec_def, expr_spec_def, update_target_def, valid_target_def]
   >> rpt strip_tac >>
   simp[Once evaluate_def, bind_def, ignore_bind_def] >> simp[Once
    evaluate_def, bind_def] >>
   qpat_x_assum `!st. P st ==> _` (qspec_then `st` mp_tac) >> simp[] >>
   Cases_on `eval_target cx tgt st` >> Cases_on `q` >> simp[] >>
   strip_tac >> gvs[] >>
   rename [`eval_target _ _ _ = (INL av, st')`] >>
   first_x_assum (qspecl_then [`av`, `st'`] mp_tac) >> simp[] >>
   Cases_on `eval_expr cx e st'` >> Cases_on `q` >> simp[] >>
   strip_tac >> gvs[return_def, bind_def] >>
   simp[bind_def, ignore_bind_def, get_Value_def, return_def] >>
   rename [`eval_expr _ _ _ = (INL _, st'')`] >>
   Cases_on `assign_target cx av (Replace v) st''` >> Cases_on `q`
    >> gvs[return_def] >>
   simp[Once evaluate_def, return_def]
QED

Theorem stmts_spec_assign_name:
  ∀P Q cx n av e.
    (⟦cx⟧ ⦃λst. P st ∧ lookup_name_target cx st n = SOME av⦄ e ⇓⦃λtv st. ∃v. tv = Value v ∧ Q (update_target cx st av (Replace v))⦄) ⇒
    ⟦cx⟧ ⦃λst. P st ∧ lookup_name_target cx st n = SOME av⦄ [Assign (BaseTarget (NameTarget n)) e] ⦃Q ∥ λ_ _. F⦄
Proof
  rpt strip_tac >>
  irule stmts_spec_assign >>
  qexists_tac `λav' st. av' = av ∧ P st ∧ lookup_name_target cx st n = SOME av` >>
  conj_tac >-
  (rpt strip_tac >> gvs[expr_spec_def] >>
   rpt strip_tac >>
   first_x_assum (qspec_then `st` mp_tac) >> simp[] >>
   Cases_on `eval_expr cx e st` >> Cases_on `q` >> simp[] >>
   strip_tac >> qexists_tac `v` >> simp[] >>
   irule lookup_name_target_is_valid_target_Replace >>
   qexists_tac `n` >>
   irule eval_expr_preserves_lookup_name_target >>
   qexistsl_tac [`e`, `INL x`, `st`] >> simp[]) >>
  rw[target_spec_def, lookup_name_target_def] >>
  simp[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_base_target cx (NameTarget n) st` >>
  Cases_on `q` >> gvs[lookup_base_target_def] >-
  (PairCases_on `x` >> gvs[return_def] >>
   drule eval_base_target_NameTarget_preserves_state >> strip_tac >> gvs[])
QED

Theorem stmts_spec_assign_scoped_var:
  ∀P Q cx n e.
    (⟦cx⟧ ⦃λst. P st ∧ var_in_scope st n⦄ e ⇓⦃λtv st. ∃v. tv = Value v ∧ Q (update_scoped_var st n v)⦄) ⇒
    ⟦cx⟧ ⦃λst. P st ∧ (cx.txn.is_creation ⇒ valid_lookups cx st) ∧ var_in_scope st n⦄ [Assign (BaseTarget (NameTarget n)) e] ⦃Q ∥ λ_ _. F⦄
Proof
  rpt strip_tac >>
  irule stmts_spec_assign >>
  qexists_tac `λav st. av = BaseTargetV (ScopedVar n) [] ∧
                       P st ∧ (cx.txn.is_creation ⇒ valid_lookups cx st) ∧ var_in_scope st n` >>
  conj_tac >-
  (rpt strip_tac >> gvs[expr_spec_def] >>
   rpt strip_tac >> first_x_assum (qspec_then `st` mp_tac) >> simp[] >>
   Cases_on `eval_expr cx e st` >> Cases_on `q` >> simp[] >>
   strip_tac >> qexists_tac `v` >> simp[] >>
   `var_in_scope r n` by metis_tac[eval_expr_preserves_var_in_scope] >>
   simp[valid_target_scoped_var_replace] >>
   simp[update_target_scoped_var_replace]) >>
  simp[target_spec_scoped_var]
QED

Theorem stmts_spec_assign_scoped_var_single_subscript:
  ∀P P' Q cx n k idx_e e.
    (⟦cx⟧ ⦃λst. P st ∧ (cx.txn.is_creation ⇒ valid_lookups cx st) ∧ var_in_scope st n⦄
       idx_e ⇓⦃λtv st. get_value_to_key tv = SOME k ∧ P' st⦄) ∧
    (⟦cx⟧ ⦃P'⦄ e ⇓⦃λtv st. ∃v a a'.
        tv = Value v ∧
        lookup_scoped_var st n = SOME a ∧
        assign_subscripts a [k] (Replace v) = INL a' ∧
        Q (update_scoped_var st n a')⦄) ⇒
    ⟦cx⟧ ⦃λst. P st ∧ (cx.txn.is_creation ⇒ valid_lookups cx st) ∧ var_in_scope st n⦄
     [Assign (BaseTarget (SubscriptTarget (NameTarget n) idx_e)) e] ⦃Q ∥ λ_ _. F⦄
Proof
  rpt strip_tac >>
  irule stmts_spec_assign >>
  qexists_tac `λav st. av = BaseTargetV (ScopedVar n) [k] ∧ P' st` >>
  conj_tac >-
  (rpt strip_tac >> gvs[expr_spec_def] >>
   rpt strip_tac >>
   first_x_assum (qspec_then `st` mp_tac) >> simp[] >>
   Cases_on `eval_expr cx e st` >> Cases_on `q` >> simp[] >>
   strip_tac >> qexists_tac `v` >> simp[] >>
   conj_tac >-
   (irule valid_target_scoped_var_subscripts >>
    qexistsl_tac [`a`, `a'`] >> simp[]) >>
   `update_target cx r (BaseTargetV (ScopedVar n) [k]) (Replace v) =
    update_scoped_var r n a'`
     by (irule update_target_scoped_var_subscripts >>
         qexists_tac `a` >> simp[]) >>
   simp[]) >>
  BETA_TAC >>
  irule target_spec_subscript_target >>
  qexists_tac `λst. P st ∧ (cx.txn.is_creation ⇒ valid_lookups cx st) ∧ var_in_scope st n` >>
  conj_tac >-
  simp[] >>
  simp[target_spec_scoped_var]
QED

Theorem stmts_spec_assign_scoped_var_subscripts:
  ∀P P' Q cx bt n sbs e.
    (⟦cx⟧ ⦃P⦄ BaseTarget bt ⇓ᵗ⦃λav st. av = (BaseTargetV (ScopedVar n) sbs) ∧ P' st⦄) ∧
    (⟦cx⟧
     ⦃P'⦄
     e
     ⇓⦃λtv st. ∃v0 v1 v2.
                 tv = Value v1 ∧
                 lookup_scoped_var st n = SOME v0 ∧
                 assign_subscripts v0 sbs (Replace v1) = INL v2 ∧
                 Q (update_scoped_var st n v2)⦄) ⇒
    ⟦cx⟧ ⦃P⦄ [Assign (BaseTarget (SubscriptTarget t ei)) e] ⦃Q ∥ λ_ _. F⦄
Proof
  cheat
QED

Theorem stmts_spec_ann_assign:
  ∀P Q cx n ty e.
    (⟦cx⟧ ⦃P⦄ e ⇓⦃λtv st. ∃v. tv = Value v ∧ st.scopes ≠ [] ∧
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
  ∀P P' Q cx (tgt:base_assignment_target) bop e.
     (⟦cx⟧ ⦃P⦄ (BaseTarget tgt) ⇓ᵗ⦃λav st. P' av st⦄) ∧
     (∀av. ⟦cx⟧ ⦃P' av⦄ e ⇓⦃λtv st. ∃v. tv = Value v ∧ valid_target cx st av (Update bop v) ∧ Q (update_target cx st av (Update bop v))⦄) ⇒
     ⟦cx⟧ ⦃P⦄ [AugAssign tgt bop e] ⦃Q ∥ λ_ _. F⦄
Proof
  rw[stmts_spec_def, target_spec_def, expr_spec_def, valid_target_def, update_target_def] >>
  simp[Once evaluate_def, bind_def, ignore_bind_def] >>
  simp[Once evaluate_def, bind_def] >>
  last_x_assum (qspec_then `st` mp_tac) >>
  simp[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_base_target cx tgt st` >> Cases_on `q` >> simp[] >-
  (Cases_on `x` >> simp[return_def] >> strip_tac >>
   rename [`eval_base_target _ _ _ = (INL (loc, sbs), st')`] >>
   first_x_assum (qspecl_then [`BaseTargetV loc sbs`, `st'`] mp_tac) >>
   simp[bind_def, return_def] >>
   Cases_on `eval_expr cx e st'` >> Cases_on `q` >> simp[] >-
   (simp[return_def, bind_def, ignore_bind_def, get_Value_def] >> strip_tac >>
    gvs[return_def] >>
    rename [`eval_expr _ _ _ = (INL _, st'')`] >>
    Cases_on `assign_target cx (BaseTargetV loc sbs) (Update bop v) st''` >>
    Cases_on `q` >> simp[] >-
    (simp[Once evaluate_def, return_def] >> gvs[]) >>
    gvs[AllCaseEqs()]) >>
   simp[])
QED

Theorem stmts_spec_aug_assign_name:
  ∀P Q cx n av bop e.
    (⟦cx⟧ ⦃λst. P st ∧ lookup_name_target cx st n = SOME av⦄ e ⇓⦃λtv st. ∃v. tv = Value v ∧ valid_target cx st av (Update bop v) ∧ Q (update_target cx st av (Update bop v))⦄) ⇒
    ⟦cx⟧ ⦃λst. P st ∧ lookup_name_target cx st n = SOME av⦄ [AugAssign (NameTarget n) bop e] ⦃Q ∥ λ_ _. F⦄
Proof
  rpt strip_tac >>
  irule stmts_spec_aug_assign >>
  qexists_tac `λav' st. av' = av ∧ P st ∧ lookup_name_target cx st n = SOME av` >>
  conj_tac >-
  (rpt strip_tac >> gvs[expr_spec_def]) >>
  simp[target_spec_name_eq]
QED

Theorem stmts_spec_aug_assign_scoped_var:
  ∀P Q cx n bop e.
    (⟦cx⟧
      ⦃P⦄
      e
      ⇓⦃λtv st.
        ∃v1 v2 v.
          evaluate_binop bop v1 v2 = INL v ∧
          tv = Value v2 ∧
          lookup_scoped_var st n = SOME v1 ∧
          Q (update_scoped_var st n v)⦄) ⇒
    ⟦cx⟧
     ⦃λst. P st ∧ (cx.txn.is_creation ⇒ valid_lookups cx st) ∧ var_in_scope st n⦄
     [AugAssign (NameTarget n) bop e]
     ⦃Q ∥ λ_ _. F⦄
Proof
  rpt strip_tac >>
  irule stmts_spec_aug_assign >>
  qexists_tac `λav st. av = BaseTargetV (ScopedVar n) [] ∧
                       P st ∧ (cx.txn.is_creation ⇒ valid_lookups cx st) ∧ var_in_scope st n` >>
  conj_tac >-
  (rpt strip_tac >> gvs[expr_spec_def] >>
   rpt strip_tac >> first_x_assum (qspec_then `st` mp_tac) >> simp[] >>
   Cases_on `eval_expr cx e st` >> Cases_on `q` >> simp[] >>
   strip_tac >> qexists_tac `v2` >> simp[] >>
   conj_tac >-
   (irule valid_target_scoped_var_update >> qexistsl_tac [`v`, `v1`] >> simp[]) >>
   `update_target cx r (BaseTargetV (ScopedVar n) []) (Update bop v2) = update_scoped_var r n v`
     by (irule update_target_scoped_var_update >> qexists_tac `v1` >> simp[]) >>
   simp[]) >>
  simp[target_spec_scoped_var]
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
  ∀P Q cx e.
     (⟦cx⟧ ⦃P⦄ e ⇓⦃λtv st. ∃v. tv = Value v ∧ Q v st⦄) ⇒
     ⟦cx⟧ ⦃P⦄ [Return (SOME e)] ⦃λ_. F ∥ Q⦄
Proof
  rw[stmts_spec_def, expr_spec_def] >>
  simp[Once evaluate_def, ignore_bind_def, bind_def] >>
  simp[Once evaluate_def, bind_def] >>
  first_x_assum (qspec_then `st` mp_tac) >> simp[] >>
  Cases_on `eval_expr cx e st` >>
  Cases_on `q` >> simp[return_def, raise_def] >>
  strip_tac >> Cases_on `x` >> gvs[get_Value_def, return_def, raise_def]
QED

Theorem stmts_spec_assert_true:
  ∀P Q cx e se.
    (⟦cx⟧ ⦃P⦄ e ⇓⦃λtv st. tv = Value (BoolV T) ∧ Q st⦄) ⇒
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
