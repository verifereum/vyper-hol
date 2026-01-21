Theory vyperHoare

Ancestors
  vyperInterpreter vyperScopes

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
  expr_spec cx (P : evaluation_state -> bool) (e : expr) (v : value) (Q : evaluation_state -> bool) <=>
    !st. P st ==>
      case eval_expr cx e st of
      | (INL val, st') =>
             if val = Value v then Q st' else F
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

open Parse;

val _ =
  temp_add_rule
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
  temp_add_rule
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
  temp_add_rule
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

Definition lookup_name_def:
  lookup_name cx st n =
    case eval_expr cx (Name n) st of
    | (INL (Value v), _) => SOME v
    | (_, _) => NONE
End

Definition lookup_name_target_def:
  lookup_name_target cx st n =
    case eval_base_target cx (NameTarget n) st of
    | (INL (loc, sbs), _) => SOME (BaseTargetV loc sbs)
    | (INR _, _) => NONE
End

                  
(**********************************************************************)
(* Helper lemmas *)

Theorem eval_expr_Name_preserves_state:
  ∀cx n st v st'.
    eval_expr cx (Name n) st = (INL (Value v), st') ==> st' = st
Proof
  simp[Once evaluate_def] >> rpt strip_tac >>
  qpat_x_assum `do _ od _ = _` mp_tac >>
  simp[bind_def, get_scopes_def, return_def] >>
  simp[get_immutables_def, get_immutables_module_def,
       get_current_globals_def, lift_option_def] >>
  simp[bind_def, get_current_globals_def, return_def] >>
  simp[lift_option_def] >>
  Cases_on `ALOOKUP st.globals cx.txn.target` >> gvs[raise_def, return_def] >>
  simp[lift_sum_def] >>
  Cases_on `exactly_one_option (lookup_scopes (string_to_num n) st.scopes)
                                (FLOOKUP (get_module_globals NONE x).immutables (string_to_num n))` >>
  gvs[return_def, raise_def]
QED

Theorem eval_base_target_NameTarget_preserves_state:
  ∀cx n st loc sbs st'.
    eval_base_target cx (NameTarget n) st = (INL (loc, sbs), st') ==> st' = st
Proof
  simp[Once evaluate_def] >> rpt strip_tac >>
  gvs[bind_def, get_scopes_def, return_def] >>
  Cases_on `cx.txn.is_creation` >> gvs[return_def] >-
  (gvs[bind_def, get_immutables_def, get_immutables_module_def,
       get_current_globals_def, lift_option_def] >>
   Cases_on `ALOOKUP st.globals cx.txn.target` >> gvs[return_def, raise_def] >>
   gvs[lift_sum_def, bind_def] >>
   Cases_on `exactly_one_option
              (if IS_SOME (lookup_scopes (string_to_num n) st.scopes) then
                 SOME (ScopedVar n)
               else NONE)
              (immutable_target (get_module_globals NONE x).immutables n
                 (string_to_num n))` >>
   gvs[return_def, raise_def]) >>
  gvs[lift_sum_def, bind_def] >>
  Cases_on `exactly_one_option
             (if IS_SOME (lookup_scopes (string_to_num n) st.scopes) then
                SOME (ScopedVar n)
              else NONE) NONE` >>
  gvs[return_def, raise_def]
QED

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
  ∀P P' cx l. ⟦cx⟧ ⦃P⦄ (Literal l) ⇓ evaluate_literal l ⦃P⦄
Proof
  rw[expr_spec_def, evaluate_def, return_def]
QED

Theorem expr_spec_name:
  ∀P cx n v. ⟦cx⟧ ⦃λst. P st ∧ lookup_name cx st n = SOME v⦄ (Name n) ⇓ v ⦃P⦄
Proof
  rw[expr_spec_def, lookup_name_def] >> rpt strip_tac >>
  Cases_on `eval_expr cx (Name n) st` >>
  Cases_on `q` >> gvs[] >>
  Cases_on `x` >> gvs[] >>
  drule eval_expr_Name_preserves_state >> simp[]
QED

Theorem expr_spec_if:
  ∀P P' Q cx e1 e2 e3 v1 v2 v3.
    (v1 = BoolV T ∨ v1 = BoolV F) ∧
    (⟦cx⟧ ⦃P⦄ e1 ⇓ v1 ⦃P'⦄) ∧
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
     ⟦cx⟧ ⦃λst. P st ∧ lookup_name_target cx st n = SOME av⦄ (BaseTarget (NameTarget n)) ⇓ᵗ av ⦃P⦄
Proof
  rw[target_spec_def, lookup_name_target_def] >> rpt strip_tac >>
  simp[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_base_target cx (NameTarget n) st` >> gvs[return_def] >>
  Cases_on `q` >> gvs[return_def] >> Cases_on `x` >> gvs[return_def] >>
  drule eval_base_target_NameTarget_preserves_state >> simp[]
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
  !P Q_ret cx. ⟦cx⟧ ⦃P⦄ [] ⦃P ∥ Q_ret⦄
Proof
  rw[stmts_spec_def] >> simp[Once evaluate_def, return_def]
QED

Theorem stmts_spec_pass:
  ∀P cx. ⟦cx⟧ ⦃P⦄ [Pass] ⦃P ∥ False⦄
Proof
  rw[stmts_spec_def] >>
  simp[Once evaluate_def, return_def] >>
  simp[Once evaluate_def, ignore_bind_def, bind_def, return_def] >>
  simp[Once evaluate_def, return_def]
QED

Theorem stmts_spec_if:
  ∀P P' Q R1 R2 cx e ss1 ss2 v1.
    (v1 = BoolV T ∨ v1 = BoolV F) ∧
    (⟦cx⟧ ⦃P⦄ e ⇓ v1 ⦃P'⦄) ∧
    (⟦cx⟧ ⦃λst. P' (st with scopes := TL st.scopes) ∧ v1 = BoolV T⦄ ss1
          ⦃λst. Q (st with scopes := TL st.scopes) ∥
            λv st. R1 v (st with scopes := TL st.scopes)⦄) ∧
    (⟦cx⟧ ⦃λst. P' (st with scopes := TL st.scopes) ∧ v1 = BoolV F⦄ ss2
          ⦃λst. Q (st with scopes := TL st.scopes) ∥
            λv st. R2 v (st with scopes := TL st.scopes)⦄) ⇒
          ⟦cx⟧ ⦃P⦄ [If e ss1 ss2] ⦃Q ∥ λv st. R1 v st ∨ R2 v st⦄
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
      (drule scopes_len_preserved >> REWRITE_TAC[evaluation_state_accfupds] >>
       simp[] >> Cases_on `r_after_ss.scopes` >> fs[]) >>
    simp[pop_scope_def] >>
    Cases_on `r_after_ss.scopes` >> gvs[return_def] >>
    simp[Once evaluate_def, return_def]) >>
   (* Exception cases *)
   rename [`eval_stmts _ _ _ = (INR _, r_after_ss)`] >>
   Cases_on `y` >> simp[] >>
   strip_tac >>
   `r_after_ss.scopes <> []` by
     (drule scopes_len_preserved >> REWRITE_TAC[evaluation_state_accfupds] >>
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
     (drule scopes_len_preserved >> REWRITE_TAC[evaluation_state_accfupds] >>
      simp[] >> Cases_on `r_after_ss.scopes` >> fs[]) >>
   simp[pop_scope_def] >>
   Cases_on `r_after_ss.scopes` >> gvs[return_def] >>
   simp[Once evaluate_def, return_def]) >>
  (* Exception cases *)
  rename [`eval_stmts _ _ _ = (INR _, r_after_ss)`] >>
  Cases_on `y` >> simp[] >>
  strip_tac >>
  `r_after_ss.scopes <> []` by
    (drule scopes_len_preserved >> REWRITE_TAC[evaluation_state_accfupds] >>
     simp[] >> Cases_on `r_after_ss.scopes` >> fs[]) >>
  simp[pop_scope_def] >>
  Cases_on `r_after_ss.scopes` >> gvs[return_def, raise_def]
QED

Definition assign_target_spec_def:
  assign_target_spec cx st (av : assignment_value) (ao : assign_operation) Q ⇔
    case assign_target cx av ao st of
    | (INL _, st') => Q st'
    | (INR _, _) => F
End

Theorem stmts_spec_assign:
  ∀P P' Q cx tgt av e v.
     (⟦cx⟧ ⦃P⦄ tgt ⇓ᵗ av ⦃P'⦄) ⇒
     (⟦cx⟧ ⦃P'⦄ e ⇓ v ⦃λst. assign_target_spec cx st av (Replace v) Q⦄) ⇒
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

Theorem assign_target_spec_consequence:
  ∀cx st av v Q Q'.
    (∀st'. Q st' => Q' st') ∧
    assign_target_spec cx st av (Replace v) Q =>
      assign_target_spec cx st av (Replace v) Q'                       
Proof
  cheat
QED

Theorem assign_target_spec_lookup:
  ∀cx st n av v.
    lookup_name_target cx st n = SOME av =>
    assign_target_spec cx st av (Replace v) (λst. lookup_name cx st n = SOME v)
Proof
  cheat
QED

Theorem stmts_spec_assign_name:
  ∀P P' Q cx n av e v.
     (⟦cx⟧ ⦃λst. P st ∧ lookup_name_target cx st n = SOME av⦄ e ⇓ v ⦃λst. assign_target_spec cx st av (Replace v) Q⦄) ⇒
     ⟦cx⟧ ⦃P⦄ [Assign (BaseTarget (NameTarget n)) e] ⦃Q ∥ λ_ _. F⦄
Proof
  cheat
QED
