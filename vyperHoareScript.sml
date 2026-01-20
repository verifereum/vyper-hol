Theory vyperHoare

Ancestors
  vyperInterpreter

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
  expr_spec cx (P : evaluation_state -> bool) (e : expr) (v : toplevel_value) (Q : evaluation_state -> bool) <=>
    !st. P st ==>
      case eval_expr cx e st of
      | (INL val, st') =>
             if val = v then Q st' else F
      | (INR _, st') => F (* ignore exceptions in expressions for now *)
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
        TOK "{{",
        TM,
        TOK "}}",
        BreakSpace(1,0),
        TM,
        BreakSpace(1,0),
        TOK "{{",
        TM,
        TOK "∥",
        TM,
        TOK "}}" ],
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
        TOK "{{",
        TM,
        TOK "}}",
        BreakSpace(1,0),
        TM,
        BreakSpace(1,0),
        TOK "⇓",
        BreakSpace(1,0),
        TM,
        BreakSpace(1,0),
        TOK "{{",
        TM,
        TOK "}}" ],
      paren_style = OnlyIfNecessary,
      block_style = (AroundEachPhrase, (PP.INCONSISTENT, 0)) };

Theorem expr_spec_consequence:
  ∀P P' Q Q' cx e v.
    (∀st. P' st ⇒ P st) ∧
    (∀st. Q st ⇒ Q' st) ∧
    (⟦cx⟧ {{P}} e ⇓ v {{Q}}) ⇒
    ⟦cx⟧ {{P'}} e ⇓ v {{Q'}}
Proof
  rw[expr_spec_def] >>
  first_x_assum (qspec_then `st` mp_tac) >> simp[] >>
  Cases_on `eval_expr cx e st` >>
  Cases_on `q` >> gvs[]
QED

Theorem expr_spec_literal:
  ∀P P' cx l. ⟦cx⟧ {{P}} (Literal l) ⇓ Value (evaluate_literal l) {{P}}
Proof
  rw[expr_spec_def, evaluate_def, return_def]
QED

Theorem expr_spec_if:
  ∀P P' Q cx e1 e2 e3 v1 v2 v3.
    (v1 = Value (BoolV T) ∨ v1 = Value (BoolV F)) ∧
    (⟦cx⟧ {{P}} e1 ⇓ v1 {{P'}}) ∧
    (⟦cx⟧ {{λst. P' st ∧ v1 = Value (BoolV T)}} e2 ⇓ v2 {{Q}}) ∧
    (⟦cx⟧ {{λst. P' st ∧ v1 = Value (BoolV F)}} e3 ⇓ v3 {{Q}}) ⇒
          ⟦cx⟧ {{P}} (IfExp e1 e2 e3) ⇓ (if v1 = Value (BoolV T) then v2 else v3) {{Q}}
Proof
  rw[expr_spec_def] >>
  simp[Once evaluate_def, bind_def] >>
  qpat_x_assum `!s. P s ==> _` (qspec_then `st` mp_tac) >>
  simp[] >>
  Cases_on `eval_expr cx e1 st` >>
  Cases_on `q` >>
  simp[switch_BoolV_def]
QED

Theorem stmts_spec_consequence:
  !P P' Q Q' R R' cx ss.
    (!st. P' st ==> P st) /\
    (!st. Q st ==> Q' st) /\
    (!v st. R v st ==> R' v st) /\
    (⟦cx⟧ {{P}} ss {{Q ∥ R}}) ==>
    ⟦cx⟧ {{P'}} ss {{Q' ∥ R'}}
Proof
  rw[stmts_spec_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `st` mp_tac) >> simp[] >>
  Cases_on `eval_stmts cx ss st` >>
  Cases_on `q` >> gvs[] >>
  Cases_on `y` >> gvs[]
QED

Theorem stmts_spec_nil:
  !P Q_ret cx. ⟦cx⟧ {{P}} [] {{P ∥ Q_ret}}
Proof
  rw[stmts_spec_def] >> simp[Once evaluate_def, return_def]
QED

Theorem stmts_spec_pass:
  ∀P cx. ⟦cx⟧ {{P}} [Pass] {{P ∥ False}}
Proof
  rw[stmts_spec_def] >>
  simp[Once evaluate_def, return_def] >>
  simp[Once evaluate_def, ignore_bind_def, bind_def, return_def] >>
  simp[Once evaluate_def, return_def]
QED


(* Scope-preserving: execution doesn't pop more scopes than it pushed *)
Definition scopes_ok_def:
  scopes_ok cx ss <=>
    !st res s st'.
      eval_stmts cx ss (st with scopes := s :: st.scopes) = (res, st') ==>
      st'.scopes <> []
End

Theorem scopes_ok_thm:
  ∀cx ss. scopes_ok cx ss
Proof
  cheat
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

Theorem stmts_spec_if:
  ∀P P' Q R1 R2 cx e ss1 ss2 v1.
    (v1 = Value (BoolV T) ∨ v1 = Value (BoolV F)) ∧
    scopes_ok cx ss1 ∧ scopes_ok cx ss2 ∧
    (⟦cx⟧ {{P}} e ⇓ v1 {{P'}}) ∧
    (⟦cx⟧ {{λst. P' (st with scopes := TL st.scopes) ∧ v1 = Value (BoolV T)}} ss1
          {{λst. Q (st with scopes := TL st.scopes) ∥
            λv st. R1 v (st with scopes := TL st.scopes)}}) ∧
    (⟦cx⟧ {{λst. P' (st with scopes := TL st.scopes) ∧ v1 = Value (BoolV F)}} ss2
          {{λst. Q (st with scopes := TL st.scopes) ∥
            λv st. R2 v (st with scopes := TL st.scopes)}}) ⇒
          ⟦cx⟧ {{P}} [If e ss1 ss2] {{Q ∥ λv st. R1 v st ∨ R2 v st}}
Proof
  rw[stmts_spec_def, expr_spec_def, scopes_ok_def] >>
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
    `r_after_ss.scopes <> []` by metis_tac[scopes_cons_lemma] >>
    simp[pop_scope_def] >>
    Cases_on `r_after_ss.scopes` >> gvs[return_def] >>
    simp[Once evaluate_def, return_def]) >>
   (* Exception cases *)
   rename [`eval_stmts _ _ _ = (INR _, r_after_ss)`] >>
   Cases_on `y` >> simp[] >>
   strip_tac >>
   `r_after_ss.scopes <> []` by metis_tac[scopes_cons_lemma] >>
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
   `r_after_ss.scopes <> []` by metis_tac[scopes_cons_lemma] >>
   simp[pop_scope_def] >>
   Cases_on `r_after_ss.scopes` >> gvs[return_def] >>
   simp[Once evaluate_def, return_def]) >>
  (* Exception cases *)
  rename [`eval_stmts _ _ _ = (INR _, r_after_ss)`] >>
  Cases_on `y` >> simp[] >>
  strip_tac >>
  `r_after_ss.scopes <> []` by metis_tac[scopes_cons_lemma] >>
  simp[pop_scope_def] >>
  Cases_on `r_after_ss.scopes` >> gvs[return_def, raise_def]
QED

(*
Theorem stmts_spec_assign:
  ∀P Q_ret cx. ⟦cx⟧ {{λst . P()}}
*)
