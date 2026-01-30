Theory vyperHoareExamples

Ancestors
  vyperHoare vyperInterpreter vyperAssignTargetSpec vyperLookup

open integerTheory

Definition example_1_def:
  example_1 = [
    AnnAssign "x" (BaseT (IntT 128)) (Literal (IntL (Signed 128) 10));
    AnnAssign "y" (BaseT (IntT 128)) (Name "x");
  ]
End

Definition sum_scoped_vars_def:
  sum_scoped_vars [] st = 0 ∧
  sum_scoped_vars (id::ids) st =
    let rest = sum_scoped_vars ids st in
    case lookup_scoped_var st id of
      NONE => rest
    | SOME v =>
        case dest_NumV v of
          NONE => rest
        | SOME n => n + rest
End

(* Helper: sum lemma when both variables have value 10 *)
Theorem sum_scoped_vars_xy_20:
  ∀st. lookup_scoped_var st "x" = SOME (IntV (Signed 128) 10) ∧
       lookup_scoped_var st "y" = SOME (IntV (Signed 128) 10) ⇒
       sum_scoped_vars ["x"; "y"] st = 20
Proof
  rw[sum_scoped_vars_def, lookup_scoped_var_def, LET_THM] >>
  simp[dest_NumV_def]
QED

(* ===== Main Theorem ===== *)

(*
  Proof Sketch using Hoare rules:

  { P0: st.scopes ≠ [] ∧ valid_lookups cx st ∧
        lookup_name cx st "x" = NONE ∧ lookup_name cx st "y" = NONE }

  AnnAssign "x" _ (Literal (IntL (Signed 128) 10))
  -- Use stmts_spec_ann_assign with expr_spec_literal
  -- expr_spec gives: Literal 10 evaluates to IntV (Signed 128) 10, state unchanged
  -- stmts_spec_ann_assign postcondition: Q (update_scoped_var st "x" (IntV (Signed 128) 10))

  { P1: st.scopes ≠ [] ∧ valid_lookups cx st ∧
        lookup_scoped_var st "x" = SOME (IntV (Signed 128) 10) ∧
        lookup_name st "y" = NONE }

  AnnAssign "y" _ (Name "x")
  -- Use stmts_spec_ann_assign with expr_spec_scoped_var
  -- expr_spec_scoped_var needs: valid_lookups cx st ∧ lookup_scoped_var st "x" = SOME v
  -- After evaluation, v = IntV (Signed 128) 10, state unchanged
  -- stmts_spec_ann_assign postcondition: Q (update_scoped_var st "y" (IntV (Signed 128) 10))

  { P2: lookup_scoped_var st "x" = SOME (IntV (Signed 128) 10) ∧
        lookup_scoped_var st "y" = SOME (IntV (Signed 128) 10) }

  By sum_scoped_vars_xy_20: sum_scoped_vars ["x"; "y"] st = 20
*)

(*
  Proof Sketch using Hoare rules:

  { P0: st.scopes ≠ [] ∧ valid_lookups cx st ∧
        lookup_name cx st "x" = NONE ∧ lookup_name cx st "y" = NONE }

  AnnAssign "x" _ (Literal (IntL (Signed 128) 10))
  -- Use stmts_spec_ann_assign with expr_spec_literal
  -- expr_spec gives: Literal 10 evaluates to IntV (Signed 128) 10, state unchanged
  -- stmts_spec_ann_assign postcondition: Q (update_scoped_var st "x" (IntV (Signed 128) 10))

  { P1: st.scopes ≠ [] ∧ valid_lookups cx st ∧
        lookup_scoped_var st "x" = SOME (IntV (Signed 128) 10) ∧
        lookup_name st "y" = NONE }

  AnnAssign "y" _ (Name "x")
  -- Use stmts_spec_ann_assign with expr_spec_scoped_var
  -- expr_spec_scoped_var needs: valid_lookups cx st ∧ lookup_scoped_var st "x" = SOME v
  -- After evaluation, v = IntV (Signed 128) 10, state unchanged
  -- stmts_spec_ann_assign postcondition: Q (update_scoped_var st "y" (IntV (Signed 128) 10))

  { P2: lookup_scoped_var st "x" = SOME (IntV (Signed 128) 10) ∧
        lookup_scoped_var st "y" = SOME (IntV (Signed 128) 10) }

  By sum_scoped_vars_xy_20: sum_scoped_vars ["x"; "y"] st = 20
*)

Theorem example_1_sum_20:
  ∀cx. ⟦cx⟧ ⦃λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
            lookup_name cx st "x" = NONE ∧ lookup_name cx st "y" = NONE⦄
       example_1
       ⦃(λst. sum_scoped_vars ["x"; "y"] st = 20) ∥ (λv st. F)⦄
Proof
  rpt strip_tac >>
  simp[example_1_def] >>
  (* Define intermediate invariant P1 after first assignment *)
  qabbrev_tac `P1 = λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                         lookup_scoped_var st "x" = SOME (IntV (Signed 128) 10) ∧
                         lookup_name cx st "y" = NONE` >>
  (* Sequence rule *)
  irule stmts_spec_cons >>
  qexists_tac `P1` >>
  conj_tac
  (* ===== First statement: AnnAssign "x" _ (Literal 10) ===== *)
  >- (irule stmts_spec_ann_assign >>
      qexists_tac `IntV (Signed 128) 10` >>
      irule expr_spec_consequence >>
      qexistsl_tac [
        `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
              lookup_name cx st "x" = NONE ∧ lookup_name cx st "y" = NONE`,
        `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
              lookup_name cx st "x" = NONE ∧ lookup_name cx st "y" = NONE`
      ] >>
      rpt conj_tac >> simp[]
      (* Goal 1: postcondition implication *)
      >- (rpt strip_tac >> simp[Abbr `P1`] >> rpt conj_tac
          >- metis_tac[lookup_name_none_to_lookup_scoped_var]
          >- simp[scopes_nonempty_after_update]
          >- metis_tac[valid_lookups_preserved_after_update]
          >- simp[lookup_after_update]
          >- (`"x" ≠ "y"` by EVAL_TAC >> metis_tac[lookup_name_preserved_after_update]))
      (* Goal 2: expr_spec for Literal *)
      >- (`IntV (Signed 128) 10 = evaluate_literal (IntL (Signed 128) 10)` by EVAL_TAC >>
          pop_assum (fn th => ONCE_REWRITE_TAC [th]) >>
          irule expr_spec_literal))
  (* ===== Second statement: AnnAssign "y" _ (Name "x") ===== *)
  >- (irule stmts_spec_ann_assign >>
      qexists_tac `IntV (Signed 128) 10` >>
      irule expr_spec_consequence >>
      qexistsl_tac [
        `λst. (st.scopes ≠ [] ∧ lookup_name cx st "y" = NONE) ∧
              valid_lookups cx st ∧ lookup_scoped_var st "x" = SOME (IntV (Signed 128) 10)`,
        `λst. (st.scopes ≠ [] ∧ lookup_name cx st "y" = NONE) ∧
              valid_lookups cx st ∧ lookup_scoped_var st "x" = SOME (IntV (Signed 128) 10)`
      ] >>
      rpt conj_tac >> simp[Abbr `P1`]
      (* Goal 1: postcondition implication *)
      >- (rpt strip_tac >> rpt conj_tac
          >- metis_tac[lookup_name_none_to_lookup_scoped_var]
          >- (irule sum_scoped_vars_xy_20 >>
              simp[lookup_after_update] >>
              `"y" ≠ "x"` by EVAL_TAC >>
              drule_all lookup_scoped_var_preserved_after_update >> simp[]))
      (* Goal 2: expr_spec for Name "x" *)
      >- (ACCEPT_TAC (SIMP_RULE std_ss []
            (Q.SPECL [`λst. st.scopes ≠ [] ∧ lookup_name cx st "y" = NONE`,
                      `cx`, `"x"`, `IntV (Signed 128) 10`] expr_spec_scoped_var))))
QED

Definition example_2_def:
  example_2 = [
    AugAssign (NameTarget "x") Add (Literal (IntL (Signed 128) 10));
    If (Builtin (Bop Gt) [Name "x"; Literal (IntL (Signed 128) 100)])
       [Assign (BaseTarget (NameTarget "x")) (Literal (IntL (Signed 128) 100))]
       [AugAssign (NameTarget "x") Add (Literal (IntL (Signed 128) 10))];
    If (Builtin (Bop Gt) [Name "x"; Literal (IntL (Signed 128) 20)])
       [Return (SOME (Name "x"))]
       [Pass];
    AnnAssign "y" (BaseT (IntT 128)) (Builtin (Bop Add) [Name "x"; Literal (IntL (Signed 128) 20)]);
    Return (SOME (Name "y"))
  ]
End

(* Proof sketch:

{ x > 0 }
x := x + 10
{ x > 10 }
if x > 100 then
  { x > 100 ∧ x > 10 }
  { T }
  x := 100
  { x = 100 }
  { x > 20 ∧ x ≤ 110 }
else
  { x ≤ 100 ∧ x > 10 }
  x := x + 10
  { x > 20 ∧ x ≤ 110 }
{ x > 0 ∧ x ≤ 110 }
if x > 20 then
  { x > 20 ∧ x > 0 ∧ x ≤ 110 }
  { x > 20 ∧ x ≤ 110 }
  return x
  { F | λv. v > 20 ∧ v ≤ 110 }
  { x ≤ 20 ∧ x > 0 | λv. v > 20 ∧ v ≤ 110 }
else
  { x ≤ 20 ∧ x > 0 }
  pass
  { x ≤ 20 ∧ x > 0 | λ_. F }
{ x ≤ 20 ∧ x > 0 | λv. (v > 20 ∧ v ≤ 110) ∨ F }
{ x ≤ 20 ∧ x > 0 | λv. v > 20 ∧ v ≤ 110 }
y := x + 20
{ y > 20 ∧ y ≤ 40 | λv. v > 20 ∧ v ≤ 110 }
return y
{ F | λv. (v > 20 ∧ v ≤ 40) ∨ (v > 20 ∧ v ≤ 110) }
{ F | λv. v > 20 ∧ v ≤ 110 }

*)
Theorem example_2_thm:
  ∀cx. ⟦cx⟧
    ⦃λst. ∃n. lookup_name cx st "x" = SOME (IntV (Signed 128) n) ∧ n > 0 ∧ n < 1000⦄
    example_2
    ⦃(λ_. F) ∥ λv _. ∃n. v = IntV (Signed 128) n ∧ n > 20 ∧ n ≤ 110⦄
Proof
  cheat
QED
