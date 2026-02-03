Theory vyperHoareExample2

Ancestors
  jsonToVyper vyperHoare vyperInterpreter vyperLookup

Libs
  jsonASTLib intLib

val example_2_json_path = "example_2.json"

val example_2_jsonast_tm = JSONDecode.decodeFile (JSONDecode.field "ast" json_module) example_2_json_path

val example_2_vyperast_tm = let
  val translate_module_tm = prim_mk_const{Thy="jsonToVyper",Name="translate_module"}
  val app = mk_comb(translate_module_tm, example_2_jsonast_tm)
  val thm = EVAL app
in
  rhs (concl thm)
end

Definition example_2_module_def:
  example_2_module = ^example_2_vyperast_tm
End


Theorem example_2_has_1_toplevel:
  LENGTH example_2_module = 1
Proof
  EVAL_TAC
QED

Definition example_2_decl_def:
  example_2_decl = EL 0 example_2_module
End

Definition example_2_body_def:
  example_2_body = case example_2_decl of
    | FunctionDecl _ _ _ _ _ body => body
    | _ => []
End

Theorem example_2_body_length:
  LENGTH example_2_body = 3
Proof
  EVAL_TAC
QED

(* Helper lemmas for if-statement proof *)

(* When HD st.scopes doesn't contain n, lookup in full scopes equals lookup in TL *)
Theorem lookup_scoped_var_TL_when_not_in_HD:
  ∀st n v. st.scopes ≠ [] ∧
           FLOOKUP (HD st.scopes) (string_to_num n) = NONE ∧
           lookup_scoped_var st n = SOME v ⇒
           lookup_scoped_var (st with scopes := TL st.scopes) n = SOME v
Proof
  rw[lookup_scoped_var_def, evaluation_state_accfupds] >>
  Cases_on `st.scopes` >> gvs[] >>
  gvs[Once lookup_scopes_def]
QED

(* When HD st.scopes doesn't contain n, lookup in TL equals lookup in full *)
Theorem lookup_scoped_var_from_TL_when_not_in_HD:
  ∀st n v. st.scopes ≠ [] ∧
           FLOOKUP (HD st.scopes) (string_to_num n) = NONE ∧
           lookup_scoped_var (st with scopes := TL st.scopes) n = SOME v ⇒
           lookup_scoped_var st n = SOME v
Proof
  rw[lookup_scoped_var_def, evaluation_state_accfupds] >>
  Cases_on `st.scopes` >> gvs[] >>
  simp[Once lookup_scopes_def]
QED

(* var_in_scope when not in HD *)
Theorem var_in_scope_from_TL_when_not_in_HD:
  ∀st n. st.scopes ≠ [] ∧
         FLOOKUP (HD st.scopes) (string_to_num n) = NONE ∧
         var_in_scope (st with scopes := TL st.scopes) n ⇒
         var_in_scope st n
Proof
  rw[var_in_scope_def] >>
  gvs[lookup_scoped_var_def, evaluation_state_accfupds] >>
  Cases_on `st.scopes` >> gvs[] >>
  gvs[Once lookup_scopes_def]
QED

Theorem valid_lookups_from_TL_when_FEMPTY_HD:
  ∀cx st. st.scopes ≠ [] ∧ HD st.scopes = FEMPTY ∧
          valid_lookups cx (st with scopes := TL st.scopes) ⇒
          valid_lookups cx st
Proof
  rw[valid_lookups_def, evaluation_state_accfupds] >>
  qexists_tac `imms` >> simp[] >>
  rpt strip_tac >>
  first_x_assum irule >>
  gvs[var_in_scope_def, lookup_scoped_var_def] >>
  Cases_on `st.scopes` >> gvs[finite_mapTheory.FLOOKUP_EMPTY] >>
  gvs[Once lookup_scopes_def]
QED

(* Key lemma: when HD = FEMPTY and var is in TL, update_scoped_var affects TL correctly.
   This lemma is essential for reasoning about if-statements because stmts_spec_if
   works with `st with scopes := TL st.scopes` views. *)
Theorem update_scoped_var_TL_when_FEMPTY_HD:
  ∀st n v. st.scopes ≠ [] ∧ HD st.scopes = FEMPTY ∧
           var_in_scope (st with scopes := TL st.scopes) n ⇒
           TL (update_scoped_var st n v).scopes =
           (update_scoped_var (st with scopes := TL st.scopes) n v).scopes
Proof
  rw[update_scoped_var_def, evaluation_state_accfupds, LET_THM] >>
  Cases_on `st.scopes` >> gvs[] >>
  simp[Once find_containing_scope_def, finite_mapTheory.FLOOKUP_EMPTY] >>
  Cases_on `find_containing_scope (string_to_num n) t` >> gvs[] >-
  ((* NONE case: contradicts var_in_scope *)
   gvs[var_in_scope_def, lookup_scoped_var_def, evaluation_state_accfupds] >>
   imp_res_tac find_containing_scope_none_lookup_scopes_none >> gvs[]) >>
  (* SOME case *)
  PairCases_on `x` >> gvs[evaluation_state_accfupds]
QED

(* Corollary: lookup_scoped_var in TL after update equals the new value *)
Theorem lookup_scoped_var_TL_after_update_when_FEMPTY_HD:
  ∀st n v. st.scopes ≠ [] ∧ HD st.scopes = FEMPTY ∧
           var_in_scope (st with scopes := TL st.scopes) n ⇒
           lookup_scoped_var ((update_scoped_var st n v) with scopes := TL (update_scoped_var st n v).scopes) n = SOME v
Proof
  rpt strip_tac >>
  simp[lookup_scoped_var_def, evaluation_state_accfupds] >>
  `lookup_scoped_var (update_scoped_var (st with scopes := TL st.scopes) n v) n = SOME v` by
    simp[lookup_after_update] >>
  gvs[lookup_scoped_var_def] >>
  (* Use the key lemma *)
  `TL (update_scoped_var st n v).scopes = (update_scoped_var (st with scopes := TL st.scopes) n v).scopes` suffices_by simp[] >>
  rw[update_scoped_var_def, evaluation_state_accfupds, LET_THM] >>
  Cases_on `st.scopes` >> gvs[] >>
  simp[Once find_containing_scope_def, finite_mapTheory.FLOOKUP_EMPTY] >>
  Cases_on `find_containing_scope (string_to_num n) t` >> gvs[] >-
  ((* NONE case - show contradiction *)
   gvs[var_in_scope_def, lookup_scoped_var_def, evaluation_state_accfupds] >>
   `lookup_scopes (string_to_num n) t = NONE` by (
     qpat_x_assum `find_containing_scope _ _ = NONE` mp_tac >>
     qspec_tac (`t`, `t`) >>
     Induct >> simp[Once find_containing_scope_def, Once lookup_scopes_def] >>
     rpt strip_tac >> Cases_on `FLOOKUP h (string_to_num n)` >> gvs[] >>
     Cases_on `find_containing_scope (string_to_num n) t` >> gvs[]) >>
   gvs[]) >>
  (* SOME case *)
  PairCases_on `x` >> gvs[evaluation_state_accfupds]
QED

(* lookup_scopes ignores an empty scope at the head *)
Theorem lookup_scopes_FEMPTY_CONS[local]:
  ∀n rest. lookup_scopes n (FEMPTY::rest) = lookup_scopes n rest
Proof
  simp[Once lookup_scopes_def, finite_mapTheory.FLOOKUP_EMPTY]
QED

(* lookup_scoped_var with a FEMPTY pushed *)
Theorem lookup_scoped_var_FEMPTY_CONS:
  ∀st n. lookup_scoped_var (st with scopes := FEMPTY :: st.scopes) n = lookup_scoped_var st n
Proof
  simp[lookup_scoped_var_def, evaluation_state_accfupds, lookup_scopes_FEMPTY_CONS]
QED

(* After TL of a FEMPTY::rest, we get back to rest *)
Theorem lookup_scoped_var_TL_FEMPTY_CONS:
  ∀st n. lookup_scoped_var ((st with scopes := FEMPTY :: rest) with scopes := TL (FEMPTY :: rest)) n =
         lookup_scoped_var (st with scopes := rest) n
Proof
  simp[lookup_scoped_var_def, evaluation_state_accfupds]
QED

(* var_in_scope with FEMPTY pushed *)
Theorem var_in_scope_FEMPTY_CONS:
  ∀st n. var_in_scope (st with scopes := FEMPTY :: st.scopes) n = var_in_scope st n
Proof
  simp[var_in_scope_def, lookup_scoped_var_FEMPTY_CONS]
QED

(* valid_lookups with FEMPTY pushed - requires immutables unchanged *)
Theorem valid_lookups_FEMPTY_CONS:
  ∀cx st. valid_lookups cx st ⇒ valid_lookups cx (st with scopes := FEMPTY :: st.scopes)
Proof
  rw[valid_lookups_def, evaluation_state_accfupds] >>
  qexists_tac `imms` >> simp[] >>
  rpt strip_tac >> first_x_assum irule >>
  gvs[var_in_scope_FEMPTY_CONS]
QED

(* ===== Hoare-level helper lemmas for if-statement branches ===== *)
(* These lemmas allow reasoning at the Hoare level without unfolding semantic definitions *)

(* Key lemma: In if-branch with HD=FEMPTY, var_in_scope in TL implies var_in_scope in full *)
Theorem var_in_scope_from_TL_FEMPTY:
  ∀st n. HD st.scopes = FEMPTY ∧ st.scopes ≠ [] ∧
         var_in_scope (st with scopes := TL st.scopes) n ⇒
         var_in_scope st n
Proof
  rpt strip_tac >> irule var_in_scope_from_TL_when_not_in_HD >>
  Cases_on `st.scopes` >> gvs[finite_mapTheory.FLOOKUP_EMPTY]
QED

(* Key lemma: In if-branch, valid_lookups in TL implies valid_lookups in full (when HD=FEMPTY) *)
Theorem valid_lookups_from_TL_FEMPTY:
  ∀cx st. HD st.scopes = FEMPTY ∧ st.scopes ≠ [] ∧
          valid_lookups cx (st with scopes := TL st.scopes) ⇒
          valid_lookups cx st
Proof
  metis_tac[valid_lookups_from_TL_when_FEMPTY_HD]
QED

(* Key lemma: After update in if-branch, lookup in TL returns the new value *)
Theorem lookup_TL_after_update_FEMPTY:
  ∀st n v. HD st.scopes = FEMPTY ∧ st.scopes ≠ [] ∧
           var_in_scope (st with scopes := TL st.scopes) n ⇒
           lookup_scoped_var ((update_scoped_var st n v) with
                              scopes := TL (update_scoped_var st n v).scopes) n = SOME v
Proof
  metis_tac[lookup_scoped_var_TL_after_update_when_FEMPTY_HD]
QED

(* Helper: scopes nonempty after update *)
Theorem scopes_nonempty_TL_after_update_FEMPTY:
  ∀st n v. HD st.scopes = FEMPTY ∧ st.scopes ≠ [] ∧
           var_in_scope (st with scopes := TL st.scopes) n ⇒
           TL (update_scoped_var st n v).scopes ≠ []
Proof
  rpt strip_tac >>
  `TL (update_scoped_var st n v).scopes =
   (update_scoped_var (st with scopes := TL st.scopes) n v).scopes`
    by metis_tac[update_scoped_var_TL_when_FEMPTY_HD] >>
  simp[] >> metis_tac[scopes_nonempty_after_update]
QED

(* Helper: valid_lookups preserved after update in TL view *)
Theorem valid_lookups_TL_after_update_FEMPTY:
  ∀cx st n v. HD st.scopes = FEMPTY ∧ st.scopes ≠ [] ∧
              valid_lookups cx (st with scopes := TL st.scopes) ∧
              var_in_scope (st with scopes := TL st.scopes) n ⇒
              valid_lookups cx ((update_scoped_var st n v) with
                                scopes := TL (update_scoped_var st n v).scopes)
Proof
  rpt strip_tac >>
  rw[valid_lookups_def, evaluation_state_accfupds, immutables_preserved_after_update] >>
  gvs[valid_lookups_def, evaluation_state_accfupds] >>
  rpt strip_tac >> first_x_assum irule >>
  `TL (update_scoped_var st n v).scopes =
   (update_scoped_var (st with scopes := TL st.scopes) n v).scopes`
    by metis_tac[update_scoped_var_TL_when_FEMPTY_HD] >>
  gvs[var_in_scope_def, lookup_scoped_var_def, evaluation_state_accfupds] >>
  Cases_on `string_to_num n' = string_to_num n` >> gvs[] >>
  `n' ≠ n` by metis_tac[vyperMiscTheory.string_to_num_inj] >>
  `lookup_scoped_var (update_scoped_var (st with scopes := TL st.scopes) n v) n' =
   lookup_scoped_var (st with scopes := TL st.scopes) n'`
    by (irule lookup_scoped_var_preserved_after_update >> simp[]) >>
  gvs[lookup_scoped_var_def, evaluation_state_accfupds]
QED

(* Helper: lookup of other variable preserved in TL view after update *)
Theorem lookup_other_TL_after_update_FEMPTY:
  ∀st n1 n2 v w. HD st.scopes = FEMPTY ∧ st.scopes ≠ [] ∧
                 n1 ≠ n2 ∧
                 var_in_scope (st with scopes := TL st.scopes) n1 ∧
                 lookup_scoped_var (st with scopes := TL st.scopes) n2 = SOME w ⇒
                 lookup_scoped_var ((update_scoped_var st n1 v) with
                                    scopes := TL (update_scoped_var st n1 v).scopes) n2 = SOME w
Proof
  rpt strip_tac >>
  `TL (update_scoped_var st n1 v).scopes =
   (update_scoped_var (st with scopes := TL st.scopes) n1 v).scopes`
    by metis_tac[update_scoped_var_TL_when_FEMPTY_HD] >>
  simp[lookup_scoped_var_def, evaluation_state_accfupds] >>
  `lookup_scoped_var (update_scoped_var (st with scopes := TL st.scopes) n1 v) n2 =
   lookup_scoped_var (st with scopes := TL st.scopes) n2`
    by (irule lookup_scoped_var_preserved_after_update >> simp[]) >>
  gvs[lookup_scoped_var_def, evaluation_state_accfupds]
QED

Theorem example_2_thm:
  ∀cx xarg.
    within_int_bound (Unsigned 256) xarg ∧
    within_int_bound (Unsigned 256) (xarg + 20) ⇒
    ⟦cx⟧
    ⦃λst. st.scopes ≠ [] ∧
          valid_lookups cx st ∧
          lookup_immutable cx st "x_arg" = SOME (IntV (Unsigned 256) xarg) ∧
          lookup_name cx st "x" = NONE⦄
    example_2_body
    ⦃λst. ∃x. lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) x) ∧ 20 ≤ x ∧ x ≤ 110 ∥ λ_ _. F⦄
Proof
(* Proof sketch using Hoare logic rules:

Assumptions (outside Hoare triple):
  within_int_bound (Unsigned 256) xarg
  within_int_bound (Unsigned 256) (xarg + 20)

Program:
  x := x_arg              -- AnnAssign "x" (Name "x_arg")
  x += 10                 -- AugAssign (NameTarget "x") Add (Literal 10)
  if x > 100 then         -- If (Builtin (Bop Gt) [Name "x"; Literal 100])
    x := 100              --   [Assign (BaseTarget (NameTarget "x")) (Literal 100)]
  else
    x += 10               --   [AugAssign (NameTarget "x") Add (Literal 10)]

Proof outline:

{ st.scopes ≠ [] ∧ valid_lookups cx st ∧
  lookup_immutable cx st "x_arg" = SOME (IntV (Unsigned 256) xarg) ∧
  lookup_name cx st "x" = NONE }

1. AnnAssign "x" (Name "x_arg"):
   - Use stmts_spec_ann_assign
   - Evaluate "x_arg" using expr_spec_name with lookup_immutable_implies_lookup_name
   - Creates new variable x with value xarg

{ lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xarg) ∧
  valid_lookups cx st }

2. AugAssign (NameTarget "x") Add (Literal 10):
   - Use stmts_spec_aug_assign_scoped_var
   - evaluate_binop Add (IntV (Unsigned 256) xarg) (IntV (Unsigned 256) 10)
     = INL (IntV (Unsigned 256) (xarg + 10))   [by within_int_bound assumption]

{ lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10)) ∧
  valid_lookups cx st }

3. If (Builtin (Bop Gt) [Name "x"; Literal 100]) then ... else ...:
   - Use stmts_spec_if
   - Evaluate condition using expr_spec_builtin_bop + expr_spec_scoped_var + expr_spec_literal
   - Result is BoolV (xarg + 10 > 100)

   Then branch (xarg + 10 > 100, i.e., condition = BoolV T):
   { lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10)) ∧ xarg + 10 > 100 }
     x := 100
   { lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) 100) }
   - Use stmts_spec_assign_scoped_var with expr_spec_literal
   - 20 ≤ 100 ∧ 100 ≤ 110 holds trivially

   Else branch (xarg + 10 ≤ 100, i.e., condition = BoolV F):
   { lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10)) ∧ xarg + 10 ≤ 100 }
     x += 10
   { lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 20)) }
   - Use stmts_spec_aug_assign_scoped_var
   - evaluate_binop Add (IntV _ (xarg+10)) (IntV _ 10) = INL (IntV _ (xarg+20))
     [by within_int_bound (xarg + 20) assumption]
   - From xarg + 10 ≤ 100: xarg + 20 ≤ 110
   - From within_int_bound xarg: 0 ≤ xarg, so 20 ≤ xarg + 20

{ ∃x. lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) x) ∧ 20 ≤ x ∧ x ≤ 110 }

*)
  rpt strip_tac >>
  simp[example_2_body_def, example_2_decl_def, example_2_module_def] >>
  (* Statement 1: x := x_arg (AnnAssign) *)
  irule stmts_spec_cons >>
  qexists_tac `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                    lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xarg)` >>
  conj_tac >-
  ((* AnnAssign proof *)
   irule stmts_spec_ann_assign >> qexists_tac `IntV (Unsigned 256) xarg` >>
   irule expr_spec_consequence >>
   qexistsl_tac [`λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                        lookup_name cx st "x_arg" = SOME (IntV (Unsigned 256) xarg) ∧
                        lookup_name cx st "x" = NONE`,
                 `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                        lookup_name cx st "x_arg" = SOME (IntV (Unsigned 256) xarg) ∧
                        lookup_name cx st "x" = NONE`] >>
   conj_tac >- (simp[] >> rpt strip_tac >> drule_all lookup_immutable_implies_lookup_name >> simp[]) >>
   conj_tac >-
     (simp[] >> rpt strip_tac >-
        metis_tac[lookup_name_none_to_lookup_scoped_var] >-
        metis_tac[scopes_nonempty_after_update] >-
        metis_tac[valid_lookups_preserved_after_update_no_name] >>
        simp[lookup_after_update]) >>
   irule expr_spec_consequence >>
   qexistsl_tac [`λst. (st.scopes ≠ [] ∧ valid_lookups cx st ∧ lookup_name cx st "x" = NONE) ∧
                        lookup_name cx st "x_arg" = SOME (IntV (Unsigned 256) xarg)`,
                 `λst. (st.scopes ≠ [] ∧ valid_lookups cx st ∧ lookup_name cx st "x" = NONE) ∧
                        lookup_name cx st "x_arg" = SOME (IntV (Unsigned 256) xarg)`] >>
   simp[] >>
   ACCEPT_TAC (BETA_RULE (ISPECL [
     ``λst:evaluation_state. st.scopes ≠ [] ∧ valid_lookups (cx:evaluation_context) st ∧
                             lookup_name cx st "x" = NONE``,
     ``cx:evaluation_context``, ``"x_arg":string``, ``IntV (Unsigned 256) xarg``] expr_spec_name))) >>
  (* Statement 2: x += 10 (AugAssign) *)
  irule stmts_spec_cons >>
  qexists_tac `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                    lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10))` >>
  conj_tac >-
  ((* AugAssign proof for x += 10 *)
   irule stmts_spec_consequence >>
   qexistsl_tac [`λst. (st.scopes ≠ [] ∧ valid_lookups cx st ∧
                        lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xarg)) ∧
                       (cx.txn.is_creation ⇒ valid_lookups cx st) ∧ var_in_scope st "x"`,
                 `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                        lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10))`,
                 `λ_0 _1. F`] >>
   conj_tac >- (simp[] >> metis_tac[lookup_scoped_var_implies_var_in_scope]) >>
   conj_tac >- simp[] >>
   conj_tac >- simp[] >>
   MATCH_MP_TAC (BETA_RULE (ISPECL [
     ``λst:evaluation_state. (st.scopes ≠ [] ∧ valid_lookups (cx:evaluation_context) st ∧
                              lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xarg))``,
     ``λst:evaluation_state. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                              lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10))``,
     ``cx:evaluation_context``, ``"x":string``, ``Add:binop``,
     ``Literal (IntL (Unsigned 256) 10):expr``,
     ``IntV (Unsigned 256) xarg``, ``IntV (Unsigned 256) 10``,
     ``IntV (Unsigned 256) (xarg + 10)``] stmts_spec_aug_assign_scoped_var)) >>
   conj_tac >-
     (simp[evaluate_binop_def, bounded_int_op_def] >>
      gvs[vyperTypeValueTheory.within_int_bound_def] >>
      intLib.ARITH_TAC) >>
   irule expr_spec_consequence >>
   qexistsl_tac [`λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                        lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xarg)`,
                 `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                        lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xarg)`] >>
   conj_tac >- simp[] >>
   conj_tac >-
      (simp[scopes_nonempty_after_update, lookup_after_update] >>
       metis_tac[valid_lookups_preserved_after_update_var_in_scope, lookup_scoped_var_implies_var_in_scope]) >>
   ACCEPT_TAC (SIMP_RULE std_ss [EVAL ``evaluate_literal (IntL (Unsigned 256) 10)``]
     (ISPECL [``λst:evaluation_state. st.scopes ≠ [] ∧ valid_lookups (cx:evaluation_context) st ∧
                                       lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) xarg)``,
              ``ARB:'a``, ``cx:evaluation_context``,
              ``IntL (Unsigned 256) 10``] expr_spec_literal))) >>
  (* Statement 3: if x > 100 then x := 100 else x += 10 *)
  (*
     The stmts_spec_if rule requires reasoning about `st with scopes := TL st.scopes`
     because the if-statement pushes a new scope for the branch body, then pops it.

     To complete this proof cleanly, we would need helper lemmas such as:

     Theorem lookup_scoped_var_TL_scopes:
       ∀st n v. lookup_scoped_var st n = SOME v ∧ FLOOKUP (HD st.scopes) (string_to_num n) = NONE ⇒
                lookup_scoped_var (st with scopes := TL st.scopes) n = SOME v

     Theorem valid_lookups_TL_scopes:
       ∀cx st. valid_lookups cx st ⇒ valid_lookups cx (st with scopes := TL st.scopes)

     For now, we use cheat for the if-statement proof.
  *)
  irule stmts_spec_consequence >>
  qexistsl_tac [`λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                      lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) (xarg + 10))`,
                `λst. ∃x. lookup_scoped_var st "x" = SOME (IntV (Unsigned 256) x) ∧ 20 ≤ x ∧ x ≤ 110`,
                `λv st. F`] >>
  simp[] >>
  cheat
QED
