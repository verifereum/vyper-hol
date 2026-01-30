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
  (* Unfold example_1 to the two AnnAssign statements *)
  simp[example_1_def] >>
  (* Define intermediate invariant P1 after first assignment *)
  qabbrev_tac `P1 = λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
                         lookup_scoped_var st "x" = SOME (IntV (Signed 128) 10) ∧
                         lookup_name cx st "y" = NONE` >>
  (* Use specialized cons rule for F return predicates *)
  irule stmts_spec_cons >>
  qexists_tac `P1` >>
  conj_tac >-
  (* ===== First statement: AnnAssign "x" _ (Literal 10) ===== *)
  (irule stmts_spec_ann_assign >>
   qexists_tac `IntV (Signed 128) 10` >>
   (* Use expr_spec for Literal - state unchanged, evaluates to the literal value *)
   irule expr_spec_consequence >>
   qexistsl_tac [
     `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
           lookup_name cx st "x" = NONE ∧ lookup_name cx st "y" = NONE`,
     `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
           lookup_name cx st "x" = NONE ∧ lookup_name cx st "y" = NONE`
   ] >>
   rpt conj_tac >> simp[] >-
    (* Prove: postcondition of expr_spec implies precondition of AnnAssign *)
    (rpt strip_tac >> simp[Abbr `P1`] >-
     metis_tac[lookup_name_none_to_lookup_scoped_var] >-
     cheat) >>
   (* Rewrite value to match expr_spec_literal form *)
    `IntV (Signed 128) 10 = evaluate_literal (IntL (Signed 128) 10)` by EVAL_TAC >>
    pop_assum (fn th => ONCE_REWRITE_TAC [th]) >>
    irule expr_spec_literal) >>
  (* ===== Second statement: AnnAssign "y" _ (Name "x") ===== *)
  irule stmts_spec_consequence >>
  qexistsl_tac [
    `P1`,
    `λst. sum_scoped_vars ["x"; "y"] st = 20`,
    `λv st. F`
  ] >>
  simp[] >>
  irule stmts_spec_ann_assign >>
  qexists_tac `IntV (Signed 128) 10` >>
  (* Use expr_spec for Name "x" - requires lookup_scoped_var st "x" = SOME v *)
  irule expr_spec_consequence >>
  qexistsl_tac [
    `λst. P1 st`,
    `λst. P1 st`
  ] >>
  rpt conj_tac >> simp[Abbr `P1`] >> rpt strip_tac >-
   (metis_tac[lookup_name_none_to_lookup_scoped_var]) >-
   (* Prove: postcondition implies postcondition for AnnAssign *)
   ((* Show sum is 20 after updating y *)
    irule sum_scoped_vars_xy_20 >> conj_tac >-
      (metis_tac[lookup_after_update]) >>
    `"y" ≠ "x"` by EVAL_TAC >>
    drule_all lookup_preserved_after_update >> simp[]) >>
  (* Prove: expr_spec for Name "x" - use explicit instantiation *)
  irule expr_spec_consequence >>
  qexistsl_tac [
    `λst. (st.scopes ≠ [] ∧ valid_lookups cx st ∧
           lookup_scoped_var st "x" = SOME (IntV (Signed 128) 10) ∧
           lookup_name cx st "y" = NONE) ∧
          valid_lookups cx st ∧
          lookup_scoped_var st "x" = SOME (IntV (Signed 128) 10)`,
    `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
          lookup_scoped_var st "x" = SOME (IntV (Signed 128) 10) ∧
          lookup_name cx st "y" = NONE`
  ] >>
  simp[] >>
  cheat
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

(* ERC20 transfer *)

(* No duplicate keys in an alist *)
Definition no_dup_keys_def:
  no_dup_keys (hm : ('k # 'v) list) <=> ALL_DISTINCT (MAP FST hm)
End

(* All values in HashMap are non-negative integers *)
Definition all_values_nonneg_def:
  all_values_nonneg (hm : (subscript # toplevel_value) list) <=>
    EVERY (\(k, tv). case tv of
      | Value (IntV _ n) => n >= 0
      | _ => T) hm
End

(* Precondition: valid ERC20 state with balances HashMap
   Includes invariants:
   - HashMap exists at balances slot
   - No duplicate keys (required for sum lemmas)
   - All values are non-negative (required for subtraction) *)
Definition valid_erc20_state_def:
  valid_erc20_state contract_addr (st : evaluation_state) <=>
    ?gbs hm.
      ALOOKUP st.globals contract_addr = SOME gbs /\
      let mg = get_module_globals NONE gbs in
      FLOOKUP mg.mutables (string_to_num "balances") = SOME (HashMap (Type (BaseT (UintT 256))) hm) /\
      no_dup_keys hm /\
      all_values_nonneg hm
End

(* Valid transfer parameters: amount parameter is within uint256 bounds
   This is guaranteed by abi_to_vyper during external call setup, but we
   need it as an explicit precondition since valid_erc20_state only validates storage *)
Definition valid_transfer_params_def:
  valid_transfer_params cx (st : evaluation_state) <=>
    ?amt. eval_expr cx (Name "amount") st = (INL (Value (IntV (Unsigned 256) amt)), st) /\
          within_int_bound (Unsigned 256) amt
End

Definition erc20_transfer_def:
  erc20_transfer = [
    Assert (Builtin (Bop GtE) [Subscript (TopLevelName (NONE, "balances")) (Builtin (Env Sender) []); Name "amount"]) (Literal (StringL 5 "error"));
    AugAssign (SubscriptTarget (TopLevelNameTarget (NONE, "balances"))
                              (Builtin (Env Sender) [])) Sub (Name "amount");
    AugAssign (SubscriptTarget (TopLevelNameTarget (NONE, "balances"))
                              (Name "to")) Add (Name "amount");
    Return (SOME (Literal (BoolL T)))
  ]
End

(* Helper: Extract the balances HashMap from state.
   Returns NONE if contract not found or balances not a HashMap. *)
Definition get_balances_hashmap_def:
  get_balances_hashmap contract_addr (st : evaluation_state) =
    case ALOOKUP st.globals contract_addr of
    | NONE => NONE
    | SOME gbs =>
        let mg = get_module_globals NONE gbs in
        case FLOOKUP mg.mutables (string_to_num "balances") of
        | SOME (HashMap vt hm) => SOME (vt, hm)
        | _ => NONE
End

(* Extract integer value from a toplevel_value, returning 0 if not an integer *)
Definition toplevel_to_int_def:
  toplevel_to_int (Value (IntV _ n)) = n ∧
  toplevel_to_int _ = 0
End

(* Sum integer values in a hashmap (alist of subscript -> toplevel_value) *)
Definition sum_hashmap_balances_def:
  sum_hashmap_balances [] = 0 ∧
  sum_hashmap_balances ((k, v)::rest) = toplevel_to_int v + sum_hashmap_balances rest
End

(* Sum of all balances - moved here so set_global_updates_balances can use it *)
Definition sum_balances_def:
  sum_balances contract_addr (st : evaluation_state) =
    case ALOOKUP st.globals contract_addr of
    | NONE => 0
    | SOME gbs =>
        let mg = get_module_globals NONE gbs in
        case FLOOKUP mg.mutables (string_to_num "balances") of
        | NONE => 0
        | SOME (HashMap _ hm) => sum_hashmap_balances hm
        | _ => 0
End

Theorem erc20_sum_balances:
  ∀cx addr b. ⟦cx⟧ ⦃λst . valid_erc20_state addr st ∧ valid_transfer_params cx st ∧ sum_balances addr st = b⦄ erc20_transfer ⦃(λ_. F) ∥ (λ_ st . sum_balances addr st = b)⦄
Proof
  cheat
QED
