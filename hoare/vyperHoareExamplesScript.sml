Theory vyperHoareExamples

Ancestors
  vyperHoare vyperInterpreter vyperAssignTargetSpec

open integerTheory

Definition example_1_def:
  example_1 = [
    AnnAssign "x" (BaseT (IntT 128)) (Literal (IntL (Signed 128) 10));
    AnnAssign "y" (BaseT (IntT 128)) (Name "x");
  ]
End

Definition sum_local_vars_def:
  sum_local_vars [] st = 0 ∧
  sum_local_vars (id::ids) st =
    let rest = sum_local_vars ids st in
    case lookup_scopes (string_to_num id) st.scopes of
      NONE => rest
    | SOME v =>
        case dest_NumV v of
          NONE => rest
        | SOME n => n + rest
End

(* Valid initial state for example_1: variables x, y don't exist yet *)
Definition valid_initial_state_def:
  valid_initial_state cx st <=>
    st.scopes ≠ [] ∧
    lookup_scopes (string_to_num "x") st.scopes = NONE ∧
    lookup_scopes (string_to_num "y") st.scopes = NONE ∧
    IS_SOME (ALOOKUP st.globals cx.txn.target) ∧
    (let gbs = THE (ALOOKUP st.globals cx.txn.target) in
       FLOOKUP (get_module_globals NONE gbs).immutables (string_to_num "x") = NONE ∧
       FLOOKUP (get_module_globals NONE gbs).immutables (string_to_num "y") = NONE)
End

Theorem example_1_sum_20:
  ∀cx. ⟦cx⟧ ⦃valid_initial_state cx⦄ example_1 ⦃(λst. sum_local_vars ["x"; "y"] st = 20) ∥ (λv st. F)⦄
Proof
  rpt strip_tac >>
  simp[example_1_def] >>
  (* Use consequence to set up the proof structure *)
  irule stmts_spec_consequence >>
  qexists_tac `λst. st.scopes ≠ [] ∧
                    lookup_scopes (string_to_num "x") st.scopes = NONE ∧
                    lookup_scopes (string_to_num "y") st.scopes = NONE ∧
                    IS_SOME (ALOOKUP st.globals cx.txn.target) ∧
                    FLOOKUP (get_module_globals NONE (THE (ALOOKUP st.globals cx.txn.target))).immutables (string_to_num "x") = NONE ∧
                    FLOOKUP (get_module_globals NONE (THE (ALOOKUP st.globals cx.txn.target))).immutables (string_to_num "y") = NONE` >>
  simp[valid_initial_state_def] >>
  (* Provide Q and R for consequence *)
  qexistsl_tac [`λst. lookup_scopes (string_to_num "x") st.scopes = SOME (IntV (Signed 128) 10) ∧
                      lookup_scopes (string_to_num "y") st.scopes = SOME (IntV (Signed 128) 10)`,
                `λv st:evaluation_state. F`] >>
  conj_tac >- simp[sum_local_vars_def, dest_NumV_def] >>
  conj_tac >- simp[] >>
  (* Split into two statements using cons *)
  irule stmts_spec_consequence >> simp[] >>
  irule_at Any stmts_spec_cons >>
  qexistsl_tac [`λv st:evaluation_state. F`, `λv st:evaluation_state. F`] >>
  simp[] >>
  (* Final postcondition P3 *)
  qexists_tac `λst. lookup_scopes (string_to_num "x") st.scopes = SOME (IntV (Signed 128) 10) ∧
                    lookup_scopes (string_to_num "y") st.scopes = SOME (IntV (Signed 128) 10)` >>
  simp[] >>
  (* Intermediate postcondition P2 (after first stmt, before second) *)
  qexists_tac `λst. st.scopes ≠ [] ∧
                    lookup_scopes (string_to_num "x") st.scopes = SOME (IntV (Signed 128) 10) ∧
                    lookup_scopes (string_to_num "y") st.scopes = NONE ∧
                    IS_SOME (ALOOKUP st.globals cx.txn.target) ∧
                    FLOOKUP (get_module_globals NONE (THE (ALOOKUP st.globals cx.txn.target))).immutables (string_to_num "x") = NONE ∧
                    FLOOKUP (get_module_globals NONE (THE (ALOOKUP st.globals cx.txn.target))).immutables (string_to_num "y") = NONE` >>
  (* Precondition P1 for first statement *)
  qexists_tac `λst. st.scopes ≠ [] ∧
                    lookup_scopes (string_to_num "x") st.scopes = NONE ∧
                    lookup_scopes (string_to_num "y") st.scopes = NONE ∧
                    IS_SOME (ALOOKUP st.globals cx.txn.target) ∧
                    FLOOKUP (get_module_globals NONE (THE (ALOOKUP st.globals cx.txn.target))).immutables (string_to_num "x") = NONE ∧
                    FLOOKUP (get_module_globals NONE (THE (ALOOKUP st.globals cx.txn.target))).immutables (string_to_num "y") = NONE` >>
  simp[] >>
  (* First statement: x := 10 *)
  conj_tac >- (
    irule stmts_spec_ann_assign >>
    qexists_tac `IntV (Signed 128) 10` >>
    irule expr_spec_consequence >>
    CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM evaluate_literal_def])) >>
    irule_at Any expr_spec_literal >>
    qexists_tac `λst. st.scopes ≠ [] ∧
                      lookup_scopes (string_to_num "x") st.scopes = NONE ∧
                      lookup_scopes (string_to_num "y") st.scopes = NONE ∧
                      IS_SOME (ALOOKUP st.globals cx.txn.target) ∧
                      FLOOKUP (get_module_globals NONE (THE (ALOOKUP st.globals cx.txn.target))).immutables (string_to_num "x") = NONE ∧
                      FLOOKUP (get_module_globals NONE (THE (ALOOKUP st.globals cx.txn.target))).immutables (string_to_num "y") = NONE` >>
    conj_tac >- simp[] >>
    simp[] >>
    rpt strip_tac >>
    simp[lookup_scopes_def, finite_mapTheory.FLOOKUP_UPDATE] >>
    Cases_on `st.scopes` >> fs[] >>
    EVAL_TAC >>
    fs[lookup_scopes_def] >>
    gvs[AllCaseEqs()] >>
    EVAL_TAC >>
    qpat_x_assum `FLOOKUP h (string_to_num "y") = NONE` mp_tac >> EVAL_TAC >>
    qpat_x_assum `lookup_scopes (string_to_num "y") t = NONE` mp_tac >> EVAL_TAC >>
    simp[]) >>
  (* Second statement: y := x *)
  irule stmts_spec_ann_assign >>
  qexists_tac `IntV (Signed 128) 10` >>
  irule expr_spec_consequence >>
  irule_at Any expr_spec_name >>
  qexists_tac `λst. st.scopes ≠ [] ∧
                    lookup_scopes (string_to_num "x") st.scopes = SOME (IntV (Signed 128) 10) ∧
                    lookup_scopes (string_to_num "y") st.scopes = NONE ∧
                    IS_SOME (ALOOKUP st.globals cx.txn.target) ∧
                    FLOOKUP (get_module_globals NONE (THE (ALOOKUP st.globals cx.txn.target))).immutables (string_to_num "x") = NONE ∧
                    FLOOKUP (get_module_globals NONE (THE (ALOOKUP st.globals cx.txn.target))).immutables (string_to_num "y") = NONE` >>
  simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      Cases_on `ALOOKUP st.globals cx.txn.target` >> gvs[] >>
      irule lookup_scopes_to_lookup_name >> simp[])
  >- (rpt strip_tac >>
      simp[lookup_scopes_def, finite_mapTheory.FLOOKUP_UPDATE] >>
      Cases_on `st.scopes` >> fs[lookup_scopes_def] >>
      gvs[AllCaseEqs()] >> EVAL_TAC)
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
