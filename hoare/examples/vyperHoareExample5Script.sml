Theory vyperHoareExample5

Ancestors
  jsonToVyper vyperHoare vyperInterpreter vyperLookup

Libs
  jsonASTLib intLib

val example_5_json_path = "example_5.json"

val example_5_jsonast_tm = JSONDecode.decodeFile (JSONDecode.field "ast" json_module) example_5_json_path

val example_5_vyperast_tm = let
  val translate_module_tm = prim_mk_const{Thy="jsonToVyper",Name="translate_module"}
  val app = mk_comb(translate_module_tm, example_5_jsonast_tm)
  val thm = EVAL app
in
  rhs (concl thm)
end

Definition example_5_module_def:
  example_5_module = ^example_5_vyperast_tm
End


Theorem example_5_has_1_toplevel:
  LENGTH example_5_module = 1
Proof
  EVAL_TAC
QED

Definition example_5_decl_def:
  example_5_decl = EL 0 example_5_module
End

Definition example_5_body_def:
  example_5_body = case example_5_decl of
    | FunctionDecl _ _ _ _ _ body => body
    | _ => []
End

Theorem example_5_body_length:
  LENGTH example_5_body = 3
Proof
  EVAL_TAC
QED

(* ===== Semantic Helper Lemmas ===== *)

(* Gauss sum: base case *)
Theorem gauss_sum_zero:
  0 * (0 − 1:int) / 2 = 0
Proof
  EVAL_TAC
QED

(* Helper: product of consecutive integers is even *)
Theorem consecutive_product_mod2:
  ∀k:int. 0 ≤ k ⇒ (k * (k − 1)) % 2 = 0
Proof
  rpt strip_tac >>
  (* Suffices: ((k%2) * ((k-1)%2)) % 2 = 0, then use INT_MOD_MUL *)
  `((k % 2) * ((k − 1) % 2)) % 2 = 0` suffices_by (
    disch_tac >>
    `(k * (k − 1)) % 2 = ((k % 2) * ((k − 1) % 2)) % 2` suffices_by simp[] >>
    irule ratTheory.INT_MOD_MUL >> simp[]) >>
  Cases_on `k % 2 = 0` >- simp[] >>
  (* k % 2 ≠ 0, so k % 2 = 1 by INT_DIVISION *)
  `k % 2 = 1` by (
    `0 ≤ k % 2 ∧ k % 2 < 2` suffices_by intLib.COOPER_TAC >>
    mp_tac (Q.SPEC `2` integerTheory.INT_DIVISION |> SIMP_RULE (srw_ss()) []) >>
    disch_then (qspec_then `k` mp_tac) >> simp[]) >>
  (* (k-1) % 2 = 0 by INT_MOD_SUB *)
  `(k − 1) % 2 = 0` by (
    `(k − 1) % 2 = (k % 2 − 1 % 2) % 2` by (
      irule (GSYM integerTheory.INT_MOD_SUB) >> simp[]) >>
    simp[]) >>
  simp[]
QED

(* Helper: algebraic identity for Gauss sum step *)
Theorem gauss_sum_identity:
  ∀k:int. 0 ≤ k ⇒ k * (k − 1) / 2 + k = (k + 1) * k / 2
Proof
  rpt strip_tac >>
  `(k * (k − 1)) % 2 = 0` by simp[consecutive_product_mod2] >>
  `(k + 1) * k = k * (k − 1) + 2 * k` by (
    simp[integerTheory.INT_RDISTRIB, integerTheory.INT_LDISTRIB,
         integerTheory.INT_SUB_LDISTRIB] >> intLib.COOPER_TAC) >>
  pop_assum (fn th => REWRITE_TAC [th]) >>
  `(k * (k − 1) + 2 * k) / 2 = k * (k − 1) / 2 + 2 * k / 2` by (
    irule integerTheory.INT_ADD_DIV >> simp[]) >>
  simp[integerTheory.INT_DIV_LMUL]
QED

(* Gauss sum: inductive step identity and bounds *)
Theorem gauss_sum_step:
  ∀k n:int. 0 ≤ k ∧ k < n ∧ n ≤ 1000000 ⇒
    within_int_bound (Unsigned 256) (k * (k − 1) / 2 + k) ∧
    k * (k − 1) / 2 + k = (k + 1) * k / 2
Proof
  rpt strip_tac >- (
    (* within_int_bound *)
    rw[vyperTypeValueTheory.within_int_bound_def] >- (
      (* 0 ≤ k * (k − 1) / 2 + k *)
      `k * (k − 1) / 2 + k = (k + 1) * k / 2` by simp[gauss_sum_identity] >>
      pop_assum SUBST_ALL_TAC >>
      `0 ≤ (k + 1) * k` by (irule integerTheory.INT_LE_MUL >> intLib.COOPER_TAC) >>
      mp_tac (Q.SPECL [`λq. 0i ≤ q`, `(k+1)*k`, `2`] integerTheory.INT_DIV_FORALL_P
        |> SIMP_RULE (srw_ss()) []) >>
      simp[] >> rpt strip_tac >> intLib.COOPER_TAC) >>
    (* Num (k * (k − 1) / 2 + k) < 2 ** 256 *)
    `k * (k − 1) / 2 + k = (k + 1) * k / 2` by simp[gauss_sum_identity] >>
    pop_assum SUBST_ALL_TAC >>
    irule arithmeticTheory.LESS_LESS_EQ_TRANS >>
    qexists_tac `1000000 * 1000000` >> conj_tac >- (
      (* Num ((k+1)*k/2) < 10^12 *)
      `0 ≤ (k + 1) * k / 2` by (
        `0 ≤ (k + 1) * k` by (irule integerTheory.INT_LE_MUL >> intLib.COOPER_TAC) >>
        mp_tac (Q.SPECL [`λq. 0i ≤ q`, `(k+1)*k`, `2`] integerTheory.INT_DIV_FORALL_P
          |> SIMP_RULE (srw_ss()) []) >>
        simp[] >> rpt strip_tac >> intLib.COOPER_TAC) >>
      `(k + 1) * k / 2 < &1000000000000` suffices_by (
        strip_tac >>
        `Num ((k + 1) * k / 2) < Num (&1000000000000:int)` suffices_by simp[] >>
        simp[integerTheory.NUM_LT]) >>
      (* (k+1)*k/2 < 10^12: use INT_DIV_FORALL_P *)
      mp_tac (Q.SPECL [`λq. q < 1000000000000i`, `(k+1)*k`, `2`]
        integerTheory.INT_DIV_FORALL_P |> SIMP_RULE (srw_ss()) []) >>
      simp[] >> rpt strip_tac >>
      Cases_on `k = 0` >- (gvs[] >> intLib.COOPER_TAC) >>
      (* k ≠ 0: bound (k+1)*k ≤ n*n ≤ 10^12 *)
      `(k + 1) * k ≤ n * n` by (
        irule integerTheory.INT_LE_TRANS >> qexists_tac `n * k` >> conj_tac >- (
          `0 < k ∧ k + 1 ≤ n` by intLib.COOPER_TAC >>
          `k * (k + 1) ≤ k * n` by simp[integerTheory.INT_LE_MONO] >>
          metis_tac[integerTheory.INT_MUL_COMM]) >>
        `0 < n` by intLib.COOPER_TAC >>
        simp[integerTheory.INT_LE_MONO] >> intLib.COOPER_TAC) >>
      `n * n ≤ 1000000 * 1000000` by (
        `0 < n` by intLib.COOPER_TAC >>
        irule integerTheory.INT_LE_TRANS >> qexists_tac `1000000 * n` >> conj_tac >- (
          `n * n ≤ n * 1000000` suffices_by simp[integerTheory.INT_MUL_COMM] >>
          simp[integerTheory.INT_LE_MONO]) >>
        simp[integerTheory.INT_LE_MONO]) >>
      intLib.COOPER_TAC) >>
    EVAL_TAC) >>
  (* algebraic identity *)
  simp[gauss_sum_identity]
QED

(* ===== Lemma 1: AnnAssign s := 0 ===== *)

(*
  Proof strategy:
  1. irule stmts_spec_ann_assign
  2. Use expr_spec_literal for Literal (IntL (Unsigned 256) 0)
  3. Postcondition obligations via lookup lemmas:
     - lookup_scoped_var st "s" = NONE (from lookup_name_none_to_lookup_scoped_var)
     - scopes_nonempty_after_update
     - valid_lookups_preserved_after_update_no_name
     - lookup_after_update
     - lookup_immutable_preserved_after_update
*)
Theorem stmt1_ann_assign_s:
  ∀cx n.
    ⟦cx⟧
    ⦃λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
          lookup_immutable cx st "n" = SOME (IntV (Unsigned 256) n) ∧
          lookup_name cx st "s" = NONE ∧
          lookup_immutable cx st "i" = NONE⦄
    [AnnAssign "s" (BaseT (UintT 256)) (Literal (IntL (Unsigned 256) 0))]
    ⦃λst. valid_lookups cx st ∧ st.scopes ≠ [] ∧
          lookup_scoped_var st "s" = SOME (IntV (Unsigned 256) 0) ∧
          lookup_immutable cx st "n" = SOME (IntV (Unsigned 256) n) ∧
          lookup_immutable cx st "i" = NONE
     ∥ λ_ _. F⦄
Proof
  rpt strip_tac >>
  irule stmts_spec_ann_assign >>
  irule expr_spec_consequence >>
  qexistsl_tac [
    `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
          lookup_immutable cx st "n" = SOME (IntV (Unsigned 256) n) ∧
          lookup_name cx st "s" = NONE ∧
          lookup_immutable cx st "i" = NONE`,
    `λtv st. (st.scopes ≠ [] ∧ valid_lookups cx st ∧
              lookup_immutable cx st "n" = SOME (IntV (Unsigned 256) n) ∧
              lookup_name cx st "s" = NONE ∧
              lookup_immutable cx st "i" = NONE) ∧
              tv = Value (IntV (Unsigned 256) 0)`] >>
  conj_tac >- simp[] >>
  conj_tac
  >- (simp[] >> rpt strip_tac >> gvs[]
      >- (drule_all lookup_name_none_to_lookup_scoped_var >> simp[])
      >- (irule valid_lookups_preserved_after_update_no_name >> simp[])
      >- gvs[scopes_nonempty_after_update]
      >- simp[lookup_after_update]
      >> simp[lookup_immutable_preserved_after_update])
  >> ACCEPT_TAC (SIMP_RULE std_ss [EVAL ``evaluate_literal (IntL (Unsigned 256) 0)``]
       (ISPECL [``λst:evaluation_state. st.scopes ≠ [] ∧
                   valid_lookups (cx:evaluation_context) st ∧
                   lookup_immutable cx st "n" = SOME (IntV (Unsigned 256) (n:int)) ∧
                   lookup_name cx st "s" = NONE ∧
                   lookup_immutable cx st "i" = NONE``,
                ``ARB:'a``, ``cx:evaluation_context``,
                ``IntL (Unsigned 256) 0``] expr_spec_literal))
QED

(* ===== Lemma 2: For loop body s += i ===== *)

(*
  Proof strategy:
  1. Use stmts_spec_consequence to connect for-body precondition to
     stmts_spec_aug_assign_scoped_var precondition
  2. Derive var_in_scope st "s" from lookup_scoped_var (tl_scopes st) "s"
     via lookup_in_tl_scopes (reversed)
  3. Evaluate Name "i" using expr_spec_scoped_var_eq
     (needs valid_lookups cx st, derived from valid_lookups cx (tl_scopes st))
  4. evaluate_binop Add gives k*(k-1)/2 + k = (k+1)*k/2 (gauss_sum_step)
  5. Postcondition: tl_scopes (update_scoped_var st "s" v)
     = update_scoped_var (tl_scopes st) "s" v
     (by tl_scopes_update_eq_update_tl_scopes, since "s" not in current scope)
*)
Theorem for_body_lemma:
  ∀cx n k.
    0 ≤ k ∧ k < n ∧ n ≤ 1000000 ⇒
    ⟦cx⟧
    ⦃λst. st.scopes ≠ [] ∧
          HD st.scopes = FEMPTY |+ (string_to_num "i", IntV (Unsigned 256) k) ∧
          valid_lookups cx (tl_scopes st) ∧
          (tl_scopes st).scopes ≠ [] ∧
          lookup_scoped_var (tl_scopes st) "s" =
            SOME (IntV (Unsigned 256) (k * (k − 1) / 2)) ∧
          lookup_immutable cx (tl_scopes st) "n" =
            SOME (IntV (Unsigned 256) n) ∧
          lookup_immutable cx (tl_scopes st) "i" = NONE⦄
    [AugAssign (NameTarget "s") Add (Name "i")]
    ⦃λst. valid_lookups cx (tl_scopes st) ∧
          (tl_scopes st).scopes ≠ [] ∧
          lookup_scoped_var (tl_scopes st) "s" =
            SOME (IntV (Unsigned 256) ((k + 1) * k / 2)) ∧
          lookup_immutable cx (tl_scopes st) "n" =
            SOME (IntV (Unsigned 256) n) ∧
          lookup_immutable cx (tl_scopes st) "i" = NONE
     ∥ λv st. F⦄
Proof
  rpt strip_tac >>
  irule stmts_spec_consequence >>
  qexistsl_tac [
    `λst. (valid_lookups cx st ∧ st.scopes ≠ [] ∧
           HD st.scopes = FEMPTY |+ (string_to_num "i", IntV (Unsigned 256) k) ∧
           lookup_scoped_var st "i" = SOME (IntV (Unsigned 256) k) ∧
           lookup_scoped_var st "s" = SOME (IntV (Unsigned 256) (k * (k − 1) / 2)) ∧
           valid_lookups cx (tl_scopes st) ∧ (tl_scopes st).scopes ≠ [] ∧
           lookup_immutable cx (tl_scopes st) "n" = SOME (IntV (Unsigned 256) n) ∧
           lookup_immutable cx (tl_scopes st) "i" = NONE) ∧
          (cx.txn.is_creation ⇒ valid_lookups cx st) ∧ var_in_scope st "s"`,
    `λst. valid_lookups cx (tl_scopes st) ∧ (tl_scopes st).scopes ≠ [] ∧
          lookup_scoped_var (tl_scopes st) "s" =
            SOME (IntV (Unsigned 256) ((k + 1) * k / 2)) ∧
          lookup_immutable cx (tl_scopes st) "n" = SOME (IntV (Unsigned 256) n) ∧
          lookup_immutable cx (tl_scopes st) "i" = NONE`,
    `λv st. F`] >>
  simp[] >>
  conj_tac >- (
    rpt strip_tac
    >- (irule valid_lookups_push_singleton >> simp[] >>
        qexistsl_tac [`"i"`, `IntV (Unsigned 256) k`] >>
        simp[] >> metis_tac[lookup_immutable_tl_scopes])
    >- (irule lookup_in_current_scope_to_lookup_scoped_var >> simp[] >>
        simp[lookup_in_current_scope_def, finite_mapTheory.FLOOKUP_UPDATE])
    >- (`lookup_in_current_scope st "s" = NONE` by (
          simp[lookup_in_current_scope_def] >>
          `string_to_num "s" ≠ string_to_num "i"` suffices_by
            simp[finite_mapTheory.FLOOKUP_UPDATE] >>
          simp[vyperMiscTheory.string_to_num_inj]) >>
        metis_tac[lookup_in_tl_scopes])
    >- (irule valid_lookups_push_singleton >> simp[] >>
        qexistsl_tac [`"i"`, `IntV (Unsigned 256) k`] >>
        simp[] >> metis_tac[lookup_immutable_tl_scopes])
    >- (irule lookup_scoped_var_implies_var_in_scope >>
        `lookup_in_current_scope st "s" = NONE` by (
          simp[lookup_in_current_scope_def] >>
          `string_to_num "s" ≠ string_to_num "i"` suffices_by
            simp[finite_mapTheory.FLOOKUP_UPDATE] >>
          simp[vyperMiscTheory.string_to_num_inj]) >>
        metis_tac[lookup_in_tl_scopes])) >>
  MATCH_MP_TAC (BETA_RULE (ISPECL [
    ``λst:evaluation_state.
        valid_lookups (cx:evaluation_context) st ∧ st.scopes ≠ [] ∧
        HD st.scopes = FEMPTY |+ (string_to_num "i", IntV (Unsigned 256) (k:int)) ∧
        lookup_scoped_var st "i" = SOME (IntV (Unsigned 256) k) ∧
        lookup_scoped_var st "s" = SOME (IntV (Unsigned 256) (k * (k − 1) / 2)) ∧
        valid_lookups cx (tl_scopes st) ∧ (tl_scopes st).scopes ≠ [] ∧
        lookup_immutable cx (tl_scopes st) "n" = SOME (IntV (Unsigned 256) (n:int)) ∧
        lookup_immutable cx (tl_scopes st) "i" = NONE``,
    ``λst:evaluation_state.
        valid_lookups (cx:evaluation_context) (tl_scopes st) ∧
        (tl_scopes st).scopes ≠ [] ∧
        lookup_scoped_var (tl_scopes st) "s" =
          SOME (IntV (Unsigned 256) (((k:int) + 1) * k / 2)) ∧
        lookup_immutable cx (tl_scopes st) "n" = SOME (IntV (Unsigned 256) (n:int)) ∧
        lookup_immutable cx (tl_scopes st) "i" = NONE``,
    ``cx:evaluation_context``, ``"s":string``, ``Add:binop``,
    ``Name "i":expr``] stmts_spec_aug_assign_scoped_var)) >>
  irule expr_spec_consequence >>
  qexistsl_tac [
    `λst. (st.scopes ≠ [] ∧
           HD st.scopes = FEMPTY |+ (string_to_num "i", IntV (Unsigned 256) k) ∧
           lookup_scoped_var st "s" = SOME (IntV (Unsigned 256) (k * (k − 1) / 2)) ∧
           valid_lookups cx (tl_scopes st) ∧ (tl_scopes st).scopes ≠ [] ∧
           lookup_immutable cx (tl_scopes st) "n" = SOME (IntV (Unsigned 256) n) ∧
           lookup_immutable cx (tl_scopes st) "i" = NONE) ∧
          valid_lookups cx st ∧
          lookup_scoped_var st "i" = SOME (IntV (Unsigned 256) k)`,
    `λtv st.
          (st.scopes ≠ [] ∧
           HD st.scopes = FEMPTY |+ (string_to_num "i", IntV (Unsigned 256) k) ∧
           lookup_scoped_var st "s" = SOME (IntV (Unsigned 256) (k * (k − 1) / 2)) ∧
           valid_lookups cx (tl_scopes st) ∧ (tl_scopes st).scopes ≠ [] ∧
           lookup_immutable cx (tl_scopes st) "n" = SOME (IntV (Unsigned 256) n) ∧
           lookup_immutable cx (tl_scopes st) "i" = NONE) ∧
          valid_lookups cx st ∧
          lookup_scoped_var st "i" = SOME (IntV (Unsigned 256) k) ∧
          tv = Value (IntV (Unsigned 256) k)`] >>
  conj_tac >- simp[] >>
  conj_tac >- (
    simp[] >> rpt strip_tac >>
    qexists_tac `IntV (Unsigned 256) ((k + 1) * k / 2)` >> simp[] >>
    conj_tac >- (
      simp[evaluate_binop_def, bounded_int_op_def] >>
      `within_int_bound (Unsigned 256) (k * (k − 1) / 2 + k)` by
        (drule_all gauss_sum_step >> simp[]) >>
      `k * (k − 1) / 2 + k = (k + 1) * k / 2` by
        (drule_all gauss_sum_step >> simp[]) >>
      simp[]) >>
    `lookup_in_current_scope st "s" = NONE` by (
      simp[lookup_in_current_scope_def] >>
      `string_to_num "s" ≠ string_to_num "i"` suffices_by
        simp[finite_mapTheory.FLOOKUP_UPDATE] >>
      simp[vyperMiscTheory.string_to_num_inj]) >>
    `lookup_scoped_var (tl_scopes st) "s" =
       SOME (IntV (Unsigned 256) (k * (k − 1) / 2))` by
      metis_tac[lookup_in_tl_scopes] >>
    `var_in_scope (tl_scopes st) "s"` by
      metis_tac[lookup_scoped_var_implies_var_in_scope] >>
    simp[valid_lookups_preserved_after_update_in_tl_scopes,
         scopes_nonempty_preserved_after_update_in_tl_scopes,
         lookup_scoped_var_update_in_tl_scopes,
         lookup_immutable_tl_scopes, lookup_immutable_preserved_after_update] >>
    metis_tac[lookup_immutable_tl_scopes]) >>
  ACCEPT_TAC (BETA_RULE (ISPECL [
    ``λst:evaluation_state. st.scopes ≠ [] ∧
       HD st.scopes = FEMPTY |+ (string_to_num "i", IntV (Unsigned 256) (k:int)) ∧
       lookup_scoped_var st "s" = SOME (IntV (Unsigned 256) (k * (k − 1) / 2)) ∧
       valid_lookups (cx:evaluation_context) (tl_scopes st) ∧
       (tl_scopes st).scopes ≠ [] ∧
       lookup_immutable cx (tl_scopes st) "n" = SOME (IntV (Unsigned 256) (n:int)) ∧
       lookup_immutable cx (tl_scopes st) "i" = NONE``,
    ``cx:evaluation_context``, ``"i":string``,
    ``IntV (Unsigned 256) k``] expr_spec_scoped_var_eq))
QED

(* ===== Lemma 3: For loop ===== *)

(*
  Proof strategy:
  1. irule stmts_spec_for_range with:
     - I = λk st. valid_lookups cx st ∧ st.scopes ≠ [] ∧
                   lookup_scoped_var st "s" = SOME (IntV (Unsigned 256) (k*(k-1)/2)) ∧
                   lookup_immutable cx st "n" = SOME (IntV (Unsigned 256) n)
     - v1 = IntV (Unsigned 256) 0, v2 = IntV (Unsigned 256) n
     - n_start = 0, m = Num n
  2. Subgoals:
     a. Num n ≤ 1000000 (from 0 ≤ n ∧ n ≤ 1000000)
     b. get_range_limits v1 v2 = INL (Unsigned 256, 0, Num n)
        (needs 0 ≤ n, via get_range_limits_def)
     c. expr_spec for e1 = Literal 0 (via expr_spec_literal)
     d. expr_spec for e2 = Name "n"
        (via expr_spec_name_eq + lookup_immutable_implies_lookup_name)
        Postcondition establishes I(0) with gauss_sum_zero
     e. Body: use for_body_lemma
  3. Postcondition: I(0 + &(Num n)) = I(n) (since 0 ≤ n)
*)
val for_range_inst = BETA_RULE (ISPECL [
    ``λst:evaluation_state. valid_lookups (cx:evaluation_context) st ∧ st.scopes ≠ [] ∧
        lookup_scoped_var st "s" = SOME (IntV (Unsigned 256) 0i) ∧
        lookup_immutable cx st "n" = SOME (IntV (Unsigned 256) (n:int)) ∧
        lookup_immutable cx st "i" = NONE``,
    ``λst:evaluation_state. valid_lookups (cx:evaluation_context) st ∧ st.scopes ≠ [] ∧
        lookup_scoped_var st "s" = SOME (IntV (Unsigned 256) 0i) ∧
        lookup_immutable cx st "n" = SOME (IntV (Unsigned 256) (n:int)) ∧
        lookup_immutable cx st "i" = NONE``,
    ``λ(k:int) (st:evaluation_state). valid_lookups (cx:evaluation_context) st ∧ st.scopes ≠ [] ∧
        lookup_scoped_var st "s" = SOME (IntV (Unsigned 256) (k * (k − 1) / 2)) ∧
        lookup_immutable cx st "n" = SOME (IntV (Unsigned 256) (n:int)) ∧
        lookup_immutable cx st "i" = NONE``,
    ``cx:evaluation_context``,
    ``"i":string``,
    ``BaseT (UintT 256):type``,
    ``Unsigned 256:int_bound``,
    ``Literal (IntL (Unsigned 256) 0):expr``,
    ``Name "n":expr``,
    ``1000000:num``,
    ``[AugAssign (NameTarget "s") Add (Name "i")]:stmt list``,
    ``IntV (Unsigned 256) 0:value``,
    ``IntV (Unsigned 256) (n:int):value``,
    ``0:int``,
    ``Num (n:int):num``
  ] stmts_spec_for_range);

Theorem stmt2_for_range:
  ∀cx n.
    0 ≤ n ∧ n ≤ 1000000 ⇒
    ⟦cx⟧
    ⦃λst. valid_lookups cx st ∧ st.scopes ≠ [] ∧
          lookup_scoped_var st "s" = SOME (IntV (Unsigned 256) 0) ∧
          lookup_immutable cx st "n" = SOME (IntV (Unsigned 256) n) ∧
          lookup_immutable cx st "i" = NONE⦄
    [For "i" (BaseT (UintT 256))
      (Range (Literal (IntL (Unsigned 256) 0)) (Name "n")) 1000000
      [AugAssign (NameTarget "s") Add (Name "i")]]
    ⦃λst. valid_lookups cx st ∧ st.scopes ≠ [] ∧
          lookup_scoped_var st "s" =
            SOME (IntV (Unsigned 256) (n * (n − 1) / 2)) ∧
          lookup_immutable cx st "n" = SOME (IntV (Unsigned 256) n) ∧
          lookup_immutable cx st "i" = NONE
     ∥ λ_ _. F⦄
Proof
  rpt strip_tac >>
  (* Wrap with consequence to adapt postcondition from I(0 + &Num n) to I(n) *)
  irule stmts_spec_consequence >>
  qexistsl_tac [
    `λst. valid_lookups cx st ∧ st.scopes ≠ [] ∧
          lookup_scoped_var st "s" = SOME (IntV (Unsigned 256) 0) ∧
          lookup_immutable cx st "n" = SOME (IntV (Unsigned 256) n) ∧
          lookup_immutable cx st "i" = NONE`,
    `λst. valid_lookups cx st ∧ st.scopes ≠ [] ∧
          lookup_scoped_var st "s" =
            SOME (IntV (Unsigned 256) ((0 + &Num n) * (0 + &Num n − 1) / 2)) ∧
          lookup_immutable cx st "n" = SOME (IntV (Unsigned 256) n) ∧
          lookup_immutable cx st "i" = NONE`,
    `λv st. F`] >>
  (* Handle consequence subgoals individually to avoid simp touching stmts_spec *)
  (* P ⇒ P' (trivial, same) *)
  (conj_tac >- simp[]) >>
  (* Q' ⇒ Q: I(0 + &Num n) ⇒ I(n) *)
  (conj_tac >- (simp[] >> rpt strip_tac >>
    `&Num n = n` by simp[integerTheory.INT_OF_NUM] >>
    pop_assum SUBST_ALL_TAC >> simp[])) >>
  (* R' ⇒ R (trivial, F ⇒ F) *)
  (conj_tac >- simp[]) >>
  (* Apply stmts_spec_for_range with pre-instantiated theorem *)
  MATCH_MP_TAC for_range_inst >>
  rpt conj_tac
  (* 1. Num n ≤ 1000000 *)
  >- (`Num n ≤ Num (&1000000:int)` suffices_by simp[integerTheory.NUM_OF_INT] >>
      `¬(Num 1000000 < Num n)` suffices_by DECIDE_TAC >>
      simp[integerTheory.NUM_LT] >> intLib.COOPER_TAC)
  (* 2. get_range_limits *)
  >- simp[get_range_limits_def]
  (* 3. expr_spec for Literal 0 *)
  >- (irule expr_spec_consequence >>
      qexistsl_tac [
        `λst. valid_lookups cx st ∧ st.scopes ≠ [] ∧
              lookup_scoped_var st "s" = SOME (IntV (Unsigned 256) 0) ∧
              lookup_immutable cx st "n" = SOME (IntV (Unsigned 256) n) ∧
              lookup_immutable cx st "i" = NONE`,
        `λtv st. (valid_lookups cx st ∧ st.scopes ≠ [] ∧
                  lookup_scoped_var st "s" = SOME (IntV (Unsigned 256) 0) ∧
                  lookup_immutable cx st "n" = SOME (IntV (Unsigned 256) n) ∧
                  lookup_immutable cx st "i" = NONE) ∧
                 tv = Value (IntV (Unsigned 256) 0)`] >>
      simp[] >>
      ACCEPT_TAC (SIMP_RULE std_ss [EVAL ``evaluate_literal (IntL (Unsigned 256) 0)``]
        (ISPECL [``λst:evaluation_state. valid_lookups (cx:evaluation_context) st ∧
                    st.scopes ≠ [] ∧
                    lookup_scoped_var st "s" = SOME (IntV (Unsigned 256) 0i) ∧
                    lookup_immutable cx st "n" = SOME (IntV (Unsigned 256) (n:int)) ∧
                    lookup_immutable cx st "i" = NONE``,
                 ``ARB:'a``, ``cx:evaluation_context``,
                 ``IntL (Unsigned 256) 0``] expr_spec_literal)))
  (* 4. expr_spec for Name "n" *)
  >- (irule expr_spec_consequence >>
      qexistsl_tac [
        `λst. (valid_lookups cx st ∧ st.scopes ≠ [] ∧
               lookup_scoped_var st "s" = SOME (IntV (Unsigned 256) 0) ∧
               lookup_immutable cx st "n" = SOME (IntV (Unsigned 256) n) ∧
               lookup_immutable cx st "i" = NONE) ∧
              lookup_name cx st "n" = SOME (IntV (Unsigned 256) n)`,
        `λtv st. (valid_lookups cx st ∧ st.scopes ≠ [] ∧
                  lookup_scoped_var st "s" = SOME (IntV (Unsigned 256) 0) ∧
                  lookup_immutable cx st "n" = SOME (IntV (Unsigned 256) n) ∧
                  lookup_immutable cx st "i" = NONE) ∧
                 lookup_name cx st "n" = SOME (IntV (Unsigned 256) n) ∧
                 tv = Value (IntV (Unsigned 256) n)`] >>
      conj_tac >- (simp[] >> metis_tac[lookup_immutable_implies_lookup_name]) >>
      conj_tac >- simp[gauss_sum_zero] >>
      ACCEPT_TAC (BETA_RULE (ISPECL [
        ``λst:evaluation_state. valid_lookups (cx:evaluation_context) st ∧
           st.scopes ≠ [] ∧
           lookup_scoped_var st "s" = SOME (IntV (Unsigned 256) 0i) ∧
           lookup_immutable cx st "n" = SOME (IntV (Unsigned 256) (n:int)) ∧
           lookup_immutable cx st "i" = NONE``,
        ``cx:evaluation_context``, ``"n":string``,
        ``IntV (Unsigned 256) n``] expr_spec_name_eq)))
  (* 5. Body spec: use for_body_lemma *)
  >> (rpt strip_tac >>
      `k + 1 − 1 = k` by intLib.COOPER_TAC >>
      `&Num n = n` by simp[integerTheory.INT_OF_NUM] >>
      `k < n` by intLib.COOPER_TAC >>
      irule stmts_spec_consequence >>
      qexistsl_tac [
        `λst. st.scopes ≠ [] ∧
              HD st.scopes = FEMPTY |+ (string_to_num "i", IntV (Unsigned 256) k) ∧
              valid_lookups cx (tl_scopes st) ∧ (tl_scopes st).scopes ≠ [] ∧
              lookup_scoped_var (tl_scopes st) "s" =
                SOME (IntV (Unsigned 256) (k * (k − 1) / 2)) ∧
              lookup_immutable cx (tl_scopes st) "n" =
                SOME (IntV (Unsigned 256) n) ∧
              lookup_immutable cx (tl_scopes st) "i" = NONE`,
        `λst. valid_lookups cx (tl_scopes st) ∧ (tl_scopes st).scopes ≠ [] ∧
              lookup_scoped_var (tl_scopes st) "s" =
                SOME (IntV (Unsigned 256) ((k + 1) * k / 2)) ∧
              lookup_immutable cx (tl_scopes st) "n" =
                SOME (IntV (Unsigned 256) n) ∧
              lookup_immutable cx (tl_scopes st) "i" = NONE`,
        `λv st. F`] >>
      (conj_tac >- simp[]) >>
      (conj_tac >- simp[]) >>
      (conj_tac >- simp[]) >>
      irule for_body_lemma >> simp[])
QED

(* ===== Lemma 4: Return s ===== *)

(*
  Proof strategy:
  1. irule stmts_spec_return_some
  2. Use expr_spec_scoped_var_eq to evaluate Name "s"
     to IntV (Unsigned 256) (n*(n-1)/2)
  3. Wrap with expr_spec_consequence
*)
Theorem stmt3_return_s:
  ∀cx n.
    ⟦cx⟧
    ⦃λst. valid_lookups cx st ∧ st.scopes ≠ [] ∧
          lookup_scoped_var st "s" =
            SOME (IntV (Unsigned 256) (n * (n − 1) / 2)) ∧
          lookup_immutable cx st "n" = SOME (IntV (Unsigned 256) n)⦄
    [Return (SOME (Name "s"))]
    ⦃λ_. F ∥ λv st. v = IntV (Unsigned 256) (n * (n − 1) / 2)⦄
Proof
  rpt strip_tac >>
  irule stmts_spec_return_some >>
  irule expr_spec_consequence >>
  qexistsl_tac [
    `λst. (st.scopes ≠ [] ∧
           lookup_immutable cx st "n" = SOME (IntV (Unsigned 256) n)) ∧
          valid_lookups cx st ∧
          lookup_scoped_var st "s" =
            SOME (IntV (Unsigned 256) (n * (n − 1) / 2))`,
    `λtv st. (st.scopes ≠ [] ∧
              lookup_immutable cx st "n" = SOME (IntV (Unsigned 256) n)) ∧
             valid_lookups cx st ∧
             lookup_scoped_var st "s" =
               SOME (IntV (Unsigned 256) (n * (n − 1) / 2)) ∧
             tv = Value (IntV (Unsigned 256) (n * (n − 1) / 2))`] >>
  simp[] >>
  ACCEPT_TAC (BETA_RULE (ISPECL [
    ``λst:evaluation_state. st.scopes ≠ [] ∧
       lookup_immutable (cx:evaluation_context) st "n" =
         SOME (IntV (Unsigned 256) (n:int))``,
    ``cx:evaluation_context``, ``"s":string``,
    ``IntV (Unsigned 256) (n * (n − 1) / 2)``] expr_spec_scoped_var_eq))
QED

(* ===== Main Theorem ===== *)

(*
  Proof structure:
  1. Unfold example_5_body to 3 statements
  2. stmts_spec_cons: split [s:=0] from [for; return]
     - stmt 1 via stmt1_ann_assign_s + consequence (F ⇒ R)
  3. stmts_spec_cons: split [for] from [return]
     - stmt 2 via stmt2_for_range + consequence (F ⇒ R)
     - stmt 3 via stmt3_return_s
*)
Theorem example_5_thm:
  ∀cx n. 0 ≤ n ∧ n ≤ 1000000 ⇒
    ⟦cx⟧
    ⦃λst.
      st.scopes ≠ [] ∧
      valid_lookups cx st ∧
      lookup_immutable cx st "n" = SOME (IntV (Unsigned 256) n) ∧
      lookup_name cx st "s" = NONE ∧
      lookup_immutable cx st "i" = NONE⦄
    example_5_body
    ⦃λ_. F ∥ λv st. v = IntV (Unsigned 256) (n * (n - 1) / 2)⦄
Proof
  rpt strip_tac >>
  simp[example_5_body_def, example_5_decl_def, example_5_module_def] >>
  (* Split: [AnnAssign s] ++ [For; Return] *)
  irule stmts_spec_cons >>
  qexists_tac `λst. valid_lookups cx st ∧ st.scopes ≠ [] ∧
                    lookup_scoped_var st "s" = SOME (IntV (Unsigned 256) 0) ∧
                    lookup_immutable cx st "n" = SOME (IntV (Unsigned 256) n) ∧
                    lookup_immutable cx st "i" = NONE` >>
  conj_tac >- (
    (* Statement 1: s := 0 *)
    irule stmts_spec_consequence >>
    qexistsl_tac [
      `λst. st.scopes ≠ [] ∧ valid_lookups cx st ∧
            lookup_immutable cx st "n" = SOME (IntV (Unsigned 256) n) ∧
            lookup_name cx st "s" = NONE ∧
            lookup_immutable cx st "i" = NONE`,
      `λst. valid_lookups cx st ∧ st.scopes ≠ [] ∧
            lookup_scoped_var st "s" = SOME (IntV (Unsigned 256) 0) ∧
            lookup_immutable cx st "n" = SOME (IntV (Unsigned 256) n) ∧
            lookup_immutable cx st "i" = NONE`,
      `λ_ _. F`] >>
    simp[] >>
    irule stmt1_ann_assign_s) >>
  (* Split: [For] ++ [Return] *)
  irule stmts_spec_cons >>
  qexists_tac `λst. valid_lookups cx st ∧ st.scopes ≠ [] ∧
                    lookup_scoped_var st "s" =
                      SOME (IntV (Unsigned 256) (n * (n − 1) / 2)) ∧
                    lookup_immutable cx st "n" = SOME (IntV (Unsigned 256) n) ∧
                    lookup_immutable cx st "i" = NONE` >>
  conj_tac >- (
    (* Statement 2: For loop *)
    irule stmts_spec_consequence >>
    qexistsl_tac [
      `λst. valid_lookups cx st ∧ st.scopes ≠ [] ∧
            lookup_scoped_var st "s" = SOME (IntV (Unsigned 256) 0) ∧
            lookup_immutable cx st "n" = SOME (IntV (Unsigned 256) n) ∧
            lookup_immutable cx st "i" = NONE`,
      `λst. valid_lookups cx st ∧ st.scopes ≠ [] ∧
            lookup_scoped_var st "s" =
              SOME (IntV (Unsigned 256) (n * (n − 1) / 2)) ∧
            lookup_immutable cx st "n" = SOME (IntV (Unsigned 256) n) ∧
            lookup_immutable cx st "i" = NONE`,
      `λ_ _. F`] >>
    simp[] >>
    irule stmt2_for_range >> simp[]) >>
  (* Statement 3: Return s *)
  irule stmts_spec_consequence >>
  qexistsl_tac [
    `λst. valid_lookups cx st ∧ st.scopes ≠ [] ∧
          lookup_scoped_var st "s" =
            SOME (IntV (Unsigned 256) (n * (n − 1) / 2)) ∧
          lookup_immutable cx st "n" = SOME (IntV (Unsigned 256) n)`,
    `λ_. F`, `λv st. v = IntV (Unsigned 256) (n * (n − 1) / 2)`] >>
  simp[] >>
  irule stmt3_return_s
QED
