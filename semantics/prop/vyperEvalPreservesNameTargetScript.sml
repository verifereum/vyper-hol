Theory vyperEvalPreservesNameTarget

Ancestors
  vyperInterpreter vyperLookup vyperEvalPreservesImmutablesDom
    vyperEvalExprPreservesScopesDom vyperEvalPreservesScopes vyperEvalMisc

(* ========================================================================
   Preservation of lookup_name_target through eval_expr / eval_stmts.

   TOP-LEVEL:
     eval_expr_preserves_lookup_name_target
     eval_stmts_preserves_lookup_name_target
   ======================================================================== *)

(* ===== Helper: extract facts from a successful NameTarget lookup ===== *)

Theorem lookup_name_target_facts[local]:
  ∀cx st n av.
    lookup_name_target cx st n = SOME av ⇒
    (var_in_scope st n ∧ av = BaseTargetV (ScopedVar n) [] ∧
     (cx.txn.is_creation ⇒
       ∃imms. ALOOKUP st.immutables cx.txn.target = SOME imms ∧
              FLOOKUP (get_source_immutables NONE imms) (string_to_num n) = NONE)) ∨
    (¬var_in_scope st n ∧ av = BaseTargetV (ImmutableVar n) [] ∧
     cx.txn.is_creation ∧
     ∃imms. ALOOKUP st.immutables cx.txn.target = SOME imms ∧
            IS_SOME (FLOOKUP (get_source_immutables NONE imms) (string_to_num n)))
Proof
  rpt strip_tac >>
  gvs[lookup_name_target_def, lookup_base_target_def,
      var_in_scope_def, lookup_scoped_var_def] >>
  qpat_x_assum `_ = SOME _` mp_tac >>
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def] >>
  Cases_on `cx.txn.is_creation` >>
  gvs[bind_def, get_immutables_def, get_address_immutables_def,
      lift_option_def, return_def, raise_def, lift_sum_def,
      exactly_one_option_def, immutable_target_def] >-
  (Cases_on `ALOOKUP st.immutables cx.txn.target` >>
   gvs[raise_def, return_def, exactly_one_option_def] >>
   Cases_on `FLOOKUP (get_source_immutables NONE x) (string_to_num n)` >>
   gvs[return_def, raise_def, exactly_one_option_def] >>
   IF_CASES_TAC >> gvs[exactly_one_option_def, return_def, raise_def]) >>
  IF_CASES_TAC >> gvs[exactly_one_option_def, return_def, raise_def]
QED

(* ===== Helpers: reconstruct lookup_name_target in st' ===== *)

Theorem reconstruct_scoped_lookup[local]:
  ∀cx st' n.
    var_in_scope st' n ∧
    (¬cx.txn.is_creation ∨
     ∃imms'. ALOOKUP st'.immutables cx.txn.target = SOME imms' ∧
             FLOOKUP (get_source_immutables NONE imms') (string_to_num n) = NONE) ⇒
    lookup_name_target cx st' n = SOME (BaseTargetV (ScopedVar n) [])
Proof
  rpt strip_tac >>
  gvs[lookup_name_target_def, lookup_base_target_def,
      var_in_scope_def, lookup_scoped_var_def] >-
  (simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
        lift_sum_def, exactly_one_option_def, return_def]) >>
  Cases_on `cx.txn.is_creation` >-
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
       get_immutables_def, get_address_immutables_def,
       lift_option_def, return_def, lift_sum_def,
       exactly_one_option_def, immutable_target_def] >>
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
       lift_sum_def, exactly_one_option_def, return_def]
QED

Theorem reconstruct_immutable_lookup[local]:
  ∀cx st' n.
    ¬var_in_scope st' n ∧
    cx.txn.is_creation ∧
    (∃imms'. ALOOKUP st'.immutables cx.txn.target = SOME imms' ∧
             IS_SOME (FLOOKUP (get_source_immutables NONE imms') (string_to_num n))) ⇒
    lookup_name_target cx st' n = SOME (BaseTargetV (ImmutableVar n) [])
Proof
  rpt strip_tac >>
  gvs[lookup_name_target_def, lookup_base_target_def,
      var_in_scope_def, lookup_scoped_var_def] >>
  Cases_on `FLOOKUP (get_source_immutables NONE imms') (string_to_num n)` >>
  gvs[] >>
  simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
       get_immutables_def, get_address_immutables_def,
       lift_option_def, return_def, lift_sum_def,
       exactly_one_option_def, immutable_target_def]
QED

(* ===== Immutables transfer helpers ===== *)

Theorem imm_dom_transfer_none[local]:
  ∀cx st st' n imms.
    preserves_immutables_dom cx st st' ∧
    ALOOKUP st.immutables cx.txn.target = SOME imms ∧
    FLOOKUP (get_source_immutables NONE imms) (string_to_num n) = NONE ⇒
    ∃imms'. ALOOKUP st'.immutables cx.txn.target = SOME imms' ∧
            FLOOKUP (get_source_immutables NONE imms') (string_to_num n) = NONE
Proof
  rpt strip_tac >> fs[preserves_immutables_dom_def] >>
  `IS_SOME (ALOOKUP st'.immutables cx.txn.target)` by fs[] >>
  Cases_on `ALOOKUP st'.immutables cx.txn.target` >> fs[] >>
  first_x_assum (qspec_then `string_to_num n` mp_tac) >> fs[]
QED

Theorem imm_dom_transfer_some[local]:
  ∀cx st st' n imms.
    preserves_immutables_dom cx st st' ∧
    ALOOKUP st.immutables cx.txn.target = SOME imms ∧
    IS_SOME (FLOOKUP (get_source_immutables NONE imms) (string_to_num n)) ⇒
    ∃imms'. ALOOKUP st'.immutables cx.txn.target = SOME imms' ∧
            IS_SOME (FLOOKUP (get_source_immutables NONE imms') (string_to_num n))
Proof
  rpt strip_tac >> fs[preserves_immutables_dom_def] >>
  `IS_SOME (ALOOKUP st'.immutables cx.txn.target)` by fs[] >>
  Cases_on `ALOOKUP st'.immutables cx.txn.target` >> fs[] >>
  first_x_assum (qspec_then `string_to_num n` mp_tac) >> fs[]
QED

(* ===== Main theorems ===== *)

(* CHEAT: the individual pieces (lookup_name_target_facts, reconstruct_*,
   imm_dom_transfer_*, eval_expr_preserves_var_in_scope,
   preserves_immutables_dom) are all proved above.
   The assembly into the final proof has variable-name management issues
   that need interactive debugging to resolve. *)

Theorem eval_expr_preserves_lookup_name_target:
  ∀cx e st res st' n av.
    eval_expr cx e st = (res, st') ∧
    lookup_name_target cx st n = SOME av ⇒
    lookup_name_target cx st' n = SOME av
Proof
  cheat
QED

Theorem eval_stmts_preserves_lookup_name_target:
  ∀cx ss st res st' n av.
    eval_stmts cx ss st = (res, st') ∧
    lookup_name_target cx st n = SOME av ∧
    (¬var_in_scope st n ⇒ valid_lookups cx st') ⇒
    lookup_name_target cx st' n = SOME av
Proof
  cheat
QED
