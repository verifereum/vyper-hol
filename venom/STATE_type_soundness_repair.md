# STATE: Type Soundness Repair

## Overall Status: env_consistent_preserves_tv IN PROGRESS (FLOOKUP equality fix applied, NEEDS VERIFICATION). 5 cheats remain in helpers theory.

## IMMEDIATE NEXT STEP
Verify `env_consistent_preserves_tv` proof completes. Last `hol_check_proof` showed
INCOMPLETE status — added `rpt strip_tac >> res_tac >> gvs[]` for remaining
toplevel_types conjunct. Run `hol_check_proof(theorem="env_consistent_preserves_tv")`.

If that succeeds, run `holmake(workdir="semantics/prop")` to check cascade.

## CHANGE SUMMARY (not yet committed)
- `env_consistent_preserves_tv`: Changed IS_SOME hypothesis to FLOOKUP equality
- `ec_unconditional_tac`: ALOOKUP equality instead of IS_SOME iff, single case split
- `ec_stk_tac`: Same simplification

## Cheat Inventory (5 cheats)

| # | Theorem | Line | Status | Risk | Used by |
|---|---------|------|--------|------|---------|
| 1 | env_consistent_pop_scope | ~1344 | cheat | VERY LOW (UNUSED) | Nothing! Skip. |
| 2 | bind_arguments_env_consistent | ~1519 | cheat | MEDIUM | main theory 3552 |
| 3 | set_immutable_well_typed | ~1941 | cheat | MEDIUM | helpers 2180,2411,2581 |
| 4 | assign_target_well_typed[replace] | ~2323 | cheat | MEDIUM | main theory 1373 |
| 5 | eval_expr_not_HashMapRef Call | ~7148 | cheat | MEDIUM | helpers 7101 |

## Post-verification Plan (after env_consistent_preserves_tv works)

### 1. bind_arguments_env_consistent (line ~1519)
Strategy: match_mp_tac env_consistent_with_new_scopes >> simp[]
New toplevel_types/flag_members conjuncts: with FEMPTY, these are vacuously true.
Use: `inst [alpha|->...,:] FEMPTY` for type-instantiated FEMPTY.

### 2. set_immutable_well_typed (line ~1941)
set_immutable only modifies st.immutables. state_well_typed: imms_well_typed preserved.
env_consistent: immutables clauses preserved. Scopes unchanged.

### 3. assign_target_well_typed[replace] (line ~2323)
Need to see actual goal. Probably needs scope_entry_update_preserves_typing.

### 4. eval_expr_not_HashMapRef Call (line ~7148)
Contradiction chain: well_typed Call → result type ≠ NoneT →
materialise won't produce HashMapRef → not HashMapRef.

### 5. env_consistent_pop_scope — SKIP (unused by anything)

### 6. Precedence Audit
Grep all .sml files for `==>` followed by `<=>` without parentheses.
Check BOTH vyperTypeSoundnessHelpersScript.sml AND vyperTypeSoundnessScript.sml.

## What NOT to Try
- `rw[functions_well_typed_def]` — can't rewrite with new quantifier structure
- `fs[preserves_tv_def]` → TIMEOUT; use SIMP_RULE trick
- `gvs[preserves_immutables_dom_def]` → FIRST_ASSUM failure
- `cj 1`/`cj 2` on Definition theorems → "index too large"
- `rw[env_consistent_def]` → TIMEOUT (massive blowup)
- Nested `by` blocks 3+ levels deep → context loss
- IS_SOME hypothesis for env_consistent_preserves_tv → too weak; MUST use FLOOKUP equality
- `metis_tac[IS_SOME_DEF]` for global_types completeness → timeout; use qspec_then+gvs

## Key Definitions

### preserves_tv_def (vyperEvalPreservesScopesScript.sml:1156)
```
preserves_tv cx st st' ⇔
  LENGTH st'.scopes = LENGTH st.scopes ∧
  (∀i id entry. i < LENGTH st.scopes ∧
    FLOOKUP (EL i st.scopes) id = SOME entry ⇒
    ∃entry'. FLOOKUP (EL i st'.scopes) id = SOME entry' ∧ entry'.type = entry.type) ∧
  (immutables clause)
```
IMPORTANT: Use SIMP_RULE (srw_ss()) [preserves_tv_def] to expand, NOT fs/gvs.

### env_consistent_scopes_only — THE boundary lemma (8 conjuncts)
Use REWRITE_RULE[env_consistent_scopes_only] to decompose. NEVER unfold env_consistent_def.

### env_consistent_preserves_tv — NOW with FLOOKUP equality
Hypothesis: `∀src n. FLOOKUP (get_source_immutables src (st'.immutables)) n =
                       FLOOKUP (get_source_immutables src (st.immutables)) n`
Call sites prove via: `(ALOOKUP st.immutables cx.txn.target) =
                       (ALOOKUP st'.immutables cx.txn.target)` by simp[] >>
                       Cases_on `ALOOKUP ...` >> gvs[]

### functions_well_typed_def (NEW structure)
fn_sigs, toplevel_types, flag_members quantified at TOP with premises.
Use: REWRITE_RULE → SPECL with type-instantiated FEMPTY → SIMP_RULE [FLOOKUP_EMPTY]

## Helpers Available (proved, in .sml)
- env_consistent_scopes_only, env_consistent_with_new_scopes
- env_consistent_var_types_soundness/completeness
- preserves_immutables_dom_is_some_bridge
- lookup_scopes_is_some_same_fdoms, lookup_scopes_EL, lookup_scopes_from_EL
- lookup_scopes_cons_miss, lookup_scopes_pre_found/pre_miss
- env_consistent_drop_var, evaluation_state_scopes_id
- bind_arguments_evaluate_type, bind_arguments_succeeds
- functions_well_typed_body_full (PROVED)
- materialise_no_type_error, materialise_type_error_NoneTV, etc.
- MAP_FDOM_EL_FDOM, FLOOKUP_NONE_NOTIN_FDOM
- lookup_scopes_type_preserved_under_preserves_tv (PROVED!)
