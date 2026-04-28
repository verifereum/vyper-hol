# LEARNINGS: Type Soundness Repair

## Helper Index by Shape

### SIMP_RULE trick for large definitions (CRITICAL — 3+ instances)
When `fs[big_def]` or `gvs[big_def]` TIMEOUTS or pollutes assumption context:
```sml
qpat_x_assum `preserves_tv _ _ _`
  (strip_assume_tac o SIMP_RULE (srw_ss()) [preserves_tv_def])
```
Expands definition into a theorem, then selectively adds consequences.
DO NOT use `fs[preserves_tv_def]` — it TIMEOUTS.
DO NOT use `gvs[preserves_tv_def]` — it pollutes context.
Instances: bridge lemma, env_consistent_preserves_tv, preserves_immutables_dom proofs.

### env_consistent preservation — FOUR patterns (12+ instances — CRITICAL)

**Pattern A: scope-only change** (pop_scope_ec, new_variable_ec, scope_bracket_preserves_ec)
```sml
match_mp_tac env_consistent_with_new_scopes >> simp[] >>
rpt strip_tac
>- (drule env_consistent_var_types_completeness >> disch_then drule >>
    simp[lookup_scopes_def, ...])
>- (drule env_consistent_var_types_soundness >> disch_then drule >>
    simp[lookup_scopes_def, ...])
```

**Pattern B: env+scope change → Weaken+PatternA** (env_consistent_pop_scope — UNUSED, skip)

**Pattern C: immutables change** (env_consistent_immutables_ptv, env_consistent_preserves_tv)
```sml
(* Step 1: Expand old env_consistent hypothesis *)
qpat_x_assum `env_consistent _ _ _`
  (strip_assume_tac o REWRITE_RULE[env_consistent_scopes_only] o
   SUBS [SYM (Q.SPEC `st` evaluation_state_scopes_id)]) >>
(* Step 2: Expand goal *)
once_rewrite_tac[GSYM evaluation_state_scopes_id] >>
simp[env_consistent_scopes_only] >>
(* Step 3: Solve conjuncts — FLOOKUP equality makes most automatic *)
rpt conj_tac >> ...
```
For var_types soundness: use `drule_all lookup_scopes_type_preserved_under_preserves_tv`.
KEY: The FLOOKUP equality hypothesis makes global_types soundness, toplevel_types, and
flag_members solvable by simp+res_tac automatically.

**Pattern D: scope entry value update** — `match_mp_tac scope_entry_update_preserves_typing >> simp[]`

### env_consistent_scopes_only — THE boundary lemma (7+ instances, NOW 8 conjuncts)
Iff decomposition of env_consistent. ALWAYS use this instead of unfolding env_consistent_def.
The 8 conjuncts in order:
1. env.type_defs = get_tenv cx
2. fn_sigs_consistent env.fn_sigs cx
3. ∀id ty. FLOOKUP env.var_types id = SOME ty ⇒ IS_SOME (lookup_scopes id scopes)
4. ∀id ty entry. FLOOKUP env.var_types id = SOME ty ∧ lookup_scopes id scopes = SOME entry ⇒ evaluate_type ... ty = SOME entry.type
5. ∀id ty. FLOOKUP env.global_types id = SOME ty ⇒ IS_SOME (FLOOKUP (get_source_immutables ...) id)
6. ∀id ty tv v. FLOOKUP env.global_types id = SOME ty ∧ FLOOKUP ... id = SOME (tv, v) ⇒ evaluate_type ... ty = SOME tv
7. toplevel_types conjunct (3 sub-clauses with src_id_opt, id, ty, ts)
8. flag_members conjunct

### env_consistent_preserves_tv — FLOOKUP equality is the RIGHT hypothesis
The theorem needs: FLOOKUP (get_source_immutables src (st'.immutables)) n =
                   FLOOKUP (get_source_immutables src (st.immutables)) n
NOT just IS_SOME. IS_SOME iff is too weak because soundness/toplevel_types need VALUE
equality (evaluate_type ty = SOME tv requires matching tv from old assumption).
Call sites prove this via ALOOKUP equality (immutables don't change).

### lookup_scopes family — KEY decomposition tools (8+ instances)
- `lookup_scopes_EL`: decompose lookup → index + FLOOKUP + no-earlier-match
- `lookup_scopes_from_EL`: reconstruct from index + FLOOKUP + no-earlier-match
- `lookup_scopes_is_some_same_fdoms`: MAP FDOM → IS_SOME iff
- `lookup_scopes_cons_miss`: FLOOKUP NONE in head → lookup_scopes skips to tail

### FLOOKUP/FDOM facts — CRITICAL for scope proofs
- `FLOOKUP_NOT_IN_FDOM`: FORWARD only (NOTIN => NONE)
- `FLOOKUP_SOME_IN_FDOM`: FORWARD only (SOME => IN)
- `FLOOKUP_NONE_NOTIN_FDOM`: IFF version (NONE iff NOTIN)
- `finite_mapTheory.flookup_thm`: Full IFF version
- `MAP_FDOM_EL_FDOM`: MAP FDOM equality → FDOM equality at index

### HashMapRef contradiction chain (6+ instances)
Chain: materialise TypeError → is_HashMapRef tv → tyv = NoneTV → expr_type = NoneT → well_typed_expr excludes NoneT → contradiction

### ec_unconditional_tac / ec_stk_tac — CALLER pattern update
After `irule env_consistent_preserves_tv`, prove FLOOKUP equality via:
```sml
`(ALOOKUP st.immutables cx.txn.target) =
 (ALOOKUP st'.immutables cx.txn.target)` by simp[] >>
Cases_on `ALOOKUP st.immutables cx.txn.target` >> gvs[]
```
This is SIMPLER than the old IS_SOME iff + double case split.

## HOL4 Precedence — CRITICAL
`a ==> b <=> c` parses as `(a ==> b) <=> c`. ALWAYS use parentheses: `a ==> (b <=> c)`.

## Tactic Anti-Patterns (CRITICAL)
- `rw[env_consistent_def]` → TIMEOUT (use env_consistent_scopes_only)
- `fs[preserves_tv_def]` → TIMEOUT (use SIMP_RULE trick above)
- `gvs[preserves_tv_def]` → pollutes context, assumption selection fails
- `gvs[preserves_immutables_dom_def]` → FIRST_ASSUM failure
- `cj N` on Definition theorems → "index too large"; use REWRITE_RULE+CONJUNCTS
- SUBST_ALL_TAC with evaluation_state_scopes_id → CORRUPTS proof (F goals)
- Nested `by` blocks 3+ levels deep → context loss, FAILS unpredictably
- `first_x_assum irule` when IH and other ∀-assumptions coexist → picks wrong one
- `metis_tac[IS_SOME_DEF]` on goals needing FLOOKUP value equality → timeout

## HOL4 Name Gotchas
- `optionTheory.SOME_11` (NOT `option_11`)
- `finite_mapTheory.flookup_thm` (IFF version of FLOOKUP/FDOM relationship)

## Proof Pattern: Standalone Lemma Extraction (5+ instances)
When by-block proof fails due to polluted context:
1. Extract into standalone Theorem
2. Prove standalone (clean context)
3. Use via drule_all/irule_at/metis_tac
Instances: var_types_not_in_head_scope, preserves_immutables_dom_is_some_bridge,
MAP_FDOM_EL_FDOM, FLOOKUP_NONE_NOTIN_FDOM, lookup_scopes_type_preserved_under_preserves_tv

## Proof Pattern: EL-decomposition + SIMP_RULE (bridge lemma pattern)
For lemmas about preserves_tv + lookup_scopes:
1. `drule lookup_scopes_EL >> strip_tac` → decompose lookup
2. `qpat_x_assum 'preserves_tv _ _ _' (strip_assume_tac o SIMP_RULE (srw_ss()) [preserves_tv_def])` → get forward facts cleanly
3. `drule MAP_FDOM_EL_FDOM >> simp[]` → FDOM equality at index
4. `metis_tac[flookup_thm]` → FLOOKUP existence
5. `irule lookup_scopes_from_EL >> qexists_tac 'i' >> simp[]` → reconstruct
This avoids list induction (which creates IH/forward-preservation confusion).

### functions_well_typed_def NEW structure (2+ instances)
REWRITE_RULE → SPECL with type-instantiated FEMPTY → SIMP_RULE [FLOOKUP_EMPTY].
For typed FEMPTY: use `inst [alpha |-> ``:type_1``, beta |-> ``:type_2``] ``FEMPTY```
at ML level — HOL4 parser CANNOT handle complex type annotations in quotations.

## Hypothesis Strength — CRITICAL
When a theorem's proof needs values from old state to match new state, IS_SOME is
insufficient. Need FLOOKUP EQUALITY. Pattern: if call sites can prove ALOOKUP/list
equality, then get FLOOKUP/get_source_immutables equality for free. Always check:
does the conclusion need VALUES from the hypothesis, or just EXISTENCE?
