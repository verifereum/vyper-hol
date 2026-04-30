# LEARNINGS: Type Soundness Repair

## `qspecl_then` with backtick terms FAILS across proof contexts (Sessions 9-12)

**Root cause:** Backtick terms like `` `env:typing_env` `` get FIXED types at SML
definition time. When `qpat_x_assum` finds a theorem with ∀-variables of matching
structure but the specializing terms' types don't match the theorem's ∀-variable types,
SPECL raises HOL_ERR. This causes `first_x_assum`/`FIRST` to skip the assumption
or fail entirely.

**Fix:** Use `drule_all` instead, which automatically matches IH antecedents against
assumptions. No explicit term specialization needed:
```sml
qpat_x_assum `∀env st res st'. well_typed_expr _ _ ∧ _ ⇒ _` drule_all >> strip_tac
```

## `drule_all` is the proven IH application pattern (Session 12)

ReturnSome (line 752) uses this successfully. Key properties:
- Automatically specializes ALL IH antecedents by matching against assumptions
- Correctly handles `eval_expr cx e st = (res,st')` → specializes `res ↦ INL tv`, `st' ↦ r`
- No type mismatch possible (no explicit term construction)
- MAY be slow in very rich contexts with many ∀-assumptions (untested)

## `first_x_assum drule_all` picks WRONG IH (Sessions 2-3, 11-12)

When multiple ∀-IHs exist (P0-P8), `first_x_assum` picks the newest, which may not
be the one we want. Fix: use `qpat_x_assum` with a function-specific pattern:
- P7: `∀env st res st'. well_typed_expr _ _ ∧ _ ⇒ _`
- P0: `∀env ret_ty st res st'. well_typed_stmt _ _ _ ∧ _ ⇒ _`
etc.

## Nested suspend structure in Resume blocks (Session 12)

Cannot blindly `cheat` outer blocks that contain inner `suspend` calls.
Example: Append block has `suspend "Append_atwt"` inside it. If you replace the
entire Append Resume with `cheat`, the inner suspend label is lost, and
`Resume eval_preserves_swt[Append_atwt]` fails with "No such label in theorem".

**Fix:** When cheating, preserve the inner `suspend` structure. Or better: don't
cheat — fix the actual IH application mechanism.

## SPECL specializes POSITIONALLY, not by name (Session 12)

`SPECL [a, b, c] th` specializes the 1st, 2nd, 3rd ∀-variables of th, regardless
of their names. The terms' TYPES must match the ∀-variables' types, or HOL_ERR.

## Cases_on pair destructuring: q = result, r = state (Sessions 9-11)
After `Cases_on \`eval_expr cx e st\``, HOL4 names:
- `q` = result component
- `r` = new state
Then `Cases_on \`q\`` gives INL `x` (success) / INR `y` (error)

## INR/INL subgoal management in Resume blocks (Sessions 9-11)
`>-` and `>|` produce gentactic, NOT tactic — cannot use in Resume blocks.
Working pattern: `TRY (close_inr_err_tac >> NO_TAC) >> ...`

## toplevel_value_typed_for_BaseT: KEY boundary lemma
`∀tenv bt tv. evaluate_type tenv (BaseT bt) = SOME tyv ∧ toplevel_value_typed tv tyv ⇒ ∃v. tv = Value v`

## State lemmas for pure operations (used 10+ times)
- materialise_state, get_Value_state, lift_option_type_state, lift_option_state
- lift_sum_state, check_state, type_check_state, return_state, raise_state
- switch_BoolV_state, handle_loop_exception_state
All prove `st' = st` (state unchanged). Use: `imp_res_tac X_state >> gvs[]`

## drule_all vs drule (Sessions 2-3, 11-12)
- `drule_all`: matches ALL antecedents against ALL assumptions. More powerful but
  potentially slower. Preferrable when antecedents are specific enough to avoid
  ambiguity.
- `drule`: matches only FIRST antecedent. Faster but may leave remaining
  antecedents as implications.
- Both are safer than `first_x_assum drule_all` which can pick wrong ∀-assumption.

## Tactic Anti-Patterns
- `simp[AllCaseEqs()]` on monadic bind chains → unsolvable nested existentials
- `gvs[PAIR_FST_SND_EQ]` on bind results → DESTROYS IH structure
- `rw[env_consistent_def]` → TIMEOUT (use env_consistent_scopes_only)
- `simp[evaluate_def]` without `Once` — HANGS
- `metis_tac` with many assumptions — TIMES OUT
- `imp_res_tac` before IH application — ADDS CLUTTER
- `>>` after case split — use `>-` to focus one subgoal
- Python scripts that cheat blocks with nested suspends — DESTROYS inner labels

## materialise chain (7 lemmas, used in 3+ blocks)
Key: materialise TypeError → is_HashMapRef → tyv = NoneTV → NoneT → well_typed excludes NoneT

## evaluate_builtin_well_typed (1 lemma, FULLY PROVED)
Takes `accounts_well_typed acc` precondition. Covers ALL builtin cases.

## augment_srw_ss makes constructor distinctness trivial
`augment_srw_ss[rewrites [exception_distinct, error_distinct]]` proves
`INR y ≠ INR (Error (TypeError s))` etc. automatically via simp[].

## Debugging workflow (Session 11-12)
NEVER rely solely on holmake for debugging (16-45s/cycle). USE hol_state_at:
1. Cheat failing blocks to get build past them
2. Use hol_state_at on each failing block to inspect REAL proof state
3. Design fix based on REAL assumptions, not guessing
4. One holmake to verify
