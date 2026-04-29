# LEARNINGS: Type Soundness Repair

## CRITICAL: imp_res_tac Silently Fails on Syntactic Mismatches

`imp_res_tac` on a lemma whose preconditions don't syntactically match any assumption **silently does nothing**. No error, no warning. The tactic appears to succeed but adds nothing to the goal state.

**THE FIX**: Write boundary lemmas whose preconditions use the EXACT same term shape as the helper lemmas.

## CRITICAL: Never Expand Monad Chains in Resume Blocks

`simp[AllCaseEqs()]` on monadic `bind`/`lift_option`/`type_check` chains creates deeply nested ∃-quantified subgoals that `gvs[]` cannot solve.

**THE FIX**: Prove standalone boundary lemmas that handle the expansion internally with targeted `Cases_on`. Then the Resume block just uses `imp_res_tac`.

## CRITICAL: New 4-Conjunct IH Breaks match_mp_tac

The IH conclusion now has 4 conjuncts (state_well_typed, env_consistent, accounts_well_typed, no-TypeError). `match_mp_tac` can't handle conjunctive conclusions properly.

**THE FIX**: Use `drule` which matches just the first antecedent, then `gvs[]` splits the conjunction.

## CRITICAL: cj Index Shift After Definition Splits

When a definition like `well_typed_expr_def` has a conjunct split (TypeBuiltin: 1→8 cases in HOL), ALL subsequent `cj N` bindings become wrong.

**THE FIX**: After ANY upstream definition change, re-verify cj indices using:
```sml
fun enumerate_cjs thm = let val cs = strip_conj (concl thm)
  fun go i [] = () | go i (c::cs) = let
    val (vs, body) = strip_forall c val (l,r) = dest_eq body
    val (head, args) = strip_comb l val s = term_to_string (hd (tl args))
  in print (Int.toString i ^ ": " ^ s ^ "\n"); go (i+1) cs end
  handle _ => go (i+1) cs
in go 1 cs end;
```
For multi-conjunct splits: `val wte_X = LIST_CONJ (map (fn i => cj i well_typed_expr_def) [11,...,18])`

**IMPORTANT**: Source-level counting is UNRELIABLE for cj indices. HOL may expand definitions internally.

## CRITICAL: gvs[PAIR_FST_SND_EQ] Destroys IH Structure

After `Cases_on` a bind result followed by `gvs[PAIR_FST_SND_EQ, UNCURRY]`, pair variables get replaced with FST/SND projections, making the IH impossible to apply (`disch_then drule` crashes).

**THE FIX**: Use `Cases_on` on the sub-result with `bind_apply` + `BETA_THM`, then `drule_all` for IH. See SubscriptTarget/AttributeTarget pattern.

## KEY DISCOVERY: evaluate_builtin_well_typed is already proved

`vyperBuiltinTypingScript.sml` contains a FULLY PROVED `evaluate_builtin_well_typed` (no cheats) covering ALL builtin cases including MakeArray, Acc, Convert, AbiEncode. Takes `accounts_well_typed acc` as precondition.

## KEY DISCOVERY: lookup_scopes_val_NONE theorem

`vyperLookupTheory.lookup_scopes_val_NONE`: `lookup_scopes_val id sc = NONE ⇔ lookup_scopes id sc = NONE`. Directly bridges `lookup_scopes_val` NONE branches to `lookup_scopes` IS_SOME contradiction.

## CRITICAL: TypeError-impossible branches — ASSUMPTION contradiction, NOT conclusion

When a NONE/FAIL branch produces `INR (Error (TypeError msg))` as the result (via `raise`):
- The no-TypeError conjunct `∀s. res ≠ INR (Error (TypeError s))` in the CONCLUSION becomes FALSE
- You CANNOT prove a false conclusion from true assumptions
- INSTEAD: derive contradiction from ASSUMPTIONS (e.g., IS_SOME vs NONE via `lookup_scopes_val_NONE`)
- **Pattern**: `fs[lookup_scopes_val_NONE, IS_SOME_EQ_NOT_NONE]` for variable-not-in-scope cases

**If the assumptions don't directly contradict** (no IS_SOME in scope), use
`drule_all env_consistent_var_types_completeness` first to derive IS_SOME.

## CRITICAL: gvs[] Solves New 4-Conjunct Conclusion Automatically

The augmented srw_ss (with exception_distinct + error_distinct) handles:
- `∀s. res ≠ INR (Error (TypeError s))` when `res = INL ...` (by INL/INR distinctness)
- `∀v ret_tv. res = INR (ReturnException v) ⇒ ...` when `res = INR (OtherError)`
- `accounts_well_typed st'.accounts` from IH assumptions
- `state_well_typed st' / env_consistent env cx st'` from IH assumptions

**THE FIX**: Replace `rpt CONJ_TAC >> first_assum ACCEPT_TAC` → `gvs[]`

## CRITICAL: TRY (tac >> NO_TAC) Hides Unsolved Goals

When `tac` doesn't fully close the goal (makes progress but leaves subgoals),
`NO_TAC` fails, `TRY` catches → the unsolved subgoal SILENTLY REMAINS.
Subsequent tactics apply to the WRONG subgoal, causing confusing downstream failures.

**THE FIX**: Use `>- tac` instead. If tac can't close, you get an explicit error
at the right location instead of a confusing failure later.

## Helper Index by Shape

### preserves_tv bridge (2 instances)
- `preserves_tv_immutables_IS_SOME_forward`: IS_SOME(old) → IS_SOME(new)
- `preserves_tv_immutables_type_preserved`: FLOOKUP old=SOME(tv,v) → ∃v'. FLOOKUP new=SOME(tv,v')

### type_check guard discharging (2 instances)
- `well_typed_target_NameTarget_in_scope`
- `well_typed_target_BareGlobalNameTarget_IS_SOME`
Pattern: `imp_res_tac <lemma>` BEFORE the big simp.

### env_consistent → IS_SOME bridge (1+ instances)
- `env_consistent_var_types_completeness`: env_consistent + FLOOKUP var_types = SOME ty ⇒ IS_SOME (lookup_scopes ...)
Pattern: `drule_all env_consistent_var_types_completeness >> simp[]`

### No-TypeError boundary lemmas (1 instance, MORE NEEDED)
- `eval_base_target_BareGlobalNameTarget_no_type_error`
Pattern: Standalone lemma handles monadic expansion. Consumer just does `imp_res_tac`.

### materialise/HashMapRef contradiction chain (6+ instances)
materialise TypeError → is_HashMapRef tv → tyv = NoneTV → expr_type = NoneT → well_typed_expr excludes NoneT → contradiction

### accounts_well_typed preservation (needed for Send/ExtCall)
accounts_well_typed is now a precondition+conclusion in ALL P0-P8.
Cases that don't modify accounts: trivially from IH.
Cases that modify accounts: Send/ExtCall — need preservation lemma.

### env_consistent preservation (4 patterns)
A: scope-only → match_mp_tac env_consistent_with_new_scopes
B: env+scope → env_consistent_pop_scope (cheat)
C: immutables → REWRITE_RULE + once_rewrite + simp
D: scope entry → match_mp_tac scope_entry_update_preserves_typing

### evaluate_builtin_well_typed bridge (1 instance)
- In Builtin_NonLen Resume block
- Pattern: assemble 5 conjuncts then `metis_tac[evaluate_builtin_well_typed]`

### IH application with bind results (3+ instances)
- AttributeTarget: Cases_on eval_base_target + drule_all for IH
- SubscriptTarget: Cases_on + drule_all + manual case decomposition
Pattern: `Cases_on sub_eval >> reverse (Cases_on `q`) >> tp_bind_err_tac >> first_x_assum drule_all`

## KEY DISCOVERY: gvs[] after drule_all Dramatically Improves Performance

Replacing `first_x_assum drule_all >> strip_tac >> rpt CONJ_TAC >> ...` with
`first_x_assum drule_all >> strip_tac >> gvs[]` in `tp_bind_err_tac` reduced build
time from 600s timeout to 41s. The manual CONJ_TAC/ACCEPT_TAC/strip_tac chain was
both incomplete (for new conjuncts) AND slower.

**Pattern**: After IH application via drule_all, always use `gvs[]` rather than
manual conjunct decomposition.

## Tactic Anti-Patterns
- `simp[AllCaseEqs()]` on monadic bind chains → unsolvable nested existentials
- `gvs[PAIR_FST_SND_EQ]` on bind results → DESTROYS IH structure
- `rw[env_consistent_def]` → TIMEOUT (use env_consistent_scopes_only)
- `fs[preserves_tv_def]` → TIMEOUT
- `imp_res_tac` on conjunction-conclusion lemmas → splits subgoals; use simple-conclusion corollaries
- `match_mp_tac` on 4-conjunct IH → use `drule`
- `metis_tac[lookup_scopes_val_SOME]` in complex contexts → TIMES OUT
- `fs[IS_SOME_EXISTS]` on goals with many assumptions → TOO AGGRESSIVE
- `simp[evaluate_def]` without `Once` — HANGS
- Source-level cj index counting → UNRELIABLE

## HOL4 Gotchas
- `optionTheory.SOME_11` (NOT `option_11`)
- `finite_mapTheory.flookup_thm` (IFF version of FLOOKUP/FDOM)
- `a ==> b <=> c` parses as `(a ==> b) <=> c`
- `well_typed_target_def` does NOT exist as ML name — part of `well_typed_expr_def`
- Implication theorems (e.g. `lift_option_state`) CANNOT be used as simp rewrites
- `imp_res_tac` silently fails on syntactic mismatches — no error
- `cj N` indices shift when upstream definitions gain/lose conjuncts — ALWAYS re-verify after changes
- `typing_env_accfupds` DESTROYS conditional FLOOKUP form needed by helper lemmas
- `DB.find` requires exact name match; `DB.match []` for pattern search but needs correct type annotations
- `lookup_scopes_val_NONE` EXISTS: `lookup_scopes_val id sc = NONE ⇔ lookup_scopes id sc = NONE`
- `IS_SOME_EQ_NOT_NONE` EXISTS: `IS_SOME x ⇔ x ≠ NONE`
- `NOT_IS_SOME_EQ_NONE` EXISTS: `¬IS_SOME x ⇔ x = NONE`

## CRITICAL: INR Error Cases — Need BOTH not-return facts AND IH drule_all

After `reverse (Cases_on \`q\`)` on a bind result, the INR (error) subgoal
needs TWO things to close all 4 conjuncts:
1. `imp_res_tac eval_expr_not_return` — gives ∀v. res ≠ INR (ReturnException v)
2. `first_x_assum drule_all >> strip_tac >> gvs[]` — gives state preservation + not-TypeError

**CRITICAL ORDERING**: `imp_res_tac eval_expr_not_return` MUST come BEFORE
`drule_all` because `drule_all` CONSUMES the `eval_expr cx e st = (res, st')`
assumption that `eval_expr_not_return` needs as precondition.

**Pattern for INR error cases (terminal, use >- not TRY)**:
```
reverse (Cases_on `q`) >-
  (simp_tac (srw_ss()) [] >>
   imp_res_tac eval_expr_not_return >>
   first_x_assum drule_all >> strip_tac >> gvs[])
```

**DRule_all WORKS on INR cases!** The P7 IH says: `well_typed_expr env e ∧ ...
eval_expr cx e st = (res,st') ⇒ state_well_typed st' ∧ env_consistent ... ∧
accounts_well_typed st'.accounts ∧ ∀s. res ≠ INR (Error (TypeError s)) ∧ ...`.
This applies regardless of whether res is INL or INR — the IH just needs
well_typed_expr + eval_expr result.

## CRITICAL: gvs[] Too Aggressive for Non-terminal Positions

`gvs[]` performs variable elimination that can remove variables needed by
later `Cases_on` calls. Only safe at terminal positions (before QED) or
where no subsequent Cases_on follows.

## CRITICAL: >> and >- Have Same Precedence (SML)

`A >> >- B` does NOT parse as `A >> (>- B)`. Both `>>` and `>-` are
left-associative with same precedence, causing type errors.

**THE FIX**: Always parenthesize: `(A >- B) >> C` or `A >> (B >- C)`

## Pattern: AttributeTarget Return-Value Closing

After IH application gives state invariants, close with:
```
gvs[return_def] >> strip_tac >> gvs[]
```
The first gvs[] unfolds return_def (creates equalities like `st' = r`).
strip_tac applies those equalities. Second gvs[] cleans up.

## CRITICAL: gvs[] in Non-terminal TRY Blocks — FORBIDDEN

`gvs[]` inside `TRY (tp_bind_err_tac >> NO_TAC)` causes silent variable
elimination. If `tp_bind_err_tac` partially succeeds (simplifies but doesn't
close), `NO_TAC` fails, `TRY` catches, and the simplified goal with
eliminated variables remains. Subsequent `Cases_on x'` fails because `x'`
was eliminated by `gvs[]`.

**THE FIX**: Split tp_bind_err_tac into two variants:
1. **tp_bind_err_close_tac** (terminal only): uses `gvs[]`, safe because
   after it no more case splits needed. Use with `>-`.
2. **tp_bind_err_tac** (non-terminal): uses only `simp_tac (srw_ss())
   [exception_distinct, error_distinct]`, no variable elimination.

**Global rule**: Never use `gvs[]` inside a `TRY` block unless the
entire block is terminal.

## Pattern: BaseT → Value v derivation

When `expr_type e = BaseT bt` and IH gives `toplevel_value_typed x tyv`:
```
`?v. x = Value v` by (
  imp_res_tac evaluate_type_BaseT_imp_not_ArrayTV >>
  imp_res_tac evaluate_type_not_NoneT_imp_not_NoneTV >>
  metis_tac[toplevel_value_typed_not_ArrayRef])
```
This works because: BaseT evaluates to BaseTV (not NoneTV, not ArrayTV),
and toplevel_value_typed with non-NoneTV non-ArrayTV means it must be Value.

## Pattern: "Not BoolV" impossible cases in switch_BoolV

When switch_BoolV gets a non-boolean Value, it produces TypeError.
This contradicts the no-TypeError conclusion. But the case IS reachable
syntactically. Handle by:
1. Derive `x = Value v` (BaseT→Value pattern above)
2. `Cases_on `v`` to split BoolV from other constructors
3. Non-BoolV cases: `gvs[]` derives contradiction (TypeError in
   assumptions but not-TypeError in IH conclusion)

## Pattern: Terminal INR case with >-

Replace `TRY (tp_bind_err_tac >> NO_TAC)` at terminal positions with:
```
>- (imp_res_tac eval_expr_not_return >>
    first_x_assum drule_all >> strip_tac >> gvs[])
```
This is explicit (fails clearly if wrong) and handles all new conjuncts.

## Helper/Pattern Classification for Remaining Blocks

### Category A: Simple expression evaluation (LOW risk)
Blocks: Name, BareGlobalName, TopLevelName, FlagMember, Literal, IfExp,
  StructLit, Subscript, Attribute, Builtin/Pop, TypeBuiltin
Pattern: eval_expr case → INL/INR split → IH application → gvs[]

### Category B: Statement with nested eval (MEDIUM risk)
Blocks: If, AugAssign, AnnAssign, Assign, Append, Array, Range
Pattern: eval_expr → switch/type_check → nested eval → IH chain

### Category C: For/iterator blocks (MEDIUM risk)
Blocks: For, for_cons, for_nil
Pattern: eval_iterator + eval_stmts recursion, need iterator IH

### Category D: External interaction blocks (HIGH risk)
Blocks: ExtCall, IntCall, Send, RawCallTarget, RawLog, RawRevert,
  SelfDestructTarget, CreateTarget
Pattern: modify accounts → need accounts_well_typed preservation

### Category E: Simple list/target blocks (LOW risk)
Blocks: exprs_cons, exprs_nil, targets_cons, targets_nil


## CRITICAL: `by` blocks silently fail with `imp_res_tac` in rich contexts

When `imp_res_tac` can't syntactically match its precondition against any
assumption, it silently does nothing. Inside a `by` block, this means the
subgoal isn't progressed and the `by` block fails — but the error message
just says "by's tactic failed" without indicating WHY.

**THE FIX**: Never use `imp_res_tac` chains inside `by` blocks when the proof
context has many assumptions. Instead, prove the chain as a standalone theorem
(boundary lemma), then use a single `imp_res_tac` on the boundary lemma inside
the `by` block. The boundary lemma has a simpler matching pattern.

Pattern: If `by (a >> b >> c)` fails, extract `a >> b >> c` into Theorem X,
then use `by (imp_res_tac X >> simp[])`.

## CRITICAL: Same tactic in different proof contexts can have different results

Raise3's `imp_res_tac evaluate_type_not_NoneT_imp_not_NoneTV >> ...` works
because after Raise3's simpler `gvs[]` cleanup, the assumption pattern matches.
In Assert3, the richer context (with guarded IH for e' and the switch_BoolV
expansion) means the same `imp_res_tac` might match a different assumption
or fail to match entirely.

**THE FIX**: Don't copy tactics between blocks verbatim. Verify that assumptions
at the point of application match the lemma's preconditions. When in doubt,
prove boundary lemmas that are robust to context changes.

## Pattern: `toplevel_value_typed_BaseT_imp_Value` boundary lemma

When `evaluate_type tenv (BaseT bt) = SOME tyv` and `toplevel_value_typed tv tyv`,
then `∃v. tv = Value v`. This subsumes the BoolT-specific version and avoids
inline imp_res_tac chains. Used in: Raise3, Assert3, and likely other expr blocks.


## CRITICAL: Same tactic in different proof contexts has different results

Raise3's `imp_res_tac evaluate_type_not_NoneT_imp_not_NoneTV >> ...` sequence works
because after Raise3's simpler `gvs[]` cleanup, the assumption pattern matches.
In Assert3, the richer context (with guarded IH for e' and the switch_BoolV
expansion) means the same `imp_res_tac` might match a different assumption
or fail to match entirely.

**THE FIX**: Don't copy tactics between blocks verbatim. Prove boundary lemmas
that are robust to context changes. A boundary lemma's `imp_res_tac` only needs
to match ONE assumption (its direct precondition), regardless of how many other
assumptions are in scope.

## Helper Shape Index: BaseT-value derivation (4 instances, NEEDS GENERALIZATION)

### Pattern: BaseT-typed toplevel values are Value constructors
Used in: Raise3 (line 847), Assert3 (line 1115), and 2 uses in not_type_error_tac
Current approach: inline `imp_res_tac evaluate_type_not_NoneT_imp_not_NoneTV >>
imp_res_tac evaluate_type_BaseT_imp_not_ArrayTV >> Cases_on `x` >> gvs[]`

### Proposed boundary lemma (HIGHEST PRIORITY for next session):
```
Theorem toplevel_value_typed_BaseT_imp_Value:
  ∀tv tyv tenv bt.
    evaluate_type tenv (BaseT bt) = SOME tyv /\
    toplevel_value_typed tv tyv ==>
    ?v. tv = Value v
```
This subsumes: evaluate_type_not_NoneT_imp_not_NoneTV + evaluate_type_BaseT_imp_not_ArrayTV
+ Cases_on + gvs chain. A single `imp_res_tac` call replaces 5+ inline tactic steps.

### Existing overlapping lemmas:
- `toplevel_value_typed_BoolT_inv` — BoolT-specific version (line 225)
- `value_has_type_BoolT_inv` — lower-level, post-gvs form (line 244)
- `toplevel_value_typed_not_ArrayRef` — general but doesn't derive Value (line 4223)
