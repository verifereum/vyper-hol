# HOL4 Proof Control Lessons

This note records proof-engineering lessons learned while working on the fresh Vyper type-soundness stack, especially statement-list and monadic preservation proofs. It complements `AGENTS.md`; use it when a HOL4 proof involves induction, monadic bind/exception semantics, or many case splits.

## 1. Track active subgoals before every nontrivial tactic

Many confusing tactic failures are caused by applying a tactic to multiple active subgoals when it was intended for one.

Danger pattern:

```sml
Cases_on `...` >> gvs[] >>
drule_all some_theorem >>
...
```

If `Cases_on` or `gvs[AllCaseEqs()]` leaves multiple branches, then `drule_all some_theorem` is applied to all of them. It may work in one branch but fail in another, producing misleading errors.

Before using tactics such as:

```sml
drule_all
first_x_assum drule_all
irule
drule
dxrule
metis_tac
```

ask: **am I working on exactly one goal?** If not, solve or isolate branches first.

When using `NO_TAC`, always inspect both:

```text
remaining goals at failed fragment: N
```

and the top goal. If `N > 1`, the next tactic would have run on multiple subgoals.

## 2. Solve semantic branches immediately

Unfolding monadic semantics usually creates branches for success, exception, type error, or impossible cases. Do not leave these branches floating.

Good pattern:

```sml
Cases_on `...` >> gvs[]
>- (
  (* solve first branch completely *)
  ...
) >>
(* only one branch remains *)
...
```

Often the secondary branch is easier to solve first. Use `reverse`:

```sml
reverse(gvs[bind_def, ignore_bind_def, AllCaseEqs()]) >- (
  (* solve exception/error branch *)
  ...
) >>
(* continue with success branch only *)
...
```

Example from statement-list exception preservation:

```sml
reverse(gvs[bind_def, ignore_bind_def, AllCaseEqs()]) >- (
  drule_all eval_stmt_type_preservation_exception >> rw[]
) >>
drule_all eval_stmt_type_preservation_success >> strip_tac >>
first_x_assum drule_all >> strip_tac >>
gvs[] >>
drule_all type_stmt_preserves_stmt_error_ok >>
rw[]
```

The important point is that after the `>- (...)`, only the intended continuation branch remains.

## 3. Avoid `rw` too early

`rw` can introduce variables, split conjunctions, destruct existentials, simplify definitions, and create many subgoals before the proof is ready.

Risky pattern:

```sml
Induct >>
rw[definition_with_cases, AllCaseEqs()] >>
...
```

Better pattern:

```sml
Induct >> simp[base_eval_defs] >>
simp[type_stmt_def, AllCaseEqs(), PULL_EXISTS] >>
rpt gen_tac >> strip_tac >>
...
```

Use `simp` to expose the structural shape, then `strip_tac` when you only want to consume the main implication. Save `rw` for small, controlled goals or final cleanup.

## 4. Do not rename away specialized information

Avoid turning a specialized semantic fact into a generic variable and then splitting it again.

Bad pattern:

```sml
Cases_on `eval_stmt cx h st` >> gvs[] >>
rename1 `eval_stmt cx h st = (res1, st1)` >>
Cases_on `res1` >> gvs[]
```

After monadic simplification, HOL may already know the specialized shape:

```sml
eval_stmt cx h st = (INL (), st1)
```

Renaming to `res1` and splitting again throws away useful branch information and can create artificial impossible branches.

Prefer:

```sml
Cases_on `eval_stmt cx h st` >> gvs[] >>
drule_all eval_stmt_type_preservation_success >> strip_tac >>
...
```

Let `gvs` preserve and exploit specialized facts like `INL ()`.

## 5. Abbreviate specialized terms; do not generalize them

If a specialized assumption is useful, preserve its shape. If a subterm is too large, abbreviate the subterm rather than renaming/generalizing the whole fact.

Example:

```sml
qmatch_asmsub_abbrev_tac `eval_stmts cx ss st_tail`
```

or:

```sml
qmatch_goalsub_abbrev_tac `eval_expr cx e st_expr`
```

Principle: **preserve specialized logical shape; abbreviate only complex pieces.**

## 6. Prefer forward reasoning for threaded induction hypotheses

For list/threaded semantics, once preservation for the head statement is established, the tail induction hypothesis usually has all premises available.

Good pattern:

```sml
drule_all eval_stmt_type_preservation_success >> strip_tac >>
first_x_assum drule_all >> rw[]
```

This is usually simpler than trying to instantiate the induction hypothesis backwards with `irule`, `qexistsl_tac`, or manual `qspecl_then`.

Successful statement-list success proof shape:

```sml
MAP_EVERY qid_spec_tac [`env'`, `st'`, `u`, `st`, `env`, `ss`] >>
Induct
>- simp[Once evaluate_def, return_def, type_stmt_def] >>
rpt gen_tac >> strip_tac >>
gvs[type_stmt_def, AllCaseEqs(), Once evaluate_def, bind_def, ignore_bind_def] >>
Cases_on `eval_stmt cx h st` >> gvs[] >>
drule_all eval_stmt_type_preservation_success >> strip_tac >>
first_x_assum drule_all >> rw[]
```

## 7. Add transport helpers for repeated env/state mismatch

If a proof repeatedly needs to move a property across an env or state transition, state a focused helper lemma.

Example issue: tail exception preservation gives:

```sml
stmt_error_ok env1 ret_ty (INR exn)
```

but the outer theorem wants:

```sml
stmt_error_ok env ret_ty (INR exn)
```

Since statement typing preserves static fields and `stmt_error_ok` depends only on `env.type_defs`, add:

```sml
Theorem type_stmt_preserves_stmt_error_ok:
  type_stmt env ret_ty s = SOME env1 /\ stmt_error_ok env1 ret_ty r ==>
  stmt_error_ok env ret_ty r
```

Then the main proof can use:

```sml
drule_all type_stmt_preserves_stmt_error_ok >> rw[]
```

Do not unfold the transport logic repeatedly in the main proof.

## 8. `drule_all` is good when the context is controlled

`drule_all` is effective for direct forward reasoning in small, well-shaped contexts:

```sml
drule_all eval_stmt_type_preservation_success >> strip_tac
first_x_assum drule_all >> strip_tac
drule_all type_stmt_preserves_stmt_error_ok >> rw[]
```

But it is dangerous when multiple branches are still active. Control subgoals first, then use `drule_all`.

## 9. Recommended skeleton for monadic list preservation

For statement-list or similar sequential monadic proofs:

```sml
MAP_EVERY qid_spec_tac [...] >>
Induct >> simp[base_eval_defs] >>
simp[type_defs, AllCaseEqs(), PULL_EXISTS] >>
rpt gen_tac >> strip_tac >>
reverse(gvs[bind_def, ignore_bind_def, AllCaseEqs()]) >- (
  (* exception/error branch, solve immediately *)
  ...
) >>
(* success branch only remains *)
drule_all head_preservation >> strip_tac >>
first_x_assum drule_all >> strip_tac >>
...
```

This keeps the proof linear and prevents tactics from being applied to unrelated branches.

## 10. Quick checklist

Before applying a nontrivial tactic:

1. How many active subgoals are there?
2. Did `Cases_on`, `rw`, or `gvs[AllCaseEqs()]` create branches?
3. Should one branch be solved immediately with `>- (...)` or `reverse(...) >- (...)`?
4. Am I preserving specialized facts like `INL ()`, or did I rename/generalize them away?
5. Would forward reasoning (`drule_all`) be simpler than backward instantiation (`irule` + witnesses)?
6. Is an env/state transport helper needed?

Use this checklist especially when proving type soundness, preservation, and no-type-error lemmas over monadic evaluators.
