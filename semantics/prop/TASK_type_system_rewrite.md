Follow the goal and plan in semantics/prop/TYPE_SYSTEM_REWRITE_PLAN.md

Update the plan as you make progress

Do not edit any files outside of semantics/prop

Make commits as you make progress, but you must explicitly not GPG sign them (GPG signing requires a password and you will get stuck).

Stop if you run into any unexpected issues including tooling issues or problems with the design/plan. The proof should be entirely straightforward, you should stop if it is not.

## 2026-06-01 Maintainer clarification: ExtCall unblocking

The previous ExtCall stop gate is narrowed as follows:

- Do not edit outside `semantics/prop`.
- Do not change evaluator/semantics definitions.
- Proof-architecture refactoring inside `semantics/prop` is allowed.
- It is acceptable to attempt a careful, linear, branch-by-branch proof of
  `eval_all_type_sound_mutual[Expr_Call_ExtCall]` that steps through the
  monadic ExtCall chain one operation at a time, closes error cases immediately,
  and keeps only one main success path active.
- It is acceptable to specialize the generated optional-driver IH only after the
  proof has reached a single concrete ExtCall success-continuation branch where
  the relevant prefix operations have already been split/discharged.
- It remains forbidden to recover the driver premise from the top-level Resume
  context by broad `simp`/`gvs`, `AllCaseEqs()` cleanup over the whole ExtCall
  prefix, or long generated-prefix adapter theorems.
