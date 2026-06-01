# STATE_type_system_rewrite
Updated: 2026-06-01

## Cursor
- component: C0.1
- status: in_progress
- active_file: semantics/prop/TYPE_SYSTEM_REWRITE_PLAN.md
- next_action: Finish the documentation-only superseding update for C0.1, then close C0.1 as proved and ask strategist review. After review, begin C0.2 and add/prove the local `eval_extcall_args_error` boundary probe before attempting the ExtCall Resume proof.
- expected_goal_shape: No HOL proof goal during C0.1. For C0.2, expect a small standalone theorem: from `eval_exprs cx es st = (INR y,args_st)`, one-step evaluation of `Call ret_type (ExtCall is_static (func_name,arg_types,ret_type)) es drv` returns `(INR y,args_st)` without any generated optional-driver prefix.
- verify_with: C0.1 is documentation-only. For C0.2 and later proof edits, use holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=300). The last clean audit build of the restored intentional-cheat baseline was tool_output:TO_type_system_rewrite-20260601T081233Z_m1671_t003.

## If This Fails
- If the C0.2 boundary probe exposes the generated optional-driver prefix, times out, or requires broad prefix cleanup/long adapter lemmas, checkpoint/close the active component as risk_mismatch and escalate to plan_oracle rather than trying tactic variants.

## Do Not Retry
- Retry the sanitized C0.1 shell (`well_typed_expr` one-step rewrite, `eval_exprs` split, explicit IH discharge, then narrow simplification of `args_res = INR y`).: E0072/m1655 showed this still leaves the generated optional-driver prefix live and times out on the argument-error branch; it is the same proof-boundary failure, not a tactic gap.
  - evidence: episode:E0072
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1655_t001
- Use broad `simp`, `gvs`, `AllCaseEqs()`, or whole-prefix cleanup on the post-`eval_exprs` ExtCall goal.: Forbidden by the maintainer clarification and repeatedly observed to produce >4KiB generated-prefix goals/timeouts before concrete success branches are isolated.
  - evidence: episode:E0067
  - evidence: episode:E0070
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1508_t001
- Direct `irule extcall_expr_sound_from_generated_ih` against the raw Resume goal or tiny `well_typed_expr_def` cleanup before it.: E0066 showed no match and even one-step cleanup timed out under the generated prefix.
  - evidence: episode:E0066
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1489_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1491_t001
- Resurrect old static/nonstatic ExtCall branch leaves C0.2/C0.3 as proof work without first proving a new boundary probe.: The stop/report replacement invalidated those leaves; they depended on C0.1 isolating the argument-success branch, which E0072 refuted.
  - evidence: episode:E0072
  - evidence: episode:E0073
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1664_t001
- Commit signed or stage untracked scratch/legacy files.: Task explicitly forbids GPG signing; untracked files are known scratch/legacy and were intentionally left uncommitted.
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1678_t001
  - evidence: tool_output:TO_type_system_rewrite-20260601T081233Z_m1679_t002

## Reflection
### Tunnel Vision Check
- Outside-the-box approach still not implemented: redesign the mutual theorem/suspend boundary so the optional-driver IH is consumed before the full ExtCall monadic prefix is reified, or prove a tiny continuation/boundary theorem whose live matchability is validated first.
- The previous work optimized the current `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result]` boundary; repeated evidence says that boundary itself is the problem, even for argument-error branches where the driver is irrelevant.
- The current PLAN decomposition is a stop/report subtree, not a proof-completion abstraction. That is correct for the task's stop-if-not-straightforward rule, but it cannot prove ExtCall.
- Do not retry tactics when the proof need is a new boundary/suspend/induction interface. A fresh expert should first ask where the optional-driver recursive-call IH is introduced and whether proof can be suspended/factored before the generated prefix enters irrelevant branches.

### What Went Wrong
- E0072 refuted the sanitized-boundary probe: after one-step typing/evaluator unfolding, splitting `eval_exprs`, and explicitly discharging the expression-list IH, the `args_res = INR y` branch still carried the full generated optional-driver prefix and timed out at narrow `simp[no_type_error_result_def]`.
- E0073/E0074/E0075 correctly converted the proof-completion attempt into a task-local stop/report state, audited that the source returned to the intentional cheat baseline, and committed the report unsigned as `e020b7978`.
- The pending C0.3 strategist review was finally accepted with no PLAN changes; query_plan then showed no executable frontier. A requested holbuild check was blocked by the PLAN gate because there is no active component/frontier, not because of a HOL source failure.

### Ignored Signals
- Earlier E0067/E0070 already showed branch-by-branch and focused-Resume attempts left the generated prefix live; the later sanitized C0.1 plan underweighted that the prefix also pollutes irrelevant error branches.
- The first timeout on a supposedly small argument-error simplification was a stop signal, not a cue to try local simplifier variants.
- Build success in this state only means build-clean-with-intentional-cheat; it must not be reported as proof completion.

### Strategy Adjustments
- Next session should not call another handoff or do proof work by default. It should treat the current task as externally blocked unless new maintainer/operator instructions supply a replacement proof architecture.
- If proof work is reauthorized, demand a first live probe that closes an early `eval_exprs` argument-error branch without the generated optional-driver prefix in the simplification goal before investing in static/nonstatic success branches.
- Keep untracked `semantics/prop/LEARNINGS_type_system_rewrite.legacy.md` and `semantics/prop/tmp_helper.txt` unstaged unless explicitly instructed.
- Continue using unsigned commits only (`git commit --no-gpg-sign`) and stage only task-owned tracked files under `semantics/prop`.

### Oracle Feedback
- Held: strategist accepted E0072 as a proof-boundary failure and replaced proof-completion work with a stop/report subtree; C0.1/C0.2/C0.3 are now reviewed/done.
- Held: the stop/report plan correctly invalidated old static/nonstatic proof leaves because their prerequisite boundary was refuted.
- Missed earlier: the replacement sanitized-boundary plan assumed the generated prefix could be kept out of the argument-error branch; E0072/m1655 showed it remains live.
- Current state is not a HOL proof problem to continue locally; it is an external-precondition blocker requiring a new authorized proof-boundary architecture.

## Evidence Pointers
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1689_t001 - strategist accepted C0.3/E0075 review with no PLAN changes and instructed stopped/blocked reporting rather than ExtCall proof search
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1691_t001 - query_plan after review shows no active component, no frontier, no Oracle next, and all C0 leaves done
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1690_t003 - holbuild request blocked by PLAN gate because no executable frontier remains
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1655_t001 - E0072 failure evidence: narrow argument-error simplification still timed out under generated optional-driver prefix
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1671_t003 - last clean targeted build of restored intentional-cheat baseline
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1678_t001 - unsigned commit `e020b7978 Report ExtCall boundary failure after E0072`
- tool_output:TO_type_system_rewrite-20260601T081233Z_m1679_t002 - post-commit status had only known untracked scratch/legacy files
- episode:E0075 - committed stop/report checkpoint for C0.3
- episode:E0072 - sanitized ExtCall proof-boundary probe stuck with risk_mismatch
