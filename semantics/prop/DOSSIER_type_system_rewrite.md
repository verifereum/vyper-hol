# DOSSIER: type_system_rewrite

PLAN: `semantics/prop/PLAN_type_system_rewrite.md`

## Component Index

| Component | Status | Diagnosis | Latest Episode | Next |
|---|---|---|---|---|
| C0 | proved |  | E0021 |  |
| C0.1 | proved |  | E0076 | Call plan_oracle(mode='review') for C0.1, then if accepted begin C0.2 and prove the local argument-error boundary probe. |
| C0.1.1 | stuck | risk_mismatch | E0033 | Ask strategist to provide a more concrete, low-risk prefix script or a different decomposition; source is currently buildable with the checkpoint placeholder. |
| C0.1.1.1 | proved |  | E0036 |  |
| C0.1.1.2 | stuck | risk_mismatch | E0038 | Call plan_oracle(mode='review') for this stuck episode and request a redesign of the ExtCall helper boundary/proof plan under the maintainer constraints. |
| C0.1.1.2.0 | proved |  | E0059 |  |
| C0.1.1.2.1 | proved |  | E0060 |  |
| C0.1.1.2.2 | proved |  | E0061 |  |
| C0.1.1.2.2.1 | stuck | risk_mismatch | E0047 | Call plan_oracle review for C0.1.1.2.2.1 and request a more robust static wrapper interface/proof strategy that avoids long generated-prefix witness plumbing. |
| C0.1.1.2.3 | stuck | risk_mismatch | E0051 | Call plan_oracle(mode="review") for C0.1.1.2.3 with this risk-mismatch evidence; request a precise replacement/augmentation for the Resume-entry proof shape or permission to factor a small matching helper if the component should remain low risk. |
| C0.1.1.2.3.1 | proved |  | E0062 |  |
| C0.1.1.2.3.1.1 | stuck | risk_mismatch | E0056 | Call plan_oracle(mode='review') for C0.1.1.2.3.1.1. Request either a genuinely matchable boundary/probe or an explicit stop decision under the task's straightforward-proof instruction. |
| C0.1.1.2.3.2 | stuck | plan_incomplete | E0058 | Call plan_oracle(mode='review') for this stuck episode and request removal/replacement of the stale scheduled C0.1.1.2.3.2 frontier or an explicit operator-facing stop state. |
| C0.1.1.2.4 | proved |  | E0063 |  |
| C0.1.1.2.5 | proved |  | E0064 | Review/handle generated PLAN diff, then report blocked/operator handoff rather than proof completion; do not reopen ExtCall proof. |
| C0.1.2 | stuck | risk_mismatch | E0065 | Ask the strategist to repair/reconcile the PLAN with source reality, or accept the operator-facing blocked stop-state rather than continuing C0.1.2. |
| C0.2 | proved |  | E0074 | Call plan_oracle(mode='review') for C0.2, then proceed to the unsigned commit/report component C0.3 if accepted. |
| C0.2.1 | proved |  | E0069 | Call plan_oracle(mode='review') and then proceed to the focused Resume proof shell component if accepted. |
| C0.2.2 | stuck | risk_mismatch | E0070 | Call plan_oracle(mode='review', component_id='C0.2.2') with this evidence and ask for a redesigned/de-risked boundary rather than more local simplifier variants. |
| C0.3 | proved |  | E0075 | Call plan_oracle(mode='review') for C0.3; if accepted, inspect query_plan for whether C0 is complete and then follow the stop/report outcome. |
| C1.1 | proved |  | E0024 | Call plan_oracle(mode='review') for C1.1, then begin C1.2 if accepted. |
| C1.1.1 | proved |  | E0012 |  |
| C1.1.2 | proved |  | E0013 |  |
| C1.1.2.0 | proved |  | E0007 |  |
| C1.1.2.1 | proved |  | E0008 | Call plan_oracle review for C1.1.2.1, then if accepted commit the source checkpoint without GPG signing before beginning C1.1.2.2. |
| C1.1.2.2 | proved |  | E0009 | Call plan_oracle review for C1.1.2.2; if accepted, commit the helper checkpoint without GPG signing, then begin C1.1.3. |
| C1.1.3 | stuck | risk_mismatch | E0014 | Call plan_oracle review for C1.1.3 with this evidence; ask for a concrete adapter theorem statement/proof route that does not reopen C1.1.2 and does not require simplifying the full guarded IH in the Resume. |
| C1.1.3.0 | proved |  | E0016 |  |
| C1.1.3.1 | proved |  | E0018 | Call plan_oracle review for C1.1.3.1, then begin queued C1.1.3.2 to refactor the `Expr_Call_ExtCall` Resume using the new conditional boundary. |
| C1.1.3.2 | stuck | risk_mismatch | E0019 | Call plan_oracle review for C1.1.3.2 with evidence and ask for a de-risked adapter/decomposition for consuming the generated guarded driver IH without broad prefix simplification. |
| C1.1.3.2.1 | stuck | risk_mismatch | E0020 | Call plan_oracle review for C1.1.3.2.1; request a higher-level redesign or operator stop per task instruction rather than another local generated-prefix adapter. |
| C1.2 | stuck | risk_mismatch | E0025 | Call plan_oracle(mode='review') for C1.2 with the checkpoint goal evidence; request replacement/decomposition that changes the mutual induction/suspend boundary or otherwise exposes a compact driver IH without generated-prefix plumbing. |

## C0

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0021`
- blocker: 
- actual effort: 1 sessions, 1 steps, 55,597 tok (55,394 in, 203 out, 54,656 cached), 8.2s, $0.037108

### Attempts / Evidence

- `E0001` (proved, , actual effort: 1 sessions, 1 steps, 138,836 tok (138,607 in, 229 out, 137,600 cached), 8.1s, $0.080705)
  - Carry-forward baseline component begun to satisfy schedule gate; no source proof work authorized or performed under C0. -> C0 has no executor work; current actionable proof frontier is C1.1 per structured plan. ()
- `E0021` (proved, , actual effort: 1 sessions, 1 steps, 55,597 tok (55,394 in, 203 out, 54,656 cached), 8.2s, $0.037108)
  - Carry-forward baseline component begun to satisfy replacement-plan schedule gate; no source proof work/edit/build authorized or performed under C0. -> C0 is a source-audit carry-forward component with no executable proof obligations; completed baseline evidence remains preserved while current source is known not build-clean due to later partial ExtCall edits. ()

### Evidence refs

- `TO_type_system_rewrite-20260531T201607Z_m0451_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260531T201607Z_m0453_t001` (use `read_tool_output` for exact output)

## C0.1

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0076`
- blocker: 
- actual effort: 1 sessions, 6 steps, 8 tools, 461,959 tok (459,256 in, 2,703 out, 435,456 cached), 60.5s, $0.417818
- next: Call plan_oracle(mode='review') for C0.1, then if accepted begin C0.2 and prove the local argument-error boundary probe.

### Attempts / Evidence

- `E0026` (proved, , actual effort: 1 sessions, 1 msgs, 5 steps, 7 tools, 1 holbuild, 300,641 tok (299,677 in, 964 out, 276,864 cached), 250.8s, $0.281417)
  - Deleted tautological `extcall_driver_continuation_premise_from_compact_ih` and replaced the C1.2 FAIL_TAC marker in Expr_Call_ExtCall Resume with the honest existing `cheat` placeholder; no generated-prefix proof attempt made. -> Focused holbuild of vyperTypeStmtSoundnessTheory succeeded, confirming cleanup is syntactically/build coherent (with the remaining authorized placeholder cheat). (`TO_type_system_rewrite-20260531T201607Z_m0541_t001`, `TO_type_system_rewrite-20260531T201607Z_m0541_t002`, `TO_type_system_rewrite-20260531T201607Z_m0542_t002`, `TO_type_system_rewrite-20260531T201607Z_m0543_t001`)
- `E0029` (stuck, risk_mismatch, actual effort: 1 sessions, 1 msgs, 26 steps, 28 tools, 10 holbuild, 1,989,391 tok (1,981,047 in, 8,344 out, 1,880,832 cached), 383.9s, $1.691811)
  - Inside `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall]`, unfolded the expression proof through `well_typed_expr_def`/`evaluate_def` and inserted FAIL probes after the first evaluator unfold and after attempting to split `eval_exprs`. -> The first probe still showed the optional-driver IH as a generated full-prefix implication over `eval_exprs`, `check`, `lift_option_type`, `lift_option`, `build_ext_calldata`, `run_ext_call`, `update_accounts`, and `update_transient`, matching the previous structural blocker rather than exposing a compact premise. (`TO_type_system_rewrite-20260531T201607Z_m0862_t001`, `TO_type_system_rewrite-20260531T201607Z_m0868_t001`, `TO_type_system_rewrite-20260531T201607Z_m0870_t001`)
  - Tried to continue the approved local branch split through `eval_exprs` and the static ExtCall spine, using targeted assumptions and theorem-level `SIMP_RULE` instead of broad generated-prefix reconstruction. -> Even basic local simplification after the split (`gvs[no_type_error_result_def]`, `simp[]`, and then `Cases_on is_static' >> gvs[]`) timed out or left the same huge generated-prefix goal; a targeted pattern for the static branch failed. This indicates the C0.1 probe is not a straightforward low-risk boundary adjustment under the current proof state. (`TO_type_system_rewrite-20260531T201607Z_m0864_t001`, `TO_type_system_rewrite-20260531T201607Z_m0866_t001`, `TO_type_system_rewrite-20260531T201607Z_m0875_t001`, `TO_type_system_rewrite-20260531T201607Z_m0877_t001`, `TO_type_system_rewrite-20260531T201607Z_m0881_t001`)
  - Reverted the experimental proof prefix back to the honest `cheat` placeholder and rebuilt `vyperTypeStmtSoundnessTheory`. -> Focused build is back to the stable cheated baseline; no broken proof prefix remains in source. (`TO_type_system_rewrite-20260531T201607Z_m0882_t001`, `TO_type_system_rewrite-20260531T201607Z_m0883_t001`)
- `E0030` (stuck, risk_mismatch, actual effort: 1 sessions, 3 msgs, 37 steps, 38 tools, 14 holbuild, 4,250,423 tok (4,237,079 in, 13,344 out, 4,083,584 cached), 712.5s, $3.209587)
  - Tried to prove Expr_Call_ExtCall by factoring through existing local helper `extcall_expr_sound_from_generated_ih`, extracting the expression-list IH and the optional driver IH from the Resume context. -> Expression-list IH could be labelled and focused baseline built, but the optional-driver IH in the live Resume context is not the compact premise expected by the helper; it remains the full generated ExtCall prefix implication. This reproduces the known proof-interface problem rather than providing a straightforward proof path. (`TO_type_system_rewrite-20260601T081233Z_m0916_t001`)
  - Tried the maintainer-authorized bounded linear proof directly inside `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall]`: unfold `well_typed_expr`/`evaluate_def` once, split `eval_exprs`, consume the expr-list IH, then split the static branch locally and close immediate branches. -> Even with targeted rewrites, the live goal remains a >4KiB generated prefix; routine local steps timed out (`simp[]`, `gvs[]`, `gvs[no_type_error_result_def]`, `gvs[return_def, raise_def]`) at successive branch points. Attempts to avoid broad simplification by extracting facts with `SIMP_RULE (srw_ss()) []` progressed only slightly, then the next local branch split again required simplification over the large prefix. This violates the plan's stop condition for broad/generated-prefix reconstruction and indicates the bounded probe is not straightforward under the current proof boundary. (`TO_type_system_rewrite-20260601T081233Z_m0919_t001`, `TO_type_system_rewrite-20260601T081233Z_m0924_t001`, `TO_type_system_rewrite-20260601T081233Z_m0926_t001`, `TO_type_system_rewrite-20260601T081233Z_m0929_t001`, `TO_type_system_rewrite-20260601T081233Z_m0931_t001`, `TO_type_system_rewrite-20260601T081233Z_m0936_t001`, `TO_type_system_rewrite-20260601T081233Z_m0940_t001`, `TO_type_system_rewrite-20260601T081233Z_m0942_t001`, `TO_type_system_rewrite-20260601T081233Z_m0944_t001`)
  - Reverted the experimental ExtCall proof prefix to the honest `cheat` placeholder and rebuilt `vyperTypeStmtSoundnessTheory`. -> Focused build is back to the stable cheated baseline; no broken proof prefix remains in source. (`TO_type_system_rewrite-20260601T081233Z_m0946_t001`, `TO_type_system_rewrite-20260601T081233Z_m0947_t001`)
- `E0066` (stuck, risk_mismatch, actual effort: 1 sessions, 1 msgs, 12 steps, 13 tools, 5 holbuild, 731,510 tok (728,814 in, 2,696 out, 694,784 cached), 133.4s, $0.598422)
  - Replaced the ExtCall_result cheat with `rpt gen_tac >> strip_tac >> FAIL_TAC` to inspect the live Resume goal without simplification. -> The live goal still contains the generated optional-driver IH as a large ExtCall prefix implication plus the expression-list IH and top-level ExtCall evaluation/typing assumptions; this confirms the helper must match the raw Resume shape if C0.1 is to succeed. (`TO_type_system_rewrite-20260601T081233Z_m1486_t001`, `TO_type_system_rewrite-20260601T081233Z_m1487_t001`)
  - Tried the direct boundary exactly as planned: `rpt gen_tac >> strip_tac >> irule extcall_expr_sound_from_generated_ih`. -> `irule` failed with `No match` on the live goal. The goal's outer Call result type is `v15` while the helper conclusion expects the outer Call result type to match the ExtCall tuple return type, and the live optional-driver IH is still conditional on the generated prefix rather than the helper's unconditional premise. (`TO_type_system_rewrite-20260601T081233Z_m1488_t001`, `TO_type_system_rewrite-20260601T081233Z_m1489_t001`)
  - Tried the smallest possible typing-boundary cleanup before applying the helper: move the top-level `well_typed_expr` assumption and rewrite once with `well_typed_expr_def`. -> Even this local cleanup timed out under the large live generated-prefix context. Continuing would require broad prefix simplification or brittle plumbing, which C0.1 explicitly forbids. Source was restored to the honest cheat and the target rebuild returned to the stable cheated baseline. (`TO_type_system_rewrite-20260601T081233Z_m1490_t001`, `TO_type_system_rewrite-20260601T081233Z_m1491_t001`, `TO_type_system_rewrite-20260601T081233Z_m1492_t001`, `TO_type_system_rewrite-20260601T081233Z_m1493_t001`)
- `E0071` (proved, , actual effort: 1 sessions, 1 msgs, 8 steps, 10 tools, 1 holbuild, 576,132 tok (573,242 in, 2,890 out, 520,192 cached), 88.2s, $0.612046)
  - Updated `semantics/prop/TYPE_SYSTEM_REWRITE_PLAN.md` to replace the authorized linear ExtCall probe section with an operator-facing generated-prefix blockage report citing E0070 evidence. -> Plan/report now states the theorem is not shown false, the source/evaluator definitions were not changed, the focused Resume still exposes the generated optional-driver prefix after `eval_exprs`, and future work needs a new proof boundary rather than more local proof search. (`TO_type_system_rewrite-20260601T081233Z_m1618_t001`, `TO_type_system_rewrite-20260601T081233Z_m1621_t001`, `TO_type_system_rewrite-20260601T081233Z_m1622_t001`)
  - Verified the restored source baseline with `holbuild(targets=["vyperTypeStmtSoundnessTheory"])`. -> Target builds on the intentional cheated baseline, confirming no broken proof edit remains after the report update. (`TO_type_system_rewrite-20260601T081233Z_m1616_t003`)
- `E0072` (stuck, risk_mismatch, actual effort: 1 sessions, 1 msgs, 16 steps, 18 tools, 5 holbuild, 1,448,724 tok (1,443,745 in, 4,979 out, 1,354,752 cached), 202.6s, $1.271711)
  - Replaced ExtCall_result cheat with sanitized Resume shell: strip result implication, rewrite `well_typed_expr` once, unfold one evaluator layer to `eval_exprs`, split `eval_exprs`, and consume the expression-list IH via explicit `impl_tac`/`rpt conj_tac` rather than bare `simp[]`. -> The shell progressed past the IH application without the earlier immediate m1595 timeout once the IH pattern was corrected; however the argument-error branch still had the generated optional-driver prefix in the live goal. (`TO_type_system_rewrite-20260601T081233Z_m1653_t001`, `TO_type_system_rewrite-20260601T081233Z_m1655_t001`)
  - Tried to close `args_res = INR y` with the narrow planned `simp[no_type_error_result_def]` after `reverse (Cases_on args_res)`. -> This timed out on the same >4KiB generated optional-driver prefix, matching the C0.1 failure condition and the explicit not-to-try warning against simplifying while that prefix remains. Source was restored to the honest ExtCall cheat baseline and the target rebuilds. (`TO_type_system_rewrite-20260601T081233Z_m1655_t001`, `TO_type_system_rewrite-20260601T081233Z_m1656_t001`, `TO_type_system_rewrite-20260601T081233Z_m1657_t002`, `TO_type_system_rewrite-20260601T081233Z_m1657_t001`)
- `E0073` (proved, , actual effort: 1 sessions, 1 msgs, 5 steps, 6 tools, 596,951 tok (595,042 in, 1,909 out, 553,856 cached), 46.9s, $0.540128)
  - Updated `semantics/prop/TYPE_SYSTEM_REWRITE_PLAN.md` ExtCall blockage section with an E0072 addendum. -> The report now records that the sanitized-boundary probe discharged the eval_exprs IH explicitly but still timed out on `args_res = INR y` because the generated optional-driver prefix remained live; it also says the old static/nonstatic C0.2-C0.5 leaves are invalidated unless a new boundary first isolates the argument-success branch. (`TO_type_system_rewrite-20260601T081233Z_m1664_t001`, `TO_type_system_rewrite-20260601T081233Z_m1665_t002`)
  - Checked report text for the new E0072/sanitized-shell markers. -> Grep confirms the dated E0072 update and no-retry sanitized-shell warning are present in the task-local plan report. (`TO_type_system_rewrite-20260601T081233Z_m1665_t001`)
- `E0076` (proved, , actual effort: 1 sessions, 6 steps, 8 tools, 461,959 tok (459,256 in, 2,703 out, 435,456 cached), 60.5s, $0.417818)
  - Updated task-local TYPE_SYSTEM_REWRITE_PLAN.md ExtCall blockage section with a 2026-06-01 superseding note after strategist replacement C0 plan. -> The plan now treats the old stop/report state as historical evidence, identifies `eval_extcall_args_error` as the first executable proof-boundary probe, preserves E0072 no-retry guidance, and keeps the restriction against edits outside `semantics/prop`/semantics-definition changes. (`TO_type_system_rewrite-20260601T081233Z_m1703_t001`, `TO_type_system_rewrite-20260601T081233Z_m1705_t002`)
  - Updated STATE cursor for the new executable C0.1/C0.2 flow. -> STATE no longer says no proof/build/edit action is legal under the old stop report; it points to closing C0.1, then beginning C0.2 and proving the local argument-error boundary probe. Diff/grep confirmed the expected markers. (`TO_type_system_rewrite-20260601T081233Z_m1704_t001`, `TO_type_system_rewrite-20260601T081233Z_m1705_t001`, `TO_type_system_rewrite-20260601T081233Z_m1705_t002`)

### Evidence refs

- `TO_type_system_rewrite-20260601T081233Z_m1699_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1700_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1703_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1704_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1705_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1705_t002` (use `read_tool_output` for exact output)

## C0.1.1

### Current Status

- result: `stuck`
- diagnosis: `risk_mismatch` This attempt used a too-broad `gvs[no_type_error_result_def]` after splitting `args_res`, which matches the forbidden broad-cleanup smell; per task instruction to stop on unexpected proof/design issues, do not continue tactic experimentation without strategist review.
- latest episode: `E0033`
- blocker: The revised checkpoint still is not straightforward to execute: a direct local prefix split/probe over the current `Expr_Call_ExtCall_result` Resume ran out of store before reaching focused static/nonstatic labels.
- actual effort: 1 sessions, 1 msgs, 9 steps, 8 tools, 3 holbuild, 663,618 tok (660,905 in, 2,713 out, 629,632 cached), 114.3s, $0.552571
- next: Ask strategist to provide a more concrete, low-risk prefix script or a different decomposition; source is currently buildable with the checkpoint placeholder.

### Attempts / Evidence

- `E0031` (progressed, plan_incomplete, actual effort: 1 sessions, 2 msgs, 17 steps, 28 tools, 3 holbuild, 1,297,535 tok (1,290,844 in, 6,691 out, 1,231,744 cached), 524.5s, $1.112102)
  - Moved `type_place_expr_Call_ExtCall_NONE` before the mutual proof; replaced the old `TRY(rename1 `ExtCall` >> suspend "Expr_Call_ExtCall")` with an ExtCall-specific prefix closing the place half and suspending `Expr_Call_ExtCall_result`; replaced the obsolete monolithic Resume with a matching cheated placeholder. -> The edited theory builds with the placeholder, so the suspend/resume structure is syntactically coherent. (`TO_type_system_rewrite-20260601T081233Z_m0961_t001`, `TO_type_system_rewrite-20260601T081233Z_m0962_t003`)
  - Temporarily replaced the new `Expr_Call_ExtCall_result` placeholder with `FAIL_TAC "probe ExtCall result boundary"` to inspect the new suspended goal, then reverted the probe to `cheat`. -> The new suspended goal still contains a large generated ExtCall prefix/conditional-driver IH assumption over `eval_exprs`, `check`, `lift_option_type`, `build_ext_calldata`, `run_ext_call`, `update_accounts`, and `update_transient`, and it is not split into static/nonstatic focused leaves as C0.1.1 required. (`TO_type_system_rewrite-20260601T081233Z_m0966_t001`, `TO_type_system_rewrite-20260601T081233Z_m0967_t001`)
- `E0032` (stuck, plan_incomplete, actual effort: 1 sessions, 2 msgs, 18 steps, 29 tools, 3 holbuild, 1,357,097 tok (1,349,634 in, 7,463 out, 1,288,960 cached), 541.5s, $1.171740)
  - Implemented the first earlier-boundary refactor exactly at the original mutual proof ExtCall suspend site: close `type_place_expr`, suspend `Expr_Call_ExtCall_result`, and add a matching cheated Resume. Verified the target builds with this placeholder. -> The source is build-coherent with the placeholder, but this only creates one result leaf, not focused static/nonstatic leaves. (`TO_type_system_rewrite-20260601T081233Z_m0961_t001`, `TO_type_system_rewrite-20260601T081233Z_m0962_t003`)
  - Probed the new leaf by temporarily replacing its placeholder with `FAIL_TAC` and rebuilding, then restored the placeholder. -> The new leaf still exposes the forbidden large generated ExtCall prefix: the driver IH is guarded by an implication over `eval_exprs`, `check`, `lift_option_type`, `build_ext_calldata`, `run_ext_call`, `update_accounts`, and `update_transient`; the leaf is not yet split into static/nonstatic focused continuation obligations. (`TO_type_system_rewrite-20260601T081233Z_m0966_t001`, `TO_type_system_rewrite-20260601T081233Z_m0967_t001`)
- `E0033` (stuck, risk_mismatch, actual effort: 1 sessions, 1 msgs, 9 steps, 8 tools, 3 holbuild, 663,618 tok (660,905 in, 2,713 out, 629,632 cached), 114.3s, $0.552571)
  - After strategist replacement, attempted to push the `Expr_Call_ExtCall_result` Resume one step further by stripping the `well_typed_expr` premise, unfolding one layer of ExtCall evaluator, case-splitting `eval_exprs`, then `Cases_on args_res >> gvs[no_type_error_result_def]` as a probe before replacing with static/nonstatic labels. -> The build ran out of store / interrupted, indicating the attempted prefix split was not the straightforward local decomposition required by the task. The experiment was reverted to the buildable cheated placeholder. (`TO_type_system_rewrite-20260601T081233Z_m0975_t001`, `TO_type_system_rewrite-20260601T081233Z_m0978_t001`, `TO_type_system_rewrite-20260601T081233Z_m0979_t001`, `TO_type_system_rewrite-20260601T081233Z_m0980_t001`)

### Ruled Out

- Continuing to tune simplification/case-splitting inside the current `Expr_Call_ExtCall_result` Resume after a store exhaustion.

### Evidence refs

- `TO_type_system_rewrite-20260601T081233Z_m0975_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m0978_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m0979_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m0980_t001` (use `read_tool_output` for exact output)

## C0.1.1.1

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0036`
- blocker: 
- actual effort: 1 sessions, 1 steps, 130,168 tok (129,889 in, 279 out, 125,824 cached), 13.9s, $0.091607

### Attempts / Evidence

- `E0034` (proved, , actual effort: 1 sessions, 3 steps, 5 tools, 266,505 tok (265,747 in, 758 out, 255,616 cached), 25.6s, $0.201203)
  - Targeted grep/read audit for ExtCall helper interface names and statements in `vyperTypeStmtSoundnessScript.sml`. -> Confirmed local helpers exist with expected shapes: `run_ext_call_accounts_well_typed`, `extcall_success_continuation_sound_cond_driver_ih`, `extcall_static_args_runtime_typed_dest`, and `extcall_nonstatic_args_runtime_typed_dest`. Also found an older proof-like block around lines 9860-9934 showing these helpers' intended use, including static/nonstatic splits and `extcall_success_continuation_sound`; for future work prefer the conditional-driver helper per plan. (`TO_type_system_rewrite-20260601T081233Z_m0986_t001`, `TO_type_system_rewrite-20260601T081233Z_m0986_t002`, `TO_type_system_rewrite-20260601T081233Z_m0987_t001`, `TO_type_system_rewrite-20260601T081233Z_m0987_t002`, `TO_type_system_rewrite-20260601T081233Z_m0987_t003`)
- `E0036` (proved, , actual effort: 1 sessions, 1 steps, 130,168 tok (129,889 in, 279 out, 125,824 cached), 13.9s, $0.091607)
  - Carry-forward audit component under replacement plan: reused accepted E0034 evidence without source edits. -> The audited helper interface remains valid for the new direct-helper strategy: `extcall_expr_sound_from_generated_ih`/`type_place_expr_Call_ExtCall_NONE` are present, and prior grep/read evidence confirmed the ExtCall helper block. No additional proof/search work required by the carry-forward component. (`TO_type_system_rewrite-20260601T081233Z_m0988_t001`, `TO_type_system_rewrite-20260601T081233Z_m0989_t001`)

### Evidence refs

- `TO_type_system_rewrite-20260601T081233Z_m0988_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m0989_t001` (use `read_tool_output` for exact output)

## C0.1.1.2

### Current Status

- result: `stuck`
- diagnosis: `risk_mismatch` This is a design/plan issue, not a missing tactic. The helper needs a different interface (accepting the generated prefix-guarded driver IH) or the proof boundary must change so the prefix facts are in scope where the driver IH is used.
- latest episode: `E0038`
- blocker: The Risk 2 direct-helper wrapper plan has a proof-interface mismatch: `extcall_expr_sound_from_generated_ih` requires an unconditional compact driver IH, but `Expr_Call_ExtCall_result` only supplies a prefix-guarded generated driver IH. The planned small adapter is not available in this context.
- actual effort: 1 sessions, 1 msgs, 15 steps, 18 tools, 6 holbuild, 959,473 tok (954,055 in, 5,418 out, 834,304 cached), 351.1s, $1.178447
- next: Call plan_oracle(mode='review') for this stuck episode and request a redesign of the ExtCall helper boundary/proof plan under the maintainer constraints.

### Attempts / Evidence

- `E0035` (stuck, risk_mismatch, actual effort: 1 sessions, 2 msgs, 30 steps, 29 tools, 8 holbuild, 3,324,634 tok (3,317,914 in, 6,720 out, 3,263,744 cached), 425.7s, $2.104322)
  - Replaced `Expr_Call_ExtCall_result: cheat` with the planned prefix skeleton: strip normal-expression implication, expose call typing, unfold one ExtCall evaluator layer, split `eval_exprs`, instantiate the generated expression-list IH, then split `args_res`. -> Initial attempt timed out on `simp[Once well_typed_expr_def]` because assumptions were too large; switching to `simp[NoAsms, Once well_typed_expr_def]` progressed past that, but the next plain `simp[]` for the generated IH implication timed out on the large prefix. (`TO_type_system_rewrite-20260601T081233Z_m0995_t001`, `TO_type_system_rewrite-20260601T081233Z_m0998_t001`)
  - Replaced the broad `simp[]` on the generated IH implication with `(impl_tac >- simp[]) >> strip_tac`, then split `args_res` and tried to suspend/placeholder static/nonstatic success leaves. -> The IH implication step succeeded and yielded the desired `INL` branch facts (`state_well_typed args_st`, `env_consistent env cx args_st`, `exprs_runtime_typed env es x`). However, attempts to introduce nested `suspend` labels or branch-local cheats produced downstream HOL source parse errors near later backtick code; after investigation this was not a clean build-coherent checkpoint. The experiment was reverted to the buildable `Expr_Call_ExtCall_result: cheat` placeholder and holbuild succeeds again. (`TO_type_system_rewrite-20260601T081233Z_m1001_t001`, `TO_type_system_rewrite-20260601T081233Z_m1003_t001`, `TO_type_system_rewrite-20260601T081233Z_m1006_t001`, `TO_type_system_rewrite-20260601T081233Z_m1009_t001`, `TO_type_system_rewrite-20260601T081233Z_m1017_t001`, `TO_type_system_rewrite-20260601T081233Z_m1020_t001`)
- `E0037` (progressed, missing_helper, actual effort: 1 sessions, 1 msgs, 14 steps, 17 tools, 6 holbuild, 884,241 tok (879,508 in, 4,733 out, 834,304 cached), 335.5s, $0.785162)
  - Replaced FAIL_TAC/cheat with the planned direct-helper wrapper: strip expression premise, label generated ExtCall driver IH and eval_exprs IH, destruct call typing with `simp[NoAsms, Once well_typed_expr_def]`, then apply `extcall_expr_sound_from_generated_ih`. -> Progressed through helper matching after destructing the call-typing annotation (`v15` became `ret_type`) and discharged the standard state/context/function premises, the reconstructed `well_typed_expr`, the eval_exprs IH, and reached exactly the helper's driver-premise subgoal. (`TO_type_system_rewrite-20260601T081233Z_m1043_t001`, `TO_type_system_rewrite-20260601T081233Z_m1045_t001`, `TO_type_system_rewrite-20260601T081233Z_m1047_t001`)
  - Inserted `FAIL_TAC "driver premise goal"` at the remaining helper premise to inspect whether the generated driver IH can be directly adapted. -> The remaining goal is an unconditional compact driver soundness premise `∀env0 st0 res0 st0'. ... eval_expr cx (THE drv) st0 = ... ⇒ well_typed_expr env0 (THE drv) ⇒ ...`, but the only generated driver IH in context is guarded by the full ExtCall success prefix (eval_exprs, target decoding, calldata, run_ext_call, updates, `returnData=[]`, `IS_SOME drv`) before producing an expression/place conjunction. Those prefix facts are not assumptions of the compact premise, so the planned `MATCH_ACCEPT_TAC`/direct adapter cannot prove it without recovering the generated prefix or changing the helper interface. (`TO_type_system_rewrite-20260601T081233Z_m1047_t001`)
- `E0038` (stuck, risk_mismatch, actual effort: 1 sessions, 1 msgs, 15 steps, 18 tools, 6 holbuild, 959,473 tok (954,055 in, 5,418 out, 834,304 cached), 351.1s, $1.178447)
  - Executed the latest direct-wrapper plan for `Expr_Call_ExtCall_result`: captured generated eval_exprs and driver IHs, destructed call typing with `simp[NoAsms, Once well_typed_expr_def]`, and applied `extcall_expr_sound_from_generated_ih`. -> The helper matched only after destructing the outer call type. Standard premises and eval_exprs IH are straightforward, but proof stops at the helper's driver premise. (`TO_type_system_rewrite-20260601T081233Z_m1043_t001`, `TO_type_system_rewrite-20260601T081233Z_m1045_t001`, `TO_type_system_rewrite-20260601T081233Z_m1047_t001`)
  - Inspected the remaining driver premise with `FAIL_TAC "driver premise goal"`. -> The remaining helper premise is an unconditional compact driver soundness theorem, whereas the only generated driver IH is guarded by the full ExtCall success prefix. There are no prefix assumptions available inside the compact premise, so a direct adapter cannot be written without resurrecting forbidden prefix recovery or changing the boundary helper interface. (`TO_type_system_rewrite-20260601T081233Z_m1047_t001`)

### Ruled Out

- Direct `MATCH_ACCEPT_TAC` of the generated `driver_ih` against the compact helper premise.
- Continuing with broad prefix reconstruction/unfolding, which the task clarification and current plan forbid.

### Evidence refs

- `TO_type_system_rewrite-20260601T081233Z_m1043_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1045_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1047_t001` (use `read_tool_output` for exact output)

## C0.1.1.2.0

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0059`
- blocker: 
- actual effort: 1 sessions, 1 msgs, 3 steps, 5 tools, 1 holbuild, 167,609 tok (166,960 in, 649 out, 150,144 cached), 23.2s, $0.178622

### Attempts / Evidence

- `E0040` (proved, , actual effort: 1 sessions, 4 steps, 3 tools, 1 holbuild, 571,787 tok (569,755 in, 2,032 out, 556,032 cached), 149.4s, $0.407591)
  - Replaced the failed E0039 `extcall_expr_sound_from_generated_prefix_ih` proof body/invalid conjunctive-helper interface with the strategist-prescribed delayed-helper skeleton `extcall_expr_sound_from_generated_prefix_delayed_ih` using a temporary `cheat`; kept `Expr_Call_ExtCall_result` as `cheat`. -> The stale timeout proof text is gone and `vyperTypeStmtSoundnessTheory` builds again, confirming a clean buildable source state for the next delayed-helper proof component. (`TO_type_system_rewrite-20260601T081233Z_m1089_t001`)
- `E0042` (proved, , actual effort: 1 sessions, 1 steps, 104,473 tok (104,245 in, 228 out, 98,688 cached), 8.1s, $0.083969)
  - Preserved E0040 buildable skeleton after E0041 proof attempt; verified `vyperTypeStmtSoundnessTheory` builds with the planned helper/Resume cheats restored. -> Build passed; the cleanup/skeleton component remains complete under the new predicate-based PLAN. (`TO_type_system_rewrite-20260601T081233Z_m1124_t001`)
- `E0045` (proved, , actual effort: 1 sessions, 1 steps, 143,126 tok (142,904 in, 222 out, 139,648 cached), 6.6s, $0.092764)
  - Verified carry-forward buildable skeleton after reverting failed E0044 monolithic helper insertion. -> `vyperTypeStmtSoundnessTheory` is build-clean in the E0043/E0042 source state; no stale failed helper body remains. (`TO_type_system_rewrite-20260601T081233Z_m1209_t001`)
- `E0048` (proved, , actual effort: 1 sessions, 1 steps, 113,939 tok (113,645 in, 294 out, 107,904 cached), 10.0s, $0.091477)
  - Audited current source after E0047 replacement for stale wrapper theorem names and verified the target builds. -> No `extcall_generated_driver_ih_elim_expr_static_success` or nonstatic sibling remains in the source grep output; only pre-existing mutual-proof suspends/cheat mentions unrelated to the abandoned wrapper path were found. `vyperTypeStmtSoundnessTheory` builds cleanly after the failed wrapper insertion was removed. (`TO_type_system_rewrite-20260601T081233Z_m1252_t001`, `TO_type_system_rewrite-20260601T081233Z_m1248_t002`)
- `E0052` (proved, , actual effort: 1 sessions, 2 steps, 1 tools, 1 holbuild, 209,322 tok (208,999 in, 323 out, 204,544 cached), 24.3s, $0.134237)
  - Verified the repaired/reverted skeleton state after E0051 review: source contains the tracked `Expr_Call_ExtCall_result` cheat placeholder and no failed partial proof/probe, and `vyperTypeStmtSoundnessTheory` builds. -> Build passed; carry-forward skeleton cleanup remains valid for the replacement helper plan. (`TO_type_system_rewrite-20260601T081233Z_m1309_t001`, `TO_type_system_rewrite-20260601T081233Z_m1314_t001`)
- `E0059` (proved, , actual effort: 1 sessions, 1 msgs, 3 steps, 5 tools, 1 holbuild, 167,609 tok (166,960 in, 649 out, 150,144 cached), 23.2s, $0.178622)
  - Audited restored ExtCall skeleton state with grep/read and rebuilt target; no proof edits made. -> `vyperTypeStmtSoundnessTheory` builds; source still has `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result]: cheat QED`; grep finds no absent/stale helper `extcall_expr_sound_from_generated_driver_ih` or abandoned static wrapper name. (`TO_type_system_rewrite-20260601T081233Z_m1396_t002`, `TO_type_system_rewrite-20260601T081233Z_m1396_t001`, `TO_type_system_rewrite-20260601T081233Z_m1397_t001`)

### Evidence refs

- `TO_type_system_rewrite-20260601T081233Z_m1396_t002` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1396_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1397_t001` (use `read_tool_output` for exact output)

## C0.1.1.2.1

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0060`
- blocker: 
- actual effort: 1 sessions, 2 steps, 2 tools, 1 holbuild, 138,257 tok (137,857 in, 400 out, 131,328 cached), 16.4s, $0.110309

### Attempts / Evidence

- `E0039` (stuck, risk_mismatch, actual effort: 1 sessions, 2 msgs, 33 steps, 34 tools, 12 holbuild, 3,595,441 tok (3,584,063 in, 11,378 out, 3,481,472 cached), 810.3s, $2.595031)
  - Added `extcall_expr_sound_from_generated_prefix_ih` with a prefix-guarded generated driver-IH premise matching TO_m1047/Resume shape and initially verified the statement with `cheat`. Then copied the old `extcall_expr_sound_from_generated_ih` proof skeleton, replacing the success-continuation call with `extcall_success_continuation_sound_cond_driver_ih`. -> The statement parses/builds with a cheat, but proving it is not a straightforward adaptation: assumption-enabled `simp[Once well_typed_expr_def]` timed out due to the huge prefix-guarded IH context; changing to `simp[NoAsms, Once well_typed_expr_def]` progressed. (`TO_type_system_rewrite-20260601T081233Z_m1060_t001`, `TO_type_system_rewrite-20260601T081233Z_m1062_t001`)
  - Replaced broad `simp[]` for the eval_exprs generated IH with `(impl_tac >- simp[]) >> strip_tac`, then tried to split `args_res` and continue static branch with targeted rewrites instead of broad gvs. -> This progressed past the eval_exprs IH timeout, but further apparently routine copied steps still timed out or failed in the huge prefix-aware context: `gvs[no_type_error_result_def]`, `simp[]` on sum-case, `Cases_on is_static' >> gvs[]`, `drule_all ... >> gvs[]`, and even deriving `vs <> []` with `Cases_on vs >> gvs[exprs_runtime_typed_def]` timed out. The helper proof requires substantial redesign to avoid carrying the giant driver IH assumption through local simplification, so it violates the task's 'entirely straightforward; stop if not' instruction. (`TO_type_system_rewrite-20260601T081233Z_m1066_t001`, `TO_type_system_rewrite-20260601T081233Z_m1069_t001`, `TO_type_system_rewrite-20260601T081233Z_m1071_t001`, `TO_type_system_rewrite-20260601T081233Z_m1073_t001`, `TO_type_system_rewrite-20260601T081233Z_m1075_t001`, `TO_type_system_rewrite-20260601T081233Z_m1077_t001`, `TO_type_system_rewrite-20260601T081233Z_m1079_t001`, `TO_type_system_rewrite-20260601T081233Z_m1081_t001`, `TO_type_system_rewrite-20260601T081233Z_m1083_t001`)
- `E0041` (stuck, risk_mismatch, actual effort: 1 sessions, 1 msgs, 25 steps, 28 tools, 8 holbuild, 2,016,330 tok (2,008,241 in, 8,089 out, 1,925,504 cached), 430.1s, $1.619107)
  - Replace helper `cheat` with delayed-IH proof skeleton copied from prior helper but keep driver IH delayed; first used `simp[NoAsms, Once well_typed_expr_def]` to destruct call typing. -> Unexpected timeout at the first call-typing simplification even with `NoAsms`; top goal remained >4KiB because the delayed driver premise was still in the consequent. This violates the 'straightforward' expectation for the repaired interface. (`TO_type_system_rewrite-20260601T081233Z_m1104_t001`)
  - Avoided simplifier by rewriting the `well_typed_expr` assumption with `rewrite_tac[Once well_typed_expr_def]`, then unfolded the ExtCall evaluator using `rewrite_tac` rather than `simp_tac`; specialized eval_exprs IH with `(impl_tac >- simp[])`. -> This progressed past the first two blockers, but the first routine branch cleanup `Cases_on args_res >> gvs[no_type_error_result_def]` timed out in a >4KiB goal before the delayed driver IH was introduced. (`TO_type_system_rewrite-20260601T081233Z_m1112_t001`, `TO_type_system_rewrite-20260601T081233Z_m1115_t001`)
  - Replaced the broad branch cleanup by manually destructing the `INL vs` case and rewriting the `case INL vs` assumption, then split `is_static`. -> Even `simp[]` on the trivial `case INL` assumption and then `Cases_on is_static >> gvs[]` timed out in the large consequent context. This shows the monolithic delayed helper is still not a straightforward proof boundary; source was restored to the buildable cheat skeleton and verified. (`TO_type_system_rewrite-20260601T081233Z_m1118_t001`, `TO_type_system_rewrite-20260601T081233Z_m1120_t001`, `TO_type_system_rewrite-20260601T081233Z_m1124_t001`)
- `E0043` (proved, , actual effort: 1 sessions, 1 msgs, 22 steps, 21 tools, 8 holbuild, 2,961,389 tok (2,954,128 in, 7,261 out, 2,872,576 cached), 415.7s, $2.061878)
  - Replaced the stale cheated delayed-helper theorem with `extcall_generated_driver_ih_def` and proved `extcall_generated_driver_ih_elim_expr[local]`. The eliminator unfolds the predicate only locally, specializes the packaged prefix theorem, strips the success condition, and returns the expr-only driver IH needed by the continuation lemma. -> `vyperTypeStmtSoundnessTheory` built successfully. The opaque boundary and eliminator are now proved; remaining ExtCall helper/Resume cheats are for downstream components. (`TO_type_system_rewrite-20260601T081233Z_m1153_t001`)
  - Initial eliminator proof used broad `rw[extcall_generated_driver_ih_def]`, then an `impl_tac` before the `returnData=[] /\ IS_SOME drv` conclusion was stripped. -> Both failed: broad `rw` timed out, and the premature `impl_tac` lacked the success-condition assumptions. Repaired by targeted `rewrite_tac[extcall_generated_driver_ih_def]`, labelling the specialized theorem with `mk_asm`, stripping the success condition first, then applying the labelled implication. (`TO_type_system_rewrite-20260601T081233Z_m1137_t001`, `TO_type_system_rewrite-20260601T081233Z_m1139_t001`, `TO_type_system_rewrite-20260601T081233Z_m1147_t001`)
- `E0046` (proved, , actual effort: 1 sessions, 2 steps, 1 tools, 1 holbuild, 135,224 tok (134,965 in, 259 out, 113,408 cached), 13.9s, $0.172259)
  - Carry-forward verification of existing `extcall_generated_driver_ih_def` and proved `extcall_generated_driver_ih_elim_expr` under active component. -> `vyperTypeStmtSoundnessTheory` builds cleanly; no source edits were needed for this carry-forward component. (`TO_type_system_rewrite-20260601T081233Z_m1222_t001`)
- `E0049` (proved, , actual effort: 1 sessions, 1 msgs, 2 steps, 1 tools, 1 holbuild, 246,054 tok (245,822 in, 232 out, 213,760 cached), 24.0s, $0.274150)
  - Carry-forward re-verification of optional `extcall_generated_driver_ih_def` / `extcall_generated_driver_ih_elim_expr` infrastructure after replanning downgraded its role. -> `vyperTypeStmtSoundnessTheory` builds cleanly; no edits were needed and no static/nonstatic wrapper adapters were introduced. (`TO_type_system_rewrite-20260601T081233Z_m1260_t001`)
- `E0053` (proved, , actual effort: 1 sessions, 2 steps, 1 tools, 1 holbuild, 227,680 tok (227,436 in, 244 out, 220,928 cached), 16.4s, $0.150324)
  - Carry-forward verification of existing `extcall_generated_driver_ih_def` and `extcall_generated_driver_ih_elim_expr` infrastructure under the replacement plan. -> `vyperTypeStmtSoundnessTheory` builds cleanly; no edits were needed. The opaque generated-driver predicate/eliminator remain available for the new matching-helper component. (`TO_type_system_rewrite-20260601T081233Z_m1322_t001`)
- `E0060` (proved, , actual effort: 1 sessions, 2 steps, 2 tools, 1 holbuild, 138,257 tok (137,857 in, 400 out, 131,328 cached), 16.4s, $0.110309)
  - Audited retained opaque generated-driver infrastructure by grepping theorem/definition names and rebuilding target; no source edits made. -> `extcall_generated_driver_ih_def` and local `extcall_generated_driver_ih_elim_expr` are present; absent downstream helper `extcall_expr_sound_from_generated_driver_ih` is not present; `vyperTypeStmtSoundnessTheory` builds cleanly. Infrastructure is retained but not treated as sufficient for the blocked ExtCall Resume. (`TO_type_system_rewrite-20260601T081233Z_m1405_t001`, `TO_type_system_rewrite-20260601T081233Z_m1405_t002`)

### Evidence refs

- `TO_type_system_rewrite-20260601T081233Z_m1405_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1405_t002` (use `read_tool_output` for exact output)

## C0.1.1.2.2

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0061`
- blocker: 
- actual effort: 1 sessions, 2 steps, 2 tools, 1 holbuild, 151,030 tok (150,674 in, 356 out, 145,664 cached), 16.9s, $0.108562

### Attempts / Evidence

- `E0044` (stuck, risk_mismatch, actual effort: 1 sessions, 3 msgs, 49 steps, 56 tools, 13 holbuild, 4,810,891 tok (4,795,059 in, 15,832 out, 4,551,680 cached), 632.5s, $3.967695)
  - Inserted `extcall_expr_sound_from_generated_prefix_driver_pred` by copying the old direct ExtCall helper and replacing the unconditional driver premise with `extcall_generated_driver_ih`; used `extcall_success_continuation_sound_cond_driver_ih` at success tails. -> The prefix proof progressed to the static run-success tail, but applying the continuation lemma exposed an existential/conditional driver premise whose exact generated-prefix state witnesses did not line up straightforwardly. (`TO_type_system_rewrite-20260601T081233Z_m1164_t001`, `TO_type_system_rewrite-20260601T081233Z_m1167_t001`)
  - Tried to discharge the conditional driver premise by deriving the exact implication with `extcall_generated_driver_ih_elim_expr`, first via `irule`, then `MATCH_MP_TAC`, with explicit prefix witnesses for static and nonstatic success branches. -> The eliminator did not match the weakened/partially simplified conditional goal directly; `MATCH_MP_TAC` produced a large existential over all prefix states, and explicit witnesses ran into non-straightforward state-type/monad-state constraints. This contradicts the Risk 2 expectation that the helper would be a straightforward template copy. (`TO_type_system_rewrite-20260601T081233Z_m1173_t001`, `TO_type_system_rewrite-20260601T081233Z_m1179_t001`, `TO_type_system_rewrite-20260601T081233Z_m1182_t001`, `TO_type_system_rewrite-20260601T081233Z_m1198_t001`, `TO_type_system_rewrite-20260601T081233Z_m1206_t001`)
  - Removed the failed helper insertion and rebuilt `vyperTypeStmtSoundnessTheory`. -> Source is restored to the previous build-clean E0043 state; the component proof itself remains unproved. (`TO_type_system_rewrite-20260601T081233Z_m1209_t001`)
- `E0050` (proved, , actual effort: 1 sessions, 2 steps, 1 tools, 1 holbuild, 261,313 tok (261,042 in, 271 out, 255,744 cached), 28.2s, $0.162492)
  - Audited `vyperTypeStmtSoundnessScript.sml` for abandoned wrapper-adapter theorem names (`extcall_generated_driver_ih_elim_expr_static_success`, nonstatic sibling, predicate-based helper, delayed helper) and rebuilt target. -> No stale wrapper/helper names were present; `vyperTypeStmtSoundnessTheory` builds cleanly. No source edits were needed. (`TO_type_system_rewrite-20260601T081233Z_m1267_t001`, `TO_type_system_rewrite-20260601T081233Z_m1268_t001`)
- `E0054` (proved, , actual effort: 1 sessions, 2 steps, 2 tools, 1 holbuild, 242,600 tok (242,219 in, 381 out, 237,824 cached), 18.4s, $0.152317)
  - Audited `vyperTypeStmtSoundnessScript.sml` for abandoned wrapper-adapter theorem/helper names and rebuilt the target. -> No stale wrapper/helper names were present; `vyperTypeStmtSoundnessTheory` builds cleanly. The abandoned wrapper-adapter path remains deleted under the replacement plan. (`TO_type_system_rewrite-20260601T081233Z_m1330_t001`, `TO_type_system_rewrite-20260601T081233Z_m1330_t002`)
- `E0061` (proved, , actual effort: 1 sessions, 2 steps, 2 tools, 1 holbuild, 151,030 tok (150,674 in, 356 out, 145,664 cached), 16.9s, $0.108562)
  - Audited deletion of abandoned wrapper-adapter/helper path by grepping stale theorem/helper names and rebuilding target; no source edits made. -> No obsolete wrapper-adapter/helper names are present in `semantics/prop/*.sml`; `vyperTypeStmtSoundnessTheory` builds cleanly. The deleted wrapper-adapter path remains absent under the stop-state plan. (`TO_type_system_rewrite-20260601T081233Z_m1412_t001`, `TO_type_system_rewrite-20260601T081233Z_m1412_t002`)

### Evidence refs

- `TO_type_system_rewrite-20260601T081233Z_m1412_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1412_t002` (use `read_tool_output` for exact output)

## C0.1.1.2.2.1

### Current Status

- result: `stuck`
- diagnosis: `risk_mismatch` The component was intended to be the sole place where static witness reconstruction is allowed, but the required reconstruction is still brittle enough to be a proof-interface/decomposition issue.
- latest episode: `E0047`
- blocker: The static branch-local wrapper is not a straightforward low-risk proof as planned: using the broad eliminator still requires a long generated-prefix witness list, while direct `irule` does not match the conclusion. Under the task instruction and proof-hygiene checkpoint, this should be redesigned rather than tuned.
- actual effort: 1 sessions, 2 msgs, 20 steps, 22 tools, 7 holbuild, 1,825,761 tok (1,818,251 in, 7,510 out, 1,731,072 cached), 360.4s, $1.526731
- next: Call plan_oracle review for C0.1.1.2.2.1 and request a more robust static wrapper interface/proof strategy that avoids long generated-prefix witness plumbing.

### Attempts / Evidence

- `E0047` (stuck, risk_mismatch, actual effort: 1 sessions, 2 msgs, 20 steps, 22 tools, 7 holbuild, 1,825,761 tok (1,818,251 in, 7,510 out, 1,731,072 cached), 360.4s, $1.526731)
  - Inserted the planned static branch-local theorem statement with `cheat` to validate parsing/type shape. -> The statement built with a cheat, confirming the planned API is syntactically/type valid in the current file. (`TO_type_system_rewrite-20260601T081233Z_m1234_t001`)
  - Tried to prove the static wrapper by directly specializing `extcall_generated_driver_ih_elim_expr` with concrete static monad witnesses and targeted simplification of `check`/`lift_option`/state accessor/update definitions. -> The proof turned into a brittle long `qspecl_then` witness list; parsing/specialization repeatedly failed, and a direct `irule extcall_generated_driver_ih_elim_expr` did not match the branch-local conclusion. This violates the task's 'straightforward; stop if not' constraint and the proof-hygiene warning against long generated-prefix plumbing, even inside this component. (`TO_type_system_rewrite-20260601T081233Z_m1236_t001`, `TO_type_system_rewrite-20260601T081233Z_m1238_t001`, `TO_type_system_rewrite-20260601T081233Z_m1246_t001`)
  - Removed the failed static theorem insertion and rebuilt the target. -> Source restored to the prior build-clean state; `vyperTypeStmtSoundnessTheory` builds from cache. (`TO_type_system_rewrite-20260601T081233Z_m1248_t001`, `TO_type_system_rewrite-20260601T081233Z_m1248_t002`)

### Ruled Out

- Direct `irule extcall_generated_driver_ih_elim_expr` on the static branch-local conclusion.
- Long `qspecl_then`/generated-prefix witness list over all broad eliminator variables in the static wrapper.

### Evidence refs

- `TO_type_system_rewrite-20260601T081233Z_m1234_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1236_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1238_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1246_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1248_t002` (use `read_tool_output` for exact output)

## C0.1.1.2.3

### Current Status

- result: `stuck`
- diagnosis: `risk_mismatch` Risk estimate/decomposition mismatch: the maintainer-approved linear proof may still be viable, but the current component lacks a precise Resume-entry tactic shape that preserves the conjunctive postcondition while reaching the concrete monadic success branch. The next plan should specify the exact initial goal manipulation (e.g. avoid premature `strip_tac` that splits the postcondition, or factor a small helper matching the current Resume goal) without broad simplification or generated-prefix adapters.
- latest episode: `E0051`
- blocker: The active low-risk component is not straightforward as planned. The Resume goal shape exposes two leading generated IH assumptions and then an already-split expression-result conjunct; naive `strip_tac` loses the whole postcondition, while direct unfolding/linearization immediately causes timeout/huge-goal symptoms. A helper application also does not match without changing the goal setup, and continuing would be proof-architecture redesign rather than tactical execution.
- actual effort: 1 sessions, 2 msgs, 25 steps, 27 tools, 6 holbuild, 2,007,636 tok (1,996,779 in, 10,857 out, 1,901,952 cached), 380.9s, $1.750821
- next: Call plan_oracle(mode="review") for C0.1.1.2.3 with this risk-mismatch evidence; request a precise replacement/augmentation for the Resume-entry proof shape or permission to factor a small matching helper if the component should remain low risk.

### Attempts / Evidence

- `E0051` (stuck, risk_mismatch, actual effort: 1 sessions, 2 msgs, 25 steps, 27 tools, 6 holbuild, 2,007,636 tok (1,996,779 in, 10,857 out, 1,901,952 cached), 380.9s, $1.750821)
  - Replaced temporary ExtCall Resume probe with a direct linear proof adapted from existing `extcall_expr_sound_from_generated_ih`, initially splitting the place conjunct and then unfolding `well_typed_expr`/`evaluate_def` locally. -> The place-conjunct split was structurally wrong for the current Resume goal: after `rpt gen_tac >> strip_tac`, the remaining goal was already the expression-result postcondition, not a conjunction. `qpat_x_assum` for `type_place_expr` failed. (`TO_type_system_rewrite-20260601T081233Z_m1290_t001`)
  - Removed the place split and tried to unfold `well_typed_expr` and apply the expression-argument IH before linear evaluator case splitting. -> `simp[Once well_typed_expr_def]` and then even the IH-antecedent `simp[]` timed out/left a huge goal. This reproduced the forbidden broad-prefix simplification smell rather than a straightforward linear branch proof. (`TO_type_system_rewrite-20260601T081233Z_m1292_t001`, `TO_type_system_rewrite-20260601T081233Z_m1294_t001`, `TO_type_system_rewrite-20260601T081233Z_m1298_t001`)
  - Stepped back and tried a small wrapper application of existing `extcall_expr_sound_from_generated_ih` by labelling the generated driver IH and args IH, avoiding generated witness lists. -> This also did not match the current goal shape: after `strip_tac`, the goal had already split to a single conjunct (`state_well_typed st'`), so `MATCH_MP_TAC` could not match the helper conclusion. A preceding `disch_tac` was invalid because the goal was not an implication. Source was restored to HEAD (`cheat`) rather than leaving a broken partial proof. (`TO_type_system_rewrite-20260601T081233Z_m1302_t001`, `TO_type_system_rewrite-20260601T081233Z_m1304_t001`, `TO_type_system_rewrite-20260601T081233Z_m1308_t001`, `TO_type_system_rewrite-20260601T081233Z_m1309_t001`)

### Ruled Out

- Starting with `reverse conj_tac`/place branch split in this Resume goal; no such top-level conjunction is present after the generated IH assumptions.
- Unfolding `well_typed_expr`/IH antecedents with broad `simp[]` at the top; it times out and produces a huge whole-prefix goal.
- Applying `extcall_expr_sound_from_generated_ih` after `strip_tac`; the goal has already been reduced to a single conjunct and no longer matches the helper conclusion.

### Evidence refs

- `TO_type_system_rewrite-20260601T081233Z_m1290_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1292_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1294_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1298_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1302_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1304_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1308_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1309_t001` (use `read_tool_output` for exact output)

## C0.1.1.2.3.1

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0062`
- blocker: 
- actual effort: 1 sessions, 2 steps, 3 tools, 1 holbuild, 166,963 tok (166,295 in, 668 out, 160,000 cached), 22.0s, $0.131515

### Attempts / Evidence

- `E0055` (stuck, risk_mismatch, actual effort: 1 sessions, 1 msgs, 18 steps, 18 tools, 5 holbuild, 2,549,954 tok (2,542,298 in, 7,656 out, 2,489,600 cached), 338.4s, $1.737970)
  - Added the planned local theorem `extcall_expr_sound_from_generated_driver_ih` with the strategist-specified interface and first verified the statement with a temporary `cheat`. -> The statement parsed and the target built, so the interface is well-typed as a theorem statement. (`TO_type_system_rewrite-20260601T081233Z_m1338_t001`, `TO_type_system_rewrite-20260601T081233Z_m1339_t001`)
  - Replaced the cheat with a proof adapted from `extcall_expr_sound_from_generated_ih`, changing the success tail to `extcall_success_continuation_sound_cond_driver_ih`. -> The copied prefix and error-branch structure progressed to the concrete static success branch. Initial premise ordering for `extcall_success_continuation_sound_cond_driver_ih` was wrong but was repaired by inspecting the goal. (`TO_type_system_rewrite-20260601T081233Z_m1340_t001`, `TO_type_system_rewrite-20260601T081233Z_m1341_t001`, `TO_type_system_rewrite-20260601T081233Z_m1342_t001`, `TO_type_system_rewrite-20260601T081233Z_m1347_t001`)
  - Tried to discharge the static success-branch conditional driver premise using `extcall_generated_driver_ih_elim_expr` after the concrete prefix facts were in context. -> The proof immediately devolved into a long `qspecl_then` list over generated prefix witnesses and failed to parse/match. This is precisely the brittle generated-prefix witness plumbing the plan and maintainer clarification forbid; the component is not a straightforward Risk 2 helper proof. Source was restored to HEAD, removing the failed helper insertion. (`TO_type_system_rewrite-20260601T081233Z_m1348_t001`, `TO_type_system_rewrite-20260601T081233Z_m1350_t001`, `TO_type_system_rewrite-20260601T081233Z_m1351_t001`, `TO_type_system_rewrite-20260601T081233Z_m1352_t001`, `TO_type_system_rewrite-20260601T081233Z_m1353_t001`, `TO_type_system_rewrite-20260601T081233Z_m1353_t002`)
- `E0057` (proved, , actual effort: 1 sessions, 2 steps, 2 tools, 1 holbuild, 185,092 tok (184,499 in, 593 out, 178,432 cached), 20.3s, $0.137341)
  - Executed the replacement stop/report component after accepted E0056: left `Expr_Call_ExtCall_result` as the original `cheat`, made no source proof edits, and verified the target builds in the restored state. -> The stop/report action is complete for this subtree. `vyperTypeStmtSoundnessTheory` builds with the original cheat; the blocker is now recorded in PLAN/DOSSIER/STATE/LEARNINGS under `semantics/prop`. No files outside `semantics/prop` were edited. (`TO_type_system_rewrite-20260601T081233Z_m1376_t001`, `TO_type_system_rewrite-20260601T081233Z_m1378_t001`, `TO_type_system_rewrite-20260601T081233Z_m1378_t002`)
- `E0062` (proved, , actual effort: 1 sessions, 2 steps, 3 tools, 1 holbuild, 166,963 tok (166,295 in, 668 out, 160,000 cached), 22.0s, $0.131515)
  - Re-audited accepted stop/report state without proof edits: grep for ExtCall Resume and invalidated helper/probe names, rebuild target, inspect status. -> `Expr_Call_ExtCall_result` Resume remains present; no `extcall_expr_sound_from_generated_driver_ih` or abandoned prefix-driver helper is present. `vyperTypeStmtSoundnessTheory` builds cleanly. Git status has only the known unrelated untracked tmp/legacy files. The `FAIL_TAC` grep matches are in other pre-existing semantics/prop scripts, not the ExtCall Resume proof state audited by this component. (`TO_type_system_rewrite-20260601T081233Z_m1420_t002`, `TO_type_system_rewrite-20260601T081233Z_m1420_t003`, `TO_type_system_rewrite-20260601T081233Z_m1420_t001`)

### Evidence refs

- `TO_type_system_rewrite-20260601T081233Z_m1420_t002` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1420_t003` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1420_t001` (use `read_tool_output` for exact output)

## C0.1.1.2.3.1.1

### Current Status

- result: `stuck`
- diagnosis: `risk_mismatch` This confirms E0055 was not just a bad helper proof; the existing eliminator's interface does not support the desired live matching in a standalone probe.
- latest episode: `E0056`
- blocker: The planned Risk 1 live-matching probe is false as stated: neither `drule_all extcall_generated_driver_ih_elim_expr` nor direct `irule` can consume the existing eliminator from the live theorem-premise assumptions without explicit generated-prefix instantiation. The plan explicitly says to stop and report a proof-interface problem rather than patching with manual witnesses.
- actual effort: 1 sessions, 1 msgs, 11 steps, 12 tools, 4 holbuild, 837,200 tok (834,286 in, 2,914 out, 787,072 cached), 203.3s, $0.717026
- next: Call plan_oracle(mode='review') for C0.1.1.2.3.1.1. Request either a genuinely matchable boundary/probe or an explicit stop decision under the task's straightforward-proof instruction.

### Attempts / Evidence

- `E0056` (stuck, risk_mismatch, actual effort: 1 sessions, 1 msgs, 11 steps, 12 tools, 4 holbuild, 837,200 tok (834,286 in, 2,914 out, 787,072 cached), 203.3s, $0.717026)
  - Added `extcall_generated_driver_ih_elim_expr_drule_probe` with the same assumptions/conclusion as `extcall_generated_driver_ih_elim_expr` and proof `rpt gen_tac >> strip_tac >> drule_all extcall_generated_driver_ih_elim_expr >> simp[]`. -> The probe failed exactly at `drule_all extcall_generated_driver_ih_elim_expr`; HOL could not prove/store the theorem from the live assumptions. This falsifies the planned Risk 1 interface probe. (`TO_type_system_rewrite-20260601T081233Z_m1366_t001`)
  - Tried the only nearby non-witness live-matching variant, `irule extcall_generated_driver_ih_elim_expr >> simp[]`, without explicit generated-prefix witnesses. -> This also failed immediately with `No match` at `MATCH_MP_TAC`; no manual `qspecl_then` witness list was attempted, per plan. The probe/interface is not mechanically consumable by live matching as planned. (`TO_type_system_rewrite-20260601T081233Z_m1368_t001`)
  - Removed the failed probe insertion and rebuilt the target. -> Source was restored to no diff for `vyperTypeStmtSoundnessScript.sml`; target builds again with the original `Expr_Call_ExtCall_result` cheat. Only harness memory files are modified by plan/episode updates. (`TO_type_system_rewrite-20260601T081233Z_m1370_t002`, `TO_type_system_rewrite-20260601T081233Z_m1372_t001`, `TO_type_system_rewrite-20260601T081233Z_m1372_t002`)

### Ruled Out

- Manual `qspecl_then`/generated-prefix witness instantiation was not retried and remains forbidden.
- A stronger adapter reconstructing generated prefix witnesses was not attempted.
- Broad simplification over evaluator prefix was not used.

### Evidence refs

- `TO_type_system_rewrite-20260601T081233Z_m1366_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1368_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1370_t002` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1372_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1372_t002` (use `read_tool_output` for exact output)

## C0.1.1.2.3.2

### Current Status

- result: `stuck`
- diagnosis: `plan_incomplete` This is a PLAN consistency issue after accepting E0057: the old sibling proof component remained scheduled even though its prerequisite helper strategy was superseded/invalidated.
- latest episode: `E0058`
- blocker: C0.1.1.2.3.2 is scheduled but its approach depends on `extcall_expr_sound_from_generated_driver_ih`, a helper that is absent because the replacement stop/report component C0.1.1.2.3.1 explicitly invalidated the prior helper/proof frontier and left the original cheat. The plan is internally inconsistent; proof work would violate the stop-report decision and not-to-try guidance.
- actual effort: 1 sessions, 2 steps, 3 tools, 195,980 tok (194,923 in, 1,057 out, 190,208 cached), 23.8s, $0.150389
- next: Call plan_oracle(mode='review') for this stuck episode and request removal/replacement of the stale scheduled C0.1.1.2.3.2 frontier or an explicit operator-facing stop state.

### Attempts / Evidence

- `E0058` (stuck, plan_incomplete, actual effort: 1 sessions, 2 steps, 3 tools, 195,980 tok (194,923 in, 1,057 out, 190,208 cached), 23.8s, $0.150389)
  - Checked the scheduled C0.1.1.2.3.2 precondition before editing: the component says to apply local helper `extcall_expr_sound_from_generated_driver_ih`. -> The helper is not present in `semantics/prop/vyperTypeStmtSoundnessScript.sml`; grep finds only the `Expr_Call_ExtCall_result` Resume. This is inconsistent with the just-accepted stop/report replacement for C0.1.1.2.3.1, which intentionally left the source with the original cheat and did not add the helper. Proceeding would require resurrecting the forbidden failed helper strategy or redesigning the plan, so no source proof edits were made. (`TO_type_system_rewrite-20260601T081233Z_m1382_t002`)
  - Inspected repository diff/status after the stop/report checkpoint and before proof edits. -> Only task-owned memory/progress files under `semantics/prop` are modified; `vyperTypeStmtSoundnessScript.sml` has no tracked diff. Untracked tmp/legacy files remain unstaged. (`TO_type_system_rewrite-20260601T081233Z_m1382_t001`, `TO_type_system_rewrite-20260601T081233Z_m1382_t003`)

### Ruled Out

- No attempt was made to resurrect the failed `extcall_expr_sound_from_generated_driver_ih` helper.
- No proof edit was made to the Resume body.
- No generated-prefix witness plumbing was attempted.

### Evidence refs

- `TO_type_system_rewrite-20260601T081233Z_m1382_t002` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1382_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1382_t003` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1380_t001` (use `read_tool_output` for exact output)

## C0.1.1.2.4

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0063`
- blocker: 
- actual effort: 1 sessions, 2 steps, 4 tools, 1 holbuild, 179,599 tok (178,913 in, 686 out, 174,848 cached), 27.2s, $0.128329

### Attempts / Evidence

- `E0063` (proved, , actual effort: 1 sessions, 2 steps, 4 tools, 1 holbuild, 179,599 tok (178,913 in, 686 out, 174,848 cached), 27.2s, $0.128329)
  - Performed final stop-state audit: git status/diff, grep ExtCall Resume/helper state, and rebuild target. -> Working tree has no tracked diff under `semantics/prop`; only known untracked `LEARNINGS_type_system_rewrite.legacy.md` and `tmp_helper.txt` remain unstaged. `vyperTypeStmtSoundnessScript.sml` still contains `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result]:` and grep finds no `extcall_expr_sound_from_generated_driver_ih`. `vyperTypeStmtSoundnessTheory` builds cleanly. This confirms the final stop-state: ExtCall result remains a deliberate cheat/blocker report, not a completed proof. (`TO_type_system_rewrite-20260601T081233Z_m1427_t001`, `TO_type_system_rewrite-20260601T081233Z_m1427_t003`, `TO_type_system_rewrite-20260601T081233Z_m1427_t002`, `TO_type_system_rewrite-20260601T081233Z_m1427_t004`)

### Evidence refs

- `TO_type_system_rewrite-20260601T081233Z_m1427_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1427_t003` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1427_t002` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1427_t004` (use `read_tool_output` for exact output)

## C0.1.1.2.5

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0064`
- blocker: 
- actual effort: 1 sessions, 3 steps, 3 tools, 185,832 tok (184,792 in, 1,040 out, 175,744 cached), 25.8s, $0.164312
- next: Review/handle generated PLAN diff, then report blocked/operator handoff rather than proof completion; do not reopen ExtCall proof.

### Attempts / Evidence

- `E0064` (proved, , actual effort: 1 sessions, 3 steps, 3 tools, 185,832 tok (184,792 in, 1,040 out, 175,744 cached), 25.8s, $0.164312)
  - Accepted C0.1.1.2 redesign/terminal handoff leaf, began C0.1.1.2.5, inspected tracked/untracked status, committed only tracked task-owned progress files with git commit --no-gpg-sign. -> Mechanical terminal handoff bookkeeping completed for the post-E0063 stop-state. Commit 2bc0e0ced recorded DOSSIER/LEARNINGS/STATE updates; untracked tmp/legacy files remained unstaged. No proof edits or ExtCall proof tactics were attempted. (`TO_type_system_rewrite-20260601T081233Z_m1441_t001`, `TO_type_system_rewrite-20260601T081233Z_m1442_t001`, `TO_type_system_rewrite-20260601T081233Z_m1440_t001`, `TO_type_system_rewrite-20260601T081233Z_m1440_t002`, `TO_type_system_rewrite-20260601T081233Z_m1443_t001`, `TO_type_system_rewrite-20260601T081233Z_m1444_t001`)

### Evidence refs

- `TO_type_system_rewrite-20260601T081233Z_m1441_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1442_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1440_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1440_t002` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1443_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1444_t001` (use `read_tool_output` for exact output)

## C0.1.2

### Current Status

- result: `stuck`
- diagnosis: `risk_mismatch` The PLAN/source interface is mismatched: no focused static placeholder exists to discharge, and the visible goal shape is the forbidden generated-prefix shape.
- latest episode: `E0065`
- blocker: C0.1.2 assumes C0.1.1 produced a focused static success placeholder with local success assumptions, but the source still exposes only the whole `Expr_Call_ExtCall_result` Resume with the generated-prefix driver premise. Continuing would violate the maintainer clarification and PLAN not-to-try guidance.
- actual effort: 1 sessions, 8 steps, 11 tools, 3 holbuild, 502,369 tok (499,778 in, 2,591 out, 469,504 cached), 92.2s, $0.463852
- next: Ask the strategist to repair/reconcile the PLAN with source reality, or accept the operator-facing blocked stop-state rather than continuing C0.1.2.

### Attempts / Evidence

- `E0065` (stuck, risk_mismatch, actual effort: 1 sessions, 8 steps, 11 tools, 3 holbuild, 502,369 tok (499,778 in, 2,591 out, 469,504 cached), 92.2s, $0.463852)
  - Began C0.1.2 and inserted a temporary FAIL_TAC probe at `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result]` after `rpt gen_tac >> strip_tac`, then restored the original `cheat`. -> The live goal is not a focused static success placeholder. It is the whole ExtCall result proof with a large generated-prefix implication as assumption 0, plus args IH and top-level eval/well-typed assumptions. Proving it would require exactly the generated-prefix recovery / whole ExtCall branch reconstruction that the task/PLAN says not to do. Source was restored and build returned to the prior cheat-clean state. (`TO_type_system_rewrite-20260601T081233Z_m1459_t001`, `TO_type_system_rewrite-20260601T081233Z_m1460_t001`, `TO_type_system_rewrite-20260601T081233Z_m1462_t001`, `TO_type_system_rewrite-20260601T081233Z_m1463_t001`)

### Ruled Out

- Starting a careful static-branch proof inside C0.1.2 as planned, because the source has no separate static placeholder; the next visible obligation is the entire ExtCall Resume goal.
- Broad unfolding or generated-prefix reconstruction from assumption 0, because it is explicitly forbidden by the maintainer clarification and prior do-not-retry entries.

### Evidence refs

- `TO_type_system_rewrite-20260601T081233Z_m1456_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1460_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1463_t001` (use `read_tool_output` for exact output)

## C0.2

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0074`
- blocker: 
- actual effort: 1 sessions, 2 steps, 3 tools, 1 holbuild, 272,504 tok (272,022 in, 482 out, 267,008 cached), 19.0s, $0.173034
- next: Call plan_oracle(mode='review') for C0.2, then proceed to the unsigned commit/report component C0.3 if accepted.

### Attempts / Evidence

- `E0027` (proved, , actual effort: 1 sessions, 6 steps, 6 tools, 491,852 tok (489,897 in, 1,955 out, 476,416 cached), 52.8s, $0.364263)
  - Updated TYPE_SYSTEM_REWRITE_PLAN.md current-status section with a 2026-06-01 blocked status, C1.2 evidence summary, redesign requirement, and do-not-retry list; replaced stale next-phase priority order with a stop gate pending ExtCall proof-interface redesign. -> Plan markdown now explicitly marks ExtCall as blocked, keeps remaining cheat inventory as context, and supersedes downstream RawCallTarget/builtin/final-validation work until redesign. Grep/diff confirm stale direct-priority wording was removed and generated-prefix warnings are recorded. (`TO_type_system_rewrite-20260531T201607Z_m0549_t001`, `TO_type_system_rewrite-20260531T201607Z_m0551_t001`, `TO_type_system_rewrite-20260531T201607Z_m0552_t001`, `TO_type_system_rewrite-20260531T201607Z_m0552_t002`)
- `E0067` (stuck, risk_mismatch, actual effort: 1 sessions, 3 msgs, 32 steps, 31 tools, 12 holbuild, 3,137,017 tok (3,129,240 in, 7,777 out, 3,021,312 cached), 416.3s, $2.283606)
  - Tried the authorized linear proof prefix inside `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall_result]`: unfold the top-level typing with `rewrite_tac[Once well_typed_expr_def]`, unfold the evaluator once, split `eval_exprs`, and apply the generated expression-list IH via `impl_tac` instead of broad `simp[]`. -> This got past the initial typing/eval unfold after replacing timeout-prone `simp[Once well_typed_expr_def]` with `rewrite_tac`, and it obtained the args IH facts. However the goal remained a >4KiB generated prefix, and even routine simplification after `Cases_on args_res` timed out. (`TO_type_system_rewrite-20260601T081233Z_m1502_t001`, `TO_type_system_rewrite-20260601T081233Z_m1503_t001`, `TO_type_system_rewrite-20260601T081233Z_m1506_t001`, `TO_type_system_rewrite-20260601T081233Z_m1508_t001`)
  - Probed after `Cases_on args_res`, then focused the `INL` args branch by extracting `exprs_runtime_typed` from the case assumption and splitting `is_static'` without whole-prefix `gvs`. -> The focused branch still exposed the entire generated ExtCall prefix in the goal. Small `rewrite_tac[]`/`simp_tac(srw_ss())[]` steps could expose `exprs_runtime_typed env es x`, but the prefix remained large and subsequent local work accumulated multiple subgoals or timeouts. (`TO_type_system_rewrite-20260601T081233Z_m1509_t001`, `TO_type_system_rewrite-20260601T081233Z_m1510_t001`, `TO_type_system_rewrite-20260601T081233Z_m1514_t001`, `TO_type_system_rewrite-20260601T081233Z_m1516_t001`, `TO_type_system_rewrite-20260601T081233Z_m1518_t001`, `TO_type_system_rewrite-20260601T081233Z_m1520_t001`)
  - In the static branch, tried to use `extcall_static_args_runtime_typed_dest`, first adding targeted cleanup of the static typing assumption (`if T then ... else ...`) and attempting to close the impossible empty-args branch locally. -> `drule_all` initially failed until the static typing assumption was normalized; after that, the empty-args branch and ordinary local simplification still timed out under the huge generated-prefix context. This is now repeating the same broad-prefix problem despite branch-by-branch tactics, violating the task's 'straightforward' and plan's >4KiB/stop conditions. Source was restored to the prior `cheat` baseline and holbuild succeeds with the existing cheat. (`TO_type_system_rewrite-20260601T081233Z_m1521_t001`, `TO_type_system_rewrite-20260601T081233Z_m1522_t001`, `TO_type_system_rewrite-20260601T081233Z_m1525_t001`, `TO_type_system_rewrite-20260601T081233Z_m1526_t001`, `TO_type_system_rewrite-20260601T081233Z_m1527_t001`, `TO_type_system_rewrite-20260601T081233Z_m1528_t001`, `TO_type_system_rewrite-20260601T081233Z_m1529_t001`, `TO_type_system_rewrite-20260601T081233Z_m1530_t001`)
- `E0074` (proved, , actual effort: 1 sessions, 2 steps, 3 tools, 1 holbuild, 272,504 tok (272,022 in, 482 out, 267,008 cached), 19.0s, $0.173034)
  - Audited the ExtCall result Resume source around the target label. -> The proof body is restored to the intentional `cheat QED` baseline; no failed sanitized-boundary proof text remains in `vyperTypeStmtSoundnessScript.sml`. (`TO_type_system_rewrite-20260601T081233Z_m1671_t001`, `TO_type_system_rewrite-20260601T081233Z_m1671_t002`)
  - Built `vyperTypeStmtSoundnessTheory` after the report update and source audit. -> The target builds successfully on the honest stopped/cheated baseline. This is not proof completion; it validates that the stopped state has no broken proof edits. (`TO_type_system_rewrite-20260601T081233Z_m1671_t003`)

### Evidence refs

- `TO_type_system_rewrite-20260601T081233Z_m1671_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1671_t002` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1671_t003` (use `read_tool_output` for exact output)

## C0.2.1

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0069`
- blocker: 
- actual effort: 1 sessions, 2 steps, 2 tools, 1 holbuild, 256,051 tok (255,633 in, 418 out, 251,648 cached), 17.9s, $0.158289
- next: Call plan_oracle(mode='review') and then proceed to the focused Resume proof shell component if accepted.

### Attempts / Evidence

- `E0068` (stuck, risk_mismatch, actual effort: 1 sessions, 3 msgs, 39 steps, 39 tools, 15 holbuild, 3,819,092 tok (3,805,764 in, 13,328 out, 3,644,544 cached), 713.1s, $3.028212)
  - Moved `extcall_static_args_runtime_typed_dest`/`extcall_nonstatic_args_runtime_typed_dest` before `eval_all_type_sound_mutual` and replaced the early ExtCall `suspend` with an inline prefix split that unfolds one layer of typing/evaluation, applies the eval_exprs IH, splits args/static/nonstatic branches, and suspends only at run_ext_call success leaves. -> The helper movement fixed the initial static name errors, but the inline proof under a broad `TRY(rename1 ...)` repeatedly either left the full generated optional-driver prefix as an unproved >4KiB goal at QED or timed out while being attempted on neighboring Send goals. Attempts to make the recognizer more specific (`qmatch_goalsub`, `qpat_assum`, `rename1` variants) did not produce a stable low-risk boundary; the source was restored to HEAD and holbuild succeeds on the existing cheat baseline. (`TO_type_system_rewrite-20260601T081233Z_m1547_t001`, `TO_type_system_rewrite-20260601T081233Z_m1550_t001`, `TO_type_system_rewrite-20260601T081233Z_m1560_t001`, `TO_type_system_rewrite-20260601T081233Z_m1576_t001`, `TO_type_system_rewrite-20260601T081233Z_m1582_t001`)
  - Probed minimal inner suspension recognition by replacing the ExtCall branch with a simple `suspend "Expr_Call_ExtCall_probe"` under several matchers. -> A quick matcher could be made to create a missing-resume label, confirming matcher reachability, but using it with the planned inline prefix proof still caused timeout/non-ExtCall interaction and did not eliminate the full generated-prefix goal. This suggests the planned C0.2.1 refactor is not straightforward at this TRY-based mutual proof skeleton. (`TO_type_system_rewrite-20260601T081233Z_m1564_t001`, `TO_type_system_rewrite-20260601T081233Z_m1572_t001`)
- `E0069` (proved, , actual effort: 1 sessions, 2 steps, 2 tools, 1 holbuild, 256,051 tok (255,633 in, 418 out, 251,648 cached), 17.9s, $0.158289)
  - Audited restored ExtCall branch around lines 5612-5618 and rebuilt `vyperTypeStmtSoundnessTheory`. -> The mutual proof skeleton is back in the safe HEAD shape: the ExtCall case proves only the place-expression conjunct via `type_place_expr_Call_ExtCall_NONE` and suspends `Expr_Call_ExtCall_result`; the target builds successfully with the existing ExtCall result cheat baseline. (`TO_type_system_rewrite-20260601T081233Z_m1586_t001`, `TO_type_system_rewrite-20260601T081233Z_m1586_t002`)

### Evidence refs

- `TO_type_system_rewrite-20260601T081233Z_m1586_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1586_t002` (use `read_tool_output` for exact output)

## C0.2.2

### Current Status

- result: `stuck`
- diagnosis: `risk_mismatch` This is not a routine tactic failure: both the earlier boundary-moving attempt and the focused Resume expose the same generated-prefix proof-interface problem, contrary to the current C0.2.2 decomposition and the task instruction to stop on non-straightforward design issues.
- latest episode: `E0070`
- blocker: C0.2.2 was rated Risk 2 because the focused Resume was expected to make prefix error cases mechanical, but the same >4KiB generated optional-driver prefix persists after the eval_exprs split and causes simplifier timeouts before concrete success cases are reached.
- actual effort: 1 sessions, 2 msgs, 15 steps, 17 tools, 3 holbuild, 2,018,351 tok (2,011,883 in, 6,468 out, 1,969,280 cached), 392.1s, $1.391695
- next: Call plan_oracle(mode='review', component_id='C0.2.2') with this evidence and ask for a redesigned/de-risked boundary rather than more local simplifier variants.

### Attempts / Evidence

- `E0070` (stuck, risk_mismatch, actual effort: 1 sessions, 2 msgs, 15 steps, 17 tools, 3 holbuild, 2,018,351 tok (2,011,883 in, 6,468 out, 1,969,280 cached), 392.1s, $1.391695)
  - Focused Resume shell: unfold ExtCall branch, split `eval_exprs cx es st`, then apply eval_exprs IH with `simp[]` to discharge the antecedent. -> The IH application timed out; holbuild showed the same large generated optional-driver prefix still present, so even the intended local eval_exprs step is polluted by the prefix context. (`TO_type_system_rewrite-20260601T081233Z_m1595_t001`)
  - Replace direct `simp[]` with `impl_tac >- simp[]`, continue to `Cases_on args_res`, and try `gvs[no_type_error_result_def]` for the argument-error branch. -> The proof progressed past the immediate IH implication but timed out on the INL branch; the generated prefix remained in the focused Resume instead of reducing to concrete static/nonstatic success branches. (`TO_type_system_rewrite-20260601T081233Z_m1599_t001`)
  - Insert `FAIL_TAC` probe after `Cases_on args_res` to inspect the live goal, then restore source to HEAD. -> Probe confirmed the full generated prefix remains as the live goal shape; source was restored afterward, leaving no proof edit to preserve. (`TO_type_system_rewrite-20260601T081233Z_m1601_t001`, `TO_type_system_rewrite-20260601T081233Z_m1602_t001`)

### Ruled Out

- Inline-under-TRY boundary move in the mutual theorem skeleton
- Direct `simp[]` to discharge the eval_exprs IH antecedent while the generated prefix is live
- `gvs[no_type_error_result_def]` immediately after `Cases_on args_res` in the focused Resume
- Broad `simp`/`gvs`/`AllCaseEqs()` cleanup of the full ExtCall prefix or long generated-prefix adapter theorem

### Evidence refs

- `TO_type_system_rewrite-20260601T081233Z_m1595_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1599_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1601_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1602_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1605_t001` (use `read_tool_output` for exact output)

## C0.3

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0075`
- blocker: 
- actual effort: 1 sessions, 6 steps, 9 tools, 847,873 tok (846,768 in, 1,105 out, 839,936 cached), 35.0s, $0.487278
- next: Call plan_oracle(mode='review') for C0.3; if accepted, inspect query_plan for whether C0 is complete and then follow the stop/report outcome.

### Attempts / Evidence

- `E0028` (proved, , actual effort: 1 sessions, 1 msgs, 6 steps, 9 tools, 558,111 tok (556,711 in, 1,400 out, 518,912 cached), 38.6s, $0.490451)
  - Audited semantics/prop diffs, staged only relevant tracked task-owned files, and committed the source cleanup/status-report checkpoint with `git commit --no-gpg-sign`. -> Unsigned commit `59acfa4d5 Record ExtCall proof-interface blocker` created. Post-commit status has only pre-existing untracked `semantics/prop/LEARNINGS_type_system_rewrite.legacy.md`; tracked task changes are committed. Focused `vyperTypeStmtSoundnessTheory` build had already succeeded after the source cleanup, and plan markdown edits do not affect HOL build. (`TO_type_system_rewrite-20260531T201607Z_m0543_t001`, `TO_type_system_rewrite-20260531T201607Z_m0556_t001`, `TO_type_system_rewrite-20260531T201607Z_m0558_t001`, `TO_type_system_rewrite-20260531T201607Z_m0558_t002`, `TO_type_system_rewrite-20260531T201607Z_m0559_t001`, `TO_type_system_rewrite-20260531T201607Z_m0560_t001`, `TO_type_system_rewrite-20260531T201607Z_m0560_t002`)
- `E0075` (proved, , actual effort: 1 sessions, 6 steps, 9 tools, 847,873 tok (846,768 in, 1,105 out, 839,936 cached), 35.0s, $0.487278)
  - Inspected tracked/untracked status and staged only tracked task-owned files under `semantics/prop` for the E0072 stop/report update. -> Only the intended tracked plan/dossier/learnings/state/report files were staged; untracked scratch/legacy files remained untracked. (`TO_type_system_rewrite-20260601T081233Z_m1675_t001`, `TO_type_system_rewrite-20260601T081233Z_m1675_t002`, `TO_type_system_rewrite-20260601T081233Z_m1675_t003`, `TO_type_system_rewrite-20260601T081233Z_m1676_t001`, `TO_type_system_rewrite-20260601T081233Z_m1677_t001`, `TO_type_system_rewrite-20260601T081233Z_m1677_t002`)
  - Committed the stopped ExtCall report/audit checkpoint with `git commit --no-gpg-sign`. -> Unsigned commit `e020b7978 Report ExtCall boundary failure after E0072` was created. Post-commit status has only the known untracked scratch/legacy files. (`TO_type_system_rewrite-20260601T081233Z_m1678_t001`, `TO_type_system_rewrite-20260601T081233Z_m1679_t001`, `TO_type_system_rewrite-20260601T081233Z_m1679_t002`)

### Evidence refs

- `TO_type_system_rewrite-20260601T081233Z_m1675_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1677_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1678_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1679_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260601T081233Z_m1679_t002` (use `read_tool_output` for exact output)

## C1.1

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0024`
- blocker: 
- actual effort: 1 sessions, 6 steps, 10 tools, 447,597 tok (445,233 in, 2,364 out, 423,168 cached), 60.6s, $0.392829
- next: Call plan_oracle(mode='review') for C1.1, then begin C1.2 if accepted.

### Attempts / Evidence

- `E0002` (stuck, risk_mismatch, actual effort: 1 sessions, 1 msgs, 11 steps, 10 tools, 3 holbuild, 1,604,921 tok (1,602,110 in, 2,811 out, 1,579,136 cached), 124.9s, $0.988768)
  - Tried proving ExtCall inline in the `Resume` by unfolding `evaluate_def`, splitting args success, then static/nonstatic and stepping monadic operations toward `extcall_return_tail_sound`. -> This violated the PLAN's helper-boundary guidance and produced repeated >4KB goals/timeouts on broad simplification (`gvs[]`, `simp[dest_AddressV_def]`) even for small list/case steps. Source was reverted to the original `cheat` so `vyperTypeStmtSoundnessTheory` builds again (with cheat warnings). (`TO_type_system_rewrite-20260531T201026Z_m0010_t001`, `TO_type_system_rewrite-20260531T201607Z_m0030_t001`, `TO_type_system_rewrite-20260531T201607Z_m0034_t001`, `TO_type_system_rewrite-20260531T201607Z_m0038_t001`)
  - Used `FAIL_TAC "probe_extcall_resume"` to inspect live ExtCall Resume context after `rpt gen_tac >> strip_tac`. -> The live context has a generated IH for args and an optional driver IH, plus a large evaluator-success implication already in assumptions. This confirms the proof should be factored into a standalone helper instead of continuing inside the Resume. (`TO_type_system_rewrite-20260531T201026Z_m0007_t001`)
- `E0022` (stuck, risk_mismatch, actual effort: 1 sessions, 1 steps, 59,854 tok (59,194 in, 660 out, 55,680 cached), 13.5s, $0.065210)
  - Executed replacement-plan mechanical stop/report leaf; did not edit, build, or retry ExtCall tactics. -> Accepted blocker evidence is recorded: C1.1.3.1 produced the useful conditional continuation helper, but C1.1.3.2/C1.1.3.2.1 both failed at deriving its conditional driver premise from generated driver_ih without brittle >4KiB generated-prefix simplification. This meets the user's stop-on-design-problem condition. ()
- `E0023` (proved, , actual effort: 1 sessions, 1 msgs, 1 steps, 52,544 tok (51,966 in, 578 out, 43,392 cached), 13.1s, $0.081906)
  - Executed terminal blocked-report leaf without edits, holbuild, source cleanup/revert, or commit, per replacement PLAN. -> C1.1's operational obligation is satisfied as a report-only component: preserved that extcall_success_continuation_sound_cond_driver_ih is useful, identified the remaining Resume need for the conditional driver premise when returnData = [] /\ IS_SOME drv, cited prior E0019/E0020/E0022 generated-prefix timeout evidence, and maintained the task-contract distinction that this is a proof-interface/design blocker rather than theorem falsehood. (`TO_type_system_rewrite-20260531T201607Z_m0464_t001`, `TO_type_system_rewrite-20260531T201607Z_m0465_t001`)
- `E0024` (proved, , actual effort: 1 sessions, 6 steps, 10 tools, 447,597 tok (445,233 in, 2,364 out, 423,168 cached), 60.6s, $0.392829)
  - Inspected `git diff -- semantics/prop/vyperTypeStmtSoundnessScript.sml` and grepped for forbidden ExtCall proof shapes. -> Identified the known-bad generated-prefix proof text inside `Resume eval_all_type_sound_mutual[Expr_Call_ExtCall]`, including long `driver_ih` qspecl plumbing and broad `asm "driver_ih" mp_tac >> simp[]`; preserved proved helper cluster (`runtime_consistent_get_tenv`, `extcall_success_continuation_sound_cond_driver_ih`). (`TO_type_system_rewrite-20260531T201607Z_m0515_t002`, `TO_type_system_rewrite-20260531T201607Z_m0515_t003`, `TO_type_system_rewrite-20260531T201607Z_m0515_t001`)
  - Replaced the partial failing ExtCall Resume body with a small reviewable skeleton that closes the place-expression half and explicitly fails at the C1.2 compact-interface checkpoint marker, without adding `cheat`. -> The long generated-prefix qspecl block and broad driver_ih simplification fallback are removed from the Resume; the source is intentionally partial for the next proof-interface component rather than a build-clean proof checkpoint. (`TO_type_system_rewrite-20260531T201607Z_m0517_t002`, `TO_type_system_rewrite-20260531T201607Z_m0519_t002`, `TO_type_system_rewrite-20260531T201607Z_m0519_t003`)
  - Removed untracked scratch `semantics/prop/tmp_extcall_helper.sml` from the working tree via a path-limited git stash because no direct delete tool is available. -> Fresh status no longer lists `tmp_extcall_helper.sml`; only task-owned markdown/source diffs and pre-existing untracked LEARNINGS legacy file remain. (`TO_type_system_rewrite-20260531T201607Z_m0518_t001`, `TO_type_system_rewrite-20260531T201607Z_m0519_t001`)

### Evidence refs

- `TO_type_system_rewrite-20260531T201607Z_m0515_t002` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260531T201607Z_m0517_t002` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260531T201607Z_m0518_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260531T201607Z_m0519_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260531T201607Z_m0519_t002` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260531T201607Z_m0519_t003` (use `read_tool_output` for exact output)

## C1.1.1

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0012`
- blocker: 
- actual effort: 1 sessions, 1 steps, 83,627 tok (83,370 in, 257 out, 80,256 cached), 6.4s, $0.063408

### Attempts / Evidence

- `E0003` (stuck, wrong_statement, actual effort: 1 sessions, 2 msgs, 10 steps, 15 tools, 3 holbuild, 750,395 tok (744,790 in, 5,605 out, 698,112 cached), 163.1s, $0.750596)
  - Inserted the PLAN-specified `extcall_after_state_update_tail_sound[local]` with `Call loc (ExtCall stat (func_name,arg_types,ret_type))` conclusion and tried the intended composition: derive runtime consistency by `update_accounts_transient_runtime_consistent`, then `irule extcall_return_tail_sound >> simp[]`. -> The proof reduced to unprovable side conditions including `∀e. drv = SOME e ⇒ ret_type = loc` and `∃ret_tv. evaluate_type env.type_defs loc = SOME ret_tv`, showing the wrapper statement is too general for the existing tail lemma, whose result expression is `Call ret_type (ExtCall stat fsig) es drv`. Source was reverted and focused build restored. (`TO_type_system_rewrite-20260531T201607Z_m0048_t001`, `TO_type_system_rewrite-20260531T201607Z_m0050_t001`)
- `E0004` (proved, , actual effort: 1 sessions, 5 steps, 4 tools, 2 holbuild, 448,149 tok (446,738 in, 1,411 out, 439,168 cached), 142.5s, $0.299764)
  - Inserted corrected `extcall_after_state_update_tail_sound[local]` using `Call ret_type (ExtCall stat (func_name,arg_types,ret_type)) es drv`; derived updated-state `runtime_consistent` via `update_accounts_transient_runtime_consistent`, then applied `extcall_return_tail_sound` with `metis_tac[]` for the driver-IH weakening and existential tail equation premises. -> Focused `holbuild(targets=["vyperTypeStmtSoundnessTheory"], timeout=120)` succeeded; C1.1.1 boundary lemma is proved and source kept. (`TO_type_system_rewrite-20260531T201607Z_m0065_t001`)
- `E0012` (proved, , actual effort: 1 sessions, 1 steps, 83,627 tok (83,370 in, 257 out, 80,256 cached), 6.4s, $0.063408)
  - Carried-forward component: no source edits; verified by existing proved episode E0004 and focused build evidence for `extcall_after_state_update_tail_sound`. -> No remaining proof work for this carried-forward bridge; retained as a stable dependency of the ExtCall helper package. (`TO_type_system_rewrite-20260531T201607Z_m0065_t001`)

### Evidence refs

- `TO_type_system_rewrite-20260531T201607Z_m0065_t001` (use `read_tool_output` for exact output)

## C1.1.2

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0013`
- blocker: 
- actual effort: 1 sessions, 1 steps, 90,602 tok (90,346 in, 256 out, 86,400 cached), 6.3s, $0.070610

### Attempts / Evidence

- `E0005` (progressed, other, actual effort: 1 sessions, 9 steps, 14 tools, 2 holbuild, 1,212,028 tok (1,210,034 in, 1,994 out, 1,180,032 cached), 122.9s, $0.799846)
  - Temporarily replaced the ExtCall Resume cheat with `FAIL_TAC "probe_extcall_c112"` to inspect the live generated IH shapes needed by the standalone helper, then restored the cheat and rebuilt. -> Probe confirmed the Resume has exactly two relevant IH assumptions: driver IH (including expression and place branches for `THE drv`, guarded by `returnData = [] ∧ IS_SOME drv`) and argument-list IH for `eval_exprs cx es`. The top goal is >4KiB, reinforcing that C1.1.2 should introduce a helper rather than prove inside the Resume. Source was restored and focused build is clean. (`TO_type_system_rewrite-20260531T201607Z_m0084_t001`, `TO_type_system_rewrite-20260531T201607Z_m0086_t001`)
- `E0006` (stuck, risk_mismatch, actual effort: 1 sessions, 4 msgs, 53 steps, 68 tools, 15 holbuild, 5,470,012 tok (5,455,465 in, 14,547 out, 5,277,056 cached), 625.3s, $3.966983)
  - Added standalone `extcall_expr_sound_from_generated_ih` with return-type annotation, consuming args IH and driver IH, then stepped ExtCall evaluator prefix to call `extcall_after_state_update_tail_sound`. -> The proof did not remain straightforward: after several refinements, applying the tail bridge required brittle manual case plumbing and produced matching/timeouts/FOL-solver failures in the static success branch. This violates the component's Risk-2 expectation and the task instruction to stop on unexpected design/proof issues. (`TO_type_system_rewrite-20260531T201607Z_m0112_t001`, `TO_type_system_rewrite-20260531T201607Z_m0129_t001`, `TO_type_system_rewrite-20260531T201607Z_m0149_t001`, `TO_type_system_rewrite-20260531T201607Z_m0151_t001`)
- `E0013` (proved, , actual effort: 1 sessions, 1 steps, 90,602 tok (90,346 in, 256 out, 86,400 cached), 6.3s, $0.070610)
  - Carried-forward component: no source edits; rely on previously proved/reviewed ExtCall helper package (`extcall_success_continuation_sound`, `extcall_expr_sound_from_generated_ih`) and focused build/review evidence. -> No remaining proof work for this carried-forward helper package; retained as stable dependency for C1.1.3 adapter work. (`TO_type_system_rewrite-20260531T201607Z_m0229_t001`, `TO_type_system_rewrite-20260531T201607Z_m0231_t001`)

### Evidence refs

- `TO_type_system_rewrite-20260531T201607Z_m0229_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260531T201607Z_m0231_t001` (use `read_tool_output` for exact output)

## C1.1.2.0

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0007`
- blocker: 
- actual effort: 1 sessions, 4 steps, 3 tools, 1 holbuild, 569,970 tok (569,517 in, 453 out, 562,176 cached), 111.9s, $0.331383

### Attempts / Evidence

- `E0007` (proved, , actual effort: 1 sessions, 4 steps, 3 tools, 1 holbuild, 569,970 tok (569,517 in, 453 out, 562,176 cached), 111.9s, $0.331383)
  - Deleted the failed partial `extcall_expr_sound_from_generated_ih` block from E0006 while keeping the small `env_consistent_get_tenv` helper, then rebuilt `vyperTypeStmtSoundnessTheory`. -> Focused build succeeded, confirming no unfinished failed proof remains and the cleanup gate is complete. The only source change left for this component is the build-clean local helper `env_consistent_get_tenv`. (`TO_type_system_rewrite-20260531T201607Z_m0158_t001`, `TO_type_system_rewrite-20260531T201607Z_m0159_t001`)

### Evidence refs

- `TO_type_system_rewrite-20260531T201607Z_m0159_t001` (use `read_tool_output` for exact output)

## C1.1.2.1

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0008`
- blocker: 
- actual effort: 1 sessions, 1 msgs, 12 steps, 12 tools, 4 holbuild, 711,735 tok (708,877 in, 2,858 out, 671,232 cached), 226.2s, $0.609581
- next: Call plan_oracle review for C1.1.2.1, then if accepted commit the source checkpoint without GPG signing before beginning C1.1.2.2.

### Attempts / Evidence

- `E0008` (proved, , actual effort: 1 sessions, 1 msgs, 12 steps, 12 tools, 4 holbuild, 711,735 tok (708,877 in, 2,858 out, 671,232 cached), 226.2s, $0.609581)
  - Added local theorem extcall_success_continuation_sound after env_consistent_get_tenv; simplified assert/update suffix, rewrote get_tenv from runtime_consistent/env_consistent_get_tenv, extracted evaluate_type witness from well_formed_type, and applied extcall_after_state_update_tail_sound with explicit conjunct/witness discharge. -> Focused build of vyperTypeStmtSoundnessTheory succeeded, validating the new boundary lemma in source. (`TO_type_system_rewrite-20260531T201607Z_m0180_t001`)
  - Initial proof ended with broad metis_tac after irule extcall_after_state_update_tail_sound. -> Failed/timed out on the packaged existential/conjunct goal; replaced with explicit conjunct_tac and qexistsl, avoiding broad FOL search. (`TO_type_system_rewrite-20260531T201607Z_m0176_t001`, `TO_type_system_rewrite-20260531T201607Z_m0178_t001`)

### Evidence refs

- `TO_type_system_rewrite-20260531T201607Z_m0180_t001` (use `read_tool_output` for exact output)

## C1.1.2.2

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0009`
- blocker: 
- actual effort: 1 sessions, 3 msgs, 42 steps, 43 tools, 14 holbuild, 4,625,694 tok (4,614,498 in, 11,196 out, 4,483,328 cached), 756.7s, $3.233394
- next: Call plan_oracle review for C1.1.2.2; if accepted, commit the helper checkpoint without GPG signing, then begin C1.1.3.

### Attempts / Evidence

- `E0009` (proved, , actual effort: 1 sessions, 3 msgs, 42 steps, 43 tools, 14 holbuild, 4,625,694 tok (4,614,498 in, 11,196 out, 4,483,328 cached), 756.7s, $3.233394)
  - Added local theorem extcall_expr_sound_from_generated_ih with generated args/driver IH premises; unfolded ExtCall evaluator prefix, split eval_exprs/static/nonstatic/failure branches, used extcall_*_args_runtime_typed_dest and run_ext_call_accounts_well_typed, then delegated success suffix to extcall_success_continuation_sound. -> Focused holbuild of vyperTypeStmtSoundnessTheory succeeded, validating the helper. Static and nonstatic success branches now use the continuation boundary rather than extcall_after_state_update_tail_sound directly. (`TO_type_system_rewrite-20260531T201607Z_m0229_t001`)
  - Initial direct irule extcall_success_continuation_sound after rewriting no_type_error_result failed to match/then left large conjunct packaging goals. -> Reordered/explicitly discharged boundary premises and used qexistsl only to package the continuation-boundary existential at success branches; avoided broad metis over the full suffix. (`TO_type_system_rewrite-20260531T201607Z_m0198_t001`, `TO_type_system_rewrite-20260531T201607Z_m0200_t001`, `TO_type_system_rewrite-20260531T201607Z_m0207_t001`)
  - Nonstatic branch needed one extra normalization of the post-run do-block after get_accounts/get_transient_storage before applying the continuation boundary. -> Simplifying update_accounts/update_transient/bind/return in the local assumption aligned the suffix premise with extcall_success_continuation_sound and build passed. (`TO_type_system_rewrite-20260531T201607Z_m0227_t001`, `TO_type_system_rewrite-20260531T201607Z_m0229_t001`)

### Evidence refs

- `TO_type_system_rewrite-20260531T201607Z_m0229_t001` (use `read_tool_output` for exact output)

## C1.1.3

### Current Status

- result: `stuck`
- diagnosis: `risk_mismatch` Risk-2 estimate remains wrong after the shallow rebase. The component needs a more precise strategist-owned adapter theorem statement/proof route, likely near the Resume and not by modifying `extcall_expr_sound_from_generated_ih`.
- latest episode: `E0014`
- blocker: The planned adapter/refactor is not straightforward: direct Resume simplification of the guarded driver IH times out, while changing the stable helper to take the guarded premise pollutes/rebreaks the helper proof and violates the instruction not to reopen C1.1.2. A precise helper-interface design is still missing.
- actual effort: 1 sessions, 2 msgs, 29 steps, 28 tools, 8 holbuild, 3,507,541 tok (3,499,626 in, 7,915 out, 3,397,504 cached), 386.9s, $2.446812
- next: Call plan_oracle review for C1.1.3 with this evidence; ask for a concrete adapter theorem statement/proof route that does not reopen C1.1.2 and does not require simplifying the full guarded IH in the Resume.

### Attempts / Evidence

- `E0010` (progressed, other, actual effort: 1 sessions, 2 msgs, 8 steps, 9 tools, 1 holbuild, 1,188,586 tok (1,186,728 in, 1,858 out, 1,146,880 cached), 250.2s, $0.828420)
  - Started replacing ExtCall Resume cheat with `type_place_expr_Call_ExtCall_NONE` plus a short Resume proof that labels generated `driver_ih` and `actual_ih`, then applies `extcall_expr_sound_from_generated_ih`. -> First build failed because the helper conclusion uses the signature return type `ret_type`, while the Resume goal still had annotation variable `v15`; source was then edited to unfold `well_typed_expr_def` and derive `v15 = ret_type` before applying the helper, but this last edit has not been rebuilt due to handoff. (`TO_type_system_rewrite-20260531T201607Z_m0242_t001`)
- `E0011` (stuck, risk_mismatch, actual effort: 1 sessions, 3 msgs, 21 steps, 23 tools, 3 holbuild, 1,992,933 tok (1,984,963 in, 7,970 out, 1,905,536 cached), 429.5s, $1.589003)
  - Expose ExtCall call annotation with `qpat_x_assum ... mp_tac >> simp[Once well_typed_expr_def] >> strip_tac >> gvs[]`, then `irule extcall_expr_sound_from_generated_ih` and discharge premises by matching labelled generated IH assumptions. -> Annotation mismatch was fixed: goal now has `Call ret_type ...`, but `rpt conj_tac` exposed that the helper wants an unconditional driver IH while the generated `driver_ih` in the Resume is guarded by ExtCall-success prefix premises and also returns expression/place conjuncts. (`TO_type_system_rewrite-20260531T201607Z_m0248_t001`)
  - Replace broad `rpt conj_tac >> (MATCH_ACCEPT_TAC labelled IH ORELSE first_assum ACCEPT_TAC)` with explicit branches for actual and driver IH premises (`asm "actual_ih" mp_tac >> simp[]`, `asm "driver_ih" mp_tac >> simp[]`). -> Actual IH premise discharged, but driver branch timed out on a huge implication headed by the prefixed generated `driver_ih`; this confirms the Resume cannot supply the helper's pure driver-IH premise by simple matching/simplification. This is a helper-interface mismatch, not a local annotation tactic issue. (`TO_type_system_rewrite-20260531T201607Z_m0256_t001`)
- `E0014` (stuck, risk_mismatch, actual effort: 1 sessions, 2 msgs, 29 steps, 28 tools, 8 holbuild, 3,507,541 tok (3,499,626 in, 7,915 out, 3,397,504 cached), 386.9s, $2.446812)
  - Tried to implement the planned generated-guarded adapter by changing `extcall_expr_sound_from_generated_ih` to accept the guarded driver IH shape directly. -> This reopened the stable C1.1.2 helper and made its proof time out on existing simplification points because the added huge guarded assumption polluted `simp`/`gvs`; this violates the plan's instruction not to reopen/optimize C1.1.2 helpers. The helper proof was restored to its prior premise/proof shape before recording this stuck episode. (`TO_type_system_rewrite-20260531T201607Z_m0283_t001`, `TO_type_system_rewrite-20260531T201607Z_m0285_t001`, `TO_type_system_rewrite-20260531T201607Z_m0287_t001`, `TO_type_system_rewrite-20260531T201607Z_m0289_t001`, `TO_type_system_rewrite-20260531T201607Z_m0294_t001`, `TO_type_system_rewrite-20260531T201607Z_m0296_t001`)
  - Restored `extcall_expr_sound_from_generated_ih` to stable source shape and reran focused build with the current Resume wrapper. -> Build returns to the known C1.1.3 failure: annotation is fixed (`Call ret_type ...`) and the actual-IH branch closes, but `asm "driver_ih" mp_tac >> simp[]` times out trying to coerce the huge generated guarded driver IH into the pure driver premise. No clean adapter was produced within the existing component guidance. (`TO_type_system_rewrite-20260531T201607Z_m0303_t001`)

### Ruled Out

- Do not modify `extcall_expr_sound_from_generated_ih` to take the huge guarded driver IH directly without a separate proof plan; it makes the stable helper proof time out.
- Do not continue `asm "driver_ih" mp_tac >> simp[]` in the Resume; repeated evidence shows it times out.

### Evidence refs

- `TO_type_system_rewrite-20260531T201607Z_m0283_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260531T201607Z_m0285_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260531T201607Z_m0287_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260531T201607Z_m0289_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260531T201607Z_m0294_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260531T201607Z_m0296_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260531T201607Z_m0303_t001` (use `read_tool_output` for exact output)

## C1.1.3.0

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0016`
- blocker: 
- actual effort: 1 sessions, 1 msgs, 5 steps, 4 tools, 1 holbuild, 710,231 tok (709,673 in, 558 out, 680,832 cached), 116.3s, $0.501361

### Attempts / Evidence

- `E0016` (proved, , actual effort: 1 sessions, 1 msgs, 5 steps, 4 tools, 1 holbuild, 710,231 tok (709,673 in, 558 out, 680,832 cached), 116.3s, $0.501361)
  - Deleted the partial failed `extcall_success_continuation_sound_from_guarded_driver_ih[local]` prefix-packaged helper and stray proof tail from `vyperTypeStmtSoundnessScript.sml`. -> Focused build now passes the helper cluster and fails later at the pre-existing `Expr_Call_ExtCall` Resume timeout, confirming the partial helper was removed and source parses/builds past the cleanup point. (`TO_type_system_rewrite-20260531T201607Z_m0360_t001`)

### Evidence refs

- `TO_type_system_rewrite-20260531T201607Z_m0357_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260531T201607Z_m0359_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260531T201607Z_m0360_t001` (use `read_tool_output` for exact output)

## C1.1.3.1

### Current Status

- result: `proved`
- diagnosis: `n/a`
- latest episode: `E0018`
- blocker: 
- actual effort: 1 sessions, 2 msgs, 34 steps, 38 tools, 13 holbuild, 2,510,676 tok (2,503,082 in, 7,594 out, 2,420,992 cached), 474.3s, $1.848766
- next: Call plan_oracle review for C1.1.3.1, then begin queued C1.1.3.2 to refactor the `Expr_Call_ExtCall` Resume using the new conditional boundary.

### Attempts / Evidence

- `E0015` (stuck, risk_mismatch, actual effort: 1 sessions, 3 msgs, 41 steps, 40 tools, 15 holbuild, 4,399,850 tok (4,384,546 in, 15,304 out, 4,232,064 cached), 616.6s, $3.337562)
  - Added local `extcall_success_continuation_sound_from_guarded_driver_ih` matching the generated guarded `driver_ih` shape and tried to prove it as a variant of `extcall_success_continuation_sound`. -> The theorem statement compiles far enough to start proof, but proof is not straightforward: broad `gvs`/`simp` over the continuation or guarded IH times out, even after labeling/removing `driver_ih` before some simplification steps. (`TO_type_system_rewrite-20260531T201607Z_m0329_t001`, `TO_type_system_rewrite-20260531T201607Z_m0349_t001`, `TO_type_system_rewrite-20260531T201607Z_m0353_t001`)
  - Tried targeted instantiation of labelled `driver_ih` after isolating the `returnData = [] /\ IS_SOME drv` branch, avoiding record-update witnesses by using live prefix variables. -> The specialized implication remains too large for `simp[]` to discharge the prefix and times out. This suggests the planned boundary statement still forces brittle simplification of the guarded IH rather than a clean adapter proof. (`TO_type_system_rewrite-20260531T201607Z_m0351_t001`, `TO_type_system_rewrite-20260531T201607Z_m0353_t001`)
- `E0017` (progressed, other, actual effort: 1 sessions, 1 msgs, 4 steps, 6 tools, 1 holbuild, 618,273 tok (615,993 in, 2,280 out, 589,824 cached), 66.2s, $0.494157)
  - Inserted `extcall_success_continuation_sound_cond_driver_ih[local]` with conditional driver-IH premise (no generated ExtCall prefix variables) and copied the continuation proof structure. -> The theorem parses and proof starts, but focused build currently fails in the proof of `get_tenv cx = env.type_defs`; the attempted `irule env_consistent_get_tenv >> gvs[runtime_consistent_def]` did not solve the subgoal. Source is partial and should not be committed. (`TO_type_system_rewrite-20260531T201607Z_m0364_t001`, `TO_type_system_rewrite-20260531T201607Z_m0365_t001`)
- `E0018` (proved, , actual effort: 1 sessions, 2 msgs, 34 steps, 38 tools, 13 holbuild, 2,510,676 tok (2,503,082 in, 7,594 out, 2,420,992 cached), 474.3s, $1.848766)
  - Added a tiny local `runtime_consistent_get_tenv` projection and used it to avoid broad simplification for the `get_tenv cx = env.type_defs` subgoal. -> The focused `get_tenv` proof progressed; holbuild moved past the earlier C1.1.3.1 failure. (`TO_type_system_rewrite-20260531T201607Z_m0377_t001`)
  - In the true `returnData = [] /\ IS_SOME drv` branch, kept `runtime_consistent` intact, specialized the conditional driver IH directly, explicitly discharged its post-update antecedent, and used `well_typed_expr_not_hashmap_place` only for the call-result hashmap-place contradiction. -> The true branch closed after avoiding the old broad guarded-IH simplification path. (`TO_type_system_rewrite-20260531T201607Z_m0394_t001`)
  - In the ABI-decode branch, asserted post-update `runtime_consistent`, unfolded it locally, and reused `evaluate_abi_decode_return_well_typed` without the obsolete `strip_tac`. -> `extcall_success_continuation_sound_cond_driver_ih` completed; the next holbuild failure is downstream in `eval_all_type_sound_mutual[Expr_Call_ExtCall]` at the queued Resume refactor, not inside this helper. (`TO_type_system_rewrite-20260531T201607Z_m0403_t001`)

### Evidence refs

- `TO_type_system_rewrite-20260531T201607Z_m0403_t001` (use `read_tool_output` for exact output)

## C1.1.3.2

### Current Status

- result: `stuck`
- diagnosis: `risk_mismatch` The conditional boundary helper itself is sound/proved, but the downstream interface still leaves the generated IH prefix too large for local consumption. The plan likely needs a smaller adapter/helper or a different Resume decomposition that avoids either broad simplification or long manual prefix instantiation.
- latest episode: `E0019`
- blocker: C1.1.3.2 was expected to be a straightforward Resume refactor, but proving the conditional driver-IH premise locally still requires manipulating/simplifying the huge generated ExtCall prefix. Even after specializing the generated IH to live static-branch variables, simplification times out; this contradicts the PLAN's risk/approach and the user instruction to stop on non-straightforward design issues.
- actual effort: 1 sessions, 1 msgs, 28 steps, 28 tools, 7 holbuild, 3,149,603 tok (3,140,298 in, 9,305 out, 3,062,272 cached), 445.4s, $2.200416
- next: Call plan_oracle review for C1.1.3.2 with evidence and ask for a de-risked adapter/decomposition for consuming the generated guarded driver IH without broad prefix simplification.

### Attempts / Evidence

- `E0019` (stuck, risk_mismatch, actual effort: 1 sessions, 1 msgs, 28 steps, 28 tools, 7 holbuild, 3,149,603 tok (3,140,298 in, 9,305 out, 3,062,272 cached), 445.4s, $2.200416)
  - Copied the previously proved ExtCall expression proof body into the `Expr_Call_ExtCall` Resume and replaced calls to `extcall_success_continuation_sound` with the new conditional boundary helper. -> This progressed past the old top-level `asm "driver_ih" mp_tac >> simp[]` timeout and reached the static success branch, but exposed brittle conjunct/existential ordering after applying the boundary. (`TO_type_system_rewrite-20260531T201607Z_m0413_t001`, `TO_type_system_rewrite-20260531T201607Z_m0426_t001`)
  - Replaced slow `metis_tac[run_ext_call_accounts_well_typed]` with targeted `drule_all run_ext_call_accounts_well_typed >> simp[]`. -> This avoided a timeout from searching a large context and progressed to the boundary-helper premise assembly. (`TO_type_system_rewrite-20260531T201607Z_m0417_t001`)
  - Tried to discharge the conditional driver-IH premise by first using `asm "driver_ih" mp_tac >> simp[]`, then by manually specializing the generated `driver_ih` with the live static-branch prefix variables before simplifying only monadic/check definitions. -> Both routes timed out on a >4KiB generated-prefix goal. The second route also violates the component's not-to-try guidance (long `qspecl_then` over the generated prefix), confirming this is not a straightforward refactor under the current interface/tactic shape. (`TO_type_system_rewrite-20260531T201607Z_m0430_t001`, `TO_type_system_rewrite-20260531T201607Z_m0433_t001`)

### Ruled Out

- Top-level `asm "driver_ih" mp_tac >> simp[]` for the conditional premise: timed out on the huge generated-prefix implication.
- Long manual `qspecl_then` of all generated prefix variables followed by simplification: also timed out and is brittle/against the component guidance.
- Using broad `metis_tac` in the large Resume context for side facts such as `run_ext_call_accounts_well_typed`: timed out; targeted `drule_all` works for that side fact only.

### Evidence refs

- `TO_type_system_rewrite-20260531T201607Z_m0413_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260531T201607Z_m0430_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260531T201607Z_m0433_t001` (use `read_tool_output` for exact output)

## C1.1.3.2.1

### Current Status

- result: `stuck`
- diagnosis: `risk_mismatch` The branch-local adapter plan did not remove the core interface problem; it only moved it into a smaller leaf. A different strategy is needed, likely avoiding generated-prefix consumption inside this Resume entirely or introducing a theorem/helper whose statement is generated by/for the exact IH shape without in-proof simplification.
- latest episode: `E0020`
- blocker: The new static adapter leaf C1.1.3.2.1 is not executable as Risk 2: even after explicit specialization, discharging the generated prefix still requires broad simplification/manipulation of a >4KiB generated implication and times out. This is exactly the failure sign in the replacement PLAN and the user asked to stop when design is not straightforward.
- actual effort: 1 sessions, 6 steps, 5 tools, 2 holbuild, 876,991 tok (874,205 in, 2,786 out, 858,368 cached), 118.1s, $0.591949
- next: Call plan_oracle review for C1.1.3.2.1; request a higher-level redesign or operator stop per task instruction rather than another local generated-prefix adapter.

### Attempts / Evidence

- `E0020` (stuck, risk_mismatch, actual effort: 1 sessions, 6 steps, 5 tools, 2 holbuild, 876,991 tok (874,205 in, 2,786 out, 858,368 cached), 118.1s, $0.591949)
  - Tried to implement the new static branch adapter by specializing generated `driver_ih` to concrete static branch variables, then extracting the compact conditional premise for `extcall_success_continuation_sound_cond_driver_ih`. -> The proof still reaches a >4KiB specialized generated-prefix goal. `impl_tac` with conjunct-by-conjunct simplification did not solve the antecedent; switching to direct simplification of the specialized implication also timed out. This repeats the E0019 failure shape despite the replacement plan's claim that this leaf is low-risk. (`TO_type_system_rewrite-20260531T201607Z_m0439_t001`, `TO_type_system_rewrite-20260531T201607Z_m0442_t001`)

### Ruled Out

- Specialize `driver_ih` with concrete static prefix variables then use `impl_tac` plus `rpt conj_tac`/targeted simp: first subgoal not solved and remains a huge implication.
- Specialize `driver_ih` then simplify monadic/check definitions over the specialized implication: timed out on a >4KiB goal.

### Evidence refs

- `TO_type_system_rewrite-20260531T201607Z_m0439_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260531T201607Z_m0442_t001` (use `read_tool_output` for exact output)

## C1.2

### Current Status

- result: `stuck`
- diagnosis: `risk_mismatch` Risk estimate was too low: the local compact bridge is easy, but the required source-level interface is absent from the generated mutual-induction Resume. The available IH is exactly the generated-prefix shape C1 forbids. This is a proof-interface/decomposition issue, not a tactic gap.
- latest episode: `E0025`
- blocker: C1.2 compact bridge theorem itself is straightforward and parses/proves, but the live ExtCall Resume checkpoint goal still provides only the generated `driver_ih` hidden behind the full ExtCall monadic prefix. The compact driver premise is not naturally available as a standalone live assumption; deriving it would require the already-forbidden generated-prefix specialization/simplification path.
- actual effort: 1 sessions, 1 msgs, 5 steps, 5 tools, 2 holbuild, 451,513 tok (448,935 in, 2,578 out, 388,992 cached), 157.8s, $0.571551
- next: Call plan_oracle(mode='review') for C1.2 with the checkpoint goal evidence; request replacement/decomposition that changes the mutual induction/suspend boundary or otherwise exposes a compact driver IH without generated-prefix plumbing.

### Attempts / Evidence

- `E0025` (stuck, risk_mismatch, actual effort: 1 sessions, 1 msgs, 5 steps, 5 tools, 2 holbuild, 451,513 tok (448,935 in, 2,578 out, 388,992 cached), 157.8s, $0.571551)
  - Added local tautological bridge `extcall_driver_continuation_premise_from_compact_ih` with only a compact conditional IH premise and no generated ExtCall prefix. -> Focused build passed this new theorem and resumed to the explicit ExtCall checkpoint marker, so the bridge statement/proof itself is mechanically acceptable. (`TO_type_system_rewrite-20260531T201607Z_m0525_t001`, `TO_type_system_rewrite-20260531T201607Z_m0526_t001`)
  - Used the explicit `FAIL_TAC "C1.2 compact ExtCall driver-continuation interface required"` marker after the cleaned ExtCall Resume prefix to inspect the live proof context. -> The goal shows assumption 0 is still the generated driver IH guarded by a large ExtCall prefix implication over `eval_exprs`, `check`, `lift_option`, `run_ext_call`, `update_accounts`, and `update_transient`; no compact standalone driver-continuation premise exists in the live context. Continuing would require forbidden generated-prefix plumbing. (`TO_type_system_rewrite-20260531T201607Z_m0524_t001`, `TO_type_system_rewrite-20260531T201607Z_m0526_t001`)

### Ruled Out

- Deriving the compact premise by specializing/simplifying assumption 0, the generated ExtCall prefix driver_ih.
- Adding a helper that takes the full generated ExtCall prefix as an assumption.

### Evidence refs

- `TO_type_system_rewrite-20260531T201607Z_m0525_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260531T201607Z_m0526_t001` (use `read_tool_output` for exact output)
- `TO_type_system_rewrite-20260531T201607Z_m0524_t001` (use `read_tool_output` for exact output)
