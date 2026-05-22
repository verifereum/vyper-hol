# STATE_type_system_rewrite
Updated: 2026-05-22

## Cursor
- component: C4.1
- status: ready
- active_file: semantics/prop/vyperTypeBuiltinsScript.sml
- next_action: Before any proof edits/builds, preserve the stable C3.3 checkpoint from this handoff: inspect `git status --short` and `git diff --cached --stat`; stage tracked task-memory changes only (`git add -u semantics/prop/DOSSIER_type_system_rewrite.md semantics/prop/STATE_type_system_rewrite.md`, plus LEARNINGS only if save_handoff changed it) and commit a small checkpoint if the diff is only the reviewed C3.3 closure/handoff. Do not stage untracked scratch files. Then begin_component('C4.1') and run the scoped static-builtin audit requested by the PLAN.
- expected_goal_shape: No live proof goal. PLAN frontier says C4.1 is Oracle next: audit reachable static builtin-typing suspended/cheated cases. It may close by audit evidence if no reachable static builtin typing cheat remains, otherwise expect finite constructor typing obligations in fresh-stack builtin/type-builtin sources.
- verify_with: For checkpoint: no build needed beyond already-clean `holbuild(targets=["vyperTypeStatePreservationTheory"], timeout=600)` for C3.3 evidence. For C4.1 after begin_component: use grep/audit plus `holbuild(targets=["vyperTypeBuiltinsTheory"], timeout=600)` or the exact fresh-stack static builtin target identified by grep.

## If This Fails
- If C4.1 audit finds a reachable static builtin-typing cheat not clearly covered by C4.1, stop and call plan_oracle before editing. If a finite C4.1 proof attempt fails or produces a large unfolded builtin goal, checkpoint_progress on C4.1 with the holbuild/grep evidence and request strategist review rather than proving C4.2/C2 around it.

## Do Not Retry
- Start editing/building C2.4 or C2.5 before C4 boundary components close.: Whole-plan rebase made remaining C2 builtin/type-builtin expression consumers dependent on C3/C4 boundary theorems; doing C2 first risks hidden CHEAT dependencies or forbidden builtin case analysis in statement soundness.
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m40826_t001
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m40867_t004
- Stage or commit untracked scratch files such as `test_*`, `test_conj*`, or `SuspBugProbeScript.sml`.: They are ad-hoc scratch files visible in git status and unrelated to stable proof progress. Only tracked task-owned source/memory changes should be committed.
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m40867_t001
- Reopen C3.1/C3.2/C3.3 unless a later build shows a real regression in their named theorems.: All three C3 leaf closures were source-audited, holbuild-verified, and accepted by strategist review this session; remaining update/subscript work should be downstream C4/C2 unless source changes invalidate them.
  - evidence: episode:E0732
  - evidence: episode:E0733
  - evidence: episode:E0734
- Assume stale dossier entries with old C3.1/C3.2 subcomponent names describe current source obligations without auditing source.: Several old C3.* dossier entries were stale or over-decomposed; current source already contained the completed C3 theorem boundaries. Source audit plus holbuild was the correct way to resolve component reality.
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m40848_t001
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m40856_t001
  - evidence: tool_output:TO_type_system_rewrite-20260522T073012Z_m40864_t001

## Reflection
### Tunnel Vision Check
- Outside-the-box for next session: C4.1 may be an audit-only component if static builtin typing cheats are not reachable from `vyperSemanticsHolTheory`; do not assume proof work exists before grep/build evidence.
- Question whether a visible `cheat` in `vyperTypeBuiltinsScript.sml` belongs to C4.1 or a later C4 leaf (generic builtin, type-builtin, ABI, raw-call). Use PLAN ownership before editing.
- Do not optimize C2 statement soundness while C4 boundaries are incomplete; that would be the wrong abstraction layer.
- If C4.1 proof requires unfolding all builtin semantics, the boundary is probably wrong or the obligation belongs to C4.2/C4.3; escalate rather than tactic-thrashing.
- A fresh expert should first ask: which current cheats are reachable from fresh-stack theories and which are old retired theories or later C4 obligations?

### What Went Wrong
- STATE at session start was stale and pointed to C3.1 even though current source already had the C3 boundary theorems proved. I avoided editing by auditing source and building before doing proof work.
- The prior dossier had many old C3.1/C3.2 subcomponent episodes with stuck tactical details that no longer reflected current source reality. Treating source as authoritative prevented unnecessary retries.
- The final C3.3 closure updated DOSSIER after the last commit; this is stable but currently uncommitted because the handoff signal arrived immediately after strategist review.

### Ignored Signals
- Do not trust old component IDs/subcomponent histories when PLAN has been rebased; component identity drift was already flagged in prior STATE and applied again to C3.
- A clean `holbuild` of `vyperTypeStatePreservationTheory` plus no source `cheat` near the named theorems is stronger evidence than stale stuck entries in DOSSIER.
- Untracked scratch files remain present across sessions; they must be consciously ignored on every commit.

### Strategy Adjustments
- For C4.1, start with an audit rather than proof: grep current source for reachable static builtin typing `cheat`/`suspend`, read the exact regions, and build the relevant target before editing.
- Continue following the rebased dependency order: C4 boundary components before C2 builtin/type-builtin expression consumers, then C5/C6 wrappers.
- When a component may already be solved in current source, close it by source audit + holbuild evidence instead of manufacturing a proof attempt.
- For builtin/type-builtin work, keep constructor analysis in C4 boundary theorems; C2 should consume exported no-TypeError/success-typing theorems.

### Oracle Feedback
- Strategist accepted C3.1/C3.2/C3.3 closures with no PLAN changes; the rebased C3 before C4/C2 order held in practice.
- The old strategist warning about stale component identities was correct: C3 source reality superseded older stuck dossier entries.
- Next strategist-owned frontier is C4.1; no high-risk blockers are present. If the static builtin audit finds an uncovered cheat, call plan_oracle rather than broadening C4.1 locally.

## Evidence Pointers
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40850_t001 - strategist accepted C3.1 binop/update-binop boundary closure
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40858_t001 - strategist accepted C3.2 assignment-operation leaf closure
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40866_t001 - strategist accepted C3.3 recursive assignment-subscript closure
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40864_t003 - `vyperTypeStatePreservationTheory` built clean for C3.3 audit
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40867_t004 - post-C3 query_plan shows C4.1 is Oracle next
- tool_output:TO_type_system_rewrite-20260522T073012Z_m40867_t001 - git status shows only tracked DOSSIER modified plus untracked scratch files
