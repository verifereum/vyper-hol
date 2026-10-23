# STATE_unwrap
Updated: 2026-10-23

## Cursor
- component: C1.3
- status: in_progress
- active_file: lowering/proofs/loweringShapePropsScript.sml
- next_action: Finish the interrupted binder rename: line 562 must read compile_ensure_in_memory src_ptr loc mem_bytes nwords is_ctor (currently still ptr). Then rebuild. Shared slots Resume now uses markerLib.RESUME_TAC; continue framed allocation, slot_copy and calldata probes. Last stable commit a2372a84 contains fully proved word-copy helper; C1.3 skeleton is uncommitted and intentionally fails.
- expected_goal_shape: After rename and shared suspension splitting, slots should reduce to framed compile_alloc_buffer; slot_copy continuation has plain src_ptr and buf.buf_operand. Split nwords=1; singleton load/MSTORE versus framed word-copy loop, then return buf operand. Calldata is separate fixed load/allocation/store/two ADD/CALLDATACOPY sequence.
- verify_with: holbuild(targets=["loweringShapePropsTheory"])

## If This Fails
- Read build state and repair matching with ho_match_mp_tac/BETA_TAC as appropriate. Record meaningful partial evidence with checkpoint_progress; only close component on terminal outcome. Escalate interface/design failures rather than duplicating semantics in consumers.

## Do Not Retry
- Use unqualified RESUME_TAC for multiply-suspended branch: Not declared in default namespace; use markerLib.RESUME_TAC.
  - evidence: tool_output:TO_unwrap-20261023T092756Z_m0146_t001
  - evidence: tool_output:TO_unwrap-20261023T092756Z_m0150_t001
- Apply irule directly to higher-order frame/fresh-label/pure-pre predicates: Often fails to infer lambda predicate; ho_match_mp_tac worked throughout checked loop proof.
  - evidence: tool_output:TO_unwrap-20261023T092756Z_m0098_t001
  - evidence: tool_output:TO_unwrap-20261023T092756Z_m0100_t001
  - evidence: source:lowering/proofs/loweringShapePropsScript.sml

## Reflection
### Tunnel Vision Check
- A fresh expert should first check the incomplete src_ptr rename before interpreting any next build error.
- The fixed runtime-copy generator needs no runtime induction; source decomposition is still appropriate.
- Alternative not explored: a smaller reusable admissibility simp boundary could reduce repeated opcode side-condition lists, but strategist explicitly accepted current repeated local simp lists and no new helpers are needed solely for brevity.
- Do not optimize unrelated generator cheats; frozen unwrap theorem and its necessary non-code boundaries remain the target.

### What Went Wrong
- Initial primitive applications failed from higher-order predicate matching, beta redexes, and irule's reordered premises; these were tactical, fixed with ho_match_mp_tac/BETA_RULE and checked goals.
- Initial plan lacked state-conditioned emission and pure-precondition interfaces. Strategist added them, and they now have short checked proofs.
- Unqualified RESUME_TAC is not exported by default despite instructions suggesting it; located markerLib.RESUME_TAC in markerLib.sig.
- Handoff interrupted src_ptr binder renaming before computation argument was updated; source is not build-clean yet.

### Ignored Signals
- Names ptr, count and size collide with existing constants and become primed after introduction; prefer src_ptr, nwords and nbytes from the start.
- A shared named suspension produces a resumption connective, not separate goals automatically.

### Strategy Adjustments
- Use markerLib.RESUME_TAC then parenthesize the whole common tactic sequence to apply uniformly to shared suspension goals.
- Keep stability subgoals separate before unfolding plain_operand_def for concrete instruction admissibility; otherwise metis sees unresolved literal plainness and times out.
- Use named Resume stages and Finalise for fixed generator compositions; every loop stage is proved and finalised.

### Oracle Feedback
- Strategist accepted non-code load/allocation, state-conditioned emit boundaries, pure-precondition boundary, and full restricted word-copy proof.
- Strategist confirmed repeated local opcode simplification lists do not violate the duplicate-helper constraint.
- Pure compiler_label facts require explicit extraction via shape_step_pure_pre, not an assumption that P's conjuncts are already in HOL context.

## Evidence Pointers
- episode:E0006 - full word-copy loop proved and reviewed; commit a2372a84
- tool_output:TO_unwrap-20261023T092756Z_m0132_t001 - successful build including finalised loop helper
- episode:E0007 - latest C1.3 partial source and rename cursor
- tool_output:TO_unwrap-20261023T092756Z_m0156_t001 - exact current helper source and incomplete rename
- tool_output:TO_unwrap-20261023T092756Z_m0150_t001 - markerLib.RESUME_TAC declaration
