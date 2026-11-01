# Pinned FMP interface comparison (C1.1)

Reference: VYPER_PIN cd74ce4f57e3771aeeab8f061fa3be45bfe8a29c;
source snapshot `.agent-files/vyper-reference/vyper` supplied by the lead.
This document records source comparison, not a theorem of Python/HOL equivalence.
`fmpReclaimProbeTheory` supplies executable HOL reference cases, not production
reclaim correctness. No executable production definitions changed in C1.1.

## Exact Python boundaries

* `passes/fmp_lowering.py:384-399`: meet is common **top** segment plus capture
  union. Python stores bottom first; HOL stores newest first, so HOL common
  prefix is the correct orientation. At joins do not keep the common bottom.
* `:401-469`: one `_step` is used by the fixpoint and emission; pop before the
  instruction's own action. DALLOCA pushes after popping; GETFMP adds capture;
  SETFMP clears both lists; RETFMP does not clear/pin state; publishing INVOKE
  clears both lists after pre-instruction popping. DRET is rejected earlier.
* `:482-490`: only DALLOCA, JMP/JNZ/DJMP, resolved needs-FMP INVOKE reclaim.
  Unresolved invokes are neither reclaim points nor clears. There is no
  synthetic block-end restore (including terminal exits).
* `:492-540`: can_reclaim false or capture veto disables all popping. Otherwise
  stop at first unknown allocation or live/pinned allocation. Restore to the
  lowest popped mark, retaining everything below it. Captures are not marks.
* `:555-577`: mark resolves to exactly one possible pointer whose allocation
  instruction is DALLOCA. Allocation liveness checks every live variable's
  possible bases, not just mark variable liveness.
* `:603-628`: escaping uses are occurrence-sensitive! Exempt propagation ops
  ADD/SUB/ASSIGN/PHI/BUMP/DALLOCA/ALLOCA; otherwise subtract occurrences in
  `memory_read_ops` and `memory_write_ops` ofst/size/distinct-max-size positions.
  Merely recognizing an address operand by equality is insufficient:
  MSTORE(ptr,ptr) still escapes as the stored value.
* `:630-678`: capture derivation is a fixpoint over single-output
  ADD/SUB/ASSIGN/PHI only (not allocation ops). Pin roots of derived escaping
  operands, not all directly-used capture roots. Veto uses live DERIVED vars.
* `analysis/liveness.py:43-61,89-93`: live_vars_at is before original instruction.
* `analysis/dynamic_memory.py:49-80`: needs-FMP closes transitively over calls;
  publishes is direct (DRET/RETFMP), sealed signatures authoritative.

## Existing HOL incompatibilities requiring implementation interfaces

1. `fmp_transfer` has only instruction/state inputs; it must gain static
   liveness, allocation/capture facts and callee summary access. It currently
   never pops, permanently disables reclaim on SETFMP/RETFMP/DRET, and does not
   clear stack/captures on SETFMP or publishing INVOKE.
2. `df_fold_forward` stores pre-instruction state at original index i and exit
   state at n. Its callback receives the instruction but not index. Either a
   validated per-block instruction-id-to-point lookup or an indexed fold adapter
   is needed; do not confuse inst_id with instruction-list index. The new step
   must be shared by analysis and candidate walk.
3. Existing `fmp_target_pinned`/`fmp_direct_memory_use` omit CALL/CREATE and size
   positions. Reuse the memory-access descriptions in `memLocDefs` (already
   include CALL/STATICCALL/DELEGATECALL and CREATE/CREATE2), but count safe
   operand occurrences. Do not retain the old whitelist as parity-equivalent.
4. `fmp_capture_escaped` counts any direct use; capture veto ignores derived
   liveness. `fmp_reclaim_entry_ok` currently checks ALL function captures, even
   ones not in scope at the point or cleared by SETFMP. Must check current state.
5. `basePtrDefs.bp_handle_inst` currently seeds only ALLOCA, not DALLOCA/BUMP;
   thus plugging existing `bp_analyze` straight into Python's allocation query
   would make every dynamic mark unknown. Also its offsets are naturals with
   subtraction underflow mapped to unknown, versus Python integer offsets.
   Reclaim only needs projected allocation identities, not exact offsets.
   Strategist must select a task-local projected-base interface or authorize
   broader basePtr repair and its downstream proof closure before implementation.
6. `fmp_block_restore` only exits at n, requires whole stack dead. Replace with
   original-instruction-point scan; no restore at n. `fmp_lower_blocks` currently
   appends endpoint restores; it must instead select and emit before each
   original instruction and consume the selected entry once.

## Probe coverage and limits

`fmpReclaimProbeScript.sml` uses eligibility/veto parameters to isolate stack
and instruction-effect behavior. Checked EVAL cases cover partial pop in both
live/dead orders, unknown blocker, lowest target, capture veto, push-after-pop,
GETFMP, SETFMP, needs/publishes/unresolved INVOKE summaries, all three branches,
RET (no endpoint), unreachable and reclaim-disabled states, join orientation
and capture union. A loop-order capture derivation requires re-iteration;
a live derived variable vetoes pop. Separate checked probes demonstrate old
MLOAD capture over-pinning, old CALL allocation pinning, occurrence counts,
and original dataflow boundary indexing. They do NOT test production capture
escape or exact base-pointer equivalence, which still require the interfaces
above. All probe theorems have their tags audited at theory end (DISK_THM only).

## Existing proof coverage and BUMP-dependent build closure

`fmpLowerProps` has structural no-raw, signature sealing, metadata and
idempotence properties only. `fmpLowerInvokeProps` proves invoke convention
shape facts; no full DALLOCA lowering execution simulation theory exists.
`fmpReclaimProps` proves successful analysis implies checked plan/target
postconditions and determinism, NOT memory preservation or Python equivalence.
Do not report their successful builds as operational soundness.

Primary explicit arithmetic consumers: `emitSim`'s `bump_round_word_correct`,
`bump_emit_ops_asm_trace`, `bump_emit_sim_from_stack`, `bump_emit_sim`; BUMP
integration in `genBlockSim` around lines 4264-4939; `fmpWfDefs`/`fmpWfProps`;
`mem2varBlockSimHelpers` around 1816 (distinguish DALLOCA from BUMP before edits).
Structural BUMP branches also occur in `venomExecProofs`, `venomMemProofs`,
`execEquivProofs`, `execEquivParamHelpers2`, `allocaRemapProofs`,
`dftCommutation`/`dftBlockSim`, `ssaRenamedSim`, `dfgSoundStep`,
`overflowElimHelpers`, `tailMergeStep`, `prevBbIndep`, `instIdxIndep`.

Build these primary logical targets after semantics changes, then their
consumers: venomExecProofsTheory, venomMemProofsTheory, fmpWfPropsTheory,
execEquivProofsTheory, execEquivParamHelpers2Theory, allocaRemapProofsTheory,
mem2varBlockSimHelpersTheory, dftCommutationTheory, dftBlockSimTheory,
ssaRenamedSimTheory, dfgSoundStepTheory, overflowElimHelpersTheory,
tailMergeStepTheory, prevBbIndepTheory, instIdxIndepTheory, emitSimTheory,
genBlockSimTheory, fmpLowerPropsTheory, fmpLowerInvokePropsTheory,
fmpReclaimPropsTheory, evalCompilerAllocationBudgetTheory.
A project-root build is still necessary to expose implicit unfolding consumers.
Ceil32 occurrences in DRET packing and raw DALLOCA must NOT be replaced globally.
