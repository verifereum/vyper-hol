# DSE local-simulation inventory (C2.4.4)

This is a source inventory and proposed interface, **not a proof certificate**.
Frozen final theorems and execution definitions are unchanged. Line references
are to the source at this checkpoint; named definitions are stable anchors.

## Verified prerequisite interfaces

- `deadStoreElimLocations`: `dse_region_matches_nonalias`,
  `bp_segment_region_matches`, `dse_region_matches_contains`, and
  `bp_segment_size_eval` connect abstract locations to concrete regions.
  The last two require an EXACT write size, not a CALL maximum.
- `deadStoreElimLiveness`: no-read at the current index, advancement when
  not clobbering, label/CFG propagation, PHI-prefix skipping, and
  `dse_exec_block_successor` are built. Reads precede clobber tests.
- `deadStoreElimMemory`: only concrete MEMORY probes and the pending-memory
  definition are built. The universal algebra in C2.4.1 is still unproved.
- `deadStoreElimSafety`: agreement on variables, labels, allocas and allocation
  frontier transports the projected safety facts. It does NOT transport an
  arbitrary `safe_inv` to a target state.

## Essential complement to coarse equivalence

`dse_equiv` is insufficient even with equal cursors and
`dse_safety_agrees`. `dse_frame` explicitly erases `vs_prev_bb`, `vs_fmp`,
`vs_call_entry_fmp`, `vs_initial_fmp`, `vs_return_pc_token`, and
`vs_alloca_next` (deadStoreElimFrameScript.sml, `dse_frame_def` and
`dse_frame_eq_reconstruct`, lines 10-17 and 109-119).

The local relation must additionally keep ALL of these erased operational
fields equal (allocation frontier already follows from safety agreement).
GETFMP, INITIAL_FMP, RETPC_PARAM, DALLOCA, DRET and PHI selection otherwise
observe differences that pending-space agreement does not control.
`lookup_var` extensional equality gives equality of `vs_vars` through
`FLOOKUP`; it is preferable to reuse the existing frame reconstruction rather
than enumerate every retained field in each opcode proof.

## Opcode coverage

References below: E = venom/defs/venomExecSemanticsScript.sml;
L = venom/analysis/shared/defs/memLocDefsScript.sml;
B = venom/analysis/base_ptr/defs/basePtrDefsScript.sml;
F = venom/defs/venomEffectsScript.sml;
O = venom/defs/venomCallOracleDefsScript.sml.

| Family | Actual observations / writes | Static boundary and remaining proof |
|---|---|---|
| Pure arithmetic/comparison/bitwise, ASSIGN, OFFSET, BUMP | Operand evaluation and output updates only. BUMP writes two vars, no FMP read. E `step_inst_base_def`, 578-610, 698-708, 833-839, 1010-1015. | Equal lookup_var and labels imply equal operand evaluation. Preserve pending bytes, allocation map and operational complement under common output updates. Runtime matches depends on allocation map, not variable map. Malformed shape may Error; frozen theorem permits source Error. |
| Call/tx/block environment, parameters, code/data/returndata sizes | Reads retained frame fields, writes outputs; E 710-736, 845-880, 895-897, 938. DLOAD reads padded data section, NOT byte memory (963-967). | Frame agreement plus operational complement. DLOAD's static memory write/read information is conservative; it does not perform a runtime write. B 395-397 and 453-455 assign BOTH the write and read location [0,32), so no-read should rule out an outstanding nonzero footprint that DLOAD would statically clobber. This needs a lemma, not a fictitious concrete write. |
| MLOAD, ILOAD | Padded 32-byte memory read. E 617 and 953. | L `mem_read_ops_def`; B treats ILOAD as undefined read (456), conservatively forcing no outstanding nonzero footprint. Padded-byte equality must imply arbitrary `read_memory` equality, then word equality. |
| MSTORE, MSTORE8 | Write exactly 32/1 bytes at evaluated offset, expand memory. E 618-619; L 191-202. | C2.4.1 insertion for deletion, common-write algebra for retention. Exact fixed size follows from `bp_segment_size_eval`. |
| ISTORE | Byte memory write AND immutable bookkeeping (`istore`). E 954-960. | Never eligible for deletion in a single space: `effects_in_space` rejects mixed effects. Retention uses MEMORY algebra and equality of immutable bookkeeping. B may conservatively classify its location undefined. |
| MCOPY | Snapshot padded source bytes, then write destination; E 620-628 and `mcopy_def` (80). Source/dest may overlap. | L 209-213 and 281-286. No-read proof comes BEFORE overwrite/filtering. Retained copy uses equal snapshots, then common-write algebra; do not reason as incremental byte copying. A deleted copy need not have equal snapshots: its source-only write becomes a pending region. |
| CALLDATACOPY, CODECOPY, DLOADBYTES, EXTCODECOPY | Padded external source snapshot then exact requested-length memory write. E 882-893, 969-1008. EXTCODECOPY reads account code. | L `mem_write_ops_def` (214-239). Exact lengths include zero. Account-code observation requires STORAGE normalization to preserve non-storage account fields. |
| RETURNDATACOPY | If source OOB: Abort ExHalt with empty returndata. Else exact requested-length memory write. E 898-912. | Source/target returndata is equal; hence same OOB test. Only successful branch has an overwrite. Handle Abort separately rather than fabricate a write footprint. |
| MEMTOP (not a distinct MSIZE opcode) | Reads rounded LENGTH memory: n2w (((LENGTH memory+31) DIV 32)*32). E 914-918. | F read_effects MEMTOP = {Eff_MEMORY}; L has no read operands, so B returns ml_undefined (457-461). Pending entries have nonzero abstract sizes; no-read therefore forces pending=[] (needs lemma). Empty pending restores exact memory including length. Disjoint padded bytes alone do NOT suffice. |
| SHA3, LOG, RETURN, REVERT | Read padded interval. SHA3 writes hash output; LOG appends log; RETURN halts with interval as returndata; REVERT aborts with interval as returndata. E 779-799, 920-935, 1020-1042. | L `mem_read_ops_def` exact operands; LOG reverses tail and reads last operand as offset (329-336). Need arbitrary interval read congruence and per-op state framing. TERMINAL result uses dse_equiv, not a continuation pending-at assertion. |
| SLOAD/TLOAD, SSTORE/TSTORE | Current contract key lookup/update, word addressed. E 630-636; venomState `contract_storage`, `sstore`, `tstore` (258-290). | B read/write key segments size 1. C2.4.2 key normalization read/overwrite/insertion probes are prerequisites. Pending key must satisfy a<dimword and n=1. sstore changes current account storage only, leaving code/balance/nonce and other accounts unchanged. |
| BALANCE, SELFBALANCE, EXTCODESIZE, EXTCODEHASH | Read non-storage account fields; EXTCODEHASH also tests account_empty. E 869-873, 939-948. | STORAGE dse_equiv intentionally erases entire accounts, so equality of sload alone is NOT enough. Need normalization consequence for arbitrary address non-storage fields and account_empty (verify its library definition). These are not yet proved. |
| CALL/STATICCALL | Observe padded argument interval, complete accounts/transient, oracle outcomes and static flag. Oracle updates logs/accounts/transient/outcomes/requests/deletions/returndata; writes TAKE retSize actual_returnData. E 480-487, 1072ff; O 11-44. | B forces undefined STORAGE/TRANSIENT reads, so pending key list must be empty. For MEMORY, equal argument interval is enough for equal request; other fields are retained by relation. Actual return length is MIN retSize (LENGTH actual_returnData), NOT declared max. L sets iao_size=NONE (240-256), preventing static full clobber. Common actual write can remove only concretely covered entries; retaining all is safe if a monotonic common-write lemma exists. |
| DELEGATECALL | E 493-505: equal argument interval/account/transient/context fields build equal EVM states; deterministic run result; same partial return-copy behavior. | Same partial-write boundary, but proof must use concrete `run`/`extract_venom_result`, not external oracle equations. No need callee induction once constructed EVM states agree. |
| CREATE/CREATE2 | Padded initcode snapshot; oracle request includes accounts/transient; updates result/output and external fields, no return-memory buffer. O `venom_create_request_def` (76ff), E `exec_create` / `exec_create2`. | Undefined key reads force empty key pending. MEMORY input interval equality plus other-frame equality gives equal request. Preserve MEMORY pending; do not invent a return overwrite. |
| INVOKE | E `run_defs` 1664-1689: setup callee, run_blocks, bind outputs/merge frame on IntRet; forward Halt/Abort. | B reads ml_undefined in all mutable spaces, hence empty pending. After operational complement is added, input states are equal; reflexivity/determinism handles recursive execution without inventing safety for the callee. No arbitrary safe_inv transfer. |
| ALLOCA | E `exec_alloca_def` 554-570: existing inst_id reuses offset; else inserts fresh inst_id at vs_alloca_next and advances frontier; writes output; no memory expansion. | Common allocation map/frontier yields same branch and returned offset. For pending runtime matches: old allocation lookups persist under a fresh-key insert, or map unchanged under reuse. Need explicit monotone lookup preservation lemma; runtime matches does not consult changed outputs. |
| GETFMP, SETFMP, DALLOCA, INITIAL_FMP, FMP_PARAM, RETPC_PARAM, RETFMP, DRET | E 670-774. DRET packs dynamic bytes beginning at call_entry_fmp, may update memory/fmp and returns adopted cursor. | Raw frame reads use conservative B undefined memory where relevant. Need operational FMP/token complement even when pending empty. For DRET, empty pending gives exact memory before packing, so same computed return payload (including adopt_fmp). |
| JMP/JNZ/DJMP | Operand/label-based branch, sets current/prev block and cursor. E 638ff, venomState `jump_to_def`. | New strengthened shared successor lemmas and dse_exec_block_successor handle successful CFG edge with no inst_wf premise. Branch equality requires equal lookup_var/labels. Block-level theorem, not local instruction theorem, propagates suffix to target PHI prefix. |
| STOP/SINK/INVALID, ASSERT/ASSERT_UNREACHABLE, SELFDESTRUCT | E 776-824, 1044-1067: halt/abort and perhaps returndata/account balance update. | B marks storage/transient terminal commit reads undefined for STOP/SINK/SELFDESTRUCT; assertions/invalid use coarse terminal relation and no future reads. MEMORY pending may survive at halt where memory unobservable. SELFDESTRUCT requires equal account non-storage fields in storage mode, or exact accounts forced by undefined read. |
| PHI | Sequential PHI always Error (826-830). At entry `eval_phis` collects values from original input state then updates outputs in parallel (1621-1632 and preceding collectors). | Equal vars, labels, vs_prev_bb yield equal selected bindings; pending memory/account fields unchanged. Need PHI theorem separate from sequential step theorem; suffix prefix skipping already built. |
| Unsupported/malformed branches | E default Error; explicit operand/output validation at each branch. | Source Error alternative suffices. No instruction well-formedness hypothesis may be inferred from wf_function. |

## Two integration issues requiring strategist decisions

1. **Erased operational fields:** pending_space + safety_agrees + cursor equality
   is not sufficient, as above. This is a missing simulation invariant, not a
   frozen-theorem counterexample; initially the states are identical and the
   deleted opcodes do not update those fields.
2. **A deleted clobber cannot simply retain all old suffix witnesses.** If an
   old footprint is statically clobbered by another removed write, old
   suffix_dead at the old location need not hold at SUC idx. The new write's
   after-store suffix witness can replace/subsume covered old obligations;
   that is a spatial union argument, NOT synchronizing the memories. For
   nonclobbered entries use dse_suffix_dead_step. A proof of insertion plus
   union subsumption (coverage plus endpoint bound) is missing from C2.4.1.
   Conversely, for retained partial writes it may be simpler to keep every
   entry, using a common-write preservation lemma with unchanged P.

## Proposed exact local signatures (for strategist approval, NOT declarations)

The names below denote proposed definitions, not existing HOL constants:

- `dse_operational_agrees s t` is conjunction of equal current_bb, inst_idx,
  prev_bb, fmp, call_entry_fmp, initial_fmp, return_pc_token.
- `dse_local_agrees sp P s t` is pending_space sp P s t /\
  dse_safety_agrees s t /\ dse_operational_agrees s t.
- `dse_local_safe bp fn inst s` abbreviates the exact projected safety
  conjunction: alloca_inv s; nonwrapping allocation bounds; bp_ptr_sound bp s;
  bp_ptrs_bounded bp fn s; bp_accesses_in_own_alloca bp inst s.
  This is obtained from an original-run witness, not assumed on arbitrary
  target states.

Proposed retained nonterminator OK theorem (all free variables universally
quantified; no lets):

```sml
dse_local_agrees sp P s t /\
dse_pending_at (cfg_analyze fn) bp sp fn bb s.vs_inst_idx P s /\
wf_function fn /\ MEM bb fn.fn_blocks /\
get_instruction bb s.vs_inst_idx = SOME inst /\
dse_local_safe bp fn inst s /\
~is_terminator inst.inst_opcode /\
step_inst fuel ctx inst s = OK s1 ==>
?v P1. step_inst fuel ctx inst t = OK v /\
  dse_local_agrees sp P1
    (s1 with vs_inst_idx := SUC s.vs_inst_idx)
    (v with vs_inst_idx := SUC t.vs_inst_idx) /\
  dse_pending_at (cfg_analyze fn) bp sp fn bb
    (SUC s.vs_inst_idx) P1 s1
```

This isolates source `safe_inv` preservation to the enclosing run proof.
P1 must be computed/certified from common actual overwrite and static liveness;
existence without those constructive boundaries is NOT yet de-risked.

For deletion use the same prefix hypotheses, replace the nonterminator premise
by selection + `all_dead_stores dead_ids (cfg_analyze fn) FEMPTY bp sp fn`,
require `dse_inst dead_ids sp inst = mk_nop_inst inst`, and conclude:

```sml
?P1. dse_local_agrees sp P1
       (s1 with vs_inst_idx := SUC s.vs_inst_idx)
       (t with vs_inst_idx := SUC t.vs_inst_idx) /\
     dse_pending_at (cfg_analyze fn) bp sp fn bb
       (SUC s.vs_inst_idx) P1 s1
```

To avoid accidental inclusion of existing NOPs, actual deletion should instead
be expressed by `inst.inst_id IN dead_ids`, memory-def opcode, empty outputs,
effects_in_space, and the eligibility tests from `dse_inst_def`. Strategist
must fix the final selection premise before proof work.

Non-OK retained branch under the same prefix hypotheses:

```sml
(~(?v. step_inst fuel ctx inst s = OK v)) ==>
  (?e. step_inst fuel ctx inst s = Error e) \/
  lift_result (dse_equiv sp) (dse_equiv sp) (dse_equiv sp)
    (step_inst fuel ctx inst s) (step_inst fuel ctx inst t)
```

This keeps equality of abort kind and IntRet payload via lift_result. Successful
jump OK must additionally preserve operational agreement and transfer live
pending obligations through the checked CFG edge at block level.

Proposed PHI boundary (same bb on both sides because stores never change PHIs):

```sml
dse_local_agrees sp P s t /\
dse_pending_at cfg bp sp fn bb 0 P s /\
eval_phis s bb.bb_instructions = OK s1 ==>
?t1. eval_phis t bb.bb_instructions = OK t1 /\
  dse_local_agrees sp P
    (s1 with vs_inst_idx := phi_prefix_length bb.bb_instructions)
    (t1 with vs_inst_idx := phi_prefix_length bb.bb_instructions) /\
  dse_pending_at cfg bp sp fn bb
    (phi_prefix_length bb.bb_instructions) P s1
```

## Relocation and remaining gaps

`dse_dead_store_step_sim_ok` (deadStoreElimProofsScript.sml 197-229) depends on
local effects classification helpers (75-190) plus shared frame/effect facts.
It cannot simply be imported downstream without a cycle. Move the contiguous
classification/deletion boundary to one helper only if needed; it does not
supply pending-byte or expansion conclusions. Existing `dead_ids` parameter
is unused. No new duplicate coarse-deletion lemma is warranted.

Besides C2.4.1-.3, strict missing boundaries are: padded interval read equality;
common write with unchanged pending list; union subsumption for deleted
clobbers; normalization preserves all non-storage account observations;
undefined abstract read forces empty pending; operational complement algebra;
old allocation-map lookup preservation; per-family execution congruence.
The arbitrary-state PHI statement also needs a general eval_phis success
congruence theorem (search before adding). This inventory does not certify
these statements and does not lower opcode integration risk.
