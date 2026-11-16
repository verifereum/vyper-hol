# D0002 allocation-frame permission audit (C1.16)

## Scope and verdict

Source-only audit, 2026-11-16. Base: fold7
`8541754d39bdf794d441e0d19fd64a00cf9c0a04`. Integration and audit HEAD:
`3c90030f1a1dc1c9b756fa35b4baf97a33647608`.

No concrete use of the superseded **alloca_inv alone implies
allocas_below_fmp** permission was found in the inspected committed task-owned
sources. This is NOT theorem qualification, proof completion, acceptance of a
staged port, or release of any wait. Existing unfinished proofs are untouched.
Only this audit document is added by C1.16; no theorem/header/provider is edited.

The corrected test is at the actual stepped target state: retain no-dalloca,
or obtain the conditional allocation bound from a direct state relation/post,
or from fmp_room together with alloca_inv. A consequent-only relation or an
unwitnessed all-H implication is not such evidence. Reachable-instruction
no-wrap is a separate resource.

## Exact committed snapshots inspected

The branch refs were observed through supported read-only git operations; no
other lane's worktree was read or synchronized for this audit.

| Lane / PLAN ownership | Committed snapshot | Owned-path comparison with audit HEAD |
|---|---|---|
| L0002 / C1.2 local entry | `8f3a44cb2105e79b5e12d9099fd6a89c904819b1` | No differences in For/checked-entry paths at this snapshot |
| L0003 / C1.3 immutable entry | `057d1191402a953b98be0617384fbbc5def1d79f` | No differences in those paths at final snapshot comparison |
| L0005 / C1.8 RaiseReason producer | `9d1d32cef255a440808b0f49bdea26f709dd6290` | 12 new RaiseReason scripts and changed root, not yet integrated |
| L0021 / C1.1.2.2 range exit bridge | `ce0376f0e0800fb4deee5bff5a4753efe1fceca4` | No committed For/checked-entry differences |
| L0027 / C1.5.8 local scalar control | `6ea2434ceaaeebb0c29dc97fc815d69f95c756b5` | New LocalControl; snapshot predates integrated LocalInstall/LocalRecovery |
| L0028 / C1.5.4.6 local copy | `cabcb0ca9c814fe4a75e6a3af591adfa63cec671` | New LocalCopy; snapshot predates integrated LocalInstall/LocalRecovery |

Older snapshot absences are not proposed deletions. Uncommitted live edits,
subsequent revisions and any not-yet-published work are **pending, not audited**.
Their owners must apply D0002 before their own ordinary build/publication.
Ownership above comes from the structured PLAN/lane-status interface; the named
owner-table file was absent here and its attempted external checkout read was
refused. No claim is made to have inspected that unavailable inventory or to
have changed any ownership.

## Premise-provenance ledger

| Declaration / source family | Actual target state and resource | Audit classification / owner |
|---|---|---|
| Range/array scalar paths, entry/start/exit/copy families; `for_checked_entry_ghost_packet` | Their explicit `~ctx_has_dalloca ctx` is retained, including helpers also taking `alloca_inv s`. No allocation inference from alloca_inv is needed. | Retained no-dalloca. C1.1/C1.2/C1.3 and existing helper producers; no restatement requested. |
| RangeStart `for_range_store_path_canonical_full` and `for_range_literal_body_start_full` | Store state `s` / post-condition state `sc`. Store helper retains no-dalloca. Body-start obtains an actual `H0` from storage_trace_domain before using stmt_state_rel at `s`; derives alloca_inv at `sc` by update/jump field preservation. It does not derive the conditional bound from that invariant alone. | Retained no-dalloca plus witnessed relation. Existing range owner C1.1. |
| Range `body_for_range_checked_full`, first expression | Initial `s0`. expr_sim_full is invoked inside stmt_frag_full elimination, whose inputs explicitly contain conditional allocation and reachable dalloca_no_wrap at `s0`. | Direct input resources, not an inference from vacuous all-H posts. C1.1. |
| Same theorem, second expression | Selected first-expression endpoint `t`. `storage_trace_horizon mid.storage_trace` is validated from the supplied domain before the first post is used. No-wrap is derived using body_inv_no_dalloca and reachable instruction membership. | Witnessed post at the actual endpoint; body_inv shortcut. C1.1. |
| RangeBody / ImmBody callback normalization | Body start state. Existing no-dalloca premise is retained; reachable-instruction no-wrap comes from absence of DALLOCA and membership, not alloca_inv. | Retained no-dalloca. C1.1 / C1.6 producer family. |
| LocalBody `for_array_local_body_outcome_full` | `sstart`. Explicit `(ctx_has_dalloca ctx ==> allocas_below_fmp sstart)` and `frag_reachable ... sstart ... ==> dalloca_no_wrap ...` inputs are passed to stmt_frag_full. Normal endpoint `t` and exceptional Halt/IntRet bounds remain in output. | Explicit resources even without a domain witness. C1.5.7 producer (L0026, integrated). |
| LocalRecovery `for_array_local_callback_pop_full` | Target `t` unchanged by source scope-pop transport. Conditional allocation at `t` is an input and remains an output; the post-pop source relation does not substitute for that input. | Explicit endpoint resource preserved. C1.5.4.7 producer (L0029, integrated). |
| LocalHandler and LocalContracts callback interfaces | Exceptional state `u` / initial `s0`. Conditional exceptional bounds are retained; callback signature includes initial conditional allocation and reachable no-wrap. | Interface text only, not a proof of unfinished consumers. Existing C1.5 owners. |
| Staged LocalControl `for_array_local_condition_full`, `scalar_seq_intro`, `for_array_local_increment_full` | States `cc`, `s`, `dd`. Every instruction-executing helper retains `~ctx_has_dalloca ctx`. | No alloca_inv-only relaxation. L0027 / C1.5.8. |
| Staged LocalCopy `for_array_local_copy_checked_full` | Copy origin `s`. Explicit no-dalloca covers word/bytes/bulk paths. Memory-code helper only describes emitted opcodes and executes nothing. | Retained no-dalloca / zero execution. L0028 / C1.5.4.6. |
| AssertReason `compile_assert_reason_frag_full_from_raise`, condition | `s0`. Conditional allocation and reachable no-wrap are present from stmt_frag_full when expr_sim_full is instantiated (direct matching of inputs). | Direct input resources. C1.9 (L0006, integrated). |
| Same theorem, selected branch and false entry | Selected endpoint `t`; false start `jump_to entry.cs_current_bb t`. Domain validates the chosen horizon before the condition post is used. False-entry no-wrap is derived from body_inv_no_dalloca and frag_reachable_members. True branch preserves allocation fields through jump. | Witnessed endpoint post; body_inv shortcut. C1.9. |
| Staged RaiseReason `compile_raise_reason_nonliteral_frag_full` | `s0` for expr_vv_sim_full. stmt_frag_full elimination supplies conditional allocation and reachable no-wrap at exactly `s0`; the normal continuation selects a valid horizon from domain before using vv_post at `t`. | Direct inputs / witnessed endpoint post. L0005 / C1.8. |
| Staged RaiseReason Head / HeadFrame / HeadGhost / HeadValue / Tail / LiteralEncoder | Execution helpers retain no-dalloca. Frame/value helpers either use direct stmt_state_rel/vv_post at the same state or consume an existing run / inst_seq_ptr certificate, rather than derive allocation from alloca_inv alone. | Retained no-dalloca or direct post/certificate. L0005 / C1.8. |
| Staged `reason_literal_entry_source_family` and Continuation | Literal origin `s`, continuation endpoint. Explicit no-dalloca in literal entry; domain yields a real horizon before state-relation extraction and unique tuple selection. Continuation likewise instantiates its domain-backed post. | Retained no-dalloca / witnessed post. L0005 / C1.8. |
| Staged RaiseReason Source, LiteralLayout, Literal/root joins | Source read/string facts and compiler-layout facts execute no new target instructions. Root selects literal/nonliteral fragment producers without weakening their inputs. | Zero-execution or composition only; no affected permission application. L0005 / C1.8. |
| Frozen For/Raise roots and For/reason bodyFullCases hunks at audit HEAD | No differences from fold7 in these files. They are not newly qualified by this audit. | No in-run permission change here. Existing root/case owners. |

The full-expression requirements were checked directly against
bodySimFullScript.sml: expr_sim_full lines 103-104, expr_vv_sim_full 155-156,
and stmt_frag_full 222-223 carry the same separate initial conditional bound
and reachable no-wrap resources. The all-H state relation is an additional
field, not a substitute for either.

## Evidence and limits

- E0042 records the initial bounded scan and inspected RaiseReason staging.
- `TO_statement_cases-L0031-20261116T044024833249Z_m0016_t006`: exact audit/base revisions.
- `..._m0014_t002`: lane branch snapshots (full prefix as above).
- `..._m0015_t001` through `..._m0015_t006`: active snapshot comparisons and remaining staged Source/Layout/root reads.
- `..._m0016_t001`, `..._m0016_t002`: staged control/copy declarations.
- `..._m0015_t007`, `..._m0016_t005`: judgment input definitions.
- `..._m0017_t003`: RangeStart actual-horizon and store-state provenance.
- `..._m0018_t003`, `..._m0018_t005`: LocalBody and AssertReason resources.
- `..._m0019_t001`, `..._m0019_t002`: prior staged nonliteral/literal provenance.
- `..._m0019_t004` through `..._m0019_t006`: final local/immutable snapshot and unchanged root/case comparisons.
- `..._m0017_t004`: 36 changed owned files versus fold7 (mostly new For helpers).
- `..._m0024_t005`: no tracked edits before adding this ledger.

A bounded ordinary `holbuild(targets=["forPtrCheckedEntryGhostTheory"])`
passed (target restored from cache, finished in 1.876 s):
`TO_statement_cases-L0031-20261116T044024833249Z_m0020_t001`, tail reproduced
in `..._m0024_t004`. This is only a current smallest-helper build check, not
qualification of the family or staged branches. No broad known-red cone was
retried. No new/edited HOL helper requires certification from this diagnostic.

No concrete repair is requested by this snapshot audit. Pending live edits
remain with their existing owners, not a new residual. D0002 must continue to
be checked in their actual consumers. All For unfinished proof obligations,
the OPEN memory-iterable resource, Log owner delivery, SEQ-6043 publication
and all operational waits retain their existing dispositions. This document
does not release them or reclassify accepted proofs.
