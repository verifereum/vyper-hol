# SEQ-3861 remaining local-hold provenance inventory

Date: 2026-11-16. Component: C1.12.1. This is a **docs-only diagnostic receipt**, not a supplier delivery, approval, proof check, or receiving-cone qualification. No hold is removed here. C1.7's G0001 wait and C1.12.2's dependency on C1.7 remain unchanged.

## Scope and reproducibility

The inventory accounts for the TASK's **32 held root/Resume bodies in 17 owners**, including its later additions. It does not inventory every pre-existing admission in those owners. Commented original proofs and orphaned Resumes are not additional held bodies.

Source snapshots:

- Declaration baseline `B = 012ecab5dd7edcdad270b6859900c1ab49819b5b`.
- Local stand-in `H = 810aa0e6ea1515c8c53ee3b50ccbdd649ebc1f4f` (never deliver).
- Inventory checkout `a804794483a1eecca07050c95ddf040103f6ed64`.
- All 17 current owner blobs equal H's blobs at the inventory snapshot. The table below records both B and H identities; use `git rev-parse REV:path` to reproduce them and `git diff --unified=0 B C -- path` for each candidate C's declaration comparison.
- TASK reports 217 declaration headers in these owners identical to B, citing `full700652-declaration-audit.json`. That receipt was **not found in lane discovery**; this document does not fabricate or independently certify its complete 217-header audit. The per-candidate comparisons below instead use the available source deltas against B. Candidate differences from B must not be excused by the TASK's B-to-H statement-identity claim.

Historical evidence was retained in component episode E0004. Tool evidence keys below use suffixes of `TO_seq3861_calldata_family-L0008-20261116T141155632895Z_`:

- `m0005_t001`: B/H raw blob pairs; `m0007_t001`: current blobs match H.
- `m0008_t001`, `m0008_t002`: Return and Intcall candidate source comparisons.
- `m0008_t003`, `m0008_t004`, `m0008_t006`: RawLog, AugAssign and TupleHead declaration differences.
- `m0010_t004`: TuplePlaces proof-only delta and TupleMixed helper-header difference.
- `m0011_t009`: FullAssign candidate's two qualifier-only edits.
- `m0020_t005`: three-commit exclusion footprint.
- `m0021_t006`: additional exact candidate blob identities.
- `m0021_t007`: complete bounded EmptyCase diff, including ancestor changes and proof edits, but no theorem-header change.
- `m0022_t001`: candidate commit changed-path lists.

## Exclusion boundary (C1.7 owns it)

Only changed-path metadata was enumerated here; excluded suppliers' theorem comparisons were **not** repeated.

| Supplier commit | Changed files under `lowering/` |
|---|---|
| `a354291137ecf9a2de4c1e4c5d99d4c47eff07de` | `assignEffectfulIndexNonemptyScript.sml` |
| `d4b90c77a6a439dbf7285bee2d97227b8802a985` | `evalNoHaltScript.sml`, `placeRelayoutBodyScript.sml`, `placeRelayoutFragScript.sml`, `placeRelayoutGasComposeScript.sml` |
| `2f5e63a3039469d1826809403ca697bd2504572e` | `assignEffectfulIndexNonmutatingScript.sml` |

The middle commit moves `widened_place_raw_rhs_outcome` to `placeRelayoutGasCompose`; this file is explicitly excluded. Additionally, `stmtSimAssignPlaceScript.sml` imports the excluded effectful suppliers and is conservatively **adapter-overlap excluded pending reconciliation**. Any additional direct adapter identified by C1.7 remains excluded too: this is not an exhaustive proof that all other files are dependency-independent. In particular a file-disjoint candidate is not a dependency-independent or receiving-qualified proof.

No instruction about taking the full supplier set is interpreted here as approval of added `halt_exit` clauses. This receipt does not release any wait.

## Owner source identities

All paths below are relative to `lowering/`. An owner's H identity is also its current identity at the inventory snapshot. These identities cover whole files, not individual theorem text.

| Owner path | B blob | H/current blob |
|---|---|---|
| `assignEffectfulIndexEmptyCaseScript.sml` | `634b1bf5ce67f2193bf0892887f10b55c275e016` | `5c574fb657a063506854cff12a9fed39b1726015` |
| `assignEffectfulIndexNonemptyScript.sml` | `9c9b59b0fc097da09a70da4cfce18cda8fde2b86` | `6c752aaad35642d9d89b520e0d26eeddfbd04dd7` |
| `assignEffectfulIndexNonmutatingScript.sml` | `869cf8c1bc10afdde720019197afa8a48da85c6e` | `edfea95dcab8bb5f0c04480ca485b593dc8c0fe5` |
| `bodyFullAssignScript.sml` | `7a9fa862ca158ca91e7a766798a3f5e92c9d65c8` | `aa8dc00afdcee4a725f1b912796f23887cc6ae41` |
| `bodySimCallIntcallScript.sml` | `0f3d785c678b18bae5da6ebc9fcb7ca0b3c3f92e` | `35223a8eb608fc8731f57421dc7f029c70498ee3` |
| `bodySimCallRawLogScript.sml` | `352cc3cf1acec4d0946f2639b2514d22173b2269` | `6a296088545c23bed88aaa063b0cd533e7c43506` |
| `bodySimDeclCasesScript.sml` | `818db4c9980aaa05aa33a01971bf658349dbff23` | `4082fe5af9b3815c52750ef0d3a1ba9ddc8aabc3` |
| `bodySimRawLogTopicsScript.sml` | `2e8135606f7f51a7f5ff56e80dccc3a86b4b1894` | `87d7dc0831224f368d19e4ac0497fc1475bde701` |
| `bodySimStmtCasesScript.sml` | `ed72c861f273d54feffc5854d4ea1d395e55ca5d` | `2fef86f8a09508810402cb2651171a5fbbf3c58e` |
| `externalReturnValuedFullScript.sml` | `72fbfddff5770c459e7e0bd8dbdd0f420a3964d2` | `f52b6d2e5b3ba557292bb7b20ec0d88d428301e3` |
| `placeRelayoutBodyScript.sml` | `ca51f8043825d02d6779e661dfea6dd547566922` | `888a568d571a1daab0354fbffb88ec395fd16edf` |
| `stmtSimAssignPlaceScript.sml` | `f0534aaac35c4be7b6900a9a84035aee3004b14f` | `62e7ae64027248bcf96330cc057b1f3ef1b8d08d` |
| `stmtSimAssignTuplePlacesScript.sml` | `425df145ae243133141860b529e8727fcb48588b` | `5a1b22686936901876d8f0ead3f8f9f224f32b2a` |
| `stmtSimAugAssignPlaceStorageScript.sml` | `613b7fc671f35014450d61b63074c30a097cc3f0` | `ad99b7c25d08500c412269740cfb983e187325c1` |
| `tupleAssignImmutableDeployScript.sml` | `67d01af09e104acf189b36adf01a1d36347292e8` | `068504dca0e3450364423ed222bc052afa41a8ca` |
| `tuplePlaceHeadOpenScript.sml` | `2285677f545bf943bf98ef26741eed8d8defb632` | `329de1ceb597910003a990b14631e6f5b449d26d` |
| `whitelist/whitelistForIterScript.sml` | `88b64705d088f95f3a4a224331ade9a65bb6d041` | `e4f0b3a18567326394fe65fc04cdc8a30c1cd6e2` |

## Candidate source manifest

Each ref is a published `origin/bot/sol/` ref observed during the bounded history inspection. Immutable commit IDs and blobs, rather than a moving ref alone, identify the comparisons. No branch is merged by this receipt.

| Key | Published ref suffix; immutable candidate commit | Owner candidate blob(s) | Declaration comparison against B; footprint caveat |
|---|---|---|---|
| R | `seq-3979-return-rs10`; `61804076a0f7b010ef7daab33f2bee0bf4476f37` | Return: `81040e67a3f29a02c18405698467825b3487f6e8` | Proof bodies only; no declaration change. Candidate commit changes only this disjoint file. All three held allocation Resumes occur in it. |
| I | `seq-4913-s1-exit`; `270a23fb9f43b2b0f3a14e3f3351f8be09fe372f` | Intcall: `5474c4df8d975a409c199e5018cba61e01fb07ac` | Held helper and public case headers unchanged; owner diff is proof-only. Commit additionally changes `bodyIntCallSeamsScript.sml`; no excluded path in its direct changed-path list, but that extra source/dependency closure is not qualified here. |
| L | `seq-4023-rawlog-topics-receiver`; `88ae9c121310df28e1b288a70090e2158b2edc14` | CallRawLog: `3bc5f782175dfe4c447829e8f6e5e31abf208cfe`; Topics: `0ea74de0912c5ffb70982aa949572e4bee392153` | **Unequal declarations**: dynamic/fixed32 predicates change from `expr_exit rr r` to `expr_exit rr r /\ halt_exit H cx ee rr r`; Topics changes `wb_args_exit rr r` to that predicate conjoined with `halt_exit`. `raw_log_body_expr_ok` header unchanged. Commit's two paths are disjoint from the exclusion list, but header approval is unresolved. |
| A | `seq4078-place-storage-checked`; `3a0e0f6b8fac04282b7ecad3a9755a08d8466e00` | AugAssign: `e50dd4649a024ab7598226366b467e8188c2b23e` | **Unequal local helper declaration**: `aug_place_storage_binop_store_outcome` exit conclusion adds `halt_exit H cx ff res r` alongside the all-tail `stmt_exit`; public compile header unchanged. Also changes `augAssignPlaceTopMemoryScript.sml`. No excluded path directly changed, but approval unresolved. |
| T | `seq-4126-tuple-halt-head10`; `e968dfdfa97d8de705c09f6734c45aa5fc4b5b0a` | TupleHead: `655f5dbb3eac271e2634c606f4849dfbcb90ff13` | **Unequal declaration**: compilation premise's `let` replaced by an expanded expression; premise and conclusion exceptional predicates both add `halt_exit H cx ee res r`. Single disjoint changed file, not a statement-identical replacement. |
| P | `seq-5208-roots-delivery`; `b571828806915256e86f587a05be089ddfaa689b` | TuplePlaces: `39f5660d2eb5413898066e7ff74a1adab20fb58c`; TupleMixed: `5fd13703eeae5a0ca07a48700dfb2a505d0673fd` | TuplePlaces owner diff is proof-only, headers unchanged. TupleMixed public compile header unchanged, but helper `tuple_immutable_unpack_outcome_open` adds `halt_exit H cx ff res r` to `expr_exit res r`. **Whole candidate cannot be taken as a disjoint commit**: its tip directly changes excluded adapter `stmtSimAssignPlaceScript.sml`; the compared tuple blobs are inherited in this branch snapshot. |
| E | `seq6065-emptycase-delivery`; `7ffb4a500e4bfed932956abcee047cf697a80b5a` | EmptyCase: `5f31ef8b0bdf06cc469c4a19943b60e286193414` | Held theorem header unchanged; no definition/header change in full owner delta. Ancestors expanded (including `placeRelayoutOutcome`, `assignPlaceEmptyStore`, `vyperStorageTrace`); remaining changes are proofs. Direct commit changes only this disjoint file; dependency qualification remains required. |
| F | `seq-4232-storage-tail-head10`; `ef718bef2033a2b2710d59f56822a7f1e889bdee` | FullAssign: `debea162026f9f35780249efc02cdf672b0cf4b5` | No declaration change, but only two `expr_sim_inv_local` lemma-qualifier substitutions against B; **not evidence that seven held proofs are repaired**. Tip changes five other storage/tail sources (see evidence `m0022_t001`), not this owner. Repair completeness unresolved. |

The above direct-commit footprints are not claims about all commits brought in by merging those branches. In particular P's excluded adapter and unknown ancestry prevent claiming a ready-to-apply disjoint branch set. Local commits `2efba0910` and `c68370ac9` had no containing remote branch at inventory time and are **not** credited as published candidates.

## Complete held-body partition

Every row inherits its owner path and B/H blob provenance from the source table. Counts are held bodies, not declarations. `Mapped` means an identified declaration-compatible owner source exists, not that the proof passed on this receiver. `Unresolved` includes incompatible headers and insufficient repair evidence. Excluded rows intentionally have no new supplier declaration comparison here.

### Excluded: 4 bodies in 4 owners

| Owner | Held theorem/body | Reason |
|---|---|---|
| `assignEffectfulIndexNonempty` | `assign_place_mutating_nonempty_case_with_store` | C1.7 three-commit supplier set. |
| `assignEffectfulIndexNonmutating` | `assign_place_nonmutating_widened_case` | C1.7 three-commit supplier set. |
| `placeRelayoutBody` | `body_assign_nonimmutable_widened_place` | Directly changed by middle supplier commit. |
| `stmtSimAssignPlace` | `compile_assign_place_case` | Direct-adapter overlap; conservative exclusion pending reconciliation. |

### Mapped, file-disjoint declarations: 7 bodies in 4 owners

| Owner | Held theorem/body | Candidate; qualification caveat |
|---|---|---|
| `externalReturnValuedFull` | `return_selected_valued_frag_full[buffered_normalize_allocation]` | R; unchanged header, proof replacement identified. |
| `externalReturnValuedFull` | `return_selected_valued_frag_full[buffered_shared_allocation]` | R; same. |
| `externalReturnValuedFull` | `return_selected_valued_frag_full[raw_allocation]` | R; same. |
| `bodySimCallIntcall` | `expr_sim_of_vv_sim_stack_memory` | I; unchanged header, proof replacement identified. |
| `bodySimCallIntcall` | `intcall_body_expr_ok` | I; same. |
| `stmtSimAssignTuplePlaces` | `compile_assign_tuple_places_stmt_frag` | P; file source is disjoint and proof-only, but **whole branch/commit is not disjoint**. |
| `assignEffectfulIndexEmptyCase` | `assign_place_effectful_empty_case` | E; unchanged header, expanded imports require receiving qualification. |

### Unresolved: 21 bodies in 9 owners

| Owner | Held theorem/body | Candidate comparison / unresolved artifact |
|---|---|---|
| `bodyFullAssign` | `body_assign_local_word_full` | F: exact headers retained, only qualifier edits; repair sufficiency unestablished. |
| `bodyFullAssign` | `body_assign_local_widened_full` | F: same; original suspended continuation is not independently credited. |
| `bodyFullAssign` | `body_assign_toplevel_word_full_framed` | F: same. |
| `bodyFullAssign` | `body_assign_toplevel_word_full_residual` | F: same. |
| `bodyFullAssign` | `body_assign_toplevel_word_full` | F: same. |
| `bodyFullAssign` | `body_assign_attr_storage_full` | F: same; later local unpushed fix is not a published replacement. |
| `bodyFullAssign` | `body_assign_toplevel_word_full_after_rhs` | F: same; late hold included. |
| `tupleAssignImmutableDeploy` | `compile_assign_tuple_mixed_stmt_frag` | P: public header unchanged, helper adds `halt_exit`; whole branch also touches excluded adapter. |
| `bodySimCallRawLog` | `raw_log_dynamic_frag` | L: changed exceptional predicate, no statement-identical replacement. |
| `bodySimCallRawLog` | `raw_log_fixed32_body_frag` | L: same. |
| `bodySimCallRawLog` | `raw_log_body_expr_ok` | L: own header unchanged, but uses changed suppliers; do not silently import the altered contract set. |
| `bodySimRawLogTopics` | `raw_log_body_topics_sim` | L: changed exceptional predicate. |
| `stmtSimAugAssignPlaceStorage` | `aug_place_storage_binop_store_outcome[normal]` | A: local helper header adds halt agreement. |
| `stmtSimAugAssignPlaceStorage` | `compile_augassign_place_storage_case` | A: own header unchanged; helper/adapter compatibility unresolved. |
| `tuplePlaceHeadOpen` | `tuple_place_head_gas_continuation_open` | T: expanded compilation premise and added halt predicates. |
| `bodySimStmtCases` | `body_augassign_toplevel_word[local]` | No compatible published replacement identified by bounded task-owner history inspection. Current/source identities retained above. |
| `bodySimDeclCases` | `expr_sim_inv_for_scope` | No published repair identified; missing candidate comparison, not assumed equal. |
| `bodySimDeclCases` | `expr_sim_inv_for_pop` | Same. |
| `bodySimDeclCases` | `body_for_array` | Same. |
| `whitelist/whitelistForIter` | `body_for_dynarray_name` | No published repair identified; missing candidate comparison, not assumed equal. |
| `whitelist/whitelistForIter` | `memory_iterator_source_classify[local]` | Same; late timeout hold included. |

Partition check: **4 excluded + 7 mapped + 21 unresolved = 32 bodies**; **4 + 4 + 9 = 17 distinct owners**. The inventory is complete as an accounting partition; the repair set is deliberately incomplete. Pre-existing admissions such as FullAssign's memory/copy/other cases are not mislabeled as new holds.

## Handoff to actual integration (C1.12.2)

A bounded file-disjoint candidate source set is:

- `lowering/externalReturnValuedFullScript.sml` -> `externalReturnValuedFullTheory` (R).
- `lowering/bodySimCallIntcallScript.sml` -> `bodySimCallIntcallTheory` (I; accompanying seams source still needs compatibility checking).
- `lowering/stmtSimAssignTuplePlacesScript.sml` -> `stmtSimAssignTuplePlacesTheory` (P's file snapshot only; branch is overlap-excluded).
- `lowering/assignEffectfulIndexEmptyCaseScript.sml` -> `assignEffectfulIndexEmptyCaseTheory` (E; expanded imported contracts still need qualification).

These are candidate output names, not an authorization to extract/merge sources or an assertion that they build. No complete source-integration set can yet be isolated: C1.7's approved source remains a prerequisite; unresolved helper-header differences, uncertain adapters, missing repairs and candidate ancestry must be reconciled before removal of all holds. No upstream proof-development campaign is proposed. The owner of C1.12.2 must use actual delivered compatible sources and receiving checks, not donor reports or this provenance receipt, and retain consumers' ownership.

## Verification boundary

This component changes only this Markdown receipt. No SML, definitions, compiler/semantic pins, target headers, or suppliers are edited, and no local hold is expanded. Per C1.12.1's explicit diagnostic boundary, no HOL build is required or claimed; family proof/build obligations remain with their existing owners and receiving qualification. Final docs-only diff, whitespace and source-change audits accompany the component close. This receipt supplies **zero theorem proof credit**.
