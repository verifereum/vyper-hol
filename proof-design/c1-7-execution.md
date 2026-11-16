# C1.7.2 — local-memory assignment execution-interface qualification

## Result and scope

This is a diagnostic deliverable, not a proof of the frozen
`bodyFullAssign.body_assign_local_memory_full`. No compiler definition,
exported helper header, frozen root, or foreign supplier was changed.
The integrated C1.5 producer builds, but its written antecedents do not yet
provide an applicable boundary for every branch of the frozen root.
In particular, the staged producer still asks for **initial source/destination
disjointness**, and both staged and direct interfaces ask for **full static
source capacity**, not merely the runtime value footprint. The empty branch
needs a joint origin/pointer/ghost header-store boundary, rather than an RHS
copy suffix. These are interface gaps requiring scoped planning and, for
changed helper contracts, exact owner approval; they are not checked
counterexamples to the frozen theorem.

## Actual compiler boundaries

Let `dty = ty`, `sty = lowered_value_type cenv e`, and let `s` below be the
successful RHS endpoint, not the initial statement state.

1. **Empty length-bearing expression**:
   `has_length_word (expr_type e) /\ is_empty_value_expr e`.
   `stmtSimAssignMem.assign_local_empty_code_parts` (1449–1462) gives exactly
   `emit_void MSTORE [Var p; Lit 0w] sa = ((),sf)` and unchanged compile env.
   It does not call `compile_expr`, `unwrap_value`, or `compile_assign_value`.
   `assignPlacePureCode.assign_place_pure_empty_code` (34–45) is the generic
   target equivalent. Consequently ordinary RHS-execution composition is
   the wrong execution skeleton for this branch.

2. **Nonempty ordinary/widened local**:
   `stmtSimAssignMem.assign_local_memory_widen_code_parts` (864–905) already
   handles `(sty = dty \/ is_bytestring_type dty)` without requiring equality.
   It supplies one `vv,sV,op,sB`, the `compile_expr` and `unwrap_value`
   equations, `lower_value`, code containment and compiler growth, and
   ```sml
   compile_assign_value cenv (Var p) LocMemory op F (vv_location vv)
     dty sty (type_memory_bytes cenv dty) sB = ((),sf)
   ```
   Prefer this existing export over generalizing the narrower
   `assign_local_memory_code_parts`.

3. **Staged location**, `vv_location vv = SOME LocMemory`:
   `compile_assign_value_def` (stmtLowering:444–467) and
   `annassignRelayoutCode.assign_memory_relayout_code` (7–28) split the suffix
   into allocation of `type_memory_bytes cenv sty`, a flat copy of that many
   bytes from `op` to the scratch buffer, and `compile_store_memory` from
   scratch to destination. Staging is explicitly for overlap safety.

4. **Direct location**, `vv_location vv = NONE`:
   the same definition gives `compile_store_memory cenv op (Var p) dty sty`.
   `body_full_assign_local_memory_value_path` admits only NONE or
   SOME LocMemory and requires `op = Var xs`. These facts must come from the
   actual expression/unwrap classification; code decomposition alone does
   not assert them. Other locations are not implicitly covered by this
   producer.

## Premise audit at the actual successful RHS state

References in this table are to `bodyFullAssignMemoryValueScript.sml` unless
qualified. A candidate pure representation fact is not credited as discharged
here; C1.7.1 owns that qualification.

| Producer antecedent | Applicable source interface / remaining check |
|---|---|
| Code equation, `loc = NONE \/ loc = SOME LocMemory` (12–13) | Widened code parts supplies the equation with `op`, not necessarily `Var xs`; expression location/operand classification is still needed. |
| Metadata, `type_widens_to`, evaluated types and type sizes (14–25) | Body/type metadata and representation qualification are needed. Distinguish `post_value_type`, `expr_type`, and lowered `sty`; no blanket equality is valid. |
| `value_has_type` and `val_wf` at both types (26) | Source read typing plus representation transport; `expr_post` describes the physical post type. |
| Operand not-fresh, lookup, compiler boundary and containment (27–28,40,48–49) | Lower-value compiler growth/not-fresh exports and the actual RHS outcome; cannot substitute the initial state for `s`. |
| Robust `val_in_memory stv v` under arbitrary agreement outside `tn.t_mem` (29–30) | Needs the RHS pointer-value post at the correct physical type, in addition to `expr_val_rel`. `expr_val_rel` alone only asserts the current memory relation. No new robust-content assumption is silently introduced. |
| Source `ptr_covers ... (type_memory_size stv)` (31), full-source no-wrap/frontier (33,35) | **Not supplied by placement alone.** `expr_val_at` bounds `val_footprint stv v`, and bytes/string literals can allocate less than static type capacity. `typedCopyPtr.expr_val_at_ptr_offset_read_covers` likewise requires the accessed interval to fit inside `val_footprint`. |
| Destination lookup and full capacity/frontier (28,32,34,36,43–44) | At `s`, `stmt_state_rel` / `local_ptrs_rel` gives local lookup, local backing, region below `vs_alloca_next`, and `type_memory_size entry.type <= cap`. `ghost_inv_at` gives destination coverage for `cap`, hence the smaller typed size. Must first obtain the current containing scope/entry and `entry.type = dtv`, not reuse a stale pre-RHS value. |
| Initial source/destination disjointness (37–38) | **Not supplied for all local sources.** `expr_val_at_def` (loweringPosts:361–375) includes a local-region alternative with no requirement that its name differ from the assigned name. `local_ptrs_rel` only separates distinct locals. The staged branch retains this premise even though staging is intended to handle overlap. |
| `allocas_from lo`, lower bounds and initial history (39,41) | Ghost invariant gives `allocas_from lo` and `lo <= frontier`; `body_full_local_region_lower_bound` derives `lo <= destination` from body invariant, a positive local region, current state relation, and `dead_lo_ok`. Bare alloca_inv supplies neither this lower bound nor actual FMP. |
| Scope update and destination type (42) | Use the actual source assignment continuation at the successful RHS state. Update is `pre ++ (sc |+ (id,entry with <|value := v; popped := []|>)) :: rest`. |
| `expr_val_at ... sty start sa ...` (45) | Must transport the physical post type to `sty` only with a proved type/representation fact; bytestring post type can remain the annotation. |
| Return operands reserved/not-fresh (44,46–47) | Obtain from body/frame/compiler invariants and preserve through the actual RHS code. |
| Conditional actual FMP | Producer derives it from its input `stmt_state_rel H0`; not from alloca_inv. For root composition instantiate H0 using a witnessed valid horizon before choosing the suffix path. |

## What the checked producer does and does not solve

`body_full_assign_local_memory_value_path` (11–66) chooses **one** `t,Gf,tf`
before its postcondition quantifiers. Its path is uniform in D; its local
state/ghost transport is uniform in H,D,d. It preserves history, allocation
frontier, previous allocations, and old variable/ghost/taint lookups.
This is the right endpoint discipline once its antecedents are available.

`bodyFullMemoryStage.body_full_memory_stage_path` (15–70) does not require
initial source/destination separation. It provides a fresh scratch region
separated from every local at the resulting state (48–49), robust scratch
contents, coverage and frontier bounds. However, it still needs full `n`
source coverage and frontier before staging (29–32), where `n` is static
`type_memory_size stv` in AssignMemoryValue. Calling Stage directly therefore
addresses the alias issue only, not the bytestring capacity issue.

The direct suffix uses `bodyFullMemoryStore.body_full_memory_store_path`
(10–53), whose full source-coverage and disjointness assumptions are also
explicit. Neither theorem may be advertised as footprint-only.

`bodyFullAssignMemoryExitCompose.assign_local_memory_full_outcome_exit`
already preserves same-H halt_exit and conditional Halt/IntRet actual-FMP
through RHS exceptions. Reuse it; there is no request to duplicate or alter
this integrated callback companion.

## Empty-branch support and missing joint boundary

Existing exports are useful but must not be combined by independent
existential choice:

- `stmtSimAssignMem.local_header_store_state` (1319–1357) proves the source
  scope/state relation for the concrete mstore update.
- `local_header_store_path` (1359–1447) chooses one endpoint with uniform-H
  state relation and an S1 `gas_marked_path F`, but no pointer/ghost tuple.
- `assignBasePtrEmptyStore.assign_base_empty_header_robust` (10–25) proves
  robust default-value layout after a clean zero header.
- `assign_base_empty_local_store_path` (27–92) gives a concrete endpoint and
  pointer ghost update, but its header uses `ghost_inv H`, `gas_path_ptr`,
  fixed lo=0, and `~ctx_has_dalloca ctx`. It is not the full origin judgment.
  `assignBasePtrLocalEmptyFragment` packages the same older ptr interface.
- `stmtSimAssignMem.assign_local_identity_rhs_all_tails` gives the source
  default-value assignment update once empty-RHS identity is proved.

The needed full boundary should execute the *one emitted header store* with
one `t,Gf,tf`, transfer `ghost_inv_at D lo d` and current scope/state relation,
retain allocation history, normal conditional FMP and uniform valid-H posts,
and use conditional actual FMP instead of no-D. Existing concrete mstore
identity/robust-layout facts are proof resources, not independent execution
witnesses to splice together.

## Exact prospective interface changes — proposals, not authorization

1. **Staged aliasing:** change only the disjointness conjunct (37–38) of
   `body_full_assign_local_memory_value_path` to
   ```sml
   (loc <> SOME LocMemory ==>
     w2n sw + type_memory_size stv <= w2n dw \/
     w2n dw + type_memory_size dtv <= w2n sw)
   ```
   Preserve every other antecedent/conclusion. Its staged proof already gets
   scratch/destination separation from Stage; direct proof still receives
   the original separation. This is a proposed exported hypothesis weakening
   requiring the exact owner ruling; no header edit has been made.

2. **Bytestring footprint boundary:** do not strengthen the frozen root with
   static source coverage. A separate approved footprint-specialized joint
   assignment boundary is needed if no existing complete export applies.
   It must take actual physical bytestring content/robustness and source
   pointer resources for the compiler's real read interval; preserve the
   existing `compile_assign_value` equation, including its static-size flat
   staging copy; and provide exactly the same source scope update and
   single-endpoint uniform-H ghost/state posts. It is *not* sound to replace
   static size by footprint in Stage without proving the full emitted copy's
   pointer safety. The exact safe read-resource contract is unresolved here;
   do not rely on an invented header or add stronger root premises.

3. **Empty header boundary:** add a subject-named full joint header-store
   producer, reusing the concrete mstore/robust-default resources above, with
   witnessed input state relation and `ghost_inv_at`, conditional actual FMP,
   lo lower bound, code containment, and exactly one concrete execution
   endpoint before uniform state/ghost posts. A complete proposed header and
   owner ruling must precede proof work; the older S1 and ptr existentials
   are not themselves such a boundary.

## Bounded checks and evidence

- Current-receiver `holbuild` passed for bodyFullAssignMemoryValueTheory,
  stmtSimAssignMemTheory, assignPlacePureCodeTheory and
  annassignRelayoutCodeTheory: TO_assignment_cases-L0044-20261116T143101046586Z_m0016_t001.
- One bounded HOL goal search tested whether source `expr_val_at`, type
  evaluation, source lookup and a destination local region/capacity alone
  discharge the full-size disjointness conjunct, immediately before the
  producer declaration. No checked closer was reported:
  TO_assignment_cases-L0044-20261116T143101046586Z_m0021_t001.
  This is an applicability test, not a proof of logical non-entailment.
  Its ranked interfaces expose footprint-only placement and the distinct
  local-region alternative. No counterexample tower was constructed.
- Exact producer/Stage headers:
  TO_assignment_cases-L0044-20261116T143101046586Z_m0016_t002 and _m0016_t003.
- Widened/empty boundaries: _m0017_t001, _m0019_t003, _m0019_t004.
- Physical-placement/current-local/ghost definitions: _m0018_t001,
  _m0018_t002, _m0021_t002, _m0021_t003 (same session prefix).
- This report carries no proof credit from unchanged foreign admissions.
  No HOL source or target header was edited. Completion of this diagnostic
  must not mark C1.7.3 or the frozen root proved; owner/strategist disposition
  of the identified interfaces is the next dependency.

Final source audit: the four built source scripts contain no occurrences of
`cheat`, `mk_thm`, `new_axiom`, `mk_oracle_thm`, `mk_axiom_thm`, `disk_thm`
or `mk_proof_thm` (_m0024_t003 through _m0024_t006). Git status at the audit
showed only this new report; tracked source diff was empty (_m0024_t001–002).
