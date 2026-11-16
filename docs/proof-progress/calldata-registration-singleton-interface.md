# Raw positional singleton interface receipt

Component: C1.9.10.2.1. Diagnostic only; no singleton or fold theorem is claimed.

## Checked artifact and scope

`lowering/calldataRegistrationSingletonProbeScript.sml` typechecks two expanded
HOL terms and their universally closed implication. They are **not theorems**,
are not installed in the theorem database, and introduce no semantic predicate.
The decoder antecedent fixes `ce/env/sf/ty/tv` and quantifies execution parameters;
it does not assume a result uniformly over every coherent type as an induction
hypothesis. The singleton consequent explicitly contains both terminal cases,
robust exact values, indexed old owners, ALLOCA history and literal-size
consistency, local and ambient freshness, world frames, common zero-event
origin paths and backward pointer-safe continuation.

The availability checks execute during the theory build. In this receiving
source, `entryPtrSeamRegister.registration_argument_prepare_guarded_joint` is
**not exported** (`Finalise ...[local]` at line 1591). The exported
`registration_argument_prepare_guarded_robust_resources` contains memory
robustness but not `gas_origin_ptr_path`; it cannot replace the joint theorem.
The phase splits, primitive-to-aggregate equality, old-local frame, indexed
prefix update, and singleton owner-instruction theorem are exported.

## Premise-discharge ledger

The following are concrete reuse routes checked against source, not a proof of
the quoted implication. Missing boundaries are listed separately below.

| Obligation | Existing route / exact facts needed |
| --- | --- |
| Source offset and nonwrap | Reuse `calldataRegistrationRawAddress.calldata_decode_args_step_exact` and the raw pointer-nonwrap boundary. The quotation exposes the load equality and nonwrapped source position as hypotheses. Do not assume canonical encoding. |
| Primitive and aggregate phases | `entryPtrSeamRegister` lines 680–764 supply aggregate phases, primitive phases and primitive-as-aggregate equality. Primitive needs `~dyn` and `DecPrimWord`; these are explicit in the quotation. No second primitive implementation is needed. |
| Nonwrapped preparation | The source-local guarded joint already provides the required origin path and prepared resources. Its robust resource projection is public but path-free. Reuse requires the visibility decision below, not reproving preparation. |
| Buffer root and range | Preparation installs owner `st.cs_next_id`, with `FLOOKUP ... = SOME (p,n)` and `ptr_covers`. With `n = type_memory_size tv` these supply the exact decoder's buffer cap and bounds. The new owner is below decoder start `first.cs_next_id`. |
| Initial decoder scratch classification | `preparation_forward_slots` places every live prepared allocation ID below `mid.cs_next_id <= first.cs_next_id`; hence the initial scratch interval is empty of owners. Do not assume arbitrary allocations are scratch. |
| Old owner bounds and robustness | The existing `registration_aggregate_singleton_joint[old_local]` source at 2103–2159 implements this route: `alloca_inv` yields `p0+n0 <= s.vs_alloca_next`; footprint at most `n0` allows preparation's robust transport. A present lookup plus freshness at `st` gives `not_fresh_at st q0`; operand-live monotonicity preserves lookup and ghost facts at `first`. Reuse `registration_owned_local_frame` for the decoder footprint/owner/robustness transport, rather than duplicate this argument. |
| Owner instruction witness | Exported `registration_singleton_owner_instruction` supplies the installed ALLOCA witness. Preserve it in the fold's indexed resource output. |
| Final literal-size consistency | The existing source at 2162–2195 uses three disjoint cases: decoder scratch interval has literal `32w`; root owner has literal `n2w n` with `n < dimword (:256)`; outside IDs use original map equality and original literal-size consistency. Instruction-ID distinctness identifies the witness instruction. |
| Allocation history/frontier | Decoder antecedent explicitly exports monotone frontier, old-owner preservation, outside-interval equality, scratch classification and alloca/frontier invariants. These cannot be replaced by `ptr_covers` alone. |
| Accepted exact value and robustness | Decoder antecedent explicitly exports `cd_decode = SOME x`, type/well-formedness, exact memory value and `!mem. mem_agree_outside ... ==> val_in_memory ...`. Memory-taint subset alone is insufficient. |
| Nonlocal and gas frame | All requested accounts/transient/logs/outcomes/requests/deletions/transaction/block/fmp/gas-readings equations are explicit decoder output clauses. They are not inferred from a memory-only frame. |
| Uniform execution/path composition | Choose runtime and ghost endpoints before `!D explicit`, then compose using `gas_origin_ptr_path_append`. Never choose different witnesses inside dead-set quantification. Run/memory continuation and backward pointer-safe continuation remain separate obligations. |
| Ambient freshness | Decoder antecedent supplies `fresh_vars_wrt limit v`. Preparation needs transport to the same ambient limit, never reverse monotonicity. This does not settle local freshness at `last`. |

## Exact residual interface obligations

1. **Guarded joint visibility.** The smallest reuse repair is to export the
   unchanged formula of `registration_argument_prepare_guarded_joint`. This
   diagnostic does not authorize or perform that supplier visibility edit.
   A scoped owner/strategist decision is required. The public path-free
   resource projection is not sufficient.
2. **Wrapped-pointer rejection with uniform ghosts.**
   `registrationGuardPtr.registration_ptr_guard_origin_frame` (227–418) and
   its pointer projection require `~(w <+ 4w)` and therefore cover passing
   guards only. `calldataRegistrationExec.registration_ptr_guard_frag_mem`
   (320–361) covers both outcomes, but its rejection conclusion says only
   `w <+ 4w /\ ?z. r = Abort Revert_abort z`; it does not expose empty
   returndata or a uniform origin-pointer path. `registration_address_owned_run`
   (433 onward) likewise offers existential run/memory rejection, not the
   common ghost endpoint. `abi_decode_ge_guard_revert` provides a sequence
   abort, not the required installed uniform origin path. The bounded check
   found no reusable rejection theorem of the required shape. A new natural
   owner boundary must establish empty returndata and endpoints before
   `!D explicit`, for the rejecting guard and its address prelude.
3. **Current as well as ambient freshness.** The quoted decoder antecedent
   concludes `fresh_vars_wrt limit v` only. The singleton consequent needs
   `fresh_vars_wrt last v`, since the next argument's preparation requires
   freshness at its current compiler state. `last <= limit` does not imply
   this: freshness monotonicity only moves to larger counters. A bounded-write
   or local-freshness boundary is required. Do not rerun the decoder at another
   limit and obtain a different existential endpoint. Keep one accepted
   endpoint with both properties.

These are availability/missing-interface findings, not a missing premise in an
admitted helper, not a frozen-target counterexample, and not a claim that the
full positional fold is de-risked. No supplier header, visibility, definition,
or frozen family statement was changed by this diagnostic.

## Evidence

- E0058 and its full source note: initial successful typecheck/availability
  diagnostic, committed in `8e0e26e11`.
- `TO_seq3861_calldata_family-L0025-20261116T173035647381Z_m0014_t004`:
  initial passing diagnostic build.
- `TO_seq3861_calldata_family-L0025-20261116T173035647381Z_m0022_t002`:
  freshness theorem search; no reverse-monotonicity rule.
- `TO_seq3861_calldata_family-L0025-20261116T175036331391Z_m0026_t002`:
  passing-guard origin-frame statement and implementation.
- `TO_seq3861_calldata_family-L0025-20261116T175036331391Z_m0026_t003`:
  guard memory interface and address rejection interface.
- `TO_seq3861_calldata_family-L0025-20261116T175036331391Z_m0027_t003`:
  existing old-local robustness and literal-size classification arguments.
