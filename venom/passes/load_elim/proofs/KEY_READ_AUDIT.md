# Key/read operational interface audit (C1.K.2.a)

This is a proposed statement package, NOT proved HOL claims. K1 is checked in
loadElimKeyReadTheory. No frozen statement or pass definition changes are proposed.

## Existing interfaces actually inspected

* `loadElimNormalizeHelpers.le_chain_valid_eval`:
  `le_chain_valid dfg visited op s ==> eval_operand (normalize_operand dfg visited op) s = eval_operand op s`.
  P5 must establish this premise on reached rebuilt DFGs; K can parameterize by
  evaluation equality and must not depend on P5.
* `memAliasProps.bp_segment_from_ops_runtime_region`:
  `bp_ptr_sound bp s /\ bp_segment_from_ops bp ops = ml /\ ml_is_fixed ml /\
   IS_SOME (eval_operand ops.iao_ofst s) ==>
   ?addr. eval_operand ops.iao_ofst s = SOME (n2w addr) /\
          memloc_runtime_region ml s = SOME (addr, THE ml.ml_size)`.
  IMPORTANT: does not establish `addr < dimword(:256)`. The word equality alone
  cannot identify addr with w2n of the operand. Do not erase this missing bound.
* `memAliasProps.ma_may_alias_sound`:
  `wf_alias_sets sets /\ ~ma_may_alias sets loc1 loc2 /\
   allocas_non_overlapping s /\ memloc_within_alloca loc1 s /\
   memloc_within_alloca loc2 s /\
   memloc_runtime_region loc1 s = SOME r1 /\
   memloc_runtime_region loc2 s = SOME r2 ==> regions_disjoint r1 r2`.
  The no-alloca corollary additionally requires both alloca fields NONE and
  both offsets and sizes defined; it does not require alloca-state premises.
* `mem2varBlockSimHelpers.mload_mstore_disjoint`:
  `off_r + 32 <= off_w \/ off_w + 32 <= off_r ==>
   mload off_r (mstore off_w val_w s) = mload off_r s`.
* `deadStoreElimProofs.sload_sstore_disjoint`, `tload_tstore_disjoint`:
  `key1 <> key2 ==> sload key2 (sstore key1 val s) = sload key2 s`,
  respectively tload/tstore. Can import, not duplicate.
* `venomInstProps.step_preserves_call_ctx`, `step_preserves_data_section`:
  `step_inst fuel ctx inst s = OK t /\ ~is_terminator inst.inst_opcode ==>
   t.vs_call_ctx = s.vs_call_ctx` (respectively data_section).
  These include INVOKE/external calls; unlike passShared's aggregate theorem,
  they do not exclude calls. Terminator OK cases need a separate wrapper.
* `passSharedProps.step_inst_preserves_all` requires successful step, nonterm,
  nonalloca, non-ext-call, not INVOKE. It preserves control/context/data/labels;
  no MEMORY write implies equal memory; no TRANSIENT write implies equal
  transient; no BALANCE AND no STORAGE write implies equal accounts.
  Storage-read preservation needs current-account/context agreement too;
  no STORAGE effect alone is not the aggregate accounts theorem's premise.

Some similar memoryCopyElisionSound facts (`runtime_region_in_word`,
`ce_memloc_runtime_w2n`, `memloc_runtime_region_allocas_eq` in its Proofs theory)
are LOCAL and cannot be imported. Their copy-specific hypotheses cannot be
silently generalized. Existing `read_at_offset` only covers M/S/T and defaults
other opcodes to ARB; K1's partial five-space read is intentionally different.

## Coverage of the actual transfer branches

| configuration | read key | configured store | other writer | no writer |
|---|---|---|---|---|
| memory MLOAD | fixed BP or normalized HD | MSTORE, 32 bytes | MEMORY effect clears all | retained |
| storage SLOAD | fixed BP or normalized HD | SSTORE, 1 slot | STORAGE effect clears all | retained |
| transient TLOAD | fixed BP or normalized HD | TSTORE, 1 slot | TRANSIENT effect clears all | retained |
| calldata CALLDATALOAD | fixed BP or normalized HD | none | no barrier | retained |
| data DLOAD | normalized HD only | none | no barrier | retained |

Load branch has priority. Well-shaped loads insert `[Var out]`; malformed loads
retain input. Well-shaped stores invalidate then insert RAW `[val_op]`;
malformed configured stores clear all. Nonnormalized stored operands need P
currentness, not a K normalization assumption. Other writers (MSTORE8, copies,
DLOAD's memory side effect, calls and INVOKE) go through barrier for writable
spaces; K need not prove retained-memory facts for a branch that clears all.
DLOAD reads data but also writes memory; do not classify it as globally pure.

## Proposed exact statements for review/decomposition

Use `norm : operand -> operand` as a parameter, and explicit op/space pairs.
All statements universally quantify free variables; none contain a HOL let.
Names here are descriptive outputs, not new component IDs.

1. **Fixed BP word region bridge (missing shared boundary).**
   `bp_ptr_sound bp s /\ allocas_in_word s /\
    bp_segment_from_ops bp ops = ml /\ ml_is_fixed ml /\
    ops.iao_max_size = SOME (Lit (n2w (addr_space_word_scale space))) /\
    eval_operand ops.iao_ofst s = SOME w /\ memloc_within_alloca ml s ==>
    memloc_runtime_region ml s = SOME (w2n w, addr_space_word_scale space)`.
   Validate this exact interface before consuming it: bounds and width are the
   two missing conclusions of the exported segment theorem. `allocas_in_word`
   bounds allocation end; within-alloca bounds offset plus access width.

2. **Read computed-key address.** For each table load/space pair:
   `inst.inst_opcode = loadop /\ inst.inst_operands = [addr] /\
    eval_operand addr s = SOME w /\ eval_operand (norm addr) s = SOME w /\
    bp_ptr_sound bp s /\ allocas_in_word s /\
    memloc_within_alloca (bp_get_read_location bp inst space) s ==>
    le_key_address space (load_get_read_key bp space norm inst) s = SOME (w2n w)`.
   Fixed branch uses (1) plus BP location/shape equations; fallback uses K1.
   Data ignores BP premises; remove unused premises in that specialization.
   Write counterpart uses the three store/space pairs, `[addr;val_op]`, and
   bp_get_write_location. Then K1 gives key read = actual read-address function.
   Successful step + inst_wf supplies operand/output shape and evaluation;
   bridge to step result/output value is a separate semantic theorem.

3. **Alias location compatibility for arbitrary retained keys (missing).**
   `bp_ptr_sound bp s /\
    le_key_address space k s = SOME a /\
    load_key_to_memloc bp space k <> ml_undefined ==>
    memloc_runtime_region (load_key_to_memloc bp space k) s =
      SOME (a,addr_space_word_scale space)`.
   This proposed implication is NOT yet validated. LK_Loc follows K1; LK_Op
   may have known operand evaluation but unknown BP offset, so nonundefined
   alone need not imply a resolved region. Audit/review must decide stronger
   meaningful premises or use a less restrictive alias boundary. Do not assert
   it as an axiom or hide this gap in a giant transfer proof.

4. **Retained read through configured stores, at explicit regions.**
   `wf_alias_sets aliases /\ ~ma_may_alias aliases readloc writeloc /\
    allocas_non_overlapping s /\ memloc_within_alloca readloc s /\
    memloc_within_alloca writeloc s /\
    memloc_runtime_region readloc s = SOME (a,addr_space_word_scale space) /\
    memloc_runtime_region writeloc s = SOME (b,addr_space_word_scale space) ==>
    le_read_address space a (store b value s) = le_read_address space a s`.
   Specialize to M/S/T with mstore/sstore/tstore and matching space; derive
   disjointness via ma_may_alias_sound then existing disjoint read lemmas.
   Word bounds on a,b required for S/T conversion injectivity; supply explicitly
   (`a,b < dimword(:256)`), not inferred from region disjointness.
   Lift to key reads via K1 transport ONLY after separately establishing
   address preservation at t. P owns operand/key epochs; K owns content facts.

5. **Read-only contents preservation.** For Calldata and Data:
   `step_inst fuel ctx inst s = OK t /\ ~is_terminator inst.inst_opcode ==>
    le_read_address space a t = le_read_address space a s`.
   Existing field theorems above suffice, including calls. Key resolution
   preservation remains separate. OK terminators and PHI batches need wrappers,
   not unfolding callees or assuming arbitrary keys stable.

## Remaining premise sourcing issues (not discharged)

`bp_ptrs_bounded` quantifies only mem_read_ops/mem_write_ops of instructions in
fn. It does NOT directly quantify arbitrary retained normalized operands or
all space-specific locations. Prove origin/shape compatibility before claiming
within-alloca for those keys. Stored LK_Op values, normalized address variables,
and PHI updates require existing P3/P5 epoch reasoning. Alias set wf must come
from the actual alias analysis. No further solver population/support theorem
can supply any of these semantic premises.

## Follow-up validation (C1.K.2.b.3)

### Fixed segment bridge: branch-level validation, not a proof certificate

The proposed statement (1) has no identified false branch. Scales are always 1
or 32, so `w2n (n2w (addr_space_word_scale space):bytes32)` is that scale.
`bp_segment_from_ops` uses iao_max_size (not iao_size), which (1) specifies.
Literal offsets are already w2n and have no alloca. A fixed Var segment requires
`bp_ptr_from_op` to return a singleton pointer with SOME offset. `bp_ptr_sound`
then supplies that same pointer's ptr_matches_var. Missing allocations are
excluded by ptr_matches_var's existential FLOOKUP, not by within-alloca (which
is vacuous if allocation is absent). At known offset, within-alloca gives
`off + scale <= sz`, and allocas_in_word gives `base + sz < dimword(:256)`.
Thus base+off is representable, and the n2w equality can be inverted. Label
segments are undefined and cannot satisfy ml_is_fixed. This suggests a direct
constructor proof for (1) without additional history premises.

All fixed load-location branches reduce to this segment form: MLOAD uses
mem_read_ops; SLOAD/TLOAD use explicit size Lit 1w; CALLDATALOAD size Lit 32w.
DLOAD keys never use locations (though BP has an independent data location).
MSTORE uses mem_write_ops; SSTORE/TSTORE use explicit word_scale literals.
The fallback norm-evaluation premise remains explicitly P-owned.

### Retained alias compatibility: an unresolved distinct-allocation branch

Negative ma_may_alias under wf_alias_sets entails negative may_overlap (both
tracked: completeness; otherwise direct fallback). This DOES NOT force fixed
offsets: may_overlap tests distinct allocated identities BEFORE unknown offsets.
A checked EVAL probe `le_unknown_offset_nonalias_probe` in
loadElimKeyInterfaceProbesTheory establishes simultaneously:

* wf_alias_sets FEMPTY;
* unknown-offset, size32, Allocation1 location is not ml_undefined;
* it does not alias a fixed size32 Allocation2 location;
* its runtime region is NONE (for any state).

This rejects proposed statement (3) even with an added negative alias premise
as a route to resolving all retained locations. It is not a pass counterexample.
Do not strengthen K1's resolver or assume this unknown location is fixed.

Exact unresolved branch for integration: LK_Op (Var v),
`bp_ptr_from_op bp (Var v) = SOME (Ptr (Allocation aid) NONE)`,
write location has a different nonempty allocation. Existing bp_ptr_sound gives
only `lookup_var v s = SOME (n2w (base + delta))` for an existential delta with
NO delta bound (ptr_matches_var NONE branch). memloc_within_alloca returns T
when offset is NONE, so it does not supply delta+width <= sz. bp_ptrs_bounded
also only quantifies mem_read_ops/mem_write_ops in fn, not arbitrary operands;
those tables do not include the S/T load/store special BP locations. Therefore
the checked fixed-region/nonalias theorem cannot simply be applied here.

A semantically sufficient but UNSOURCED premise for this branch would be
`?base sz delta. FLOOKUP s.vs_allocas aid = SOME (base,sz) /\
 eval_operand (Var v) s = SOME (n2w (base+delta)) /\
 delta + addr_space_word_scale space <= sz`.
Together with allocas_in_word and disjoint allocations this gives an actual
bounded subregion. This premise is NOT part of the frozen contract and must
not be silently added. Integration must either prove it for actual reached
key origins/analyses, or use a checked execution probe to investigate a genuine
pass violation. The diagnostic alone proves neither conclusion.

For the remaining alias branches: empty regions have no writes/reads; mismatch
of allocated-vs-absolute forces may_overlap; same allocation/absolute unknown
offset forces may_overlap; equal-allocation fixed offsets use numeric region
proofs. Unknown-offset locations against a different allocation are the key
remaining hole; a strict-region-only interface does not cover them.

### Minimal read-only wrappers

`venomExecProofs.eval_phis_only_updates_vs_vars` is exported with exact statement
`eval_phis st insts = OK t ==> t = st with vs_vars := t.vs_vars`.
This directly yields calldata/data contents preservation after PHIs, but NOT
operand/key-address preservation. Successful terminators can be handled by a
field wrapper restricted to `is_terminator inst.inst_opcode` and `step_inst ...
= OK t`; JMP/JNZ/DJMP use jump_to, other terminators do not produce OK. The
existing local `mmBlockSimProofs.step_inst_ok_preserves_call_ctx` demonstrates
this split but is not importable. Minimal requested outputs are equal call_ctx
and data_section for successful terminators; combine with nonterminator field
theorems and K1 reads, rather than unfolding run_blocks or INVOKE.

## Actual-analysis exclusion checkpoint (E0056 interface)

`loadElimBPEmptyTheory.le_step_preserves_analyze_empty` now composes
`le_step_preserves_no_alloca` with `le_bp_analyze_empty`. Its antecedent is
exactly `fn_inst_wf fn /\ le_step_preserves bp dfg fn /\
bp_assigns_stable bp dfg /\ dfg_assigns_sound dfg s`; the cfg used by the
analysis is arbitrary. `le_step_preserves_analyze_ptr_none` exports
`bp_ptr_from_op (bp_analyze cfg fn) op = NONE` for every operand. This is
empty **queries**, not an assertion that the finite map is FEMPTY.

Consumer check: `loadElimKeyReadOperationalScript.sml` lines 71–99
(`le_fixed_segment_runtime_word`) distinguishes literal addresses from Var
addresses with `bp_ptr_from_op = SOME (Ptr alloc off)`. For the analyzed
original fn under the above antecedent, every such SOME branch is excluded,
including both SOME and NONE offsets. In `bp_segment_from_ops_def` a Var
therefore takes the unallocated, unknown-offset result (`ml_alloca = NONE`,
`ml_offset = NONE`); literal addresses retain their fixed w2n interpretation,
and labels still yield ml_undefined. Thus the different-allocation
unknown-offset counterexample branch documented above cannot originate in
this actual BP analysis. The local segment-key bridge (lines 119–139) and
configured read/write key bridges (141–153, 180–191) still apply to arbitrary
supplied BP maps; their statements must not be weakened or silently
specialized. DLOAD's operand-only branch (156–163) is independent of BP.

This only resolves the BP-origin obstruction for this analyzed function.
It proves neither arbitrary retained-key currentness nor normalization
validity. Later rounds analyze transformed functions: they still need a
separate no-ALLOCA preservation argument (or their own wrapper antecedent)
before using `le_bp_analyze_empty`. Do not transfer the original universal
step hypothesis to rebuilt DFGs or transformed functions.

## Checked empty-query key boundary (C1.K.2.b.6)

`loadElimAbsoluteKeyTheory` defines `le_absolute_key`: operand keys are
unconstrained; location keys have no allocation, a word-sized region in the
selected space, and a representable absolute offset. `le_empty_read_key_shape`
and `le_empty_write_key_shape` prove this for the configured opcode/operand
shapes under empty BP queries; `le_dload_key_shape` covers Data separately.
`le_absolute_location_address` proves state independence only for such location
keys. It says nothing about persistence of an operand key's evaluation.

`le_empty_read_key_address` and `le_empty_write_key_address` resolve computed
keys without allocation hypotheses. They explicitly require equal defined
evaluation of source and normalized addresses. DLOAD uses the existing
`le_dload_key_address`, which needs only the normalized evaluation. These are
local address facts, not analysis-origin or normalization-currentness theorems;
those hypotheses still need discharge at reached consumers. Retained-store
content preservation and retained-key origin remain separate obligations.

## Checked retained-key content boundary (C1.K.2.b.7)

`loadElimRetainedReadTheory` proves retained-domain membership exposes two
nonundefined key locations and a negative alias test. Under empty BP queries
and `le_absolute_key` for both keys, `le_retained_absolute_disjoint` derives
disjoint bounded word regions at defined resolved addresses. In particular,
unknown-offset Var operand keys cannot survive that negative alias test against
a nonempty word region. No allocation-state invariant is needed.

The three `le_retained_*_content` lemmas preserve reads at a fixed address
across primitive memory/storage/transient stores. Their `*_key_read`
corollaries expose the additional post/pre key-address equality explicitly;
this is not inferred from nonaliasing. These facts do not establish key origin
in a solver lattice, normalized evaluation agreement, or persistence across
an instruction's output assignment. Those remain integration obligations.

## Solver/key-shape lifting audit (C1.K.2.b.8.2)

### Exact API and reusable invariant contract

Source paths below are relative to `venom/`.

| Stage | Source and actual call/result | Shape obligation/provider |
|---|---|---|
| Load entry | `passes/load_elim/defs/loadElimDefsScript.sml:283-289`: `load_analyze ctx fn = df_analyze Forward NONE load_join load_transfer load_edge_transfer ctx (OPTION_MAP (\lbl. (lbl,SOME FEMPTY)) (fn_entry_label fn)) fn` | Both NONE and SOME FEMPTY satisfy `le_keys_satisfy`, by `le_keys_satisfy_empty`. |
| Initial state | `analysis/dataflow/defs/dfAnalyzeDefsScript.sml:181-186,215-225`: `init_df_state bottom lbls` has empty ds_inst and all listed boundaries bottom; optional entry overwrites one boundary | Empty/default maps and optional empty entry satisfy shape; convergence invariant for the actual override is `le_solver_entry_init`. |
| Join input | Same file:144-160: `df_joined_val dir bottom join edge_transfer ctx entry cfg st lbl` folds neighbor boundary values from bottom and optionally joins entry value | Requires **bilateral** closure `P a /\ P b ==> P (load_join a b)`, provided by `le_keys_satisfy_join`. Identity edge is `load_edge_transfer ctx src dst ll = ll` (load defs:274-277). |
| Block process | Dataflow defs:162-177: `df_process_block dir bottom join transfer edge ctx entry cfg bbs lbl st` folds instructions and joins old boundary with final value; it changes only ds_boundary | Transfer shape is `le_absolute_keys_transfer`, for every instruction, under configured context and empty BP queries. Old boundary also needs shape; do not identify it with fresh exit. |
| Worklist | Dataflow defs:229-241: `SND (wl_iterate changed process deps wl0 st0')`, with `changed lbl old new = (df_boundary bottom new lbl <> df_boundary bottom old lbl)`, Forward deps = cfg_succs_of cfg, wl0 = cfg_dfs_pre | Finite-step preservation alone does not justify WHILE result. Termination is already owned/proved by C1.S.2, not a new K obligation. |
| Population | Dataflow defs:192-205: `df_populate_inst dir bottom join transfer edge ctx entry cfg bbs lbls st` uses the **fixed** input st for joined boundaries and FUNIONs each fold's inst_map into ds_inst | Requires bilateral join, transfer, edge and boundary shape; prefix fold stores pre-instruction values plus exit. Wrapper below already covers population and default indices. |
| Query | Dataflow defs:63-68,83-88: `df_at bottom st lbl idx` and `df_boundary bottom st lbl` default to bottom on absent map lookup | Shape therefore holds even at arbitrary/nonexistent indices if established by the full invariant wrapper; no bounded-index premise needed. |

`analysis/dataflow/dfAnalyzePropsScript.sml:141-169` is NOT directly usable:
its join premise is `!a b. P a ==> P (join a b)`. With P =
`le_keys_satisfy (le_absolute_key space)` and a = NONE, load_join returns
arbitrary b, so unilateral closure is false. Boundary/process/restricted
variants at 280-371 retain that same problem.

The exact reusable replacement already exists in this task:
`passes/load_elim/proofs/loadElimBilateralInvariantScript.sml:121-144`,
`le_df_analyze_invariant_bilateral`. Argument order is
`dir bottom join transfer edge ctx entry fn P leq m b Q`. Its premises are:

* `P bottom`; optional entry value satisfies P;
* `!a b. P a /\ P b ==> P (join a b)`;
* `!inst a. P a ==> P (transfer ctx inst a)`;
* `!src dst a. P a ==> P (edge ctx src dst a)`;
* `!lbl st. Q st ==> leq st (df_process_block dir bottom join transfer edge ctx entry (cfg_analyze fn) fn.fn_blocks lbl st)`;
* the same process preserves Q;
* Q holds at init_df_state with the actual optional entry override;
* `bounded_measure Q leq m b`.

Conclusions are simultaneously `!lbl idx. P (df_at bottom
(df_analyze dir bottom join transfer edge ctx entry fn) lbl idx)` and
`!lbl. P (df_boundary bottom (df_analyze dir bottom join transfer edge ctx
entry fn) lbl)`. Its implementation already packages combined worklist
invariance, empty ds_inst before population, bilateral boundary preservation
and `populate_inst_P`. Do not duplicate this machinery or rely on generic
[local] lemmas. The exported generic bilateral boundary-only theorem is in
`analysis/dataflow/proofs/dfAnalyzeProofsScript.sml:2188-2213`; no new generic
wrapper is missing.

### Convergence witnesses and intended next statement (not proved here)

Use exactly the convergence witnesses used by
`loadElimNonemptyScript.sml:36-63`, replacing only its element predicate:
Q = `le_solver_inv (set (fn_labels fn)) (le_generated_keys ctx (fn_insts fn))
(le_generated_operands (fn_insts fn))`, leq = `le_solver_leq`,
m = `le_solver_rank (set (fn_labels fn)) (le_generated_keys ctx (fn_insts fn))
(le_generated_operands (fn_insts fn))`, and
b = `CARD (set (fn_labels fn)) * (1 + CARD (le_generated_keys ctx (fn_insts fn)) *
(CARD (le_generated_operands (fn_insts fn)) + 1))`.
`loadElimSolverHelpersScript.sml:210-260` supplies process closure,
inflationarity and bounded measure; `loadElimConvergenceScript.sml:7-28`
supplies optional-entry initialization. C1.S.2.c.2's
`le_load_analyze_fixpoint` (same file:41-67) proves stable equations under
wf_function. It is not by itself a no-invented-keys theorem.

Concrete next lifting statement, suitable for a separate authorized proof:

```sml
wf_function fn /\ le_configured_context ctx /\
(!v. bp_get_ptrs ctx.lctx_bp v = []) ==>
(!lbl idx. le_keys_satisfy (le_absolute_key ctx.lctx_addr_space)
  (df_at NONE (load_analyze ctx fn) lbl idx)) /\
(!lbl. le_keys_satisfy (le_absolute_key ctx.lctx_addr_space)
  (df_boundary NONE (load_analyze ctx fn) lbl))
```

All element premises have providers in loadElimKeyShapeInvariant:
empty/entry, bilateral join and unrestricted-instruction transfer. The
unrestricted closure is valid here, unlike generated-support closure:
configured load/store guards enforce shape regardless of instruction membership.
It must NOT be derived from membership in le_generated_keys (an overapproximation).
Imports needed for the future instantiation include loadElimBilateralInvariant,
loadElimConvergence and loadElimSolverHelpers. No additional convergence proof
or solver iteration induction is warranted.

For bounded prefixes, existing `le_analyze_prefix_fold` in
`loadElimSolverProvenanceScript.sml:92-113` gives the exact fold at
`df_at NONE (load_analyze ctx fn) lbl n` over `TAKE n bb.bb_instructions`,
assuming wf_function, reached label, lookup_block = SOME bb, n <= LENGTH,
and the explicit process fixpoint (dischargeable by le_load_analyze_fixpoint).
Its shape preservation is already `le_absolute_keys_fold`. This is an
alternative bounded consumer, not a replacement for arbitrary-index population.

### Consumer contract and outstanding semantic gaps

| Consumer | Available static/local fact | Required dynamic conclusion and owner |
|---|---|---|
| Singleton eliminated load | `le_analyze_singleton_origin` gives entry retention or last generating instruction with preserved static lookup; future lifting gives absolute-key shape | C1.P.3 must select the actual producing read/store event, establish defined read and value there, and transport both key address and singleton value to the consumer despite loop/PHI redefinitions. Shape does not imply this. |
| Redundant store with normalized alternatives | Retained-store content lemmas in loadElimRetainedRead preserve a fixed read under negative alias; `*_key_read` requires explicit address equality | C1.P.3 must prove selected read equals the current compared store value; C1.P.5 must establish le_chain_valid for every normalization. Equality of normalized syntax alone is not evaluation agreement. |
| Generated PHI | `le_analyze_selected_predecessor`/`le_analyze_selected_exit` expose containment in concrete predecessor/exit maps; `le_analyze_multivalue_origin` preserves the static list through the prefix | C1.P.4 must evaluate the chosen incoming operand in the predecessor **pre-PHI snapshot**, prove find_join_block placement, then persistence of fresh output/read to eliminated load. C1.P.3 supplies selected read validity; no simultaneous truth of all alternatives. |
| Computed read/write address | le_empty_read_key_address and le_empty_write_key_address require equal defined source/normalized evaluations; dload uses le_dload_key_address | C1.P.5 must supply exact le_chain_valid_eval antecedent at reached rebuilt-DFG use. C1.P.3/P.4 must preserve LK_Op evaluation over the relevant intervals (and labels for Label operands). Absolute LK_Loc address independence is already local. |
| Later rounds | No-ALLOCA preservation permits new empty-BP-query analyses | C1.P.5 and round simulation still owe reached normalization and original/transformed history compatibility. Never transfer original universal step preservation to transformed DFGs. |

These P.3/P.4/P.5 conclusions remain unproved gaps in integration, not new
assumptions of the frozen theorem. The key-shape lifting itself has no such
dynamic premises and can be separated from them by strategy review.

Validation for this diagnostic: loadElimKeyShapeInvariantTheory builds at the
default tactic timeout (2026-11-05). No final-theorem or frozen-definition edits.
