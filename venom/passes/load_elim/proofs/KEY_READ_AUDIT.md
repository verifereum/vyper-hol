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
