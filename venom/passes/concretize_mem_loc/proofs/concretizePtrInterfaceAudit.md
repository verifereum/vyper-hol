# Target-prefix proof-interface audit (C1.5.90.18)

This is a design checkpoint, not a theorem or a claim of simulation. Source
locations below are relative to this directory unless stated otherwise.
The frozen stage statements and executable definitions are unchanged.

## Quantifier direction and candidate invariant

The eventual boundary must have the shape

    StageAssumptions(C,C',vs,lo) /\ target_history(vs,C',ht,at)
    ==> exists h,a,witnesses. source_history(vs,C,h,a) /\ Paired(h,a,ht,at,witnesses).

`StageAssumptions` denotes the frozen premises, not additional run hypotheses.
No source history, returned-value equality, read agreement or write exclusion
is an input here. Actual source histories may occur as inputs to *local*
extension lemmas only after the induction has constructed them.

Proposed `Paired` clauses (not yet defined or proved):

1. Actual histories with an order-preserving event alignment. Current and saved
   cursors refer to corresponding functions, labels and retained instruction
   indices. Deleted NOP intervals are source stutters, not target events. PHI
   entry is atomic. Equal predecessor labels do not mean equal entire blocks.
2. `ptr_source_ownership` for the source history, activation tokens/registry,
   births, tagged parameters/current variables and saved maps. Retain births
   after return; importing a pointer does not change its owner token.
   Erasure gives the numerical ghosts used by `ptr_discipline`.
3. One coherent `ptr_stage_placements C' positions` map. Relate each active
   birth to the actual owner's output metadata, not an independently selected
   layout. Local alignment uses the actual per-function positions (whose
   values are positions, as opposed to the global map's position/size pairs).
4. Tagged variables/parameters have syntactic support in the source `fn_pv`
   and `P`; record saved-frame support too. This is derivable on an already
   constructed source history (see below), not a consequence of word transport.
5. `ptr_vars_transport births positions TG tn source target` and analogous
   argument/saved-state relations. Untagged values agree outside source masks;
   tagged values have modular displacement. No positive-size, in-range or
   nonwrapping condition is imposed on arbitrary intermediate pointer words.
6. Equal label lookup tables and all scalar-observable shared fields, or
   appropriate taint-masked storage/transient-storage relations. Track account,
   calldata/code/data/environment, returndata, return-PC and external outcome
   information explicitly. Memory length equality is neither appropriate nor
   needed merely to transport a load. FMP/allocator fields cannot all be equal.
7. A ledger of *past actual* paired successful writes with post-write agreement
   outside the source post-taint, actual footprints and owner/offset mapping.
   Include initial fixed-region bytes as a sentinel. Record aligned source and
   target event indices separately. No assertion about future reads or global
   initialized memory is admissible: dead slots are intentionally reused.

## Checked exports and their exact scope

* `concretizePtrValueTransportScript.sml:5-35`: value/lookup/variables/argument
  definitions. NONE-tagged values use `word_agree_except`; SOME-tagged values
  satisfy `y = x - n2w base + n2w pos` with birth and placement lookups.
  `ptr_vars_transport_eval` (87) requires Var-or-Lit. SOME/NONE inversions
  (74,81,114,121) work in both directions. No tag-support theorem is hidden here.
* `concretizePtrAffineTransportScript.sml:20,45`: ASSIGN transports a supplied
  successful source/target step respectively, for one Var/Lit operand and one
  output. `ptr_affine_transport` (79-94) constructs BOTH successful steps from
  success on either side, Var/Lit operands, two empty masks, ADD with at most
  one tagged operand or SUB with untagged right operand, and the variable
  relation. It does not establish those premises from syntax. Wrapping and
  zero-size probes are local algebra/operational checks, not prefix coverage.
* `concretizePtrValueSelectionScript.sml:18-29`: PARAM requires related
  parameter lists with all-empty masks and literal index/single output;
  success on either side gives both partners. `ptr_eval_operands_transport`
  (63) is OPTREL over Var/Lit lists. `ptr_setup_callee_transport` (49) only
  needs equal block-list nullness; it supplies empty-variable and argument
  relations, not callee execution or control alignment.
* Selection: `ptr_eval_one_phi_transport` (82) and `ptr_eval_phis_transport`
  (130) require equal previous-block labels and Var/Lit resolved choices.
  They preserve parallel reads from original states (probe at 253).
  `ptr_entry_transport` (205) requires the SAME looked-up bb on both sides
  and a successful SOURCE entry; it is not the production entry theorem.
  `ptr_bind_outputs_transport` (183) uses the SAME scalar vals list.
  `ptr_return_bind_transport` (231) assumes `ret.iret_values = ret'.iret_values`;
  it preserves variable relation through merge/adopt/bind, not memory or a
  complete return observation.
* `concretizePtrSourceOwnershipScript.sml`: `ptr_source_ownership_total` (138)
  tags a supplied source history. `ptr_source_ownership_prov_erases` (300)
  and parameter/saved variants (292,308) require absence of DALLOCA.
  `ptr_source_ownership_live_cache` (566) locates a tagged current variable
  in the active owner stack. These are source-only, not paired executions.
* IMPORTANT existing support boundary: `concretizePtrParamSupportScript.sml`
  already defines `ptr_params_ok` and `ptr_static_support` (6-14).
  `ptr_frame_current_static` (125-130) obtains both from `frame_reachable`,
  EVERY fn_ptr_ok and EVERY per-function inst_wf. `ptr_frame_saved_static`
  (134) handles saved frames. `ptr_static_step`, `ptr_static_entry`, and
  `ptr_static_invoke_params` are already checked. Thus a new induction for
  dynamic support would duplicate work: erasure plus birth-domain support
  converts a tagged SOME lookup into numerical SOME and these exports give
  fn_pv/P membership. The global value construction has not yet connected them.
* `concretizePtrStagePlacementsScript.sml:28-33`:
  stage, NONE input eom, shape, distinct ids and callee_first imply existence
  of coherent positions. `ptr_stage_placements_live_owner` (59-77) additionally
  uses run-state/no-DALLOCA, ownership, tag and numerical lookups; concludes
  active owner depth, registry/cache identity and actual output metadata lookup.
* `ptr_gap_ownership_aligned`, concretizePtrDeletedGapHistoryScript.sml:188,
  advances a supplied ownership history over exactly the deleted NOP gap to
  a retained cursor. It does not preserve the paired value relation by itself.
* `ptr_endpoint_protected_livesets`, concretizePtrProtectedLivesetsScript.sml:8,
  selects a last SOURCE writer and production liveset membership throughout
  the suffix. Requires an already constructed source history, access_ok at
  all its observations, an untainted owned endpoint byte, a read/INVOKE address,
  no revert-forward, owner/stage/analysis facts and other frozen well-formedness
  premises. It does not say that no TARGET write hits the byte.
* `ptr_output_local_local_separation` (concretizePtrLayoutOutputScript.sml:135)
  and `ptr_output_suspended_descendant_separation`
  (concretizePtrCallSeparationScript.sml:8) provide layout geometry under their
  respective local/imported conflict and placement hypotheses, not arbitrary
  event noninterference. `concretizePtrWriteFootprintScript.sml:15-80` checks
  MSTORE footprint/owned relocation/same-owner exclusion/fixed footprint;
  it is not exhaustive write coverage. `concretizePtrOwnedStoreAdvanceScript.sml`
  is a store-advance library, not a read-recovery or universal-prefix theorem.
* `ptr_chrono_step_byte_frame` and `ptr_chrono_history_byte_frame`
  (concretizePtrOperationalBytesScript.sml:7,30) frame bytes outside actual
  source-memory-write ranges. `ptr_chrono_last_writer_agreement` (39-50)
  consumes post-write equality AND source/target suffix exclusion. It uses
  a COMMON index n and w for two histories; source NOP stuttering requires
  aligned-index adaptation, not direct application with unequal event counts.

## Dependency matrix

| Clause/transition | Initialization source | Preservation inputs / checked supplier | Remaining gap |
|---|---|---|---|
| Stage metadata | ptr_stage_placements_exists | live_owner, actual stage lookup | connect coherent map to each transformed block's instruction map |
| Source history/owners | source root and source_ownership_total | tagged_chrono_step, erasure/live_cache exports | actual partner transitions must first be constructed |
| Dynamic support | empty ghosts; frame_current_static | frame/saved_static + ownership erasure/domain | compose exports once; do not assume tagged support from values |
| Initial scalar values | same vs variables/entry ghosts | lookup transport reflexivity | exact entry fields/labels and target PHI-prefix correspondence |
| ALLOCA / cached ALLOCA | registry birth cache | actual exec_alloca + placement/size exports | extend paired values and ledger while output executes literal ASSIGN |
| Deleted NOP | ledger block alignment | gap_ownership_aligned | preserve values/fields across inserted source interval |
| ASSIGN, ADD/SUB | variable relation | assign_back / affine_transport | derive shape and masks from source access/taint/syntax and support |
| Other scalar pure ops | equal untainted inputs | actual step_inst_base operation | exhaustive taint-aware operators, including shifts of tainted words; Label eval |
| PHI/block entry | predecessor/cursor agreement | eval_phis_transport | same PHI prefix with changed tails, reverse successful entry, ghost/cursor updates |
| EQ/LT/GT | source access_ok at current prefix | same numerical site and closed in-site values (ptrDiscipline:544-553) | tags may differ at zero-size/equal numerical births; prove equal displacement or exclusion, then bounded target values for ordered comparison |
| Branch/assert/DJMP | scalar field agreement | equal empty-mask condition/selector; actual semantics | comparison results must already agree; target success must select source-successful branch |
| Memory read | initial fixed sentinel or last source writer | protected_livesets + layout separation + paired ledger + byte frame | exhaustive target footprint exclusion, owner-relative mapping, aligned indices and taint; not supplied by local value theory |
| Memory write/copy | actual paired instruction | MSTORE interfaces; source access_ok/taint_ok | other writers incl MCOPY, MSTORE8, copies/external writes; copied bytes depend on current read recovery |
| INVOKE | decoded name + related args | eval_operands/setup + ownership call rule | label operands if present; zero scalar masks from taint_ok; corresponding callee/entry/saved cursor, shared-field/ledger preservation |
| Internal return | saved value relation | scalar bind + merge/adopt (conditional) | derive equal RET values using ptr_use_ok/taint_ok, labels/token; actual IntRet, restoring owner and full shared state |
| External effects | equal environment/outcome inputs | step_inst_base dispatch and call helper definitions | CALL/STATICCALL/DELEGATECALL/CREATE/CREATE2 account/storage rollback, returndata and output-memory footprints; not just MSTORE |
| Terminal/error/revert | actual reachable endpoint | frame_reachable has only next/block/call/ret rules | Halt/Abort/Error do not extend history; prove absence of a source-success mismatch whenever target DOES extend; special revert-forward and RETURNDATACOPY OOB distinctions |

## Nontrivial unresolved semantic cases

`ptrDisciplineScript.sml:118-137` forbids Labels only for ADD/SUB with a
syntactic pointer operand. `affine_pointer_ops` plus derived tagged support
supplies the one-pointer arithmetic restriction, while `taint_ok` (562-580)
forces arithmetic operand masks empty. For scalar arithmetic or ASSIGN,
Var/Lit cannot simply be postulated: `venomStateScript.sml:328-331` evaluates
Label through `vs_labels`. An equal-label-map boundary can handle this without
changing executable syntax. PHI syntax uses Label selectors; only the SELECTED
value operand needs the value-evaluation relation.

Comparison restriction is stronger than unrestricted relocation but weaker
than tag equality: access_ok supplies equal *numerical* (base,size), including
closed endpoints and size zero. Same tag means same displacement; EQ then
follows by cancellativity, but unsigned LT/GT also need a nonwrapping relocated
closed interval. Different tags cannot be identified just from equal numerical
pairs; active-owner geometry/zero-size analysis must resolve their placements.
This is an explicit integration risk, not a checked counterexample.

Memory recovery can be acyclic for the CURRENT read: the source prefix ends
BEFORE executing that read. Its current operands come from the already
preserved variable relation; access_ok and taint_ok apply to that reachable
endpoint without requiring successful evaluation of the read result. Select
untainted endpoint bytes and their last writers on that finite prefix, then
exclude target suffix writes using previously paired event footprints and
retrospective livesets. Recover bytes before executing the source read, and
only then extend values/ledger. The missing step is exclusion, not permission
to assume read equality. For fixed bytes use the initial sentinel; for tainted
bytes prove exactly the permitted mask propagation. Ordinary protected-liveset
hypotheses exclude revert-forward, so exceptional forwarding needs a separate
argument rather than reuse with an unproved negation.

Semantics inventory: step_inst_base (venomExecSemanticsScript.sml:578-1130)
includes storage/transient operations, ILOAD/ISTORE, hash/log/RETURN memory
reads, calldata/code/data/returndata writes, environment/account reads and
external calls/creation. CALL helpers at 364-535 use observed outcomes and
rollback/account fields. Equal variable maps alone do not imply equal outputs
of these operators. MEMTOP/FMP operations forbidden by fn_ptr_ok must be
eliminated from syntax, not handled by an assumption of equal allocator state.
`frame_reachable` (ptrDiscipline:454-506) stops at active instructions and has
no terminal-result constructor. Full equality of dead terminal payloads is
unnecessary for these invariants; returning callee data or an external outcome
that affects a later reachable instruction is NOT dead.

## Smallest proposed next boundary (requires strategist authorization)

First compose the already checked source-support interfaces, without defining
a new paired invariant or proving more opcode wrappers. Precise schema:

    ptr_source_ownership vs C h a tokens registry births PT TG saved /\
    EVERY no_dalloca C.ctx_functions /\
    EVERY (fn_ptr_ok P) C.ctx_functions /\
    EVERY (EVERY inst_wf o fn_insts) C.ctx_functions
    ==> (!v tag. FLOOKUP TG v = SOME tag ==> v IN fn_pv P a.po_fn) /\
        (!k tag. k < LENGTH PT /\ EL k PT = SOME tag ==> k IN P a.po_fn.fn_name).

Here no_dalloca abbreviates the existing EVERY instruction <> DALLOCA clause;
this is a statement schema only. Ownership gives a real source history and
frame reachability, erasure gives SOME numerical provenance from SOME tags
(using its domain clause), and frame_current_static supplies support. Saved
variants should reuse frame_saved_static if actually needed, not copy its
induction. There is no target execution or desired value conclusion in these
premises: this is a genuinely acyclic source boundary, not universal coverage.
It closes the specific premise gap advertised by .16/.17 cheaply using existing
exports. An inline derivation may suffice instead of another named synonym.

After that, prioritize a comparison/closed-endpoint compatibility probe and a
production PHI-prefix/Label interface, not an omnibus prefix theorem. Those
are independent of memory read recovery and test whether the proposed value
relation can preserve control at all. Only after these checkpoints design the
paired invariant and exhaustive writer/reader dispatch: initialization ->
source support and metadata -> affine/selection/control -> paired write ledger
-> current-endpoint retrospective exclusion -> reads -> prefix induction.
Calls and external shared-state preservation must participate in that induction;
a callee execution or equal return list cannot be assumed as its conclusion.
The final risk remains high until these integration obligations are proved.

## Verification

The existing affine, selection and concretizeStagePtr targets were rebuilt
successfully for this audit. This confirms the cited local source is buildable,
NOT that frozen final obligations have been discharged. No HOL source or frozen
statement was edited by this audit.

## Production comparison diagnostic (C1.5.90.21)

`concretizePtrComparisonProbeTheory` now checks production transformation and
actual `step_inst` computations (raw allocator starts at 64, not zero).
For sizes `[0;0;32]`, `[0;32;0]`, and `[32;0;0]`, all three production
positions are 0; metadata preserves the respective sizes. Comparing p and q
by EQ/LT/GT gives respectively `(1,0,0)`, `(1,0,0)`, `(0,1,0)` in the source,
and `(1,0,0)` in all three outputs. Thus the third *production* computation
has a changed decision, not just an arbitrary-map relation countermodel.
Per the checkpoint's stop rule, closed-endpoint experiments are deferred to
strategist review rather than proceeding with universal prefix transport.

This is NOT a counterexample to either frozen theorem. In the changed-decision
case p's numerical provenance is `(64,32)` and q's is `(96,0)`. The comparison
clause of `access_ok_def` requires the SAME `(b,sz)` for both operands and
therefore excludes this source comparison from a pointer-disciplined execution.
Zero-sized ALLOCA itself is not forbidden by `inst_wf_def` (only a literal
operand and one output are required). The probe does not assert the full frozen
antecedent. The diagnostic correctly distinguishes executable syntax from the
semantic discipline.

Premise audit for ComparisonTransport: source ownership gives tag erasure and
birth support, but does not identify tags when numerical sites coincide.
Half-open allocation-table disjointness gives no zero-size uniqueness. In the
checked `[0;0;32]` case p and q have distinct zero-size births with identical
raw base 64 and identical production position 0, so comparisons agree there;
this does not prove universal equality of production positions for coincident
births. Common displacement for the two comparison operands remains an
integration obligation. Source closed bounds are supplied by the comparison
clause of `access_ok`, not by arbitrary pointer arithmetic. Strict target
endpoint bounds must come from successful checked layout: the production
completion checks `pos + sz < dimword (:256)` and rejects overflow, whereas
`ctx_eom_bounded eom C'` with unconstrained natural eom alone cannot imply it.
No universal compatibility or target-prefix coverage claim is discharged.

Verification: holbuild on ComparisonProbe and StagePtr succeeds; the latter is
only a regression check and still contains its pre-existing unresolved cheats.
No frozen statement, executable definition or pointer-discipline definition
was changed.

### Premise-filtered follow-up

Strategist review classified the differing-site test above as excluded and
reauthorized the remaining finite diagnostics. `ptr_cmp_live_zero_births`
places a positive allocation before two consecutive zero-size births, with
MSTORE through the positive pointer after all comparisons. Its production
metadata is `[(20,0,32);(21,0,0);(22,0,0)]` (keys are Allocation ids).
The actual raw birth records are `(64,32),(96,0),(96,0)`; both zero-size
pointers evaluate to 96 raw and 0 after production transformation. EQ/LT/GT
agree as `(1,0,0)`. `ptr_cmp_live_birth_records` also checks inst_wf for this
function and all three earlier examples. These are not full ctx shape/SSA/
reachability/ptr_discipline certifications.

`ptr_cmp_closed_endpoint_decisions` executes EQ/LT/GT on 64/96 versus 0/32
and on the reversed pairs, obtaining respectively `(0,1,0)` and `(0,0,1)`.
The zero-size coincident pair 96/96 versus 0/0 gives `(1,0,0)`.
Both target endpoints 32 and 0 are checked strictly below dimword(:256).
These endpoint tests use one common displacement -64 (or -96 for the
zero-size case); unlike the live-birth experiment they are local operand
computations, not an entire production-transformed function.
`ptr_cmp_common_site_access` separately checks access_ok for each comparison
on the common source site (64,32), in both operand orders, and on (96,0).
No semantic premise is inferred from syntactic well-formedness alone.

Still missing for universal use: deriving equal displacement for coincident
numerical sites with distinct owner tags in arbitrary production contexts;
deriving the relevant owner's strict layout endpoint bound; constructing the
source prefix before invoking source discipline; transporting variable values
and taint, control, memory reads and calls. None is supplied as an assumption
of a purported universal theorem here. No checked common-site example changes
a decision, and no frozen-theorem counterexample is claimed.
