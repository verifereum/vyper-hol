# Numeric and demand interface audit

Diagnostic for C0.analysis.global.numeric_demand_audit. No theorem asserted by
this note is a new assumption of the stage contract. Source locations below
refer to the audited SML source. Frozen statements and executable definitions
are unchanged.

## 1. Actual production dependency chain

`venomPassDispatcherScript.sml:163-173,226-235` calls
`concretize_function_fuel_in_context (concretize_memloc_fuel fn)` with the
current unit context and global reserved intervals. In
`concretizeMemLocDefsScript.sml:1238-1249` the nontrivial branch calls
`compute_function_layout_fuel_in_context`; that function constructs exactly
`cfg_analyze fn` at lines 1118-1121, then runs `bp_analyze_fuel` and
`compute_alloc_map_fuel_in_context`. Production fuel is
`4 * (LENGTH (fn_insts fn) + LENGTH fn.fn_blocks + 1)` (1198-1201).
The no-liveness evaluator branch is separate and must not be assumed to run
these analyses.

IMPORTANT correction to the anticipated interface: ConcretizeMemLoc liveness
DOES NOT consume `bp_segment_from_ops`, `completely_contains`, `may_overlap`,
or even `ptr_off`. Its consumer is `find_base_allocas` (101-108), which erases
ALL offsets. `ml_liveat_inst` (188-215) records incoming live/read/callee demand,
then kills only a singleton write base whose literal write size equals the
allocation size, with no read of the same base. `ml_kill_write` (175-184)
does not test the pointer offset. This is exactly the predicate
`ptr_ml_can_kill` in concretizePtrReadCoverageScript.sml:142-148.
Consequently a universal exact-offset theorem is NOT a prerequisite of this
pass's safe-kill argument. The necessary numeric fact is size plus runtime
confinement, not correctness of SOME offsets in BP.

A different BP consumer, `bp_segment_from_ops` (basePtrDefsScript.sml:295-313),
uses singleton pointer lists to produce relative offsets; `memloc_runtime_region`
(memLocDefsScript.sml:111-120) adds the runtime allocation base as a NATURAL.
`completely_contains` (56-67) compares fixed relative intervals with equal
allocation keys. `may_overlap` (71-92) uses distinct allocation keys to exclude
overlap. Those interfaces require numerical soundness and bounded regions;
they must not be used as if they were already justified by Local base coverage.
They are not on the production liveness call path above.

## 2. HOL-shaped obligations: distinguish directions

In the following sketches `R` is a reachable active frame equipped with the
existing origin map, P witness, well-formedness and successful-step facts;
it is NOT an opaque proposed new premise of the stage theorem.

### Optional fixed-pointer interface (not needed for liveness)

A useful *word-valued* statement would be:

```
R /\ FLOOKUP om v = SOME (OriginLocal aid,(b,sz)) /\
bp_get_ptrs bp v = [Ptr (Allocation aid) (SOME off)] ==>
lookup_var v s = SOME (n2w (b + off))
```

This is not yet proved. Conversion into the existing natural runtime-region
interface additionally needs `b + off < dimword (:256)` and agreement between
this origin instance and `FLOOKUP s.vs_allocas aid`. Then, for literal-sized
`ops`, one could conclude

```
memloc_runtime_region (bp_segment_from_ops bp ops) s = SOME (b+off,n)
```

when `ops.iao_ofst = Var v` and `ops.iao_max_size = SOME (Lit (n2w n))`,
with `n < dimword (:256)`. Without the nonwrapping hypotheses a word equality
is NOT an equality of natural addresses. Unknown-offset membership alone says
nothing useful about containment; use access_ok for actual accesses instead.

For Incoming origins the actual constructor is `OriginParameter k`, not a BP
allocation. BP has no PARAM seed (basePtrDefs:178-179); do NOT replace that tag
by `Allocation k`. Resolve its site via PG and the saved caller argument,
ultimately reaching an ancestor Local origin. This needs a stack relation,
not the fixed-pointer statement with a renamed tag.

### Conservative access/base coverage needed here

```
R /\ mem_read_ops inst = SOME ops /\ ops.iao_ofst = Var v /\
FLOOKUP om v = SOME (OriginLocal aid,(b,sz)) ==>
MEM (Allocation aid) (find_base_allocas bp (Var v))
```

The analogous write statement is needed. Current/saved canonical production
base coverage is checked by `origin_frame_current_production_coverage` and
`origin_frame_saved_production_coverage` in concretizeAnalysisScanCoverage.
Their precise well-formedness/SSA hypotheses must still be supplied by stage
invariants. They give base membership, NOT numeric offsets. Combined with
`access_ok` (ptrDiscipline:518-545), non-revert nonempty accesses through a
provenance-bearing operand satisfy `b <= addr /\ addr+n <= b+sz`.
For Incoming accesses preserve caller allocation demand via INVOKE argument
coverage, rather than requiring a local BP seed for the parameter.

### Minimal safe-kill arithmetic and semantic bridge

The essential arithmetic is simply:

```
b <= addr /\ addr+n <= b+sz /\ n = sz ==> addr = b
```

For an actual `ptr_ml_can_kill (Allocation aid) bp sizes inst`, prove a
semantic bridge that either the instruction does not successfully continue,
or every relevant runtime instance of aid that carries future untainted byte
demand has its entire region overwritten. For a nonempty instance this uses:
(1) write origin is Local aid (not merely membership in BP),
(2) actual write length = `inst_write_size inst` = site size = sizes aid,
(3) `access_ok` confines the write to that SAME instance,
(4) writes remove old-byte demand, and reads are re-added before the kill.
Zero-sized sites have no byte demand. Revert forwarding needs its own
terminal/revert branch; access_ok deliberately does not confine it.

For consumers that really use `completely_contains`, the separate bridge is:

```
completely_contains outer inner /\
memloc_runtime_region outer s = SOME (a,n) /\
memloc_runtime_region inner s = SOME (b,m) ==>
m = 0 \/ (a <= b /\ b+m <= a+n)
```

Even that natural-interval implication only proves a real write kills the
inner region AFTER proving that the outer region is actually written.
It does not justify `ml_kill_write` by itself, nor is it required there.

## 3. Transfer audit and pitfalls

| Branch | Source behavior | Required semantic boundary / status |
|---|---|---|
| ALLOCA | BP seeds inst_id at SOME 0 (basePtrDefs:89-92,121); origin records Local id | Local base coverage checked. Site size and actual successful ALLOCA shape must link to get_alloca_size/context_alloca_size. Reexecution is cached within a frame (see section 5); distinct INVOKE activations remain separate. |
| ASSIGN | copies the source list, including empty (174-177) | Origin Local flow checked; any optional numeric proof uses successful operand evaluation, not definedness of every static variable. |
| PHI | unions old result with all available operand lists, normalizes per base (167-172) | Local membership at production fuel checked, so a reached Local alternative is not omitted under those hypotheses. SOME offset precision does not follow. Static phi_pv_all_var and the write-root disjointness clause must rule out local/incoming mixing for a must-write. |
| ADD literal | natural addition to offset, either operand order (128-139) | Word-valued equality may be modular; natural equality needs a separate no-wrap fact. Not needed by base-only liveness. |
| SUB literal | SOME subtraction only if literal <= old offset; otherwise NONE (149-155) | Unknown is conservative for base membership; optional exact numeric theorem needs the left-pointer shape and successful step. |
| variable ADD/SUB | writes unknown offsets only when exactly one eligible operand is tracked, otherwise leaves old result (140-162) | Existing Local flow descriptor proof uses affine restrictions; cannot reason from an arbitrary partially propagated map. |
| PARAM | no BP binding; origin uses PG and tags OriginParameter | Incoming demand must be lifted from saved caller. fn_ptr_ok:133-137 excludes a write address statically derived from BOTH Local and incoming roots. Reads/calls can still combine origins and need may-coverage. |
| loop revisit | BP repeated static scans; runtime SSA names may be assigned on multiple dynamic visits | CORRECTION: exec_alloca caches the site by inst_id within the current frame. A revisit does not create another base/size instance. concretizeAnalysisBoundary already proves exec_alloca_cached_site/frame; concretizeAnalysisInstanceProbe checks a loop admitted by SSA, fn_defs_reach_uses and fn_ptr_ok, with old/new origin agreement. Distinct INVOKE activations still need frame-indexed origin agreement. |

At arbitrary finite fuel, a PHI can have only one discovered alternative and a
fixed offset despite an undiscovered alternative. The production Local base
coverage theorem excludes omission of a *reached Local base* under its exact
hypotheses, not omission of Incoming provenance and not incorrect precision
for two paths to the same base. Thus no universal fixed-pointer claim follows
from the existing checked work. This is an auxiliary-interface limitation,
not a checked counterexample to either frozen stage theorem.

## 4. Demand invariant and dependency graph

Use byte demand for an origin INSTANCE `(tag,(b,sz))`: bytes from that instance
whose current untainted value is needed by a later observable read before a
complete overwrite (and before a terminal revert can discard it). The desired
Local boundary is: such demand at an active indexed instruction implies
`MEM (Allocation aid) (ml_lookup liveat addr)`; writes at the current index
must also interfere with every retained demanded instance. To obtain liveset
membership one additionally needs `MEM (Allocation aid) (ml_lookup used addr)`.
Keep this distinct from a claim that every syntactically allocated site is
live at all times. For a saved caller carry demand at its INVOKE index through
the whole callee execution, resolving Incoming sites back to caller instances.

| Obligation | Existing checked boundary | Still missing |
|---|---|---|
| Local origin -> production base | OriginReach/OriginCoverage/ScanCoverage current and saved theorems | Stage supplies exact wf/SSA hypotheses; operand/read/write corollaries |
| Current reads are recorded | ptr_liveat_records | Backward semantic demand induction across real CFG edges and safe kills |
| Non-kill retention | ptr_liveat_preserves with ptr_ml_can_kill | Semantic complete-write bridge above, including Incoming exclusion and loop instances |
| Writes appear in livesets | ptr_fuel_liveness_covers_write, independent of fuel | Relate runtime write's Local base to syntactic operand; pair it with other site's demand |
| Forward used | ml_used_inst:248-261 merges bases of ALL operands; INVOKE imports also merged | Runtime allocation-use history -> production used membership |
| Suspended caller at INVOKE | ml_liveat_inst:195-205 includes callee metadata AND all argument bases before kill; used does likewise | Caller future-demand retained at call; Local argument membership; stack Incoming resolution; callee duration/interference lifting |
| Callee allocation summaries | callee_mems_used/imported_mems_used:896-923; apply_context_concretize_layout:1190-1195 records own + transitive imports | callee_first induction over actual stage visitation; observed callee footprints covered by fn_mems_used; unique IDs prevent size conflation |
| Liveness fuel | ml_iterate_fuel:424-435, context_mem_livesets:932-941; fuel is linear in instruction+block count | Quantitative propagation of each demand/use fact through <= block-count simple paths, early-exit stability, sorted-set lookup invariants, and read/write timing. BP base fuel proof does not prove this. |
| Liveset intersection -> layout | ml_livesets_insts:353-363 intersects liveat and used; context allocator:954-978 imports fixed intervals by liveset | Pairwise simultaneous-demand membership -> interval separation, not merely completion against reserved intervals |

No numeric convergence premise or def_available_at premise was introduced.
Availability must be derived at each actual successful use, or its precise
necessity demonstrated before exercising the task's limited allowance. The
recommended next planning decision is to prioritize the base-only semantic
safe-kill/instance boundary and liveness fuel, not universal BP exact offsets.
No new counterexample was constructed or verified by this diagnostic.

## 5. Instance validation follow-up (checked bounded probes)

`concretizeAnalysisInstanceProbeTheory` builds with no cheats (tool output
TO_concretize_sim-20261104T015749Z_m2134_t001). These are diagnostics, not
universal safe-kill or stage theorems.

### Same-frame reexecution

`aip_loop` has entry ALLOCA seed, then loop PHI old = [entry:seed, loop:a],
ALLOCA a, MSTORE a, MLOAD old and a loop/exit branch. `aip_loop_ssa`,
`aip_loop_definite_assignment` and `aip_loop_ptr_ok` check the exact three
structural predicates, with P = K {}. Thus those predicates do admit revisits;
it would be wrong to infer their impossibility from SSA. `aip_loop_bases`
computes old's production bases as [Allocation 1; Allocation 10]. The store
through a has singleton [Allocation 1] and satisfies ptr_ml_can_kill with size
32 (`aip_static_kill`). On a second visit the backedge PHI selects Local 1,
(256,32) (`aip_loop_old_origin`); the ALLOCA returns 256 again and origin_out
returns that same site (`aip_second_visit_cached`). `aip_cached_no_fresh_bytes`
checks no fresh tainted region is introduced. The full MSTORE range is
[(256,32)] and the old-site word read after that store is 9
(`aip_cached_write_range`, `aip_old_read_after_full_store`, the latter reusing
the general mload_mstore_same boundary).

Consequently the proposed *fresh old/new instance on each loop iteration*
objection is withdrawn. Reexecution preserves the instance; the ALLOCA itself
neither kills nor freshly taints its existing byte demand. The subsequent
full write kills its old contents. No allocation-event index is needed to
distinguish visits to this ALLOCA within one frame. Across INVOKEs retain a
frame-activation index: setup_callee starts with empty vs_allocas, while the
caller map is saved/restored. A universal theorem must still show that every
Local aid provenance in a given frame agrees with that frame's cached site,
not merely assume equality from its static tag. It must handle Incoming sites
by resolving saved arguments, not by relabelling them Local.

### Incoming exclusion

`aip_param_has_no_local_base` checks PARAM gives an Incoming origin and no BP
base. By itself its store cannot kill Allocation 1. `aip_mixed` is a diamond
merging ALLOCA a with PARAM p at a PHI v. Production BP returns [Allocation 1]
for v (`aip_mixed_bp`). Nevertheless v belongs to BOTH derived-root sets
(`aip_mixed_roots`), and `aip_mixed_rejected` proves ~fn_ptr_ok (K {0}) aip_mixed.
The frozen write-root-disjointness clause is essential, not redundant with
BP completeness.

The missing universal interface can be stated without inventing BP PARAM
seeds. Under the actual reachable-frame, parameter-witness, SSA/well-formedness
hypotheses (to be enumerated/proved, not added to the stage contract):

```
FLOOKUP om v = SOME (OriginParameter k,site) ==>
 v IN pointer_derived_vars fn (ptr_roots P fn DIFF alloca_roots fn)
```

A separate *static* analysis-origin boundary is needed:

```
MEM (Allocation aid) (find_base_allocas bp (Var v)) ==>
 v IN pointer_derived_vars fn (alloca_roots fn)
```

For production bp, combining these with fn_ptr_ok and a Var write address
excludes Incoming provenance whenever the analyzed write set is nonempty.
Local base coverage alone proves neither implication. Mixed reads remain
permitted and require may-demand propagation through both local and incoming
origins. These statements remain proposed interfaces, not checked universal
results of this diagnostic.

### Opcode/actual-write audit

Sources: memLocDefsScript.sml mem_write_ops (roughly 190-258),
concretizeMemLocDefsScript.sml inst_write_size (132-140),
codegenRelScript.sml source_memory_write_ranges (131 onward),
venomExecSemanticsScript.sml step_inst_base (599-609, 863-893, 935-989).
`ptr_literal_write_range_size` already proves the generic fact that a reported
range has the literal write size. It does NOT prove every byte in that range
is successfully written. Do not duplicate that lemma.

| Opcode | inst_write_size = SOME n | Successful actual effect | Failure/revert qualification |
|---|---|---|---|
| MSTORE | n=32, two operands | mstore writes 32 bytes at evaluated dst | Undefined operands/wrong arity give Error, no successful continuation |
| MSTORE8 | n=1, two operands | mstore8 writes one byte | Same Error cases |
| MCOPY | third operand Lit n | mcopy reads padded source memory then writes exactly n bytes at dst | Undefined operands/arity Error; reads happen before write; own-base read prevents the static kill |
| CALLDATACOPY | third operand Lit n | TAKE n of source tail ++ REPLICATE n 0, then write_memory_with_expansion | Error if operand undefined or arity invalid; padded source guarantees n bytes |
| DLOADBYTES | third operand Lit n | Same padded n-byte write from data section | Same Error cases |
| CODECOPY | third operand Lit n | Same padded n-byte write from code | Same Error cases |
| EXTCODECOPY | fourth operand Lit n | Same padded n-byte write from account code | All four operands must evaluate; wrong arity Error |
| RETURNDATACOPY | third operand Lit n | In-bounds branch writes TAKE n of returndata tail | Out-of-bounds branch is Abort ExHalt_abort, not OK; reported range alone does not imply a write |
| ISTORE | n=32 | Writes immutable bytes, NOT vs_memory | fn_ptr_ok forbids pointer-derived operands at ISTORE. Must exclude before a memory safe-kill conclusion |
| CALL/DELEGATECALL/STATICCALL | NONE even with literal return buffer length | Partial return-buffer writes; range is a maximum, not a must-write | Not kill eligible; do not infer full overwrite from source_memory_write_ranges |
| Other opcodes | NONE | No liveness must-write via this interface | INVOKE handled through summaries/frame simulation, not a local literal write |

Zero size is vacuous byte demand. The revert-forward exemption suppresses
access_ok confinement even at preceding RETURNDATACOPY, so the ordinary
confined-write proof must explicitly exclude that branch. A separate terminal
simulation discharges revert behavior. No successful-write theorem is claimed
here for all opcodes: the table identifies the exact cases that a future
semantic boundary must prove.

### Proposed demand bridge after this diagnostic

Index current/saved demand by frame activation plus (tag,base,size) and byte,
with a future observable untainted read witness before complete overwrite or
terminal revert. ALLOCA first allocation creates fresh/tainted contents;
cached ALLOCA revisits preserve existing demand and provenance. Backward
propagation across successful full writes removes the overwritten byte demand,
while read demand is recorded before a same-site kill. To connect that model
to production liveat/used, the outstanding universal steps are: frame-local
Local-origin/cached-site agreement; Incoming root membership and static
BP-to-alloca-root membership; actual successful full-write effects (excluding
ISTORE); CFG backward/forward propagation and fuel; and imported callee
coverage through saved frames. None is replaced by the bounded computations.
No stage counterexample has been established, no premises changed.
