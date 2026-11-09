# Latest-join suffix interface audit (C1.P.4.2.3.4.2.12)

This is a diagnostic proposal, NOT a theorem, axiom, or new premise of the
frozen result. No consumer-currentness claim is certified here.

## 1. Exact source goal and shared hypotheses

In the signatures below `H` is a **textual abbreviation only** for this
conjunction (not a proposed HOL constant):

```
wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
(!v. bp_get_ptrs ctx.lctx_bp v = []) /\
ctx.lctx_aliases = ma_analyze ctx.lctx_bp fn ctx.lctx_addr_space /\
fn_entry_label fn = SOME s0.vs_current_bb /\
is_fixpoint (df_process_block Forward NONE load_join load_transfer
  load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
  (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
  (load_analyze ctx fn) /\
le_occ_prefix C fn s0 (pre ++ PhiOcc bb u p :: suffix) i s /\
(!bb' n fuel u' t'. MEM (StepOcc bb' n fuel u' t')
  (pre ++ PhiOcc bb u p :: suffix) ==> dfg_assigns_sound ctx.lctx_dfg u')
```

Proposed actual-action source interface, expanding H at declaration time:

```
H /\
compute_phi_action m (cfg_analyze fn) (load_analyze ctx fn) key
  s.vs_current_bb i = SOME pa /\
bb.bb_label = pa.pa_join_lbl /\
i.inst_opcode = ctx.lctx_config.lc_load /\
i.inst_operands = [addr] /\
key = load_get_read_key ctx.lctx_bp ctx.lctx_addr_space
  (normalize_operand ctx.lctx_dfg []) i /\
FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn)
  s.vs_current_bb s.vs_inst_idx)) key = SOME ops /\
1 < LENGTH ops /\
(!b x y. MEM (PhiOcc b x y) suffix ==> b.bb_label <> pa.pa_join_lbl)
==> le_key_read ctx.lctx_addr_space key u =
    le_key_read ctx.lctx_addr_space key s
```

The load-shape and point lookup must be linked to the actual action use site,
not merely to an arbitrary action returned for some other instruction. The
candidate is not asserted proved or sufficient for all subsequent rounds.
The local sufficient certificate below deliberately separates this remaining
static extraction obligation from semantic read preservation.

## 2. Capture's ORIGINAL PHIs: no-write justification exists

`le_phi_definition_key_cut` already proves that a reachable PHI output `v`
forces the index-zero lookup of `LK_Op (Var v)` to be NONE. It is NOT
singleton-restricted. Thus any SOME ops at the capture block's index zero
excludes its address variable from **all original PHI outputs**. Use
`le_occ_phi_static`, `le_phi_prefix_take`, and `phi_prefix_all_phi` exactly
as in `le_retained_occ_key_no_write`, but replace its singleton predicate
by index-zero presence. `le_ordinary_definition_key_cut` likewise excludes
an ordinary output from a key present immediately before that instruction.
Neither requires simultaneous evaluation of the alternatives.

`le_absolute_key_occ_after` then transports the address across the capture
PhiOcc; `le_phi_read_occ_after` transports fixed-address reads. The chain
must start at u, INCLUDE `PhiOcc bb u p`, and end at s. Starting only at p
would omit the key-address hazard. LK_Loc is handled by
`le_absolute_location_address`; literal LK_Op needs no variable no-write.

## 3. Exact sufficient retention certificate and its missing extraction

For every StepOcc b n k x y in `PhiOcc bb u p :: suffix`, require

```
?vs. 1 < LENGTH vs /\
 FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn)
   b.bb_label n)) key = SOME vs /\
 FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn)
   b.bb_label (SUC n))) key = SOME vs
```

For every PhiOcc b x y in that list, require

```
?vs. 1 < LENGTH vs /\
 FLOOKUP (unwrap_load_lattice (df_at NONE (load_analyze ctx fn)
   b.bb_label 0)) key = SOME vs
```

Lists may DIFFER between blocks. The sufficient semantic signature is H,
these two universal membership conditions, and
`le_absolute_key ctx.lctx_addr_space key`, implying the equality in section
1. Address existence need not be a new premise: if its value at u is NONE,
address transport makes both key reads NONE; if SOME a, word evaluation or
the absolute-location shape gives a < dimword (:256).

Missing local generalizations: `le_configured_retained_step_read` and
`le_retained_occ_read` currently take SOME [op] and non-generation. For a
multivalue output no generator can have overwritten that key (generators
write singletons). Store invalidation membership and nonstore effect lemmas
in TransferRetention are singleton-shaped although their proofs only use
presence plus exclusion of overwrite. Reuse `le_retained_store_regions`
and the region/read interfaces; do not duplicate their alias analysis.
`le_occ_chain_retained_read` is ALREADY general enough once local read
preservation and address no-write are established.

Missing STATIC extraction from section 1: reverse the find_join walk along
the actual suffix, stopping at its latest join occurrence. For each FULL
intermediate block use `le_two_distinct_boundary_preserves` and
`le_analyze_boundary_preserving_reverse`; reverse inclusion gives a superset,
not an identical list. Transport two distinct alternatives. For the PARTIAL
consumer block use `le_analyze_multivalue_origin` and the transfer-fold
multivalue-through-prefix fact, not a theorem about its final boundary.
At capture only its input and executed prefix need retain the key; do NOT
require its whole block fold to preserve if capture and consumer coincide.
PHI transfer is identity; `le_analyze_phi_prefix_lookup` supplies the bridge.
Point support gives ALL_DISTINCT before length is used to choose two values.
Placement alone does not export these per-occurrence conditions yet.

## 4. Target extension/framing and exclusion of recapture

Existing EXACT extensions (OperationalHistory) are:

```
le_oper_history r h /\
step_inst fuel C j (le_history_end r h) = OK t
==> le_oper_history r (h ++ [(set j.inst_outputs,t)])

le_oper_history r h /\ eval_phis (le_history_end r h) js = OK t
==> le_oper_history r (h ++ [(le_phi_outputs js,t)])
```

`le_oper_history_neutral_extend` handles index/edge normalization; use the
actual normalizations from occurrence semantics. `le_oper_history_frame`
then derives framing, rather than assuming framed target execution.

Needed syntactic interfaces (not present as named load-elim theorems):

```
set (load_elim_inst ctx actions ll inst).inst_outputs SUBSET
  set inst.inst_outputs

le_phi_outputs (phis_for_block actions lbl ++ rest) SUBSET
  ({a.pa_phi_out | MEM a actions /\ a.pa_join_lbl = lbl} UNION
   le_phi_outputs rest)
```

The first follows from `load_elim_inst_changed` and shared mk_assign/mk_nop
definitions (NOP clears outputs). The second uses generated PHI shape and
its leading-PHI prefix, not an assumption that all of rest is PHIs.
For source-origin instructions, prefix freshness excludes pa.pa_phi_out.
For inserted outputs, `le_collected_action_outputs_distinct` says any action
writing pa.pa_phi_out equals pa; latest join selection excludes that action's
label from later PhiOccs. This excludes writes to ONE selected captured
output, not to every generated variable forever. Normalization events have
empty write sets. Derive zero epoch and use history lookup persistence.

## 5. Target rest-PHI success is not automatic

`execEquivParamBase.eval_phis_agreement` is NOT an appropriate interface
for the frozen padded-memory relations: `valid_state_rel_def` requires exact
`vsr_frame` equality, including memory. Differing trailing zero bytes violate
that requirement. Do not attempt to discharge it with variable agreement.

The checked replacement is `loadElimPhiTransportTheory`:

- `le_snapshot_batch_transport` transports successful snapshot batches and
  relates their results under any relation closed under paired identical
  `update_var` operations. Reads always use the original incoming snapshots.
- `le_eval_phis_transport` specializes this to the leading PHI prefix.
- `le_eval_phis_prefix_eq` gives exact result equality for equal leading
  prefixes, including errors, reusing `abiEncoderObserver.eval_phis_prefix`.
- `le_eval_one_phi_agreement` derives incoming read agreement from equal
  `vs_prev_bb`, equal `vs_labels`, and lookup agreement on Var operands.
  Label operands require label-map agreement; no memory agreement is used.
- `le_configured_rest_phis_transport` combines these with .21's
  `le_configured_transformed_phi_prefix` for arbitrary indexed input lattices.
  From successful source PHIs and incoming agreement it constructs successful
  transformed rest PHIs and relates their results. It does not assume target
  rest success or require an exact-memory relation.

Source freshness and prefix-excluded lookup agreement must still discharge
this consumer's Var condition. Its explicit paired-update closure must be
proved for the relation used by coupling; the frozen equivalences are not
imported or redefined by the helper theory.

`le_occ_prefix_all_entries_phis_success` can then extend rest success to the
prepended batch. Its selected-input availability comes from
ReachedSourceAgreement, not from assuming success of the augmented batch.
The new transport theorem only relates the ORIGINAL/rest PHI results: the
inserted prefix writes fresh outputs on the target side alone. A separate
captured-prefix framing argument must extend that relation while recording
the selected generated output and its key read. Paired identical updates
must NOT be imposed on that inserted prefix. DynamicCapture's rest-success
premise is now constructible through the checked consumer, but its selected
input and full-batch capture/framing obligations remain at actual use sites.
Neither this interface nor source retention supplies local step simulation
for .13: singleton loads, multivalue loads using captured values, redundant
stores with padded memory, calls, and invariant closure still need checked
pass-specific boundaries before constructing actual target suffix execution.

## 6. Noncircular coupling signature and dependency order

Proposed generic history-construction signature, with explicit local
obligations rather than postulated target transitions:

```
(!x y r. E x y /\ R x r ==> ?outs t.
   le_oper_event r outs t /\ R y t) ==>
!x y r. RTC E x y /\ R x r ==>
 ?h. le_oper_history r h /\ R y (le_history_end r h)
```

This is a standard RTC witness-construction SCHEMA, not a missing pass proof: the
hard premise is the local extension for the pass-specific coupled invariant.
For load elimination R must carry source/target state agreement, actual
prefix position and captured outputs needed at that position. E must expose
one real source occurrence, and the local premise must construct the actual
transformed instruction/batch and index/edge normalization, not an arbitrary
le_oper_event. Do not introduce this weak generic schema as a substitute for
the pass simulation framework's real control-flow/run_blocks obligations.

Order: (a) multivalue static retention extraction; (b) presence-based key
no-write including capture PHIs and generalized local retained-read semantics;
(c) source u-to-s read equality independent of ANY target trace;
(d) syntactic target write subsets and padded relation/PHI agreement;
(e) coupled induction, deriving target rest success and augmented success
at each entry, then capture, constructing real step/phi/neutral history;
(f) at a replaced load, use (c) plus capture-output persistence to discharge
its local simulation obligation. All earlier replaced loads in (e) must be
handled by the induction hypothesis on their reached prefixes; assuming the
complete target suffix to justify them is circular. Other singleton/store
simulation and invariant preservation remain separate prerequisites, not
consequences of this audit. Current source has conditional history transport,
NOT this coupled induction. Do not rate its discharge mechanical yet.

Search audit: checked existing DefinitionCuts, SingletonSuffix,
SingletonCurrentness, TransferRetention, RetainedStore, DynamicCapture,
JoinPlacement and OperationalHistory; searched shared pass helpers, simulation
(eval_phis_agreement), analysis definitions/cut machinery and proved memory
pass framing locations. No new duplicate lemma was introduced.

## 7. Local padded simulation audit (.23; supersedes stale proposals above)

Status: diagnostic only. The SML helper build `loadElimPhiTransportTheory`
passes (2026-11-08); no semantic statements below have been added to SML.
Sections 2--3's missing source-retention work is now supplied by
`loadElimLatestRead.le_occ_latest_join_source_read` (lines 144--173).
Section 4's proposed syntactic interfaces are now checked in
`loadElimTargetWrites` (lines 8--16, 25--35, 87--122).
The generic schema in section 6 is NOT the selected implementation route.

### 7.1 Actual framework interface and its limitation

The exact consumer available at `simulation/passSimulationPropsScript.sml:291`
is (notation and binders retained):

```sml
!R_ok R_term bt fn.
  (!s. R_ok s s) /\
  (!s1 s2. R_ok s1 s2 ==> R_term s1 s2) /\
  (!s1 s2. R_ok s1 s2 ==>
    s1.vs_current_bb = s2.vs_current_bb /\
    s1.vs_inst_idx = s2.vs_inst_idx /\
    s1.vs_halted = s2.vs_halted) /\
  (!bb. (bt bb).bb_label = bb.bb_label) /\
  (!bb. MEM bb fn.fn_blocks ==>
    !fuel ctx s1 s2. R_ok s1 s2 ==>
      (?e. run_block fuel ctx bb s1 = Error e) \/
      lift_result R_ok R_term R_term
        (run_block fuel ctx bb s1) (run_block fuel ctx (bt bb) s2))
  ==> !fuel ctx s. s.vs_inst_idx = 0 ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result R_ok R_term R_term
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (function_map_transform bt fn) s)
```

It cannot yet be instantiated: adding source invariants/reached captures to
R_ok breaks universal reflexivity, while using only padded state agreement
makes its arbitrary-state per-block premise unavailable. It also quantifies
over every run context, not only the fixed no-MEMTOP context. The exact-frame
`valid_state_rel` alternatives and the non-PHI prepend theorem do not repair
this mismatch. Proposal for strategist: use direct `run_defs` induction with
an explicit reached-prefix invariant, or authorize a reachable, fixed-context
variant of this consumer. Do NOT state its arbitrary block premise as an IH.
The local result shape required in either route is source-error-or-lift_result;
for successful source OK, target OK must be constructed, not assumed.

### 7.2 Observer and bound audit

`venomExecSemanticsScript.sml:1663--1723` defines mutually recursive
step_inst/exec_block/run_blocks. INVOKE is NOT trivial just because its syntax
is unchanged: it recursively runs a callee on two different memories.
For calls use full variable agreement (`padded_exec_equiv {}`) inside the
callee, not caller reserved-prefix exclusion: ctx functions have no freshness
premise. Setup initializes both callee variable maps equally. The no-MEMTOP
premise on ALL ctx functions supports recursive same-program simulation,
including calls back to the untransformed original function.

Inspection of every explicit vs_memory occurrence in that semantics gives:
MCOPY (line 82), RETURN/REVERT (785/796), SHA3 (930), LOG (1035) use padded
slices; call return-copy (463) uses expanded writes; merge_callee_state (1431)
copies callee memory; MEMTOP (916) alone observes its raw length. MLOAD/ILOAD
are covered by padded mload; ISTORE's executable memory is MSTORE (103).
External-call helpers also need their account/call-context observers from the
memory-erased execution frame, not just byte equality. These are proof
obligations, not a checked exhaustive opcode congruence theorem.

`loadElimMemoryRel.read_memory_range_ext` states
`(!i. read_memory i 1 s = read_memory i 1 t) ==>
 !i n. read_memory i n s = read_memory i n t` (50--59).
`padded_exec_equiv_mload` and `padded_exec_equiv_mstore_mload` (61--69,
120--129) have NO memory-length or in-bounds premise. The latter relates s
to mstore off (mload off s) s even when the store grows memory.
`loadElimPaddedSimHelpers` provides paired expanded-write closure (24--36),
paired update_var closure (38--45), adopt_return (47--55), merge (57--67),
setup (69--82), bind_outputs (94--102). Setup/bind still assume both option
results; these are not call totality theorems.

No local padded law above needs either state's LENGTH memory < dimword.
Word-address bounds (`a < dimword`) in key interfaces are different from
whole-memory length bounds. In particular MSTORE can extend past dimword
at a word-representable near-maximum address; initial memory length is NOT
an invariant supplied by the frozen step-preservation premise. Do not put a
per-step two-state memory-length bound in the coupling predicate. If an
opcode proof later needs it, prove the actual restricted observer law rather
than asserting propagation. The frozen initial bound remains available at
entry; it does not license arbitrary later bounds.

### 7.3 Local-simulation matrix

In this table V is the reserved-prefix set; P means the existing
`padded_exec_equiv V`. Q additionally equates current_bb, prev_bb and idx.
At body positions idx agreement is replaced by the offset relation below.
Every row needs concrete inst_wf/source membership when it uses opcode shape.
Terminal relations discard control-field equality, as in the frozen theorem.

| Source -> actual target | Input and side conditions | Required conclusion | Reusable / genuinely missing |
|---|---|---|---|
| i -> i, non-INVOKE including terminators | P; same prev_bb/labels for PHI-like observers; equal input operands (source freshness discharges Var exclusion); i.opcode <> MEMTOP | source Error, or `lift_result Q P P (step_inst k C i s) (step_inst k C i t)` after comparing equalized input indices; branch target/prev fields agree for OK terminators | Range/mload, paired write/update laws above are pieces. Missing exhaustive padded step_inst_base congruence incl RETURN/REVERT/LOG/hash/external calls and control projection. Exact-frame state_equiv lemmas do not suffice. |
| INVOKE i -> i | P, equal args and labels; all C.ctx_functions exclude MEMTOP | same result constructors, equal IntRet payload/abort tag; P for Halt/Abort and restored caller Q for OK | Missing same-callee padded run_blocks induction with `{}` relation, option totality for setup and bind, then call result assembly. setup/merge/adopt/bind laws alone do not construct the recursive result. |
| configured load i -> mk_assign_inst i op | P, `[addr]`, `[out]`, current singleton SOME [op], normalization validity and actual key address; evaluated op agrees across states | source OK s' implies target OK t' with P s' t' and control fields preserved | `le_occ_prefix_singleton_current` gives `le_key_read space key s = eval_operand op s` under its reached-source premises. KeyReadOperational lines141--162 bridges actual address. Missing local load-to-ASSIGN result theorem, including successful/defined value (source OK gives it). |
| configured load i -> mk_assign_inst i (Var pa.pa_phi_out) | P, load shape/key address; latest-join selected capture, `lookup_var pa.pa_phi_out t = le_key_read space key s` | same successful conclusion as singleton row | Source equality from LatestRead lines144--173; selected capture from DynamicCapture; target persistence from .21 write exclusion plus actual constructed events. Missing local semantic assembly; no agreement on this generated variable may be inferred from P. |
| redundant store i -> mk_nop_inst i | P, `[addr;val]`; selected current witness or selected current alternative from nonempty all-equivalent lattice list; normalize soundness yields actual stored value equals key read | source OK s' implies target OK t', P s' t'; no exact-memory conclusion for MSTORE | padded_exec_equiv_mstore_mload supplies one-state identity and transitivity/paired laws combine it with P. RetainedStore lines67--161 proves nonalias read persistence, NOT redundant-store identity or all-equivalent-selected-value extraction. Missing that extraction and configured MSTORE/SSTORE/TSTORE NOP assembly. |
| original PHIs -> original PHIs ++ generated PHIs (one snapshot) | incoming Q; original Var freshness and labels; selected input availability for every inserted action; distinct generated outputs/source-output disjointness | construct actual target batch OK q, P source-post q, selected generated lookups equal incoming source key reads | .22 constructs transformed original/rest success with any paired-update-closed R. DynamicCapture constructs generated++rest success/capture. Missing actual-order and unilateral fresh-update framing bridge (see below). |
| body index n -> n+g; edge -> edge | same bb/prev; P; g=LENGTH (phis_for_block actions lbl); both states refer to matched original instruction | after nonterminator increment mapped indices still related; terminators restore matching successor indices; next PHIs start at respective prefix lengths | le_occ_after_def lines38--44 gives source normalization; OperationalHistory neutral extension preserves lookups. Missing actual transform get_instruction/phi-prefix-length arithmetic and synchronized edge/control lemma. Cannot assert raw idx equality inside shifted blocks. |

Search before proposals: load-elim MemoryRel/PaddedSimHelpers/ByteHelpers,
SingletonCurrentness/RetainedStore/KeyReadOperational/LatestRead; shared
allocaRemapProofs has padded safe-access lemmas but a different remapping
relation; simulation and analysis searches found no padded step_inst theorem.
Memory-copy-elision Sound lines964 and1221 uses its own invariant/exact-state
simulation, not this padded inserted-PHI relation. No duplicate theorem added.

### 7.4 Actual PHI order: entry calculation and required bridge

`analysisSimDefs:236--246` uses TAKE pplen transformed ++ generated ++ DROP
pplen transformed. Original PHIs are unchanged by
`le_configured_transformed_phi_prefix`. DynamicCapture's helper instead
executes generated ++ transformed-rest. Both batches read the SAME incoming
snapshot. One must NOT sequentially eval original PHIs and then generated
PHIs with the original-post state as snapshot.

At a reached PhiOcc bb u p, the IH supplies incoming P u r plus equal
prev_bb/labels. .22 with R=P and paired-update closure constructs target
rest OK z. ReachedSourceAgreement discharges selected availability from the
source prefix (and source DFG, configured empty-BP, fixpoint hypotheses).
DynamicCapture then constructs generated++rest OK q and its selected lookup.
To obtain the ACTUAL order, commute snapshot updates to disjoint output
sets. Original freshness and collected-action source disjointness discharge
the cross-disjointness; generated output distinctness discharges capture
non-overwrite. This is the missing bridge, not a target-PHI-success premise.
Unilateral updates to V preserve P but must be proved, since paired closure
alone says nothing about an update only to r. A direct snapshot theorem for
original++generated could replace the reorder proof, at strategist choice.

### 7.5 Concrete coupling predicate proposal (textual, NOT a new definition)

The following are expansion macros for a future signature, not assumed
constants or a second definition of the frozen relations:

* `A = collect_phi_actions m ctx (cfg_analyze fn) (load_analyze ctx fn) fn`.
* `V = {v | isPREFIX "$le_phi_" v}`.
* `T bb = analysis_block_transform_prepend NONE (load_analyze ctx fn)
    (load_phi_prepend A) (\ll j. [load_elim_inst ctx A ll j]) bb`.
* `J es i s t` is the conjunction:
  `le_occ_prefix C fn s0 es i s /\ padded_exec_equiv V s t /\
   s.vs_current_bb = t.vs_current_bb /\ s.vs_prev_bb = t.vs_prev_bb /\
   t.vs_inst_idx = s.vs_inst_idx + LENGTH (phis_for_block A s.vs_current_bb)`
  together with, for EVERY actual action pa and EVERY matching decomposition
  `es = pre ++ PhiOcc bb u p :: suffix` where
  `MEM pa A /\ bb.bb_label = pa.pa_join_lbl /\
   (!b x y. MEM (PhiOcc b x y) suffix ==> b.bb_label <> pa.pa_join_lbl)`,
  the clause `lookup_var pa.pa_phi_out t = le_key_read ctx.lctx_addr_space key u`
  for each actual `compute_phi_action ... key ... = SOME pa` origin.

The capture clause is indexed by the latest occurrence of EACH action's
join, not by all alternatives and not just the current load. At a revisited
join its latest snapshot replaces the previous clause. At body steps .21
excludes all original-instruction writes; at other joins distinct outputs
exclude overwriting the selected action. At entry-before-PHIs use the same
predicate WITHOUT idx-offset/capture clauses for not-yet-visited joins,
and with raw indices equal (normally zero); after PHIs install the body
version. At an OK terminator exit use raw indices equal again. Terminal
states need only padded_exec_equiv. This is a phase-indexed predicate, not
a single universally reflexive R_ok suitable for 7.1.

Backward check at a replaced captured load: action lookup must first identify
the correct collected pa. Placement supplies a join decomposition; finite
prefix chooses the latest such occurrence. IH capture clause gives target
lookup = read at u. `le_occ_latest_join_source_read` changes read at u to
read at s. Actual key-address/normalization converts that into the load's
word; the local captured-load row then constructs target OK. No complete
target suffix or successful target next step occurs in these antecedents.

Antecedent classification:

| Antecedent | Origin / remaining prerequisite |
|---|---|
| wf/function inst wf/SSA, original freshness, fn/C functions no MEMTOP, initial idx/entry/invariants | frozen premises |
| configured ctx, alias analysis equalities, solver fixpoint, empty original BP | established helper facts for original wrapper; round-to-round re-establishment remains genuinely missing, not a frozen hypothesis |
| reached source prefix | induction hypothesis, extended only by actual source successful semantics |
| DFG at source StepOcc; BP/allocation invariants after steps/PHIs | frozen preservation premise plus established source invariant lemmas where applicable; integration of normalized idx-zero states and PHI closure still needs checking, not target invariant transfer |
| P and index mapping at paired current states | induction hypothesis, base P reflexivity; missing local rows must preserve it |
| selected incoming availability | established source/capture facts (ReachedSourceAgreement), with source DFG and predecessor distinctness discharged separately |
| actual target batch OK and new generated captures | CONCLUSIONS of .22 + DynamicCapture + missing actual-order/framing bridge; never antecedents of J |
| captured outputs at current target state | induction hypothesis established at actual batch, preserved using .21 with constructed step/PHI/neutral events |
| source latest-join read equality | established source theorem LatestRead, requires actual-action/lookup/shape linkage |
| singleton currentness | established source theorem SingletonCurrentness, not arbitrary-state lattice validity |
| all-equivalent redundant-store selected value, local opcode congruence, INVOKE result, index arithmetic | genuinely missing semantic helpers |

### 7.6 Small flat semantic obligation proposal for strategist review

These are exact proposed HOL term texts USING the existing padded relation;
none are checked declarations. Q below must be expanded as P plus the three
control equalities; it is not a request to duplicate frozen definitions.
Local semantic lemmas can use P and separately conclude control equalities.
No theorem below quantifies over an assumed local-step simulation oracle.

(1) Noncall unchanged semantic boundary:
```sml
padded_exec_equiv V s t /\
s.vs_current_bb = t.vs_current_bb /\ s.vs_inst_idx = t.vs_inst_idx /\
s.vs_prev_bb = t.vs_prev_bb /\ i.inst_opcode <> INVOKE /\
i.inst_opcode <> MEMTOP /\
(!v. MEM (Var v) i.inst_operands ==> lookup_var v s = lookup_var v t) ==>
(?e. step_inst_base i s = Error e) \/
lift_result Q (padded_exec_equiv V) (padded_exec_equiv V)
  (step_inst_base i s) (step_inst_base i t)
```
Needs opcode observer audit discharged, no memory bound; includes terminators.

(2) Same-program callee boundary, separate from pass simulation:
```sml
EVERY (\f. !i. MEM i (fn_insts f) ==> i.inst_opcode <> MEMTOP) C.ctx_functions /\
(!i. MEM i (fn_insts f) ==> i.inst_opcode <> MEMTOP) /\
padded_exec_equiv {} s t /\
s.vs_current_bb = t.vs_current_bb /\ s.vs_inst_idx = t.vs_inst_idx /\
s.vs_prev_bb = t.vs_prev_bb ==>
(?e. run_blocks k C f s = Error e) \/
lift_result Q0 (padded_exec_equiv {}) (padded_exec_equiv {})
  (run_blocks k C f s) (run_blocks k C f t)
```
Q0 expands Q with V={}. Prove by actual run_defs induction using (1), snapshot
transport and call option totality; this supplies the recursive INVOKE row.

(3) Configured load replacement, using an evaluated value rather than
assuming a transformed step succeeds:
```sml
le_configured_context ctx /\ padded_exec_equiv V s t /\
i.inst_opcode = ctx.lctx_config.lc_load /\
i.inst_operands = [addr] /\ i.inst_outputs = [out] /\
eval_operand addr s = SOME a /\
le_key_address ctx.lctx_addr_space key s = SOME (w2n a) /\
le_key_read ctx.lctx_addr_space key s = SOME w /\
eval_operand replacement t = SOME w /\
step_inst k C i s = OK s' ==>
?t'. step_inst k C (mk_assign_inst i replacement) t = OK t' /\
     padded_exec_equiv V s' t'
```
Control preservation is a separate elementary projection. Singleton and
captured-currentness are two ways to discharge replacement evaluation;
normalization/key-address must be proved upstream, not inferred from this.

(4) Redundant configured store boundary:
```sml
le_configured_context ctx /\ padded_exec_equiv V s t /\
ctx.lctx_config.lc_store = SOME i.inst_opcode /\
i.inst_operands = [addr; value] /\ i.inst_outputs = [] /\
eval_operand addr s = SOME a /\ eval_operand value s = SOME w /\
le_read_address ctx.lctx_addr_space (w2n a) s = SOME w /\
step_inst k C i s = OK s' ==>
?t'. step_inst k C (mk_nop_inst i) t = OK t' /\
     padded_exec_equiv V s' t'
```
Needs the semantic idempotency laws above. Separate missing upstream
all-equivalent-list selection must establish its read premise, including
multivalue store cases; do not substitute simultaneous currentness of vs.

(5) PHI actual-order/framing and (6) index/control bridge:
Use the exact bodies in 7.4 and matrix with actual T; the first must construct
`?q. eval_phis r (T bb).bb_instructions = OK q /\ padded_exec_equiv V p q`
and all selected lookups, from the reached source PhiOcc and incoming IH.
The second must prove, for matched active body positions,
`get_instruction (T bb) (n + LENGTH (phis_for_block A bb.bb_label)) =
 SOME (load_elim_inst ctx A (df_at NONE (load_analyze ctx fn) bb.bb_label n) i)`
from `get_instruction bb n = SOME i` and
`phi_prefix_length bb.bb_instructions <= n`, plus actual prefix-length and
terminator exit equations. These are concrete missing syntax/semantics
boundaries, not a new generic history relation.

Recommendation: keep .13 blocked until these flat obligations and the
reachable fixed-context consumer choice are planned. In particular the audit
does NOT establish any final/one-round correctness claim or authorize proof
of the frozen target before its machinery is validated.

## 8. Redundant-store selected-witness audit (.30)

### 8.1 Checked semantic interface (not currentness)

`loadElimStoreEquivalenceTheory` exports `le_store_equiv_eval` and
`le_store_equiv_list_read`. Both build without admissions. The first uses
`dfgCorrectnessProofTheory.normalize_operand_eval_proof`:

```sml
!dfg visited op s. dfg_assigns_sound dfg s ==>
  eval_operand (normalize_operand dfg visited op) s = eval_operand op s
```

The exact test is the case expression at load_elim_inst_def lines 484–487:
normalize only Var/Var; otherwise require syntactic equality. Searches in
shared and simulation found no equivalent boundary; analysis supplies the
normalization theorem. The closest memory-copy helper,
`operand_equiv_norm_eval`, is local and uses the broader operand_equiv test,
so cannot serve as an exported exact-test interface here.

The checked list consumer requires **current-state** `dfg_assigns_sound d s`,
EVERY of that test against value, one member op, and key-read/evaluation
equality for that member. It does not require successful evaluation. Current
DFG soundness is separate from historical StepOcc soundness: the active store
has not yet been appended to es. In the final theorem it must come from the
initial/PHI/step invariant (normalized index zero as appropriate), not from
MEM (StepOcc ... s ...) es.

### 8.2 Exact proposed source-only obligation (UNPROVED)

The intended generalization of le_occ_prefix_singleton_current is:

```sml
le_occ_prefix C fn s0 es i s /\
wf_function fn /\ fn_inst_wf fn /\ wf_ssa fn /\
le_configured_context ctx /\ ctx.lctx_dfg = dfg_build_function fn /\
(!v. bp_get_ptrs ctx.lctx_bp v = []) /\
ctx.lctx_aliases = ma_analyze ctx.lctx_bp fn ctx.lctx_addr_space /\
fn_entry_label fn = SOME s0.vs_current_bb /\
is_fixpoint (df_process_block Forward NONE load_join load_transfer
  load_edge_transfer ctx (OPTION_MAP (\l. (l,SOME FEMPTY)) (fn_entry_label fn))
  (cfg_analyze fn) fn.fn_blocks) (cfg_analyze fn).cfg_dfs_pre
  (load_analyze ctx fn) /\
(!bb n fuel u t. MEM (StepOcc bb n fuel u t) es ==>
  dfg_assigns_sound ctx.lctx_dfg u) /\
FLOOKUP (unwrap_load_lattice
  (df_at NONE (load_analyze ctx fn) s.vs_current_bb s.vs_inst_idx)) key = SOME vs
==> ?op. MEM op vs /\
         le_key_read ctx.lctx_addr_space key s = eval_operand op s
```

No extra nonemptiness premise is necessary: le_analyze_point_lookup_nonempty
supplies vs <> [] at the reached active point. No extra current-state DFG
premise is asserted necessary for this witness conjecture itself; it IS
necessary for applying the checked list consumer. There is no checked proof
or counterexample for the displayed generalization. In particular no
no-write certificate is silently being added as a pass premise.

### 8.3 Backward selection: exact interfaces and changes in list

`le_join_selected_lookup` has b = SOME m and
FLOOKUP (unwrap_load_lattice (load_join a b)) k = SOME vs as premises;
it yields `?ws. FLOOKUP m k = SOME ws /\ (!v. MEM v ws ==> MEM v vs)`.
It does NOT itself yield ws <> [].

`le_analyze_selected_predecessor` additionally requires wf_function, the
explicit fixpoint, reachable lbl, its lookup_block, predecessor membership,
and `df_boundary ... pred = SOME m`. From an index-zero SOME vs lookup it
yields the same sublist inclusion on ws. Actual occurrence edges provide the
predecessor and DFS membership; le_analyze_boundary_some provides SOME m;
le_analyze_boundary_lookup_nonempty provides ws <> [].
`le_analyze_selected_exit` similarly requires reachable lbl, its block and
`df_at ... lbl (LENGTH bb.bb_instructions) = SOME exit`. From boundary SOME vs
it yields an exit lookup SOME ws with set ws SUBSET set vs. Point nonemptiness
is again separate. These interfaces already support arbitrary lists, unlike
le_analyze_singleton_predecessor/exit, whose last step forces ws = [op] using
nonemptiness AND inclusion in an actual singleton.

Thus at a block transition there can be two successive sublist selections
(join and accumulated old-boundary absorption). Neither is equality. A
backward certificate must carry changing nonempty lists and inclusions, then
choose a generator whose operand belongs to the final list. A witness chosen
before a join cannot be replaced arbitrarily while preserving a previously
proved semantic equality. le_occ_prefix_singleton_suffix instead fixes one
op and EVERY (le_singleton_retained_occ ... op) over the whole suffix; its
statement cannot simply replace [op] by vs.

### 8.4 Unproved preservation cases, including singleton transitions

Within a block a non-generating transfer retains the lookup; a generating
transfer replaces it by [op]. le_analyze_multivalue_prefix is applicable only
while 1 < LENGTH vs. Once a predecessor/exit sublist is singleton, use the
singleton origin/retention case, NOT the multivalue lemma. At entry,
`le_analyze_entry_no_lookup` (loadElimActualGenerationScript.sml:141),
already used in SingletonSuffix[start], excludes ANY lookup from initialized
SOME FEMPTY, even with incoming CFG edges. Original PHI-prefix transparency
then contradicts SOME vs; do not assume the entry has no predecessors.

Key-address no-write already follows from presence via
le_ordinary_definition_key_cut and le_phi_definition_key_cut. Value no-write
is the unresolved additional difficulty: le_ordinary_definition_value_cut
and le_phi_definition_value_cut exclude only `SOME [Var v]`, not membership
of Var v in a longer list. They cannot justify transporting an arbitrarily
selected witness across original PHIs that redefine it. Generalizing those
cuts to all-member exclusion may be too strong: an alternative originating
on another predecessor need not dominate this occurrence. The proof needs
only the actual selected witness to survive, or a justified reselection.
This is a genuine proof gap, not evidence of falsehood of the frozen theorem.

For stores, non-generating retention must establish disjoint-write read
preservation for arbitrary nonempty retained lists, including singleton
lists selected at joins. Existing multivalue-only read retention does not
cover that transition; existing singleton retention covers it only with its
fixed operand/non-generation certificate. A generating store/load instead
restarts at its own checked generation-read boundary, with historical DFG
soundness and address/output separation. No simultaneous currentness of all
members is required or justified.

### 8.5 Consumer derivation and bounded alternative

At an actually eliminated store obtain vs <> [] and EVERY exact test from
load_elim_inst_def. Discharge the source-only witness above, then apply
le_store_equiv_list_read using current-state DFG soundness. Successful source
store semantics provides eval_operand value s = SOME w and eval_operand addr
s = SOME a. The normalized write-key/address boundary identifies key read
with le_read_address space (w2n a) s. This supplies the read-equals-w premise
of the already checked store-to-NOP boundary; target step success is its
CONCLUSION, never an assumption.

If arbitrary selected-witness preservation is too strong, the narrower
candidate is the same source configuration plus current-state DFG soundness
and EVERY exact test against this store value, concluding directly
`le_key_read ctx.lctx_addr_space key s = eval_operand value s`.
It would need an all-equivalent-specific treatment of PHI overwrites and
normalization; the checked semantic test alone does not solve that case.
Do not assume normalization equalities hold in every historical state.
This alternative is a proposal for strategy review, not a new theorem or a
weakening of the frozen statement. No witness induction or coupling was
started in .30.
