# Source-order exchange audit (C1.4.9.4)

This is a design checkpoint, not a proved simulation. No source-success,
exchange diamond, or callee termination premise is being added to the frozen
task. Existing residual and pseudo-prefix theories build cleanly. The missing
work is not just a trace-to-prefix coercion.

## Verified interfaces

Line references refer to the source at this checkpoint.

* `dftGasInvResidualTraceScript.sml:8-15` defines
  `inv_ev_trace orc p d fuel ctx xs s t`: an instruction-list trace of actual
  nonterminating-opcode OK steps, updating the index to `SUC` after each step.
  Its fuel is fixed; it does not assert block fetches.
* `dftGasInvPrefixRunScript.sml:5-14` defines
  `inv_ev_prefix orc p d ctx bb n s t`: each of the n OK steps has an actual
  `get_instruction bb s.vs_inst_idx = SOME inst` witness and its own fuel.
  These are distinct interfaces.
* `dftGasInvResidualTraceScript.sml:62-72` exports exactly:

```sml
!pre s.
wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
EVERY inst_wf bb.bb_instructions /\
dft_remaining_inv fn bb (pre ++ y::post) s /\
~s.vs_call_ctx.cc_static /\ inv_memory_observation y.inst_opcode /\
EVERY (\x. inst_shape_ok x /\ ~is_terminator x.inst_opcode /\
  ~dft_must_order x y) pre ==>
?t. inv_ev_trace orc p d fuel ctx pre s t /\
  dft_remaining_inv fn bb (y::post) t /\
  (!op. MEM op y.inst_operands ==> eval_operand op t = eval_operand op s)
```

* `dftRunRelScript.sml:524-537`, `dft_remaining_inv fn bb todo s`, records
  original nonpseudo membership, distinctness, original relative order of
  todo, current block, strict-dominator definedness, defined outputs of
  instructions outside todo, and required noncall/non-CODECOPY label bindings.
  It is not a trace or a value-equivalence assertion.
* `dftGasInvSSAProbeScript.sml:77`, `inv_remaining_ev_step`, is the oracle
  deletion-preservation producer. The residual theorem uses its empty-pre
  instance; arbitrary scheduled deletions must use its general instance.
* `dftRunRelScript.sml:393-400`, `dft_inversion_not_must_order`, takes
  `dft_block_rel bb bb'`, target distinct IDs, original x/y membership,
  nonpseudo x/y, source x-before-y and target y-before-x, and concludes
  `~dft_must_order x y`.
* `dftRunRelScript.sml:344-355`, `dft_inversion_compatible`, concludes
  `dft_abort_compatible x.inst_opcode y.inst_opcode` from preserved order of
  abort-incompatible original pairs and the same opposite ID orders.
  `dftScheduleOrderScript.sml:41-51` packages the needed order property as
  `dft_fallible_order_kept fn fn'`. It is separate from `dft_block_rel`.
* `dftRunRelScript.sml:2777-2787`, `dft_crossing_swap_pair`, takes wf_ssa,
  wf_function, block membership, EVERY inst_wf, EVERY non-alloca, x/y original
  membership, nonpseudo x/y, source x-before-y, no must-order x y and abort
  compatibility. It concludes `dft_gas_swap_pair x y`, both inst_wf, and
  that x is not an outputless effectless root.
* `dftRunRelScript.sml:1246-1255` defines `dft_gas_swap_pair x y` as both
  def/use disjointness directions, def/def disjointness, effects independence,
  dft_abort_compatible, both nonterminators, both non-allocas, both nonpseudos.
  `dft_gas_swap_pair_sym` proves symmetry. One-sided no-must-order is NOT this
  contract. The crossing producer obtains reverse def/use disjointness from
  SSA source order (`dft_reverse_dependency_disjoint`) and output disjointness
  from SSA (`ssa_disjoint_defs`), not from no-must-order alone.
* `dftRunRelScript.sml:1884-1888`, `dft_nongas_pair_success`, has signature:

```sml
dft_gas_swap_pair a b /\ ~gas_pair a.inst_opcode b.inst_opcode /\
inst_wf a /\ inst_wf b /\
step_inst fuel C a s = OK sa /\ step_inst fuel C b sa = OK sab ==>
?sb. step_inst fuel C b s = OK sb /\ step_inst fuel C a sb = OK sab
```

  Thus it *does* produce opposite-order success from ONE successful pair,
  unlike a theorem assuming success of both orders. However it is list
  semantics, not ev_step. Its indexed form `dft_indexed_nongas_pair_ok`
  (1902-1911) starts with y then x with SUC index, produces x then y and
  equates final states after setting both indices to `SUC (SUC s.vs_inst_idx)`.
* `dftRunRelScript.sml:2627-2636`, `dft_nongas_suffix_swap`, requires swap
  pair, nongas-pair, inst_wf x/y, nonstatic state, defined y variable operands,
  required y label bindings, and non-outputless-effectless x. Conclusion is
  `dft_res_rel (dft_exec_suffix fuel C (x::y::tail) s)
               (dft_exec_suffix fuel C (y::x::tail) s)`.
  This is not an actual source-prefix witness. `dft_gas_suffix_swap`
  (2676-2681) instead existentially changes the initial gas reading list;
  `dft_suffix_swap_variant` (2720-2729) combines those interfaces. Neither
  supplies fixed-oracle exchange. `dft_extract_head_variant` (2802-2814)
  inherits the no-alloca and reading-list-variation restrictions.
* `dftStructuralScript.sml:151-155`, `from_block`, allows either the original
  instruction or its flipped representative. `dftPermSimScript.sml:1223-1225`
  proves `is_flippable i.inst_opcode ==> step_inst_base (flip_operands i) st =
  step_inst_base i st`; its 1258-1260 counterpart is for step_inst, not ev_step.

## Explicit invariant proposal

Use occurrence IDs (unique in the block), not record equality with flipped
representatives. Let B be the original nonpseudo body, Q the scheduled body,
T the already consumed original representatives of a prefix of Q, and R the
original residual list. Keep all of the following together:

1. There is a pointwise `from_block` correspondence between consumed Q
   occurrences and T, with identical IDs and no repeats; Q's remaining IDs
   are exactly R's IDs. In particular
   `R = FILTER (\x. ~MEM x.inst_id (MAP (\i. i.inst_id) T)) B`.
2. There is an ACTUAL `inv_ev_trace orc p d fuel ctx T s0 sT` (after proving
   representative replacement). `dft_remaining_inv fn bb R sT` holds.
   Keep nonstaticness, initial block identity and fixed oracle event frame.
3. For the observation y, split R as pre ++ y::post and B as S ++ y::U.
   Scheduler inversion supplies no-must-order and abort compatibility for
   every missing predecessor in pre. Apply `inv_remaining_trace_extension`
   at sT, obtaining actual T++pre execution and unchanged y operands.
4. Normalize T++pre into S++Z, where Z contains exactly the consumed
   occurrences originally after y (in original order, for definiteness).
   At every adjacent exchange carry the actual successful pair, the static
   inversion certificate in ORIGINAL and SCHEDULED ID orders, representative
   identity, and normalized indices. Do not carry a diamond as a premise.
   Reconstruct the opposite-order pair using a future oracle success-exchange
   theorem, preserving the common final normalized state.
5. Split the normalized actual trace after S, obtaining sS. Prove that Z
   frames y's operands and initial-FMP observation; it cannot simply be
   removed from sS++Z's result. Then normalize sS's index to the source fetch
   position and convert the S trace into `inv_ev_prefix` using fetch facts.

Initialization: T=[], R=B at an actual post-pseudo block entry. Entry-label
initialization is checked by `inv_entry_trace_extension`; arbitrary block
entry is NOT covered by that entry-label hypothesis. Preservation of (1) is
finite-list deletion plus unique IDs; preservation of (2) uses actual OK
steps and `inv_remaining_ev_step`, after representative replacement. Items
(4) and (5), including their allocation and call cases, remain gaps.

## Exact candidate obligations (NOT proved or inserted into a theory)

A minimal same-context exchange kernel to validate next is:

```sml
dft_gas_swap_pair x y /\ inst_wf x /\ inst_wf y /\
ev_step orc p d fuel ctx y s = OK sy /\
ev_step orc p d fuel ctx x
  (sy with vs_inst_idx := SUC s.vs_inst_idx) = OK syx ==>
?sx sxy.
  ev_step orc p d fuel ctx x s = OK sx /\
  ev_step orc p d fuel ctx y
    (sx with vs_inst_idx := SUC s.vs_inst_idx) = OK sxy /\
  (sxy with vs_inst_idx := SUC (SUC s.vs_inst_idx)) =
  (syx with vs_inst_idx := SUC (SUC s.vs_inst_idx))
```

This is a proposed producer from one actual successful ordering, NOT a
conditional theorem assuming a diamond. Nongas noncall cases may reuse the
indexed list theorem. GAS uses the fixed `(p,d,inst_id)` oracle word instead
of reading-list permutation. Same-context INVOKE still requires a proof:
the two orders must give the same setup arguments, caller frame effects,
callee input and finite returning execution. Excluding INVOKE from *pre*
does NOT exclude it from T or from exchanges inside T. Two INVOKEs cannot
form a no-must-order crossing (`dft_must_order_invokes`, RunRel:376-378), but
one INVOKE with a pure partner remains. Do not assume the callee returns in
the new order; reuse the existing successful callee witness after proving
its input equality/frame relation. Cross-context reflection is separate.

The kernel's no-alloca restriction comes from dft_gas_swap_pair. It must NOT
be silently added to the task. Either derive no-alloca for each inversion
from actual scheduling, or supply an allocation-specific observation/frame
argument (not a claim of full state commutation).

An exact restricted extraction contract, exposing rather than hiding that
restriction, is the following candidate. This is a same-context producer;
it does not solve changed-context reflection. Assume T contains original
representatives already (their bridge is another gap).

```sml
wf_ssa fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
EVERY inst_wf bb.bb_instructions /\
EVERY inst_shape_ok bb.bb_instructions /\
EVERY (\i. ~is_alloca_op i.inst_opcode) bb.bb_instructions /\
ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
dft_block_rel bb bb' /\
ALL_DISTINCT (MAP (\i. i.inst_id) bb'.bb_instructions) /\
(!x z. MEM x bb.bb_instructions /\ MEM z bb.bb_instructions /\
  ~dft_abort_compatible x.inst_opcode z.inst_opcode /\
  id_before (MAP (\i. i.inst_id) bb.bb_instructions) x.inst_id z.inst_id ==>
  id_before (MAP (\i. i.inst_id) bb'.bb_instructions) x.inst_id z.inst_id) /\
bb.bb_instructions = pseudos ++ (S ++ y::U) /\
EVERY (\i. is_pseudo i.inst_opcode) pseudos /\
EVERY (\i. ~is_pseudo i.inst_opcode) (S ++ y::U) /\
MAP (\i. i.inst_id) bb'.bb_instructions =
  MAP (\i. i.inst_id) pseudos ++
  (MAP (\i. i.inst_id) T ++ y.inst_id::later) /\
EVERY (\i. MEM i (S ++ y::U)) T /\
dft_remaining_inv fn bb (S ++ y::U) s0 /\
s0.vs_inst_idx = LENGTH pseudos /\ ~s0.vs_call_ctx.cc_static /\
inv_ev_trace orc p d fuel ctx T s0 sT /\
inv_memory_observation y.inst_opcode ==>
?sS. inv_ev_prefix orc p d ctx bb (LENGTH S) s0 sS /\
  sS.vs_inst_idx = LENGTH pseudos + LENGTH S /\
  (!op. MEM op y.inst_operands ==> eval_operand op sS = eval_operand op sT) /\
  sS.vs_initial_fmp = sT.vs_initial_fmp
```

The restricted contract is a proof-design test only. Its alloca premise has
no task-level producer identified here. It must not become another standalone
conditional helper without resolving that gap. Operand equality here uses the
original y; observing a flipped target representative needs the appropriate
range/operand correspondence, not arbitrary positional operand equality.

## Premise provenance / remaining obligations

| Premise or transition | Producer or explicit gap |
|---|---|
| unique original occurrence IDs | wf_function block ID distinctness, RunRel:2792-2793; target IDs additionally required by inversion interface |
| original/target inverse order | source residual split + scheduled consumed/unconsumed ID split; list bookkeeping still to prove |
| no-must-order in source direction | dft_inversion_not_must_order; not symmetric reasoning |
| reverse def/use and disjoint outputs | dft_crossing_swap_pair via source-order SSA, provided its other premises hold |
| effects independence, nonroot x, nonterminator y in a crossing | dft_must_order_def:54-62; source-earlier x nonterminator also uses wf source order |
| abort compatibility | separate fallible-order preservation and opposite ID orders; not supplied by dft_block_rel |
| nonpseudo | original body and from_block; actual flips need representative replacement |
| no-alloca | GAP: inst_shape_ok:304-313 bans six opcodes but not ALLOCA; residual totality of ALLOCA does not imply its commutation |
| actual-state nonstaticness | inv_ev_step_call_ctx / inv_ev_prefix_call_ctx; carry through actual trace induction |
| defined inserted operands | dft_remaining_inv and inv_remaining_head_operands; preserved by inv_remaining_ev_step; not assumed from target readiness |
| actual successful missing predecessors | inv_remaining_trace_extension, applied after arbitrary consumed-prefix residual invariant is established |
| general post-pseudo initialization | GAP outside entry-label case; needs actual block-entry dominance/label facts |
| pair success in opposite order | GAP: proposed oracle kernel; existing indexed list kernel is a useful boundary but not fixed-oracle proof |
| same-context INVOKE | GAP described above; actual finite returning witness must be replayed, not assumed |
| trailing Z operand frame | GAP: source y-before-z and target z-before-y yield ~must_order y z, whereas inv_crossing_operand_frame expects ~must_order z y AND z<>INVOKE; need SSA reverse-dependency bridge and label/call frames |
| initial FMP agreement | needs successful-step frame, including INVOKE adopt_return_fmp; not implied merely by nonstaticness |
| representative replacement | flip_operands_step_inst_base exists; oracle lift and nonflippable memory-observation identity must be established |
| index normalization | existing list indexed theorem suggests shape; ev_step index insensitivity must cover returning INVOKE and fixed event identity |
| trace-to-inv_ev_prefix | GAP: show every EL of S is fetched in bb starting at LENGTH pseudos, and replay after index normalization; inv_ev_trace has no fetch premise |
| cross-context callee runs | separate finite fuel reflection obligation, still unresolved; same-context exchange cannot discharge it |
| revert forwarding | separate concrete scheduler cut obligation, still unresolved |

## Review recommendation

Do not certify source observation transport from residual completion. Before
more infrastructure is authorized, resolve the allocation exclusion at the
actual inversion consumer and validate the one-success oracle exchange kernel
(including a returning INVOKE with a pure partner). Then address residual
initialization for general blocks, trailing observation framing, representative
replacement and fetch conversion as connected consumers. No new component IDs
or executable theorem claims are introduced by this report.

## Checked extraction consumer and integration audit (C1.4.9.15)

`dftGasInvExtractionTheory.inv_lookup_scheduled_observation` now implements
this restricted contract for a genuine scheduled prefix. Its input is an
`inv_ev_ftrace` of the actual target records, with existential fuel per step,
and source/target block lookups under `dft_fn_rel`. The target split is at an
instruction whose ID equals the original observation's ID. The theorem
produces an actual `inv_ev_prefix`, the exact source index, operand agreement
for the original observation and initial-FMP agreement.

The from_block bridge converts the executed prefix to original records,
including flipped representatives. A separate suffix normalization and
injective source-ID permutation lifting produce the full original schedule;
the consumer does not assume that schedule's record PERM. Residual deletion,
completion, inversion-only sorting and trailing-suffix framing are checked.
No new no-ALLOCA hypothesis is used: the actual `dft_fn_rel` boundary supplies
allocation exclusion and the inversion swap certificates. This supersedes
the old gaps in rows for schedule bookkeeping and no-alloca above.

Remaining task-level obligations are not discharged by this consumer:

* Produce `dft_remaining_inv` at arbitrary actual post-pseudo block entries.
  The entry-label-only producer does not establish this for loop/jump entries;
  dominance, predecessor labels and PHI input availability must be connected
  to the actual oracle execution.
* Reflect finite returning INVOKEs across C' and C by well-founded fuel
  induction. All extraction traces here run in the **same** ctx. Local INVOKE
  exchange and arbitrary per-step fuels do not imply changed-context runs.
* Connect actual reachable states to the block-slice inputs and project memory
  ranges for flipped target observations; operand agreement is stated for the
  original observation, not positional equality of flipped operand lists.
* Prove concrete DFT revert-forward preservation. Neither the list sorting
  result nor `dft_block_rel` implies ASSIGN-only forwarding intervals.

These are integration obligations, not premises to add to the frozen theorem.

## Integration checkpoint C1.4.9.16: rule-by-rule producers

Checked extraction signature: `inv_lookup_scheduled_observation` in
`dftGasInvExtractionScript.sml:346-363` is authoritative. It assumes aligned
source/target lookups and `dft_fn_rel`, a source pseudo/body split, a target
split `pseudos ++ scheduled ++ targetobs::targetpost`, observation-ID equality,
source body residual initialization at s0, s0 index/nonstaticness, actual
same-context `inv_ev_ftrace ... scheduled s0 sT`, and a memory-observation
opcode. Its conclusion is exactly a fetched source prefix, source index,
original-observation operand equality and initial-FMP equality. The following
are producer obligations, not hypotheses to add to the frozen theorem.

| ev_reachable rule (Defs:145-178) | Available input / required bridge |
|---|---|
| entry | Context LIST_REL supplies corresponding function lookup; entry-label preservation supplies source label. `enters_block` performs PHIs only. It does **not** execute all pseudos: PARAM/FMP_PARAM/etc must be replayed before invoking body extraction. Entry-label strict dominance is vacuous; inv_entry_pseudo_initialized can be used after a successful common pseudo run and label readiness. Observations in the pseudo prefix need separate trivial projection. |
| next | Consecutive actual OK nonterminator steps append to a target ftrace with existential per-step fuel. Non-INVOKE replay in source ctx is context independent. For INVOKE, the returning witness must first be reflected across contexts; local exchange cannot do that. Each observation is reconstructed afresh from its block-entry state, not from the previous reconstructed source observation. |
| block | The terminator OK step and `enters_block` expose the next PHI state, with depth SUC d. Need same observable control-flow/label state at the old block boundary, matching next-block lookup, equal PHI selections, and preservation of strict dominating definitions into the new entry. Extraction of memory observations alone does not establish this boundary relation. |
| callee | No returning witness is required for entering a callee. Need source reachability of the caller INVOKE and agreement of decoded argument evaluations, FMP and shared effect fields at call setup. Then setup_callee uses a fresh variable/alloca frame and source entry label; depth SUC d and frame `(d,id)::p` match. A callee may diverge after entry. |

General block-entry invariant still needed: at a matching current block label,
strict_dom_vars_defined for the **source** function, and the restricted label
availability clause of dft_remaining_inv (RunRel:533-536), together with equal
PHI predecessor selection and availability of its selected inputs. After PHIs
and all remaining pseudos succeed, their output definitions are available;
these are precisely the already-produced definitions required by
RunRel:531-532. The distinctness/order clauses come from wf_function and the
source split, not execution. `inv_remaining_ev_step` preserves the invariant
within a block, but does not prove its transfer along a terminator edge.
`enters_block` alone has no dominance assertion; that transfer must be proved
from actual predecessor execution/SSA dominance rather than assumed from an
arbitrary current label. Re-entry through a loop is a required case.

### Proposed finite-return contract (UNPROVED, not a new assumption)

At the recursion boundary the needed direction is target-to-source IntRet:

```
!fuel p d C C' fn fn' s ret t'.
  LIST_REL dft_fn_rel C.ctx_functions C'.ctx_functions /\
  dft_fn_rel fn fn' /\ [entry shape, label and dominance readiness] /\
  ev_blocks orc p d fuel C' fn' s = IntRet ret t' ==>
  ?t. ev_blocks orc p d fuel C fn s = IntRet ret t /\
      merge_callee_state caller t = merge_callee_state caller t'
```

Here caller is universally quantified, not existentially selected. The merged
state equality is the minimal checked use-site demand from Defs:56-61:
return values and iret_adopt_fmp must be identical; merge copies exactly
memory, transient, accounts, returndata, logs, outcomes, requests, pending
deletions, gas_readings and immutables (Semantics:1468-1481). It does not copy
callee vars, current/prev block, instruction index, allocas or FMP. Thus exact
callee-state equality is stronger than the INVOKE consumer needs. In contrast,
`gas_variant` alone is not enough for literal same-state step replay: merge
copies gas_readings too. The oracle never consumes that list, so either prove
its preservation and exact merged equality or introduce and validate a
reading-insensitive trace/observation interface. No such relation has been
selected or proved here. For normal inter-block continuations, variable values,
control labels, prev_bb and FMP **are** needed; the merge projection is not a
sufficient block-boundary relation. The bracketed entry readiness is unresolved
and must be replaced by a producer-backed invariant before this contract can
be a theorem. It is deliberately not an executable conditional final theorem.

The quantification is over all p,d and every finite fuel; no claim about
termination, a uniform reachability fuel, or out-of-fuel reflection is needed
for crossing a returning call. Defs:83-100 at SUC fuel invokes its block at
fuel and depth SUC d. That block's INVOKE calls ev_blocks at that same fuel,
frame `((SUC d,id)::p)` and depth SUC d; the callee's first block is one depth
higher. This is strict fuel descent relative to the containing ev_blocks.
Within a block use instruction remainder descent; ev_step -> ev_blocks has
same fuel but decreases the lexicographic secondary measure 1 -> 0. The
second measure for ev_block is `2 + (LENGTH instructions - idx)` (Defs:101-107).
Oracle events use p,d,id, not instruction index, so reorderings/flips preserve
the event only when the original ID and block-depth/frame are preserved.

Dependency direction: general block-entry readiness and pseudo replay feed a
finite block reconstruction. Returning-call reflection at smaller fuel must
be available **before** changing that block's target trace to source context.
Full block reconstruction (including terminators and all effects, not only
memory operands) then supplies same-fuel ev_blocks reflection through jumps.
Only after this mutually organized induction is proved can reachability next
cross returning calls. Reachability callee uses argument/setup agreement but
not termination. A theorem assuming all callee reflections or all source
prefixes would conceal this cycle, not solve it.
