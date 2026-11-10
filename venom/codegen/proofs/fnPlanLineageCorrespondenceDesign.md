# Unequal-cleanup correspondence: bounded design checkpoint

Status: **candidate rejected as a complete proof interface**. This is a design
record, not a theorem, counterexample, or authorization to implement a relation.
No new HOL definition or semantic executor is introduced here.

## Exact consumer and selected result

The checked selected result is `lineage_singleton_block_physical_transfer` in
fnPlanLineageScript.sml:5592. Its signature is:

```sml
codegen_ready_fn fn /\ fn_entry_label fn = SOME entry /\ lbl <> entry /\
cfg_reachable_of (cfg_analyze fn) pred /\
lookup_block pred fn.fn_blocks = SOME pred_bb /\
lookup_block lbl fn.fn_blocks = SOME bb /\
MEM lbl (cfg_succs_of (cfg_analyze fn) pred) /\
cfg_preds_of (cfg_analyze fn) lbl = [pred] /\
generate_fn_plan_with_cleanup_analyzed (liveness_analyze fn) dfg (cfg_analyze fn)
  ch growth fn spill_base lbl_ctr = SOME (fn_ops,ps_end) /\
lineage_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
  (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl psL /\
dfs_block_state (liveness_analyze fn) dfg (cfg_analyze fn) fn
  (init_cleanup_plan_state ch growth spill_base lbl_ctr) lbl psD /\
psD.ps_stack = prefixD ++ core /\ psL.ps_stack = prefixL ++ core /\
(!v. MEM v (live_vars_at (liveness_analyze fn) pred
                (LENGTH pred_bb.bb_instructions)) ==>
  ~MEM (Var v) prefixD /\ ~MEM (Var v) prefixL) /\
generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
  (psD with <|ps_cleanup_height := hD; ps_cleanup_promised := bD|>) =
  SOME (bops,afterD) ==>
?choice afterL q residualD residualL prefD prefL.
  generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
    (psL with <|ps_cleanup_height := NONE; ps_cleanup_promised := choice|>) =
    SOME (bops,afterL) /\
  afterD = q with <|ps_stack := residualD ++ q.ps_stack;
    ps_cleanup_height := hD; ps_cleanup_growth := psD.ps_cleanup_growth;
    ps_cleanup_promised := prefD|> /\
  afterL = q with <|ps_stack := residualL ++ q.ps_stack;
    ps_cleanup_height := NONE; ps_cleanup_growth := psL.ps_cleanup_growth;
    ps_cleanup_promised := prefL|> /\
  (!v. MEM v (live_vars_at (liveness_analyze fn) lbl (LENGTH bb.bb_instructions)) ==>
    ~MEM (Var v) residualD /\ ~MEM (Var v) residualL)
```

The arbitrary endpoint consumer has **no existing SML theorem declaration**.
C3.correspondence.endpoint is a planned obligation, not a callable theorem.
Its precise stack-only version uses exactly the antecedent above and replaces
its consequent by:

```sml
!h b afterA.
  generate_block_plan (liveness_analyze fn) dfg (cfg_analyze fn) fn bb
    (psL with <|ps_cleanup_height := h; ps_cleanup_promised := b|>) =
    SOME (bops,afterA) ==>
  ?rD rA tail.
    afterD.ps_stack = rD ++ tail /\ afterA.ps_stack = rA ++ tail /\
    (!v. MEM v (live_vars_at (liveness_analyze fn) lbl
                    (LENGTH bb.bb_instructions)) ==>
      ~MEM (Var v) rD /\ ~MEM (Var v) rA)
```

All free variables in these displayed signatures are universally quantified at
the outside. The live-out queried here is this block's live-out (the block is
the predecessor in the subsequent history step), not the live-out of `pred`.
The latter appears only in the entry prefix hypothesis. This distinction must
not be hidden by the phrase "predecessor live-out".

## Cleanup: the actual unmatched cuts

These are the expressions in clean_stack_plan_def:762-801. For the singleton
predecessor with more than one successor and a successful predecessor lookup:

* `inputs = input_vars_from pred bb.bb_instructions (live_vars_at lv lbl 0)`;
* `layout = live_vars_at lv pred (LENGTH pred_bb.bb_instructions)`;
* `to_pop = FILTER (\v. ~MEM v inputs) layout`;
* `physical = FILTER (\op. IS_SOME (stack_get_depth op p.ps_stack)) (MAP Var to_pop)`;
* `retained = FILTER (\op. below_all_live op inputs p.ps_stack) physical`;
* `to_cleanup = FILTER (\op. ~MEM op retained) physical`;
* `ok = p.ps_cleanup_promised \/ cleanup_elision_safe p.ps_cleanup_height
  p.ps_cleanup_growth cfg fn bb (LENGTH p.ps_stack - LENGTH to_cleanup)`;
* `promised = p.ps_cleanup_promised \/ (ok /\ ~NULL retained)`.

These are explanatory equalities, not new definitions. There are three active
branches, independently on each side:

1. `NULL inputs /\ ok`: `([],p with <|ps_stack := MAP (K dead_stack_marker)
   p.ps_stack; ps_cleanup_promised := promised|>)`.
2. `~NULL inputs /\ ok`: if `popmany_plan to_cleanup p = (c,m)`, result is
   `(c,m with <|ps_stack := mark_dead_stack retained m.ps_stack;
   ps_cleanup_promised := promised|>)`.
3. `~ok`: `popmany_plan (MAP Var to_pop) p`.

If predecessor lookup fails, the predecessor has at most one successor, or
there is not exactly one predecessor, the relevant branch returns `([],p)`.
Only the singleton active case matters for the outstanding bridge.
Neither `physical` nor `retained` can be shared between the two runs without
proof: both depend on that run's stack. Arbitrary overrides can change `ok`.
The post-cleanup code equality known from two complete runs is only
`cD ++ wD = cA ++ wA` after cancelling their common label. It is not `cD=cA`.

## A concrete synchronized candidate, and its failure point

For a fixed `lv, lbl, insts`, consider configurations `(i,p,pre,rem)`.
Here `i` is the source instruction cursor, `p` an actual planner state, `pre`
the emitted prefix, and `rem` the remaining emitted code. The following is a
fully HOL-expressible candidate relation (the symbol R below is only the
abbreviation of this displayed formula; it is not an undefined semantics):

```sml
R i p pre rem j q pre' rem' <=>
  i = j /\ i <= LENGTH insts /\ pre = pre' /\ rem = rem' /\
  FDOM p.ps_spilled = FDOM q.ps_spilled /\
  ?rp rq tail.
    p.ps_stack = rp ++ tail /\ q.ps_stack = rq ++ tail /\
    (!v. MEM v (live_vars_at lv lbl i ++
                  FLAT (MAP (\inst. inst.inst_outputs) (DROP i insts))) ==>
      ~MEM (Var v) rp /\ ~MEM (Var v) rq)
```

It observes a common physical suffix, not merely a filtered live sequence.
It requires prefix exclusion of future definitions as well as present live
variables; otherwise silent aliases can introduce a queried name in a prefix.
It imposes no allocator or spill-offset equality. FDOM equality is strictly
weaker than equality of spill maps; it must not be strengthened silently.
At source end the formula immediately implies the required suffix/exclusion
conclusion. It is not defined in terms of that desired endpoint or a future
successful proof: its assertions concern only the current configurations.

The proposed interfaces, with every variable universally quantified, would be:

* Initialization: under the exact consumer antecedent and the arbitrary
  successful run above, and the two actual equations
  `clean_stack_plan lv cfg fn bb pD = (cD,mD)` and
  `clean_stack_plan lv cfg fn bb pA = (cA,mA)`, conclude
  `R 0 mD cD wD 0 mA cA wA`, where the actual worker equations are
  `generate_block_insts_plan lv dfg cfg fn lbl (bb_is_halting bb)
  0 (LENGTH bb.bb_instructions) 0 bb.bb_instructions mD = SOME(wD,afterD)`
  and the identical equation with `mA,wA,afterA`.
* One-source-step preservation: if `i < LENGTH insts`,
  `R i p pre (cp ++ rem) i q pre' (cq ++ rem')`,
  `generate_inst_plan lv dfg cfg fn (EL i insts)
  (live_vars_at lv lbl (SUC i)) halt next_term lbl p = SOME(cp,p')`,
  and the identical equation on `q,cq,q'`, conclude
  `R (SUC i) p' (pre ++ cp) rem (SUC i) q' (pre' ++ cq) rem'`.
  Here `halt` and `next_term` are universally quantified Booleans, not semantic
  placeholders; a consumer instantiates them as in the actual worker recursion.
* Terminal elimination: `R (LENGTH insts) p pre [] (LENGTH insts) q pre' []`
  implies `?rp rq tail. p.ps_stack=rp++tail /\ q.ps_stack=rq++tail /\
  (!v. MEM v (live_vars_at lv lbl (LENGTH insts)) ==>
  ~MEM (Var v) rp /\ ~MEM (Var v) rq)`.

**Initialization is not supplied.** In particular its `pre=pre'` is exactly
the unsupported cleanup cut equality. Removing that conjunct does not fix
preservation: `cp++rem=cq++rem'` at two instruction starts need not establish
`cp=cq`. Removing common-suffix or future-definition exclusion instead leaves
no way to establish the terminal consumer. Thus this candidate is not ready
for implementation. No assertion here is that initialization is false under
the full reachability hypotheses; it is an identified missing argument.

## Finite preservation/supplier table

| Actual branch | Necessary relational fact | Checked supply / outstanding gap |
|---|---|---|
| Cleanup inactive | entry common suffix survives unchanged | Algebraic, but does not cover active singleton cleanup |
| Empty-input elision | all cells become marker; both cuts must still synchronize with a possibly nonempty other cleanup | Marker action known from definition; cross-branch cut alignment **not supplied** |
| Pop-and-mark | relate actual `to_cleanup` pops, then forget `retained` names without forgetting physical slots | Chosen paired cleanup supplied by lineage_singleton_paired_setup; arbitrary `h,b` case **not supplied** |
| Full popmany | same physical suffix after potentially moving live cells around buried dead cells | **Not** a consequence of prefix live exclusion alone; no arbitrary paired-cleanup theorem supplied |
| Pre-codegen / malformed INVOKE | cannot be successful branch | generate_inst_plan_pre_codegen_none / malformed_invoke_none |
| PHI | source depth, duplication if source stays live, SOPoke alias, possible dead-output pop | Definition inspected; singleton blocks have no PHIs by ready/phis_at_joins, as used in selected proof. Do not generalize to join PHIs without their existing schedule machinery |
| OFFSET | output push associated to SOPushOfst, no dead-output pop | Explicit branch in generate_offset_plan; requires matched producer cut before using it |
| Parameter / NOP | no state action, no emission | Definitions; nonentry singleton has no parameter suffix. Empty chunks cannot supply cuts |
| Regular ASSIGN | operand materialization/reorder, silent pop/push rename, dead-output pop, optimistic swap, release | No genuine producer anchor for the alias. Needs equal source cursor AND corresponding consumed physical cell; no such supplier from flattened code alone |
| Regular ordinary producer | same input observations, common output naming at matched producer | Emission anchor position uniqueness supplies matched emitted positions only when ordinal and retained-head premises already hold |
| INITIAL_FMP / BUMP | distinct emission forms, BUMP multi-op/multi-output behavior | Must use actual emission equations, not one source = one op; local access cancellation is insufficient |
| INVOKE / dynamic-label emitters | input/return layout, fresh-label action, outputs and subsequent reordering | Existing emission projection does not establish the alias/physical correspondence premises |
| JMP join | restores all spilled targets, reorders, join_reached guard | Availability/selected replay machinery exists; restores and reorder contain the same words as other stages and do not themselves delimit source cuts |
| All regular postprocessing | dead-output pop, optimistic swap, release_dead_spills | Must establish next-live exclusion and spill-domain correspondence from actual paired states, not final spill equality |

The primitive suffix-cut results apply only once both configurations are at
valid access starts: `d < LENGTH p.ps_stack`, `e < LENGTH q.ps_stack`, plus
positive distances for swaps. A successful `stack_get_depth` lookup can
supply validity for that individual access; a successful block run cannot.
The new lemmas do not supply *simultaneous* starts in the table above.
`emission_anchor_position_unique` similarly needs equal retained ordinals and
retained heads on both sides; it does not supply silent ASSIGN cuts.

## Checked suppliers and exact remaining boundary

* `lineage_state_actual_dfs_fields` supplies equal actual DFS non-stack fields
  at entry, not at arbitrary intermediate cuts.
* `lineage_singleton_paired_setup` selects `NONE,choice` on the lineage side;
  its cleanup code is identical to the reference cleanup. It does not quantify
  over arbitrary `h,b`. This is the first quantifier mismatch.
* `lineage_singleton_setup_core_seed` supplies core availability and
  future-output/live exclusion **after that selected paired setup**.
* `lineage_singleton_block_physical_transfer` then supplies the selected
  block endpoint, not an arbitrary same-code endpoint.
* `singleton_block_equal_cleanup_endpoints` requires identical cleanup code
  and identical cleaned state up to bookkeeping. Its exact premise is
  `clean_stack_plan lv cfg fn bb p=(c,m)` and
  `clean_stack_plan lv cfg fn bb q=(c,m with <|ps_cleanup_height:=h;
  ps_cleanup_growth:=g; ps_cleanup_promised:=b|>)`. It cannot discharge the
  arbitrary unequal-cleanup case.

A replacement asynchronous candidate would need separate source cursors and
pending *partial instruction/cleanup phases*, together with a correspondence
for the remaining physical cells and silent source aliases at those phases.
Merely putting arbitrary residual lists into R does not supply this relation.
The existing whole-instruction worker state does not expose those phases.
This record therefore returns a **precise failed synchronized candidate** for
strategy review, not a new source-free parser project or a speculative
asynchronous definition. The next decision belongs to the strategist: derive
a genuine cleanup/source alignment supplier under the actual singleton
hypotheses, or replace this route with a concrete phase relation whose
initialization and silent-alias cases are justified. No candidate satisfying
all three interfaces is currently supplied by the inspected machinery.

## Successor-demand decision (2026-11-10)

**Bounded outcome: reject the observation weakening as a supplied proof
interface.** This does not reject the frozen theorem and is not checked
falsehood evidence. The missing implication is history admission -> numeric
successor observations (or a common suffix supplying them). Even granting
initial observations does not yet supply their preservation through the worker.
No new HOL helper, definition, executor, diagnostic, or proof hole is proposed
by this decision.

### Endpoint normalization and an explicit candidate

Write `a` for the *actual* predecessor endpoint in lineage_state_step and `s`
for the successor DFS input. The next lineage input is
`s with <|ps_stack := a.ps_stack; ps_spilled := a.ps_spilled|>`.
The admission equation is **`a.ps_spilled = s.ps_spilled`**, not equality to
an arbitrarily chosen reference predecessor endpoint. It pins the new input
spill map; its allocator, label counter and other non-stack fields are those
of `s`, regardless of `a.ps_alloc`. Thus equal allocators at the *next input*
are available by record update, not inferred about predecessor intermediates.

Here is a concrete initial-demand candidate, expressed entirely by stack
queries rather than future successful executions. All displayed variables
are universally quantified outside the equivalence; the auxiliaries are
explicit arguments, not implicit choices or new constants. `bb` is the
successor and `pb` the predecessor. This is a design formula only:

```sml
D lv cfg fn pred succ pb bb inputs layout removed a s <=>
  lookup_block pred fn.fn_blocks = SOME pb /\
  lookup_block succ fn.fn_blocks = SOME bb /\
  cfg_preds_of cfg succ = [pred] /\
  inputs = input_vars_from pred bb.bb_instructions (live_vars_at lv succ 0) /\
  layout = live_vars_at lv pred (LENGTH pb.bb_instructions) /\
  removed = FILTER
    (\op. ~below_all_live op inputs s.ps_stack)
    (FILTER (\op. IS_SOME (stack_get_depth op s.ps_stack))
      (MAP Var (FILTER (\v. ~MEM v inputs) layout))) /\
  a.ps_spilled = s.ps_spilled /\
  (!v. MEM v (layout ++ inputs) ==>
    stack_get_depth (Var v) a.ps_stack = stack_get_depth (Var v) s.ps_stack) /\
  (!v. MEM v layout ==>
    below_all_live (Var v) inputs a.ps_stack =
    below_all_live (Var v) inputs s.ps_stack) /\
  LENGTH a.ps_stack - LENGTH removed = LENGTH s.ps_stack - LENGTH removed
```

This deliberately strong initial candidate supplies exact option-valued
numeric depths, not just membership or relative ordering. Its last conjunct
allows the same height-safety test if the reference cleanup fields are used
on both sides. It is already *too strong* to be an appropriate invariant of
marker prefixes: arbitrary bottom prefix lengths are intentionally allowed
by the checked suffix consumer, but need not satisfy this height equality.
Dropping the height conjunct is possible for selected cleanup: choose
`NONE,choice` with `choice` equal to the reference `ok`, as the checked paired
setup does. This avoids equality of height tests, not equality of the stack
queries or their preservation. Inactive cleanup need not use these queries
at all. The candidate is therefore an audit of a tempting weakening, not a
claim of minimal necessary conditions.

### Finite cleanup observation audit

The table concerns cleanup of the **next successor** from the normalized
input. The same four cases can occur when analyzing the arbitrary predecessor
run, but its cleanup code cannot be identified with the reference cleanup
code from whole-block code equality.

| Case in clean_stack_plan | Observations needed for a paired selected action | Does exact admission spill equality supply them? |
|---|---|---|
| Inactive | No stack query; return the input unchanged. Subsequent worker still needs physical correspondence. | No. It supplies only the input spill map, not stack depths. |
| Empty inputs, `ok` | Empty code and all cells mapped to marker. Different lengths can remain as excluded prefixes; no live input depth must be matched. To match this branch select `NONE,T` if the reference elides. | Does not select or exclude this branch. Marking does not write ps_spilled. |
| Nonempty inputs, `ok` | `physical` uses presence for layout-minus-inputs; `retained` uses below_all_live; popmany needs numeric depths of removed operands and valid physical windows. Marking must not lose needed input/future-output exclusion. | Supplies none of these stack facts. Popmany and marking preserve ps_spilled, including deep swap paths. |
| `~ok`, full popmany | Lookups of all to_pop operands, including NONE cases; depth ordering, contiguous-top test and sequential swap/pop effects. Matching initial presence alone does not match these actions. | Does not exclude the branch or pair it with either elision branch. Full popmany also preserves ps_spilled. |

For the active query computation the checked suffix theorem supplies more
than set equality: `stack_get_depth_bottom_excluded` and
`below_all_live_bottom_excluded` give equal queries on a common core. In its
marked and popped branches, `popmany_plan_shared_core_replay` supplies the
*whole resulting common physical core and equal allocator*. There is no
corresponding checked consequence from D's finite query vector alone.
The empty-input branch can take an empty common core and marker-only
prefixes. Thus the suffix proof is not merely a verbose proof of presence.

All four cleanup branches preserve ps_spilled. This does **not** prove that
the *complete predecessor run* always passes the admission check: later
restores/releases may change its map. It establishes the narrower, sufficient
negative decision: admission equality cannot by itself identify the cleanup
branch or any intermediate numeric depth. In a continuation with no spill-map
updates the restriction distinguishes no cleanup choices at all. In other
continuations a separate theorem about those actual updates would be needed;
final equality cannot be substituted at the cleanup cut.

### Worker and terminal consumer audit

The actual consumer `analyzed_worker_cleanup_replay` (:2849-2884) takes a
single base state `p0`, with the two stacks `prefixP ++ p0.ps_stack` and
`prefixQ ++ p0.ps_stack`. It requires (i) core live-in availability,
(ii) both prefixes exclude every instruction's next-live and outputs, and
(iii) terminal JMP target distinctness and availability at every specified
native prefix. It returns a common final base record, hence equal alloc and
spill projections. It does not accept equality of entry depth vectors as a
substitute for the common base record.

`lineage_singleton_setup_core_seed` supplies (i) and (ii) **after selected
paired setup**, not for arbitrary cleanup overrides. The analyzed edge-live
subset in `analyzed_single_pred_excluded_prefix_cleanup` (:1453-1464) moves
successor inputs into predecessor live-out; it does not supply either
endpoint suffix or endpoint depth equality. `lineage_state_actual_dfs_fields`
supplies non-stack input equality. These checked suppliers are compatible
with the suffix route, but none establishes D on arbitrary admitted endpoints.

For a terminal JMP, `lineage_singleton_core_terminal_targets` and
`ordinary_core_terminal_targets` supply target distinctness and stack-or-map
availability. They do not supply target numeric depths. The worker consumer
first transports the ordinary prefix with a common physical suffix, then
restores/reorders all targets. `join_reached` checks the final target suffix;
it does not retroactively align earlier source cuts or access distances.
A successor that itself has one predecessor need not end in JMP, so a terminal
join condition cannot be assumed for every singleton successor.

Two symbolic stress tests localize the failed weakening without a fixture:

* A regular ASSIGN may emit no genuine producer anchor. The regular planner
  still materializes its input, reorders, pops the consumed cell and pushes
  its output name (:278-319). Equal initial queried names/depths do not say
  which unqueried cells become exposed after those mutations, or exclude an
  output alias in an unmatched prefix. The existing worker avoids this by
  future-output exclusion and a shared physical tail throughout, not by an
  initial finite query vector. No claim of an actual reachable counterexample
  is made by this missing preservation argument.
* do_swap selects shallow/deep at distance 16; do_dup at distance 15. In the
  deep cases (:75-134 of stackPlanOps) emitted offsets and final allocator
  depend on the allocated physical window. Both preserve ps_spilled.
  Membership and relative order leave distance unspecified; D fixes the
  initial queried distances but not all later window observations. Exact
  spill-map equality therefore cannot justify equal code or output allocator
  for this weakening. Resetting allocator at the next lineage input does not
  repair different allocation *during* successor replay.

### Localized conclusion and review boundary

Initialization at the function entry remains checked by
`lineage_dfs_entry_block_universal_endpoints`; joins have their separate
checked actual replay. The unresolved singleton-history induction would have
to establish D's numeric stack queries, or the existing common-suffix premise,
for **every actual arbitrary predecessor cleanup override** whose complete
code and admitted successor map agree. No inspected theorem does so. The
admission premise supplies the map conjunct of D only. Even hypothesizing D
at one endpoint supplies no checked source-step preservation or implication
to the current worker's stronger common-core hypotheses.

Decision: do not implement D or replace the sufficient suffix interface with
it. This bounded pass identifies two distinct missing arrows, rather than a
new lemma queue: arbitrary admitted history -> successor numeric physical
observations; and initial finite observations -> worker-preserved physical
correspondence. A strategist must supply a concrete argument for those arrows
(or an alternative arbitrary-history theorem) before realization/integration
can proceed. The analysis is not a proof that the frozen theorem is false,
and authorizes neither a fixture nor more source-free parsing.

## Same-input cleanup rigidity: scalar decision (2026-11-10)

**Outcome: the proposed scalar deduction is underdetermined, even granting
its strongest useful accounting hypotheses.** This is an algebraic obstruction
to the proposed argument, not a counterexample to the theorem or to a possible
stronger physical rigidity result. No SML change is made.

Compare two block runs starting from exactly the same psL except cleanup
height/promise. Call their cleanup chunks `cF,cE`, cleaned heights `HF,HE`,
worker chunks `wF,wE` and final heights `ZF,ZE`. They emit the same whole code:
`cF ++ wF = cE ++ wE`. This comparison correctly avoids unequal incoming
stacks. It does not, however, remove the unequal cleanup/worker cuts.

### Physical-height ledger

Use integer differences throughout this paragraph; natural subtraction would
hide underflow. For this audit only, the additive code weight W assigns +1 to
SOPush, SOPushLabel, SOPushOfst, SODup and SORestore; -1 to SOSpill; -n to
SOPop n; and zero to SOSwap, SOPoke, SOEmit, SOLabel, SOInitialFmp and the
remaining constructors. It is a bookkeeping weight, **not EVM stack
semantics**. In particular emitted opcodes do not directly mutate ps_stack
in generate_emit_ops. W of an append is the sum of W of its pieces. The
following is an accounting analysis of the existing definitions, not a new
proved accounting theorem.

| Planner stage | Actual height change and comparison with W |
|---|---|
| do_restore | +1 on SOME, 0 on NONE; exactly W of its actual code. Deleting the map key does not create a silent physical pop. |
| restore_spilled_plan | Sum of actual successful restores. Repeated requests may later miss; count actual code, not initial domain cardinality. |
| do_spill_tos / do_spill_at | -1 on a nonempty stack; on empty stack the truncating pop has change 0 rather than W=-1. Actual selected spills need nonemptiness. Swaps themselves preserve height. |
| Shallow do_swap | Height and W both unchanged, even for saturated indexing. |
| Deep do_swap | With chunk=dist+1 and H=input height, code spills min(chunk,H) cells and restores chunk; physical change is max(H,chunk)-H, exactly the same W. In the valid-depth case both are zero. Allocation/free effects are not height changes and need not be identity. |
| Shallow do_dup | Height +1 and W=+1, regardless of the value returned by peek. |
| Deep do_dup | With k=dist-15, the code spills min(k,H), restores k and duplicates once; W=1+k-min(k,H), whereas stack_dup increases height by 1. Defect is min(k,H)-k. Valid depth implies k<=H and defect zero. |
| emit_one_input / emit_input_plan | Literal/ordinary label push +1; successful variable dup/restore as above; missing variable with no restore/dup changes height by 0. INVOKE label input is a silent +1, but actual compute_operands INVOKE removes labels, so that exceptional input case is absent in the regular worker. |
| reduce_depth / reorder | Sum spill/restore/swap changes. An absent unfixed operand may skip everything; equivalent-operand pokes preserve height. Missing operands do not justify enough height for later silent consumption. Adequacy/nonempty hypotheses are required to discard the defects just listed. |
| Regular silent consumption/output insertion | With M=LENGTH(compute_operands inst), O=LENGTH inst.inst_outputs and H4 the pre-consumption height, exact change is -min(M,H4)+O. It equals O-M plus the nonnegative saturation term max(0,M-H4). |
| generate_emit_ops | No ps_stack change. Subtract W of this stage's emitted chunk when relating the complete instruction code to planner height. Its weight is fixed by the source branch/shape: e.g. JMP pushes a label in code but not in ps_stack; INVOKE emits two labels without pushing them here. Fresh label text does not affect W. BUMP uses its actual fixed bump_emit_ops weight, not an assumed EVM opcode effect. |
| Dead-output popmany | Sum actual emitted pop amounts, with negative sign. Search hits give valid depths; the contiguous-top fast path has a valid deepest cell. Missing requests emit nothing and change no height. No assumption that requested-list length equals number actually popped is needed. |
| optimistic_swap | Swap height/W accounting above; allocator may change in deep paths. |
| release_dead_spills | Physical height and code both unchanged. Domain shrinkage and freed slots are not physical stack changes. |
| OFFSET | Label branch pushes an output and SOPushOfst: +1 on both sides; other branch 0. |
| NOP / parameter dispatch | No action; rejected dispatches cannot be successful. Singleton nonentry workers have no PHIs, so no PHI ledger is needed for this decision. |
| ASSIGN | Same regular ledger, including silent -M+O and any saturation term. With the usual one input/output and adequate consumption, source correction is zero and no producer opcode is required. Silence does not imply no state change. |

For an adequate regular instruction with valid access windows, the precise
form of the prospective identity is

`Hout - Hin = W(actual_instruction_code) + O - M - W(emit_chunk)`.

Without adequacy, add the consumption saturation term and the primitive
access defects just tabulated. This shows why successful SOME alone cannot
supply the identity with a source-only correction. For a singleton worker,
all *source-only* corrections sum to a fixed K for its source instruction
list, after accounting for OFFSET/NOP separately. Restores, releases and
missing accesses must not be estimated from the final spill map; actual
code weight handles the restores, while the defects remain explicit until
appropriate validity facts are supplied.

Cleanup has no source consumption/output correction: inactive and
empty-input marking have height change 0 and W=0. Pop-and-mark has change
minus its actual number of popped slots, as does full popmany; marking itself
changes only identities. The pop counts need not be guessed from list length.
Starting from the SAME stack fixes physical/retained lists before the branch,
but does not give equal cleanup chunks. In the best-case simple accounting
where full cleanup removes r more retained slots than elision, write
`HE = HF + r`. Equivalently `W(cF)-W(cE) = -r`. The obstruction below already
holds granting this favorable description; complications with pop counts do
not rescue it.

### The first algebraic obstruction

Grant, more strongly than currently checked, that *both* workers have zero
validity/saturation defects and the same source correction K. Whole-code
equality yields only

`W(wF) - W(wE) = W(cE) - W(cF) = r`.

The worker ledger then gives

`(ZF - HF) - (ZE - HE) = r`.

Since `HF-HE=-r`, substitution gives **`ZF-ZE=0`**, not `r=0`.
All occurrences of r cancel. This remains underdetermined even if final
height equality is supplied independently: it is the same equation again.
Hence the suggested phrase "worker height change is independent of cleanup
choice" is the missing extra premise, not a consequence of fixed source
correction K. The actual worker height change includes W of its worker code;
whole-code equality does not give `W(wF)=W(wE)` across unequal cuts.

In particular a difference in emitted input dup/restore or postprocessing pop
counts is an explicit term in W(wF)-W(wE); it cannot be set to zero using
source equality. One need not construct a reachable compensating execution
to reject this deduction: the conservation equations themselves permit
exactly the compensation required by whole-code equality. This decision
asserts no such execution exists or does not exist. Nonzero defects would
add still more unsupplied terms, not a rigidity proof.

The spill admission equation does not close this scalar system. Even granting
that both compared endpoints have the same spill map, net restore counts
cannot be recovered from it: spill insertions can interleave with restores,
release can delete entries without physical change, and scratch spill/restore
paths do not change ps_spilled at all. The selected replay is not automatically
admitted to a particular successor map merely because the arbitrary one is;
no part of this audit assumes that additional endpoint equality.

Nor does r=0, if obtained elsewhere, automatically prove equal cleanup states:
full removal uses swaps/pops while elision marks cells, and zero *height*
difference need not identify the resulting order or allocator. That would
require a branch-specific physical equivalence theorem, not conservation.
If one could instead show the exact same cleanup state and code up to
bookkeeping, existing deterministic cleanup-update worker facts would apply;
this audit supplies neither antecedent.

### Decision boundary

Reject scalar conservation alone as an arbitrary-cleanup rigidity supplier.
The first obstruction is the explicit unmatched term W(wF)-W(wE): the equation
needed to make it zero is precisely not supplied by whole-block code equality.
A proof that retained cells remain inert throughout both actual workers might
supply an independent difference invariant, but it is a new physical argument
and is **not** derived or authorized here. Preserve the selected replay and
all earlier checked helpers. Return this finite negative algebraic decision
for strategy review rather than implement accounting helpers whose strongest
possible identity still cancels the retained-slot variable.

## First retained-region action: physical decision (2026-11-10)

**Bounded outcome: no complete first-action supplier obtained.** The precise
remaining branch is comparison of an in-progress deep scratch access in full
cleanup with the other run's access/ASSIGN worker prefix. The operation-level
shielding results below resolve some tempting objections, but they do not
supply a paired physical assertion at that asymmetric phase. This is not a
claim that unequal branches can emit equal complete code.

### Same-input branch reduction

For the SAME incoming stack, `physical`, `retained` and `to_cleanup` are
identical before the override-dependent Boolean `ok` is evaluated. Inactive
cleanup is identical. Two nonempty-input runs with the same `ok` have the
same actual popmany action and marking, differing only in bookkeeping. Two
empty-input runs with `ok` both map every position to marker. These cases
can use the existing cleanup-update/deterministic-worker interface.

Only opposite `ok` choices remain. In full cleanup the requests are
`MAP Var to_pop`; in elision they are `to_cleanup` (or no pops for empty
inputs). Sorting is by initial depths for each entire request list. The
contiguous fast-path test is also over the entire list. Removing retained
requests can change that test; one cannot factor full cleanup as the elided
cleanup plus a tail. Within an individual-pop execution, a retained request
is handled at its *current* depth: swap that cell with TOS, then pop. This
moves the old top cell into the retained cell's position. Thus full removal
can move a live original cell downward, and it is incorrect to model it as
list filtering of dead original identities.

### Bulk boundary exchange: what is actually settled

The exact schematic fast path is

`base ++ removed ++ [top]`, with request depths `1,...,n` and
`LENGTH removed=n`.

It emits the depth-n swap and SOPop n; the result is `base ++ [top]`.
The deepest removed original cell is exchanged with top before removal;
it is a *requested* cell, not an arbitrary unrequested sentinel. This
explains both the downward relocation and the boundary hazard for an
unjustified proposed protected core.

For a legitimately framed stack `prefix ++ core`, the case
`n=LENGTH core` cannot satisfy this contiguous test together with request
exclusion from prefix: depth n lies outside core and the test includes n.
The existing `popmany_plan_shared_core_replay` uses precisely that valid-hit
bound; `Setup.popmany_plan_bottom_frame` (:1575) requires request/prefix
DISJOINT. Thus the boundary does **not** defeat that checked theorem and
must not be advertised as a counterexample to it. A proposed inertness
argument that has not established request exclusion at its actual cut
cannot invoke the bound. This is the exact missing premise when a chosen
original-cell region is casually called a protected core.

For a well-formed ASSIGN, one input and one output are fixed by inst_wf.
After regular output insertion its output is at TOS. If dead-output removal
runs, `popmany_plan_appended_singleton` (:1849) gives exactly SOPop 1 and
removes the appended occurrence, including in the presence of older copies.
There is no contiguous depth-one boundary exchange in this ASSIGN output
pop. ASSIGN is nevertheless not a state no-op: its input may restore/dup,
its reorder may move cells, its silent consumption/push renames a slot, and
its first optimistic swap may move a different next-live cell. Literal or
label ASSIGN input also emits its own push anchor. None of this can be
replaced by an assumption that every original cell keeps its name.

A multi-output instruction's dead outputs can use the contiguous fast path
when a retained live output is on top. With a valid common suffix containing
all requested outputs, the n=LENGTH(core) contradiction above still applies.
One must first show that suffix contains the actual requested output cells;
no argument here transfers such a suffix from the selected run to an arbitrary
worker phase. The producer's actual emission also cannot be erased merely
because its later dead outputs are popped.

### Optimistic swap and empty-input limits

The first optimistic swap is a do_swap at the lookup depth of
`Var (LAST next_liveness)` unless a guard makes it inactive. The checked
`optimistic_swap_plan_shielded_bottom_frame` (:1505) accepts exactly empty
live, exclusion of that name from prefix, or an actual suffix hit. These
are real local sufficient conditions, including deep swaps. The common-core
selected worker supplies such facts via its indexed exclusion/availability
seed; the actual asymmetric comparison has not supplied a suffix or its
hit at the matching worker phase. Global stack-or-map availability is not
a suffix hit, and does not identify original-cell locations.

For empty inputs, elision turns every position into marker with empty code.
Full cleanup removes whatever predecessor-layout requests actually hit,
possibly leaving old non-layout debris. It is unsound to conclude that its
entire resulting stack is marker-only. Input demand is empty, but later
fresh definitions and their uses may still create a nonempty live-out. The
empty-input case therefore still needs an initialized difference argument
through the actual worker, or a proof that full cleanup cannot match that
worker's emitted prefix. It is not settled just by taking an empty common
core at block end.

### Exact unresolved operation/phase

Take the actual first retained request handled in a full-cleanup
`popmany_individual` execution. If its current distance d exceeds 16,
its do_swap starts a scratch window of d+1 original/current cells. The
first code is SOSpill off, followed by more spills before the restores.
The opposite cleanup may already have finished and its worker may be inside
a deep do_dup (input preservation) or do_swap (input/reorder/optimistic
access). These also start with SOSpill off from the same starting allocator
or from an allocator reached after earlier accesses. The **first emitted
SOSpill alone** does not specify which source operand was accessed or how
many scratch cells will follow. Marked identities and silent ASSIGN rename
steps are not emitted cell-identity observations.

To conclude separation at the first spill touching the retained region, one
needs a paired assertion at that code position: the worker's current scratch
window ends strictly above that original retained region, and any earlier
common spills/restores have corresponding physical cells despite silent
renames. Alternatively one needs both executions certified at matching
primitive starts with their valid depths, so the existing primitive cut
inverses can compare the complete scratch templates. Neither premise follows
from equality of the remaining flattened code prefix or from the full run's
valid lookup alone. A bound on the worker's *initial selected core* does not
supply it at a position inside an arbitrary worker scratch sequence.

This is a localized missing native premise, not a proposal to parse source
cuts: actual input/reorder/optimistic equations must provide the protected
region and its evolution through ASSIGN, spills and partial scratch accesses.
The full cleanup equations supply its own request depth, but not that paired
phase fact. The bulk request-exclusion lemma and the ASSIGN top-singleton
lemma settle their local cases only once those actual contexts are supplied.
Equal spill maps do not label scratch cells, since scratch accesses preserve
ps_spilled. Accepted primitive inverses similarly start from simultaneous
valid access boundaries, not this unmatched interior position.

Decision: stop this bounded first-action pass at this explicit deep scratch
phase premise. No initialized physical separation invariant or arbitrary
endpoint theorem has been proved. The analysis does not authorize another
parser, interpreter, fixture, or speculative primitive helper queue. Any
next strategy must justify that actual paired region/phase assertion or
avoid it with a different complete argument; naming it as an invariant is
not its initialization proof.
