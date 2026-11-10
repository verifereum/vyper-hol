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
