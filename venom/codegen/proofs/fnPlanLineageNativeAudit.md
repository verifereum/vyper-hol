# Native instruction/transfer boundary audit (C3.bridge.native_audit)

2026-11-07. Diagnostic source audit, NOT a new invariant or proof of native
reachability. Existing audit owners are StageAuditScript.sml:72-166,
:1375-1444 and PathScript.sml:390-421; reuse their warnings rather than
re-proving fixtures. New contribution: consolidate full dispatch coverage and
identify which checked interfaces are already sufficient versus missing.
No universal physical_live preservation claim is made.

## Notation and transfer equation

In this document only, V(L)=set(MAP Var L), I(S,p)=lineage_inventory S p,
D=inst.inst_outputs, U=inst_uses inst, A=compute_operands inst, L=next_liveness.
Set-level liveness_transfer is (V(L) DIFF V(D)) UNION V(U), by
livenessDefs.live_update_def/MEM_FOLDL_append_unseen and inst_defs_def.
Compute_operands_inst_uses (Callers:8) is only the forward implication;
its converse needs branch shape (e.g. LOG's removed topic must be Lit).
Repeated variables occur once in transfer but many times in A. The emitter
uses remaining operand variables ++ L to duplicate all but last dead use.
Literals and labels are not in U. They are transient physical operands where
compute_operands includes them, and must be consumed, not put into I's core.

## Complete generate_inst_plan dispatch matrix

Source: stackPlanGen:514-536; regular subdispatch :268-341.

| Branch | Transfer / physical action | Multiplicity / terminal exception | Existing owner; missing producer |
|---|---|---|---|
| pre-codegen opcode | NONE; no successful transition | excluded by codegen_ready_inst | generate_inst_plan_pre_codegen_none; no new invariant needed |
| malformed INVOKE | NONE | ready INVOKE is label-headed | generate_inst_plan_malformed_invoke_none, invoke_operands_wf; argument/output arities are NOT guaranteed by codegen_ready_fn alone |
| PHI, no selected depth | identity despite transfer removing D and adding all syntactic alternatives | SOME result does not ensure selected source | PhiTemporal/PhiInventory, NativeTargets.ready_unrenamed_phi_partition, JoinEntry.analyzed_edge_phi_matching_total; need predecessor-specific physical selection |
| PHI, selected dead source | rename one selected occurrence to output; if !halting and output dead, pop output | other alternatives absent from selected predecessor need not be represented; halting retains dead output | Replay rename interface, PhiResources.dead_phi_selected_erased/dead_phi_retained_count_balance/dead_phi_fresh_result_resource; full sequential exact inventory and freshness producer missing |
| PHI, selected still-live source | duplicate selected source then rename top duplicate, optional dead-output pop | duplicated intermediate is not distinct; source retained | PhiTemporal write phase and resource interfaces; readiness phi_block_ready excludes incoming names from post-prefix live list, but converting that into EACH evolving PHI next-live is separate work |
| OFFSET | well-shaped [Lit;Label], singleton output: push Var out; U=[] | no dead pop or spill release, even in nonhalting block | Stages.generate_offset_plan_frame; StageAudit.offset_retains_output/offset_multiplicity_ledger. offset_outputs_used is static existence, NOT dynamic freshness or immediate next-live membership |
| PARAM/FMP_PARAM/RETPC_PARAM | per-inst identity, but transfer normally removes output | entry pushes ALL params before dispatch; block loop filters params out | Setup.native_parameter_lineage_inventory/native_parameter_depth_exists; canonical_param_prefix owns placement. Do not assert ordinary per-param transfer preservation |
| NOP | identity, ready operands=[] and inst_wf outputs=[] so transfer identity | spilled map unchanged | dispatch definition + readiness/inst_wf; straightforward identity corollary, no separate general machinery needed |
| remaining opcodes | regular pipeline | subrows below | Setup/Inventory/Reorder/Physical interfaces |

Readiness: codegen_ready_fn also supplies SSA distinct static outputs,
well-formed instructions, def-dominates-uses, single-use form, normalized CFG,
entry with no predecessors and no PHIs, PHIs only at joins, JMP-only incoming
edges for multi-predecessor blocks, phi operand disjointness and post-prefix
deadness. It does NOT alone supply dynamic physical freshness on loop visits,
empty spills, a shared stack hit, or deletion of stale residual prefixes.

## Regular pipeline submatrix

| Branch | Actual effect / transfer compatibility | Existing owner / missing boundary |
|---|---|---|
| JMP | A=[] for well-shaped JMP. Restore every target spill, reorder target suffix, release spills not in L; outputs=[] | Liveness.analyzed_live_out_jmp equates analyzed L to target set. join_reached checks suffix ONLY. Inventory restore and PhysicalOps singleton boundaries do not prove arbitrary target reorder exact inventory or erase non-target residual names |
| JNZ/DJMP | A=get_non_label_operands; labels excluded. Variables agree with U, outputs=[] | bounded ordinary materialisation/reorder/pop in Inventory/Reorder; Callers.analyzed_computed_operand_demand supplies input coverage from incoming analyzed live coverage |
| INVOKE | A excludes labels; outputs arbitrary distinct SSA names, ordinary consume/push | generate_emit_ops changes fresh-label counter, NOT stack or spill map. Setup.generate_emit_ops_core_resource and copied Reorder.generate_emit_ops_slots; common label-counter/allocator equality still needed for replay |
| LOG | A=TL operands, removes literal topic count | ready_inst + inst_wf ensure topic Lit, no removed variable use; no outputs; ordinary consume/release |
| INITIAL_FMP | A=[], singleton pushed output; emit SOInitialFmp leaves planner state unchanged | ordinary fresh-output machinery; dead singleton retention in halting blocks applies |
| BUMP | two operands/two outputs; emit [SODup 2;SOEmit ADD] leaves planner state unchanged | physical planner push/pop model already handles two outputs; dead outputs always popped even in halting blocks. Distinct outputs from SSA; transient multiplicity remains ordinary materialisation obligation |
| other ordinary / EVM named opcodes / ASSIGN | A=python_stack_operands; same variable support, possible reversal. Push literals/labels, restore/duplicate variables; pop LENGTH A and push D | all four variable ASSIGN source/output conservation branches now Physical (E0429/E0431/E0432). General bounded preparation/pop already Setup.native_regular_live_inventory, subject to its exact premises below |
| commutative choice | choose either A or swapped last two operands by cost | selected list PERM A (Setup.native_regular_stages); do NOT assume same reorder state/cost from arbitrary prefixes |
| no outputs | release_dead_spills L only; no optimistic swap | no stack sweep of old dead residuals |
| outputs and nonhalting OR length>1 | pop dead D; if any live output then optimistic swap; release | Setup regular_post_emit_tail_*; Physical.physical_live_native_live_assign_from_consumed factors checked ASSIGN instance |
| halting and exactly one output | keep even dead D; optional optimistic only if output live | StageAudit.regular_dead_output_stages checked by EVAL. is_halting=bb_is_halting bb for EVERY instruction, so exact I(V(L),p) is invalid at interior dead-output positions, not merely at final terminator |

The final halting terminator (RETURN/REVERT/STOP/INVALID/SELFDESTRUCT) has
no label operands under readiness and no outputs under inst_wf. Its CFG
successors are empty by get_successors. This does NOT remove the need to
replay earlier dead-output-producing instructions in that block. DRET/RET
are not bb_is_halting opcodes; treat according to regular dispatch, not as
an exception just because their names suggest return. Raw FMP operations are
pre-codegen; INITIAL_FMP/BUMP are explicitly admitted.

## Exact candidate stable-boundary statements (UNVERIFIED unless cited)

1. Existing, proved: Setup.native_regular_live_inventory supplies
I(V(L),qs) and a marker-core residual budget for non-JMP regular planning.
It requires marker-prefix decomposition, residual_budget_wf on the core,
computed-input and live-through coverage, inventory upper support in
V(operand_vars A ++ L), fresh distinct outputs, bounded/marker-free A, and
(!halting OR LENGTH D>1 OR EVERY (MEM-in-L) D). Do not recreate this theorem.
Callers.ordinary_position_invariant already supplies structural resources,
live lower coverage and demand_available upper support under explicit inputs;
Path.definition_support_output_fresh uses SSA plus demand upper support.
The missing bridge is actual reachable supply of those premises, NOT another
arbitrary-state ASSIGN proof. Physical_live alone need not supply the residual
budget's allocator premises; inspect residual_budget_wf_canonical before use.

2. UNVERIFIED local specialization worth testing: for ready non-JMP ordinary
instruction i with set(U)=set(operand_vars A), ALL_DISTINCT D, output names
absent from incoming resources and A, the retention condition above, and
I((V(L) DIFF V(D)) UNION V(U),p), successful planning gives I(V(L),q).
First decide whether exact inventory alone supplies required residual budget;
otherwise retain structural resource hypotheses explicitly and derive them
from a separate native producer. This is not yet a global theorem.

3. UNVERIFIED PHI boundary must use a predecessor-indexed represented set S,
not full liveness_transfer (which mentions all alternatives): unique present
selected a, fresh output y, dead a, output retained iff live or halting;
I(S,p) ==> I((S DELETE Var a) UNION kept_y,q). A spilled source is not enough.
Use existing PhiResources balances and NativeTargets partitions first.

4. Exact I(V(L),p) is NOT proposed for arbitrary halting interior/unused-path
OFFSET states. Existing structural resource/demand support interfaces are
safer there. No new residual invariant is defined by this audit. Global
integration must decide whether to restrict exact-live claims to appropriate
nonhalting boundaries or carry explicit retained-name accounting.

## Every optimistic-swap call and observation requirement

There are exactly two call sites in stackPlanGen: regular postprocessing
:337 and prepare_params_plan:601. Regular call disabled when no live output;
inside optimistic_swap_plan it is also disabled by term, D=[], L=[], or
operand_equiv(LAST D,LAST L). Enabled query is stack_get_depth(Var(LAST L))
in the state AFTER emission, consumption, dead-output deletion, BEFORE release.
For entry params it is after param dead-pop, uses dfg_empty and LAST params,
and term reflects first non-param instruction. Setup.native_parameter_depth_exists
is a hit in final prepared state; at the query itself use the earlier exact
param-pop inventory/coverage proof (initial spills empty), not circular reuse
of final swap state.

Setup.optimistic_swap_plan_shielded_bottom_frame suffices for each prefix:
L=[] OR query absent in prefix OR query present in common current suffix.
Suffix_hit_frame requires actual STACK membership; demand_covered_frame
requires every live query in STACK. Inventory's stack-OR-spill coverage is
insufficient. Setup.optimistic_swap_plan_core_inventory preserves inventory,
not residency or common observation. Deep do_swap can change allocator, so
equal emit_ops or equal stack support does not certify whole-state agreement.

## Remaining setup / edge boundaries and minimal next work

Clean_stack_plan: identity for preds not singleton, <=1 predecessor successor,
or missing predecessor lookup. Otherwise pop/mark using predecessor live-out
layout, edge inputs and below_all_live. NULL-input+ok marks all stack slots;
nonempty+ok pops to_cleanup and marks retained; !ok pops MAP Var to_pop.
Spills are not globally released here. Existing Inventory marker-prefix replay
is conditional; an arbitrary-variable residual prefix is NOT covered.

Minimal suggested next bounded obligation (strategist-owned, UNVERIFIED):
inspect whether physical_live plus canonical residual-budget facts can feed
existing native_regular_live_inventory without extra allocator hypotheses.
Then specialize transfer only for non-PHI/non-JMP ordinary branches with the
explicit retention condition; reuse existing Callers demand/freshness results.
Do NOT schedule global induction until OFFSET/halting-retained support and
predecessor-indexed PHI accounting are settled. Query shielding remains an
independent producer even after inventory specialization. Successful join
suffix plus exact target inventory can eliminate non-marker prefixes, but
neither premise may be silently assumed on native paths.

Residual-budget inspection result: reorderSim:155 defines it as
plan_slots_bounded base ps AND spill_alloc_layout_wf alloc spilled AND two
pointwise count bounds. Its canonical theorem :213 explicitly requires
both allocator conditions in addition to distinctness and disjointness.
Thus physical_live alone does NOT discharge that existing interface. The
next proof should either use independently validated native allocator facts,
or request an allocator-independent generalization of the primitive exact
conservation argument. Merely rewrapping canonical will not solve this gap.
