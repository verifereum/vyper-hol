# Physical realization interface audit (C3.validity.interface)

Source audit only; no new theorem, executor, or fixture is asserted here.
The emission target rebuilt successfully on 2026-11-10 (tool m19076).

## Consumer, not a stronger surrogate

`singleton_block_equal_cleanup_endpoints` (EntryProduction:3129) assumes
identical cleanup code AND cleanup endpoints identical modulo the three
cleanup fields. It cannot cancel different cleanup prefixes of equal block
code. `lineage_singleton_block_physical_transfer` (Lineage:5592) chooses a
NONE-height replay and returns a common suffix with live-out-free prefixes;
it does not characterize another arbitrary override producing that code.
The missing consumer is precisely that latter endpoint, not another selected
replay. Inputs can have different-length irrelevant bottom prefixes.

## Existing physical relation and execution

codegenRel:48,63,318: `plan_stack_rel lo vs stk concrete` relates LAST-as-top
planner stacks to HD-as-top word stacks, with equal lengths. Marker cells
are unconstrained values, not deleted cells. `plan_spill_rel` requires for
EVERY mapped nonmarker operand an evaluated value equal to the 32-byte
memory read at its offset. Equal spill maps alone do not establish this
predicate or specify a common initial physical memory. `venom_asm_rel` also
requires memory agreement outside the allocation interval and shared source
and assembly environments. It is not injective in source variable names.
Different variables and arithmetic expressions can evaluate to the same word.

planExec:46-72 is a compiler to assembly, NOT a partial token executor.
`SOPush (Var _)` and `SOPoke` compile to nothing. Spill/restore compile to
PUSH-address plus MSTORE/MLOAD. Thus a literal stack_op cursor and an assembly
PC are different indices, and SOPoke must not become a physical write.
Actual JUMP/INVOKE assembly control flow is not a straight-line local trace.

## Exact interface inventory

In this table R means `venom_asm_rel lo ps vs st`, P means
`asm_block_at prog st.as_pc (execute_plan initial_fmp ops)`, A means every
SOSpill/SORestore offset in ops is < dimword(:256), L means
`spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled`. These are abbreviations
for auditing only. Primitive conclusions are existence of st' executing
LENGTH(execute_plan initial_fmp ops) assembly steps, preserving R with the
result planner state, and advancing PC by that length unless noted.

* do_swap: doSwapSim.do_swap_venom_asm_rel_numeric:5108 requires
  `do_swap dist ps=(ops,ps')`, dist < LENGTH ps.ps_stack, L, A, R, P.
  The small version:485 additionally dist<=16 but does not need L/A.
  The big version:4922 instead bounds the temporary spill_alloc_n addresses.
  Gap: no R/P/numeric-address premise is in the singleton consumer.
* do_dup: doSwapSim.do_dup_venom_asm_rel_numeric:4835 has exactly the
  analogous premises with do_dup. It does NOT require ALL_DISTINCT or a
  special dist=17 shape. Do not accidentally use the stronger caller lemma.
  Gap: same as swap; lookup distance bounds are local proof obligations,
  not a consequence of a block returning SOME alone.
* do_restore: generatedPrefixSim.do_restore_venom_asm_rel_numeric:9 requires
  the do_restore equation, A, R, P (no L premise). The map's stored word
  comes from plan_spill_rel inside R, NOT from domain membership alone.
* reduce_depth_plan: reorderSim.reduce_depth_plan_venom_asm_rel_addresses:3056
  requires residual_budget_wf base pending ps, target_len<=LENGTH ps.ps_stack,
  target_len<=16, its defining equation, A, R, P. residual_budget_wf includes
  slots boundedness and L plus per-operand stack multiplicity constraints.
* reorder_one: reorderSim.reorder_one_venom_asm_rel_residual_addresses:3358
  additionally requires pending_inventory_wf, idx<LENGTH pending, MEM op
  pending, pending length<=stack length and <=16, marker exclusion for op
  AND all its operand_equiv aliases, and alias soundness
  `operand_equiv dfg op1 at ==> operand_val vs lo op1=operand_val vs lo at`
  for pending op1 and at in the input stack/spills. Returns both budgets.
  Gap: syntactic availability is not this semantic alias premise.
* clean_stack_plan: cleanOpsSim.clean_ops_sim:646 requires R,
  LENGTH ps.ps_stack<=17, the cleanup equation and P. It returns some n
  and the related endpoint, with PC advance equal to emitted assembly length.
  The general-depth interface fnFrameCleanStack.clean_stack_plan_frame_sim:271
  requires generated_plan_state_wf_marked, fn_frame_inv, region membership,
  lower/upper allocation bounds, A, P and computed lo/o2pc. It preserves the
  frame invariant and marked wellformedness. Neither <=17 nor the frame
  context is supplied by our arbitrary-prefix consumer. Marking is silent
  physical observation loss, not stack deletion.
* ASSIGN: deepInstSim.assign_postfix_sim_numeric:426 requires L, the exact
  popmany and optimistic-swap stage equations, A, R, P; returns a relation
  after release_dead_spills. Full assign_inst_ok_sim_marked:481 also requires
  generated_plan_state_wf_marked, ready/membership/inst_wf, input availability,
  operand count<=16 and post-input stack length, label resolution, alias
  soundness, output freshness, numeric addresses, source step and memory
  safety (same general signature as initial_fmp below). Emission.generate_
  emit_ops_assign_emission:645 proves the emit stage is empty, not the
  whole instruction: literal/label input pushes may still occur.
* PHI: deepInstSim.phi_dup_rename_sim_numeric:1126 requires a valid dup
  distance, L, A, R, P for ds++tail, nonmarker selected operand with
  operand_val=SOME v, and output absent from both stack and spill domain.
  Returns R for `stack_poke 0 (Var out)` against `update_var out v vs`.
  Full phi_inst_ok_sim_marked:1169 additionally needs the selected cell's
  value to equal resolve_phi on vs_prev_bb. No injective alias conclusion.
* OFFSET: strongPrefixSim.simple_op_push_ofst:351 requires
  FLOOKUP lo lbl=SOME off, R, and placement of [AsmPushOfst lbl delta].
  It pushes Lit(n2w(off+delta)) and advances one instruction. Gap: the
  task has no lo; arbitrary labels do not have a supplied label environment.
* BUMP: emitSim.bump_emit_sim_from_stack:435 requires R, actual physical
  stack `sz::base_val::rest`, distinct output names, both names absent from
  input stack/spills, and placement of bump_emit_ops. Executes TWO steps,
  yielding next_out=base_val+sz and ptr_out=base_val. Only next_out has a
  genuine ADD producer; ptr_out aliases the retained base value.
  Full deepInstSim.bump_inst_ok_sim_marked:1659 has the general source-step
  obligations, not a source-free realization theorem.
* INITIAL_FMP: strongPrefixSim.initial_fmp_push_venom_asm_rel:307 requires
  R and placement of the encoded push; pushes Lit(n2w initial_fmp).
  Full deepInstSim.initial_fmp_inst_ok_sim_marked:1421-1529 requires ready,
  marked WF, inst membership/WF, variable availability, bounded input arity,
  adequate post-input length, labels and local label PCs, evaluation and DFG
  alias soundness, marker/alias exclusion, output freshness, A, R, P,
  n2w initial_fmp=vs_initial_fmp, generate_inst_plan=SOME, and a successful
  source step with inst_memory_safe. Gap: these semantic hypotheses are
  absent from the theorem being proved; none follows from code equality.
* INVOKE: fnFrameBoundary.gen_invoke_frame_sim:163 requires a context plan,
  compiled assembly, unit_shape_ok, codegen_context_obligations Inv,
  reachability_closed Inv, active source instruction, nonstatic call state,
  callee return-PC facts and callee simulation at this fuel, frame/region
  invariants, in addition to local planner hypotheses. Not reusable as
  a context-free token realization theorem. Emission:671 gives four anchors
  [push return label; push callee label; JUMP; return label] and increments
  label counter. It does not execute the callee or produce returned tokens.

## Checked suppliers versus explicit gaps

Lineage.lineage_state_successful_run_available:1165 quantifies arbitrary h
and promised and supplies ordinary input/live-out stack-or-spill membership
for successful overridden runs. It is applicable to the consumer (DFS can
be converted to lineage). It does not supply values, memory initialization,
physical validity, numeric address bounds, or a <=17 stack bound.
Lineage.lineage_state_unit_resources:4533, successful_exit_unit_resources:4550
and prefix_unit_resources:4567 supply per-variable count+spill-indicator<=1
(including arbitrary successful overrides). They are not bounds on marker
multiplicity, literal multiplicity, or total physical height. Do not infer
ALL_DISTINCT of the whole stack from them.
Inventory.emit_input_plan_marker_core_budget:2302 transports a GIVEN
residual_budget_wf on the core under a marker bottom prefix. It does not
establish the physical relation or initial memory, and its hypothesis
cannot be silently strengthened to a budget on the full marker stack.

Observation.observe_mark_dead_stack:10 preserves positional observations
when the observation set excludes markers and retained cells. It is neither
an executor nor an inverse for loss of observation.
PhiTemporal.phi_origin_schedule_trace:558 and schedule_replay:589 require
phi_origin_schedule_ready and two projections of a shared cell list.
Replay also requires equal allocations. They supply selected aligned PHI
traces, not a shared cell list extracted from arbitrary equal emitted code.
Using that shared list as an arbitrary-run premise would beg correspondence.

## Proposed boundary, fully quantified, for strategist review ONLY

Use mathematical metavariables `TExec B k ops S M` (partial, unbounded token
stack/memory execution with operation-position cursor) and `Realizes Q rho
ps S M` (alias-aware source observation relation). Neither is defined yet.
S is LAST-as-top to avoid hidden reversals; M is a partial nat->token map.
`Initialized rho ps M` must mean explicitly:
  forall op off. FLOOKUP ps.ps_spilled op=SOME off /\ op<>dead_stack_marker
    ==> exists t. FLOOKUP M off=SOME t /\ rho op=SOME t.
It must also assert compatibility of simultaneous spill bindings. Merely
FDOM coverage is insufficient. `Realizes` must relate every physical stack
cell (including unobserved marker cells), not filter cells out.

The candidate realization (not correspondence) statement is:
  forall lv dfg cfg fn bb p q hp bp hq bq ops ap aq Q
         B k Sp Sq M rhop rhoq.
    ReadyAndStageInvariants(lv,dfg,cfg,fn,bb,p,q) /\
    generate_block_plan lv dfg cfg fn bb (override p hp bp)=SOME(ops,ap) /\
    generate_block_plan lv dfg cfg fn bb (override q hq bq)=SOME(ops,aq) /\
    p.ps_spilled=q.ps_spilled /\
    Initialized rhop p M /\ Initialized rhoq q M /\
    Realizes Q rhop p Sp M /\ Realizes Q rhoq q Sq M
    ==> exists Sp' Sq' Mp' Mq' rhop' rhoq'.
      TExec B k ops Sp M=SOME(Sp',Mp',k+LENGTH ops) /\
      TExec B k ops Sq M=SOME(Sq',Mq',k+LENGTH ops) /\
      Realizes Q rhop' ap Sp' Mp' /\ Realizes Q rhoq' aq Sq' Mq'.
Here override changes only height/promised. B must specify source-free
signatures for emissions, including call-return abstract effects; it cannot
smuggle source instruction indices into equal code. ReadyAndStageInvariants
is an EXPLICIT UNRESOLVED GAP, not a proposed extra task hypothesis: its
needed content is the local inventory/height/layout conditions audited above,
without numeric word bounds if the executor is unbounded. The two arbitrary
overrides are not yet proved to satisfy a sufficient such invariant.

This conditional boundary deliberately does NOT conclude Sp'=Sq' or Mp'=Mq'.
The consumer's Sp and Sq can have unequal irrelevant bottom prefixes, so
common code determinism cannot give that equality. A separate frame/cell
correspondence theorem must say what common suffix or observations survive
and account for ASSIGN, PHI and BUMP aliases. Even common initial memory does
not make intermediate/final memories equal when physical stacks differ.
No injective word interpretation can repair this: there are finitely many
words and aliases deliberately identify syntactically different names.

Review decision requested: select the precise alias-aware observation and
source-free INVOKE emission signature, and validate a consumer-compatible
frame/validity boundary before authorizing any interpreter implementation.
Existing numeric simulations are useful local mathematical evidence, not a
direct discharge of arbitrary-history realization or correspondence.
