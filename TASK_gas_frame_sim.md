# TASK: Simulate GAS against the running function frame

## Meta
Status: planned
Priority: P1
Created: 2026-11-02
Location: venom/codegen/proofs/gasFrameSimScript.sml

## Theorem Statement (FROZEN)

```sml
Theorem gas_inst_frame_sim:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' r ra rest mem0.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode <> INVOKE /\
    inst.inst_opcode = GAS /\
    (* inst_wf doesn't fix the operand count of the read-only opcodes. *)
    (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) /\
    (* The context-level memory obligations (codegen_memory_obligations). *)
    source_memory_reads_disjoint cp inst vs /\
    context_source_memory_writes_disjoint cp inst vs /\
    (* Return-PC variables are only copied (unit_shape_ok's fn_shape_ok). *)
    opaque_use_ok fn /\ retpc_shape_ok fn /\
    ~is_param_opcode inst.inst_opcode /\
    (* The invariant's region clause for the output planner state. *)
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
    ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    generated_plan_state_wf base ps /\
    codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\
    ~is_terminator inst.inst_opcode /\
    (* Dischargeable at block level from codegen_ready_fn + MEM bb/inst *)
    inst_wf inst /\
    (* The EVM has LOG0 to LOG4 only; inst_wf allows larger topic counts. *)
    (inst.inst_opcode = LOG ==>
     ?tc rest. inst.inst_operands = Lit tc :: rest /\ w2n tc <= 4) /\
    (* ASSERT's failure branch pushes the shared revert label. *)
    (inst.inst_opcode = ASSERT ==> IS_SOME (FLOOKUP lo "revert")) /\
    (* EVM compatibility: DUP depth limit. Dischargeable from evm_compatible
       (LOG tc <= 4, INVOKE args bounded by fn arity). Pipeline obligation. *)
    LENGTH (compute_operands inst) <= 16 /\
    (* Stack depth after input emission >= operand count.
       Dischargeable from plan_state invariant (stack tracks emitted inputs). *)
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (* Every variable input must be owned by the planner: each is either
       shallow enough to duplicate or available from the spill map.
       generated_plan_state_wf is structural and does not imply ownership. *)
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      (?d. stack_get_depth op ps.ps_stack = SOME d /\ d <= 15) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (* Label resolution: all label operands in label_offsets.
       Pipeline obligation from compute_label_offsets over full program. *)
    (!l. MEM (Label l) (compute_operands inst) ==>
         IS_SOME (FLOOKUP lo l)) /\
    (* Labels defined in the instruction's own code resolve to their own
       positions (labels are unique in prog). *)
    (!lbl i. i < LENGTH (execute_plan cp.cp_initial_fmp ops) /\
             EL i (execute_plan cp.cp_initial_fmp ops) = AsmLabel lbl ==>
             ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
                   FLOOKUP o2pc off = SOME (as.as_pc + i)) /\
    (* Cross-layer operand evaluation agreement.  In particular, Label
       operands must agree between vs_labels and generated label offsets. *)
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op (frame_view fn ra vs) =
          operand_val (frame_view fn ra vs) lo op) /\
    (* DFG alias soundness: planner-equivalent operands denote the same
       runtime word under the current value state and label environment.
       This is an explicit pipeline obligation for alias-only reorder steps. *)
    (!op at. operand_equiv dfg op at ==>
             operand_val (frame_view fn ra vs) lo op =
             operand_val (frame_view fn ra vs) lo at) /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
      (compute_operands inst) /\
    (* SSA freshness: output variables not yet in plan state.
       Dischargeable from ssa_form + plan_state invariant
       (plan tracks defined vars, SSA ensures no redefinition). *)
    EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
                      inst.inst_outputs) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
          EVERY (\out. case op of Var x => x <> out | _ => T)
                inst.inst_outputs) /\
    (* PHI soundness: stack-found phi var evaluates to resolved phi value.
       Dischargeable from block entry invariant: predecessor placed the
       resolved PHI value at the expected stack position. *)
    (!dist prev val_op.
       inst.inst_opcode = PHI /\
       stack_get_phi_depth (FILTER is_var_operand inst.inst_operands)
         ps.ps_stack = SOME dist /\
       vs.vs_prev_bb = SOME prev /\
       resolve_phi prev inst.inst_operands = SOME val_op ==>
       operand_val (frame_view fn ra vs) lo (stack_peek dist ps.ps_stack) =
         eval_operand val_op (frame_view fn ra vs)) /\
    (* Spill well-formedness for prefix ops.
       Dischargeable: provable from generate_inst_plan output
       (plan generator produces spill-well-formed prefixes). *)
    prefix_spill_wf cp.cp_initial_fmp lo (FRONT ops) ps /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' /\
          context_spill_step_safe cp vs vs' ==>
      ?n as'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        fn_frame_inv ctx cp lo fn ra rest mem0 ps' vs' as' /\
        as'.as_pc = as.as_pc + LENGTH (execute_plan cp.cp_initial_fmp ops)
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

- `gasFrameSimTheory` builds and saves `gas_inst_frame_sim` without admissions.
- No new admissions, axioms, hypotheses, time-limit increases, or executable changes.
- Existing inherited admissions outside this theorem need not be removed. Do not use an admitted general codegen simulation or opcode-emission simulation as the proof of the GAS case.
- Helpers belong in this new theory unless moving them is necessary; leave frozen upstream theorems unchanged.
- If false, report a concrete counterexample rather than changing the statement.

## Build

`holbuild -j2 build gasFrameSimTheory`

## Background

Venom GAS now pops vs_gas_readings, defaulting to zero at exhaustion. Assembly GAS pops as_gas_readings with the same convention. The running frame invariant embeds their equality. GAS output is ordinary data and may be stored, returned, or used in arithmetic. This theorem has the existing per-instruction frame-simulation premises, specialized to GAS with no additional assumptions.

## Domain Constraints

- Keep the default 2.5-second tactic timeout. Do not wrap proof search in TRY/ORELSE.
- Do not exclude GAS or restrict the uses of its result.
- Do not change source semantics, shared definitions, or frozen upstream theorem statements.
- Do not edit or commit Alan working files as deliverables.

## Available Resources

- `venom/codegen/proofs/genFrameSimScript.sml`: existing jump/frame simulation helpers; the frozen GAS statement was specialized from the parked general instruction statement.
- `venom/codegen/proofs/genBlockSimScript.sml`: instruction-plan decomposition and prefix execution.
- Prove GAS transport through `frame_view` directly. The parked general `frameViewStep` theorem is admitted and is neither imported nor available on this base.
- `venom/codegen/defs/frameRelScript.sml`: fn_frame_inv and frame_view.
- `venom/codegen/defs/codegenRelScript.sml` and `venom/codegen/defs/contextCodegenRelScript.sml`: stack, spill, memory, and shared oracle equality.
- `venom/codegen/proofs/asmFrameScript.sml`: extending executions below the frame.
- `venom/codegen/proofs/prefixSimScript.sml`, `venom/codegen/proofs/mixedPrefixSimScript.sml`, `venom/codegen/proofs/strongPrefixSimScript.sml`.
- `venom/codegen/defs/planExecScript.sml`, `venom/codegen/defs/stackPlanGenScript.sml`, `venom/codegen/defs/stackPlanOpsScript.sml`.
- `venom/defs/venomExecSemanticsScript.sml`, `venom/defs/venomStateScript.sml`: GAS and state definitions.
- `venom/codegen/defs/asmSemScript.sml`: assembly GAS and steps.

## Notes

The statement has an independent audit before the proof run. Its placeholder build may stop in inherited ancestors; if so the owner records that limitation and checks the final proof after those dependencies build.

Current base: current main plus checked spill-planner proof repair and the oracle branch. The initial build on the old instruction-worker base stopped in `doSwapSim$spill_alloc_wf_after_spill` at the default step timeout before this statement parsed. That allocator proof was separately repaired without changing statements or definitions. The GAS statement remains byte-identical; only the missing, admitted general frame-view import was removed. Re-audit against the current planner definitions before starting Alan.
