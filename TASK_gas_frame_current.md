# TASK: Finish the current GAS frame simulation

## Meta
Status: planned
Priority: P1
Created: 2026-11-04
Location: venom/codegen/proofs/

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
    opaque_use_ok fn /\
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
    (!op at. MEM op (compute_operands inst) /\
             (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
              MEM at (compute_operands inst)) /\
             operand_equiv dfg op at ==>
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
    !vs'. step_inst fuel ctx inst vs = OK vs' ==>
      ?n as'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        fn_frame_inv ctx cp lo fn ra rest mem0 ps' vs' as' /\
        as'.as_pc = as.as_pc + LENGTH (execute_plan cp.cp_initial_fmp ops)
```

Do not modify this statement. Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `gasFrameSimTheory` builds with the frozen theorem proved and its existing GAS_FRAME_SIM_AUDIT gate passing.
2. No new admissions, axioms, executable definitions or strengthened hypotheses. Retain all existing proof text unless replacing it with a checked proof.
3. Reuse existing SSA/frame facts; do not duplicate even a local theorem already present elsewhere. Existing parent theorem statements and definitions are frozen.

## Build

```sh
holbuild -j2 build gasFrameSimTheory
```

## Background

The existing GAS leaf is being reconciled with the current per-instruction frame interface. The full-oracle semantics and relations are already present on this branch. The leaf has no return-PC shape requirement or extra readings-equality hypothesis. Its frame and memory postconditions are unchanged.

## Domain Constraints

- Keep the frozen root, all definitions and all other existing theorem statements unchanged. Internal proof bodies may change; new helper theorems may be added only after searching for existing equivalents.
- Do not change holproject.toml, tactic timeouts, semantics or planner definitions. Do not add imports of admitted correctness theorems to discharge this root.
- Do not wrap proof search in TRY/ORELSE. Keep the default tactic timeout.
- Reuse the existing frameViewFacts/frameViewScalar/genFrameSim facts rather than restoring removed duplicate SSA or frame helpers.
- Do not modify another worktree or push any branch.

## Available Resources

| Resource | Location | Description |
|---|---|---|
| Frozen root and current proof | venom/codegen/proofs/gasFrameSimScript.sml | Existing GAS plan and frame proof |
| Shared frame results | venom/codegen/proofs/genFrameSimScript.sml | Exported context_venom_asm_rel_local and frame_local_result |
| Scalar state transport | venom/codegen/proofs/frameViewScalarScript.sml | New checked exec_gas_frame_view and unchanged environment_base_frame_view |
| SSA and frame view facts | venom/codegen/proofs/frameViewFactsScript.sml | noncopy_output_not_retpc, frame_view_update_var, frame_view_gas_readings |
| Frame invariant | venom/codegen/defs/frameRelScript.sml | fn_frame_inv and fn_frame_inv_gas_readings |
| Assembly frame transport | venom/codegen/proofs/asmFrameScript.sml | asm_steps_frame |
| GAS semantics | venom/defs/venomExecSemanticsScript.sml | exec_gas and step_inst |
| Assembly relation | venom/codegen/defs/codegenRelScript.sml | GAS readings agreement in venom_asm_rel |
| Context relation | venom/codegen/defs/contextCodegenRelScript.sml | Context memory and GAS readings agreement |

## Notes

Independent source audit found the frozen root PROVABLE on the full-oracle substrate. The latest owner check built frameViewFactsTheory, frameViewScalarTheory and genFrameSimTheory. gasFrameSimTheory currently fails in the preceding gas_frame_lift proof at end-of-proof with existential instantiation goals. Its proof is retained. Consequently the revised frozen root has not yet been reached by the parser in this reconciliation build. Its original proof is retained as well. No statement or definition change is authorized to fix the remaining proof.
