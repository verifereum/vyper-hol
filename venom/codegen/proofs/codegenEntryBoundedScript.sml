(*
 * The Venom-to-assembly half of codegen_correct, with resource bounds,
 * for the sufficient-gas theorem S7g: a context run that terminates
 * within fuel, with memory accesses below M, is simulated by an
 * assembly run of bounded length whose steps before a RETURNDATACOPY
 * touch memory only below a bound.
 *
 * TOP-LEVEL:
 *   codegen_entry_asm_bounded - asm_run_bounded from entry_asm_state
 *)

Theory codegenEntryBounded
Ancestors
  codegenEntrySim asmRunBounded codegenEntryRel contextCodegenRel unitMemInv
  codegen asmSem venomExecSemantics venomState unitShapeDefs
  passSimulationDefs

(* Why it should hold.  codegen_entry_asm_sim is proved by
   gen_fn_simulation (venomToAsmProps), an induction over fuel through
   gen_fn_sim_at (fnSimSpec) and the block and instruction step lemmas
   (fnBlockBody*, fnFrameDeep*, deepInstSim); its ?n are not bounded and
   its intermediate assembly states are hidden, so the bound has to be
   carried by that induction rather than derived from its result.
   - Steps: the fnFrameDeep* wrappers already conclude
     as'.as_pc = as.as_pc + LENGTH (execute_plan ...) and pick n as that
     length plus a small constant for terminators, postambles and
     INVOKE.  Venom fuel counts blocks per function and INVOKE runs the
     callee with the block's fuel, and the reachable call graph is acyclic
     (codegen_context_obligations), so a bound over fuel, the plan's code
     lengths and the call depth is static.
   - Memory: stack plans (execute_plan of stack ops) touch memory only in
     SOSpill/SORestore (PUSH off; MSTORE/MLOAD), whose offsets
     plan_slots_bounded (fnBlockBodySteps) puts below the region's spill
     end; the one emitted Venom opcode has the instruction's operand
     values on top of the stack (regular_inst_ok_sim_marked,
     frame_terminal_prefix_setup_marked, regular_abort_frame_prefix_deep
     expose that state), so its ranges are inst_mem_ranges, below M by
     the hypothesis.  In a revert forwarding (in_revert_forward,
     revert_forward_pair) body_inv_static excludes spills, so its first
     memory access is the RETURNDATACOPY, where asm_run_bounded stops.
   - unit_shape_ok's inst_shape_ok excludes DELEGATECALL, CREATE, CREATE2
     and SELFDESTRUCT from the unit, so no plan emits them.
   N and H depend only on the program, fuel and M.  M bounds the Venom
   run's own memory accesses (inst_mem_ranges) outside a revert
   forwarding (in_revert_forward), whose first memory access is its
   RETURNDATACOPY; H also covers the spill slots and the other static
   offsets the generated code adds. *)
Theorem codegen_entry_asm_bounded:
  !rpolicy unit cp prog fuel M.
    generate_context_plan unit.cu_context = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\
    unit_shape_ok unit
    ==>
    ?N H. !Inv vs es.
      codegen_context_obligations Inv unit.cu_context cp /\
      codegen_reachability_package Inv unit.cu_context vs /\
      initial_ctx_rel cp prog unit.cu_context vs es /\
      terminates (run_context fuel unit.cu_context vs) /\
      (!fn inst s. Inv unit.cu_context fn inst s /\ ~in_revert_forward fn s ==>
         EVERY (\(off,len). len = 0 \/ off + len <= M) (inst_mem_ranges inst s))
      ==>
      asm_run_bounded (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
        prog H N (entry_asm_state vs es)
Proof
  cheat
QED
