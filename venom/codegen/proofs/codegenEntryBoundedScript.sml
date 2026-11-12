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
  passSimulationDefs frameRel venomInst codegenRel venomRunBounded
  contextCodegenRelProps

(* The assembly state as starts codegen's program prog for the Venom
   state vs at the context's entry: at PC 0 with an empty stack, memory
   and shared state related, and vs a fresh, non-static entry state whose
   labels are prog's offsets. *)
Definition codegen_asm_entry_rel_def:
  codegen_asm_entry_rel cp prog vs as <=>
    as.as_pc = 0 /\ as.as_stack = [] /\
    ~vs.vs_halted /\ ~vs.vs_call_ctx.cc_static /\
    vs.vs_vars = FEMPTY /\ vs.vs_params = [] /\
    n2w cp.cp_initial_fmp = vs.vs_initial_fmp /\
    (!l. FLOOKUP vs.vs_labels l =
         OPTION_MAP n2w (FLOOKUP (SND (compute_label_offsets prog)) l)) /\
    context_memory_rel cp vs.vs_memory as.as_memory /\
    shared_state_rel vs as
End

Theorem codegen_asm_entry_fn_state_rel:
  !cp prog vs as fe lbl ra.
    codegen_asm_entry_rel cp prog vs as /\
    get_params (HD fe.fn_blocks).bb_instructions = [] /\
    fn_entry_label fe = SOME lbl ==>
    fn_entry_state_rel cp fe
      (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)
      as ra []
Proof
  rw[codegen_asm_entry_rel_def] >>
  gvs[fn_entry_label_def, entry_block_def] >>
  gvs[fn_entry_state_rel_def, fn_has_retpc_def,
      shared_state_rel_def, venom_asm_terminal_rel_def]
QED

Theorem initial_ctx_codegen_asm_entry_rel:
  !cp prog ctx vs es.
    initial_ctx_rel cp prog ctx vs es ==>
    codegen_asm_entry_rel cp prog vs (entry_asm_state vs es)
Proof
  rw[initial_ctx_rel_def] >>
  gvs[initial_state_rel_def, initial_codegen_state_rel_def,
      stack_params_rel_def, msg_ctx_rel_def] >>
  simp[codegen_asm_entry_rel_def, entry_asm_state_def,
       shared_state_rel_def, venom_asm_terminal_rel_def] >>
  Cases_on `ctxt.stack` >> gvs[] >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[]
QED

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
Theorem codegen_entry_asm_bounded_state:
  !rpolicy unit cp prog fuel M.
    generate_context_plan unit.cu_context = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\
    unit_shape_ok unit
    ==>
    ?N H. !Inv vs as.
      codegen_context_obligations Inv unit.cu_context cp /\
      codegen_reachability_package Inv unit.cu_context vs /\
      codegen_asm_entry_rel cp prog vs as /\
      terminates (run_context fuel unit.cu_context vs) /\
      (!fn inst s. Inv unit.cu_context fn inst s /\ ~in_revert_forward fn s ==>
         EVERY (\(off,len). len = 0 \/ off + len <= M) (inst_mem_ranges inst s)) /\
      (!fn inst s. Inv unit.cu_context fn inst s ==> inst_create_size_ok inst s)
      ==>
      asm_run_bounded (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
        prog H N as
Proof
  cheat
QED

(* The bound from the codegen frame's initial context. *)
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
         EVERY (\(off,len). len = 0 \/ off + len <= M) (inst_mem_ranges inst s)) /\
      (!fn inst s. Inv unit.cu_context fn inst s ==> inst_create_size_ok inst s)
      ==>
      asm_run_bounded (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
        prog H N (entry_asm_state vs es)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all codegen_entry_asm_bounded_state >>
  disch_then (qspecl_then [`fuel`, `M`] strip_assume_tac) >>
  qexistsl_tac [`N`, `H`] >> rpt strip_tac >>
  drule initial_ctx_codegen_asm_entry_rel >> strip_tac >>
  first_x_assum irule >> qexistsl_tac [`Inv`, `vs`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* Two memory invariants of a run hold together, with the conjunction of
   their reachability witnesses. *)
Theorem mem_inv_conj:
  mem_inv M1 ctx vs /\ mem_inv M2 ctx vs ==>
  mem_inv (\c f i s. M1 c f i s /\ M2 c f i s) ctx vs
Proof
  simp[mem_inv_def] >>
  disch_then (CONJUNCTS_THEN2 (qx_choose_then `I1` strip_assume_tac)
                               (qx_choose_then `I2` strip_assume_tac)) >>
  qexists_tac `\c f i s. I1 c f i s /\ I2 c f i s` >>
  simp[codegen_reachability_package_conj]
QED

(* The bound from the Venom run's resource bound: venom_run_bounded's
   memory invariant has its own reachability witness, and the conjunction
   of it with Inv carries both the obligations and the memory bound. *)
Theorem codegen_entry_asm_bounded_run:
  !rpolicy unit cp prog fuel M.
    generate_context_plan unit.cu_context = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\
    unit_shape_ok unit
    ==>
    ?N H. !Inv vs as.
      codegen_context_obligations Inv unit.cu_context cp /\
      codegen_reachability_package Inv unit.cu_context vs /\
      codegen_asm_entry_rel cp prog vs as /\
      venom_run_bounded fuel M unit.cu_context vs /\
      mem_inv (\ctx fn inst s. inst_create_size_ok inst s) unit.cu_context vs
      ==>
      asm_run_bounded (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
        prog H N as
Proof
  rpt gen_tac >> strip_tac >>
  drule_all codegen_entry_asm_bounded_state >>
  disch_then (qspecl_then [`fuel`, `M`] strip_assume_tac) >>
  qexistsl_tac [`N`, `H`] >> rpt gen_tac >> strip_tac >>
  fs[venom_run_bounded_def] >>
  qpat_x_assum `mem_inv (\ctx fn inst s. in_revert_forward fn s \/ _) _ _`
    (fn th1 =>
     qpat_x_assum `mem_inv (\ctx fn inst s. inst_create_size_ok inst s) _ _`
       (fn th2 => mp_tac (MATCH_MP mem_inv_conj (CONJ th1 th2)))) >>
  disch_then (qx_choose_then `MemInv` strip_assume_tac o
              REWRITE_RULE [mem_inv_def]) >>
  qpat_x_assum `!Inv vs as. _` (qspecl_then
    [`\c f i s. Inv c f i s /\ MemInv c f i s`, `vs`, `as`] mp_tac) >>
  simp[] >> disch_then irule >>
  gvs[codegen_context_obligations_conj, codegen_reachability_package_conj] >>
  metis_tac[]
QED
