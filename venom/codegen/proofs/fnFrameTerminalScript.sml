(*
 * Terminal results of an instruction in the block induction behind
 * venomToAsmProps$gen_fn_frame_simulation: an instruction whose step Halts
 * or Aborts, run against frameRel$fn_frame_inv as genFrameSim's lemmas do.
 * The conclusion is venom_asm_terminal_rel, which reads no stack, so the
 * frame's rest needs no lifting beyond the run on top ++ rest.
 *
 * TOP-LEVEL:
 *   gen_inst_halt_frame_sim   — an instruction whose step Halts
 *   gen_inst_abort_frame_sim  — an instruction whose step Aborts
 *)

Theory fnFrameTerminal
Ancestors
  fnFrameTerminalPrep fnFrameTerminalHalt fnFrameTerminalAbort asmIR
  blockSimHelpers opcodeClass
  genFrameSim frameRel contextCodegenRel codegenRel
  unitShapeDefs genBlockSim stackPlanGen stackPlanTypes planExec asmSem
  venomExecSemantics venomState venomInst livenessDefs dfgDefs cfgDefs

(* Used for an instruction whose step Halts (STOP, RETURN, SELFDESTRUCT)
   in the block induction: gen_fn_frame_simulation's Halt clause.  The
   premises are gen_inst_frame_sim's minus those only an OK result uses
   (SSA freshness, PHI soundness), as the
   block induction supplies them for every instruction.  INVOKE's Halt is
   gen_invoke_frame_sim's.

   Why it should hold: gen_inst_halt_sim (genBlockSim) run on the frame's
   own stack against frame_view fn ra vs with the assembly memory, as
   gen_inst_frame_sim does; RETURN reads only bytes outside every spill
   region (source_memory_reads_disjoint), where context_memory_rel makes
   the memories agree; the terminal step on top ++ rest halts with the
   same non-stack fields, and venom_asm_terminal_rel reads no stack.
   Operands are never return-PC variables (opaque_use_ok). *)
Theorem gen_inst_halt_frame_sim:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' r ra rest mem0.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode <> INVOKE /\
    source_memory_reads_disjoint cp inst vs /\
    opaque_use_ok fn /\
    ~is_param_opcode inst.inst_opcode /\
    (* The invariant's region clause for the output planner state, as in
       gen_inst_frame_sim: the prefix's transient spills lie below
       ps'.ps_alloc.sa_next_offset, so this keeps them inside the region
       whose bytes source_memory_reads_disjoint keeps the payload out of.
       fn_frame_inv bounds only ps at entry, which isn't enough
       (fnFrameTerminalPrep$terminal_escape_halt_counterexample). *)
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
    ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    generated_plan_state_wf base ps /\
    codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\
    inst_wf inst /\
    LENGTH (compute_operands inst) <= 16 /\
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      (?d. stack_get_depth op ps.ps_stack = SOME d /\ d <= 15) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (!l. MEM (Label l) (compute_operands inst) ==>
         IS_SOME (FLOOKUP lo l)) /\
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op (frame_view fn ra vs) =
          operand_val (frame_view fn ra vs) lo op) /\
    (!op at. MEM op (compute_operands inst) /\
             (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
              MEM at (compute_operands inst)) /\
             operand_equiv dfg op at ==>
             operand_val (frame_view fn ra vs) lo op =
             operand_val (frame_view fn ra vs) lo at) /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
      (compute_operands inst) /\
    prefix_spill_wf cp.cp_initial_fmp lo (FRONT ops) ps /\
    (!off. MEM (SORestore off) ops ==> off < dimword(:256)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) ==>
    !vs'. step_inst fuel ctx inst vs = Halt vs' ==>
      ?n as'.
        asm_steps lo o2pc prog n as = AsmHalt as' /\
        venom_asm_terminal_rel vs' as'
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  gen_tac >> disch_tac >>
  SUBGOAL_THEN ``inst.inst_opcode = STOP \/ inst.inst_opcode = RETURN \/
    inst.inst_opcode = SELFDESTRUCT`` assume_tac
  >- (drule step_inst_halt_opcodes >> strip_tac >> simp[] >>
      qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
      gvs[generate_inst_plan_def, is_pre_codegen_opcode_def]) >>
  drule_all frame_terminal_prefix_setup >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  qpat_x_assum `_ \/ _ \/ _` strip_assume_tac
  >- suspend "stop"
  >- suspend "return"
  >> suspend "selfdestruct"
QED

Resume gen_inst_halt_frame_sim[stop]:
  `vs' = halt_state (vs with vs_returndata := [])` by
    (qpat_x_assum `step_inst _ _ _ _ = Halt _` mp_tac >>
     simp[Once step_inst_def, step_inst_base_def]) >>
  `name = "STOP"` by fs[venom_to_evm_name_def] >>
  `asm_block_at prog mid.as_pc [AsmOp "STOP"]` by metis_tac[] >>
  drule_all terminal_stop_step >>
  disch_then (qspecl_then [`lo`, `o2pc`] strip_assume_tac) >>
  qexistsl_tac [`n + 1`, `st'`] >> conj_tac
  >- (irule asm_steps_compose_halt >> qexists `mid` >> gvs[]) >>
  gvs[]
QED

Resume gen_inst_halt_frame_sim[return]:
  qpat_x_assum `step_inst _ _ _ _ = Halt _` mp_tac >>
  simp[Once step_inst_def, step_inst_base_def, AllCaseEqs()] >>
  strip_tac >>
  `inst.inst_operands = [off_op; sz_op]` by metis_tac[] >>
  `name = "RETURN"` by fs[venom_to_evm_name_def] >>
  `asm_block_at prog mid.as_pc [AsmOp "RETURN"]` by metis_tac[] >>
  `mid.as_stack = off :: sz :: DROP 2 mid.as_stack` by
    (qpat_x_assum `!values. eval_operands _ _ = _ ==> _` mp_tac >>
     simp[compute_operands_def, python_stack_operands_def,
       ir_specific_operand_order_def, eval_operands_def]) >>
  `MEM (w2n off, w2n sz) (source_memory_read_ranges inst vs)` by
    simp[source_memory_read_ranges_def, memory_range_of_operands_def] >>
  drule_all context_source_payload_agree >> disch_tac >>
  drule_all terminal_return_payload_step >>
  disch_then (qspecl_then [`o2pc`, `lo`] strip_assume_tac) >>
  qexistsl_tac [`n + 1`, `st'`] >> conj_tac
  >- (irule asm_steps_compose_halt >> qexists `mid` >> gvs[]) >>
  gvs[]
QED

Resume gen_inst_halt_frame_sim[selfdestruct]:
  qpat_x_assum `step_inst _ _ _ _ = Halt _` mp_tac >>
  simp[Once step_inst_def, step_inst_base_def, AllCaseEqs()] >>
  strip_tac
  (* the static guard's other disjunct: the operand evaluates, so
     eval_operands can't be NONE *)
  >~ [`eval_operands _ _ = NONE`] >- gvs[eval_operands_def] >>
  `name = "SELFDESTRUCT"` by fs[venom_to_evm_name_def] >>
  `asm_block_at prog mid.as_pc [AsmOp "SELFDESTRUCT"]` by metis_tac[] >>
  `mid.as_stack = addr :: DROP 1 mid.as_stack` by
    (qpat_x_assum `!values. eval_operands _ _ = _ ==> _` mp_tac >>
     simp[compute_operands_def, python_stack_operands_def,
       ir_specific_operand_order_def, eval_operands_def]) >>
  drule_all terminal_selfdestruct_rel_step >>
  disch_then (qspecl_then [`o2pc`, `lo`] strip_assume_tac) >>
  qexistsl_tac [`n + 1`, `st'`] >> conj_tac
  >- (irule asm_steps_compose_halt >> qexists `mid` >> gvs[]) >>
  gvs[]
QED

Finalise gen_inst_halt_frame_sim

(* Used for an instruction whose step Aborts (REVERT, ASSERT,
   ASSERT_UNREACHABLE, INVALID, a faulting RETURNDATACOPY or CREATE) in
   the block induction: gen_fn_frame_simulation's Abort clause.  Premises
   as gen_inst_halt_frame_sim's, plus genBlockSim$gen_inst_abort_sim's
   placement of the shared revert postamble for ASSERT
   (fnPlanPlace$revert_postamble_placed) and the own-label resolution
   ASSERT_UNREACHABLE's fresh label needs (fnPlanPlace$dfs_block_code_placed).
   A revert forwarding's RETURNDATACOPY and REVERT are exempt from the
   memory obligations; they are revert_forward_frame_sim's.

   Why it should hold: gen_inst_abort_sim lifted as in
   gen_inst_halt_frame_sim; spill offsets are disjoint by
   generated_plan_state_wf; REVERT's payload is outside every spill
   region. *)
Theorem gen_inst_abort_frame_sim:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' r ra rest mem0.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode <> INVOKE /\
    ~vs.vs_call_ctx.cc_static /\
    source_memory_reads_disjoint cp inst vs /\
    opaque_use_ok fn /\
    ~is_param_opcode inst.inst_opcode /\
    (* The invariant's region clause for the output planner state, as in
       gen_inst_frame_sim: the prefix's transient spills lie below
       ps'.ps_alloc.sa_next_offset, so this keeps them inside the region
       whose bytes source_memory_reads_disjoint keeps the payload out of.
       fn_frame_inv bounds only ps at entry, which isn't enough
       (fnFrameTerminalPrep$terminal_escape_halt_counterexample). *)
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
    ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    generated_plan_state_wf base ps /\
    codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\
    inst_wf inst /\
    (inst.inst_opcode = ASSERT ==>
     ?off pc. FLOOKUP lo "revert" = SOME off /\ off < dimword (:256) /\
              FLOOKUP o2pc off = SOME pc /\
              asm_block_at prog pc
                (execute_plan cp.cp_initial_fmp revert_postamble)) /\
    LENGTH (compute_operands inst) <= 16 /\
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      (?d. stack_get_depth op ps.ps_stack = SOME d /\ d <= 15) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (!l. MEM (Label l) (compute_operands inst) ==>
         IS_SOME (FLOOKUP lo l)) /\
    (!lbl i. i < LENGTH (execute_plan cp.cp_initial_fmp ops) /\
             EL i (execute_plan cp.cp_initial_fmp ops) = AsmLabel lbl ==>
             ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
                   FLOOKUP o2pc off = SOME (as.as_pc + i)) /\
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op (frame_view fn ra vs) =
          operand_val (frame_view fn ra vs) lo op) /\
    (!op at. MEM op (compute_operands inst) /\
             (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
              MEM at (compute_operands inst)) /\
             operand_equiv dfg op at ==>
             operand_val (frame_view fn ra vs) lo op =
             operand_val (frame_view fn ra vs) lo at) /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
      (compute_operands inst) /\
    prefix_spill_wf cp.cp_initial_fmp lo (FRONT ops) ps /\
    (!off. MEM (SORestore off) ops ==> off < dimword(:256)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps =
      SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) ==>
    !a vs'. step_inst fuel ctx inst vs = Abort a vs' ==>
      ?n as'.
        ((a = Revert_abort /\ asm_steps lo o2pc prog n as = AsmRevert as') \/
         (a = ExHalt_abort /\ asm_steps lo o2pc prog n as = AsmFault as')) /\
        venom_asm_terminal_rel vs' as'
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = REVERT`
  >- (drule_all gen_inst_revert_frame_sim >>
      disch_then (qspec_then `o2pc` strip_assume_tac) >>
      qexistsl_tac [`n`, `out`] >> simp[]) >>
  Cases_on `inst.inst_opcode = ASSERT`
  >- (qpat_x_assum `inst.inst_opcode = ASSERT ==> _` drule >> disch_tac >>
      drule_all gen_inst_assert_frame_sim >> strip_tac >>
      qexistsl_tac [`n`, `out`] >> simp[]) >>
  Cases_on `inst.inst_opcode = ASSERT_UNREACHABLE`
  >- (drule_all gen_inst_assert_unreachable_frame_sim >> strip_tac >>
      qexistsl_tac [`n`, `out`] >> simp[]) >>
  Cases_on `inst.inst_opcode = INVALID`
  >- (drule_all gen_inst_invalid_frame_sim >>
      disch_then (qspec_then `o2pc` strip_assume_tac) >>
      qexistsl_tac [`n`, `out`] >> simp[]) >>
  `MEM inst.inst_opcode [CREATE; CREATE2; RETURNDATACOPY]` by
    (drule step_inst_abort_opcodes >> simp[] >> metis_tac[]) >>
  drule_all gen_inst_ext_fault_frame_sim >>
  disch_then (qspec_then `o2pc` strip_assume_tac) >>
  qexistsl_tac [`n`, `out`] >> simp[]
QED
