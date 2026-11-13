Theory symInstDispatch
Ancestors
  symInstPieces symZeroInstSim symEmitSim codegenSymRel stackPlanGen
  fnPlanLineageInventory venomWf asmIR venomInst

Theorem istore_operand_shape[local]:
  inst.inst_opcode = ISTORE /\ inst_wf inst ==>
  ?dst value. inst.inst_operands = [dst; value] /\
    compute_operands inst = [dst; value]
Proof
  strip_tac >> gvs[inst_wf_def, listTheory.LENGTH_EQ_NUM_compute] >>
  simp[compute_operands_def, python_stack_operands_def, ir_specific_operand_order_def]
QED

Theorem assertion_operand_shape[local]:
  (inst.inst_opcode = ASSERT \/ inst.inst_opcode = ASSERT_UNREACHABLE) /\
  inst_wf inst ==>
  ?cond. inst.inst_operands = [cond] /\ compute_operands inst = [cond]
Proof
  strip_tac >> gvs[inst_wf_def, listTheory.LENGTH_EQ_NUM_compute] >>
  simp[compute_operands_def, python_stack_operands_def, ir_specific_operand_order_def]
QED

Theorem sym_non_bump_inst_symbolic_run:
  !fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' r ra rest mem0
   env ret srest labs0 ss.
    lo = SND (compute_label_offsets prog) /\
    o2pc = build_offset_to_pc prog /\
    inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS /\
    (ef_read0 inst.inst_opcode ==> inst.inst_operands = []) /\
    source_memory_reads_disjoint cp inst vs /\
    context_source_memory_writes_disjoint cp inst vs /\
    opaque_use_ok fn /\ ~is_param_opcode inst.inst_opcode /\
    MEM r cp.cp_regions /\ r.sr_fn_name = fn.fn_name /\
    r.sr_spill_base <= ps'.ps_alloc.sa_spill_base /\
    ps'.ps_alloc.sa_next_offset <= r.sr_spill_end /\
    generated_plan_state_wf_marked base ps /\ codegen_ready_fn fn /\
    MEM inst (fn_insts fn) /\ ~is_terminator inst.inst_opcode /\ inst_wf inst /\
    (inst.inst_opcode = LOG ==>
     ?tc args. inst.inst_operands = Lit tc :: args /\ w2n tc <= 4) /\
    (inst.inst_opcode = ASSERT ==> IS_SOME (FLOOKUP lo "revert")) /\
    LENGTH (compute_operands inst) <= 16 /\
    LENGTH (compute_operands inst) <=
      LENGTH (SND (emit_input_plan inst.inst_opcode
        (compute_operands inst) next_liveness ps)).ps_stack /\
    (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
      IS_SOME (stack_get_depth op ps.ps_stack) \/
      IS_SOME (FLOOKUP ps.ps_spilled op)) /\
    (!l. MEM (Label l) (compute_operands inst) ==> IS_SOME (FLOOKUP lo l)) /\
    (!lbl i. i < LENGTH (execute_plan cp.cp_initial_fmp ops) /\
             EL i (execute_plan cp.cp_initial_fmp ops) = AsmLabel lbl ==>
             ?off. FLOOKUP lo lbl = SOME off /\ off < dimword (:256) /\
                   FLOOKUP o2pc off = SOME (as.as_pc + i)) /\
    (!op. MEM op (compute_operands inst) ==>
          eval_operand op (frame_view fn ra vs) =
          operand_val (frame_view fn ra vs) lo op) /\
    (!op at. MEM op (compute_operands inst) /\
             (MEM at ps.ps_stack \/ at IN FDOM ps.ps_spilled \/
              MEM at (compute_operands inst)) /\ operand_equiv dfg op at ==>
             operand_val (frame_view fn ra vs) lo op =
             operand_val (frame_view fn ra vs) lo at) /\
    EVERY (\op. op <> dead_stack_marker /\
      !at. operand_equiv dfg op at ==> at <> dead_stack_marker)
      (compute_operands inst) /\
    EVERY (\op. EVERY (\out. case op of Var x => x <> out | _ => T)
                      inst.inst_outputs) ps.ps_stack /\
    (!op. op IN FDOM ps.ps_spilled ==>
          EVERY (\out. case op of Var x => x <> out | _ => T) inst.inst_outputs) /\
    (!dist prev val_op.
       inst.inst_opcode = PHI /\
       stack_get_phi_depth (FILTER is_var_operand inst.inst_operands)
         ps.ps_stack = SOME dist /\ vs.vs_prev_bb = SOME prev /\
       resolve_phi prev inst.inst_operands = SOME val_op ==>
       operand_val (frame_view fn ra vs) lo (stack_peek dist ps.ps_stack) =
         eval_operand val_op (frame_view fn ra vs)) /\
    EVERY (\s. case s of SOSpill off => off < dimword(:256)
      | SORestore off => off < dimword(:256) | _ => T) ops /\
    (!off. MEM (SORestore off) ops ==> off < dimword (:256)) /\
    fn_frame_inv ctx cp lo fn ra rest mem0 ps vs as /\
    generate_inst_plan liveness dfg cfg fn inst
      next_liveness is_halting next_is_term bb_label ps = SOME (ops, ps') /\
    asm_block_at prog as.as_pc (execute_plan cp.cp_initial_fmp ops) /\
    dfg = dfg_build_function fn /\ MEM fn ctx.ctx_functions /\ fn_shape_ok fn /\
    label_flow_ok ctx /\
    (!op w. inst.inst_opcode = ADD /\
            inst.inst_operands = [op; Label "code_end"] /\
            eval_operand op vs = SOME w ==> w2n w < dimword (:256) DIV 2) /\
    sym_data_label prog env "code_end" /\
    (MEM (Label "runtime_begin") inst.inst_operands ==>
     sym_data_label prog env "runtime_begin") /\ asm_static_wf prog /\
    sym_frame_inv prog env ctx cp fn ret srest labs0 ps as ss /\
    inst.inst_opcode <> BUMP ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' ==>
      ?ss'. sym_steps prog env
        (LENGTH (execute_plan cp.cp_initial_fmp ops) -
          (if inst.inst_opcode = ASSERT_UNREACHABLE then 1 else 0)) ss = SymOK ss' /\
        sym_kinds_ok cp fn ret srest ps' ss' /\
        (!b. context_spill_byte cp b /\ ~closure_spill_byte ctx cp fn.fn_name b ==>
          FLOOKUP ss'.sym_mem_labels b = FLOOKUP labs0 b)
Proof
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  `!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    (rpt strip_tac >>
     qpat_x_assum `!op. _ ==> IS_SOME (stack_get_depth _ _) \/ _` mp_tac >>
     simp[stack_get_depth_is_some, finite_mapTheory.FLOOKUP_DEF, COND_RAND]) >>
  `~is_pre_codegen_opcode inst.inst_opcode` by
    metis_tac[generate_inst_plan_pre_codegen_none, optionTheory.NOT_SOME_NONE] >>
  drule_all sym_shaped_prepared_emission_families >>
  simp[optionTheory.IS_SOME_EXISTS, listTheory.MEM] >> strip_tac >> simp[]
  >- (drule_all sym_named_inst_symbolic_run >>
      `inst.inst_opcode <> ASSERT_UNREACHABLE` by
        metis_tac[venom_to_evm_name_def, optionTheory.NOT_SOME_NONE] >> simp[])
  >- (drule_all_then strip_assume_tac sym_generated_assign_sim >>
      gvs[sym_frame_inv_def] >> metis_tac[])
  >- (drule_all_then strip_assume_tac sym_generated_phi_sim >>
      gvs[sym_frame_inv_def] >> metis_tac[])
  >- (drule_all_then strip_assume_tac sym_generated_nop_sim >>
      gvs[sym_frame_inv_def] >> metis_tac[])
  >- (`?x. inst.inst_operands = [] /\ inst.inst_outputs = [x]` by
        (qpat_x_assum `inst_wf inst` mp_tac >> simp[inst_wf_def, listTheory.LENGTH_EQ_1]) >>
      drule_all sym_initial_fmp_inst_symbolic_run >> simp[])
  >- (drule_all_then strip_assume_tac istore_operand_shape >>
      qpat_assum `compute_operands inst = _` (fn ops_eq =>
        qpat_assum `inst.inst_opcode = ISTORE` (fn opc_eq =>
          every_assum (assume_tac o PURE_REWRITE_RULE [ops_eq, opc_eq]))) >>
      drule_all_then MATCH_ACCEPT_TAC sym_istore_inst_symbolic_run)
  >- (`?cond. inst.inst_operands = [cond] /\ compute_operands inst = [cond]` by
        metis_tac[assertion_operand_shape] >>
      qpat_assum `compute_operands inst = _` (fn ops_eq =>
        qpat_assum `inst.inst_opcode = ASSERT` (fn opc_eq =>
          every_assum (assume_tac o PURE_REWRITE_RULE [ops_eq, opc_eq]))) >>
      drule_all_then MATCH_ACCEPT_TAC sym_assert_inst_symbolic_run)
  >- (`?cond. inst.inst_operands = [cond] /\ compute_operands inst = [cond]` by
        metis_tac[assertion_operand_shape] >>
      qpat_assum `compute_operands inst = _` (fn ops_eq =>
        qpat_assum `inst.inst_opcode = ASSERT_UNREACHABLE` (fn opc_eq =>
          every_assum (assume_tac o PURE_REWRITE_RULE [ops_eq, opc_eq]))) >>
      drule_all_then MATCH_ACCEPT_TAC sym_assert_unreachable_inst_symbolic_run)
  >> (`?tc selected. inst.inst_operands = Lit tc :: selected /\ w2n tc <= 4 /\
        compute_operands inst = selected` by
        (qpat_x_assum `inst.inst_opcode = LOG ==> _` mp_tac >>
         simp[] >> strip_tac >> simp[compute_operands_def]) >>
      qpat_assum `compute_operands inst = _` (fn ops_eq =>
        qpat_assum `inst.inst_opcode = LOG` (fn opc_eq =>
          every_assum (assume_tac o PURE_REWRITE_RULE [ops_eq, opc_eq]))) >>
      drule_all_then MATCH_ACCEPT_TAC sym_log_inst_symbolic_run)
QED
