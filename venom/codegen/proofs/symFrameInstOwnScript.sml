(* Ordinary instruction frames at supplied label offsets and fixed own code. *)
Theory symFrameInstOwn
Ancestors
  symBumpInstSim symInstDispatch symShuffleSim codegenSymRel fnFrameDeepInst
  asmSymModeOwn asmSymBridge asmSymSem fnPlanPrefix frameRel
  contextCodegenRel codegenRel unitShapeDefs stackPlanGen stackPlanTypes
  planExec asmSem venomExecSemantics venomState venomInst dfgDefs

Theorem bump_operand_shape:
  inst.inst_opcode = BUMP /\ inst_wf inst ==>
  ?base_op size_op ptr next.
    inst.inst_operands = [base_op; size_op] /\
    inst.inst_outputs = [ptr; next] /\
    compute_operands inst = [base_op; size_op]
Proof
  strip_tac >>
  gvs[venomWfTheory.inst_wf_def, listTheory.LENGTH_EQ_NUM_compute] >>
  simp[compute_operands_def, python_stack_operands_def,
       ir_specific_operand_order_def]
QED

Theorem sym_inst_frame_sim_deep_own:
  !allow_own own fuel ctx cp lo o2pc prog liveness dfg cfg fn inst next_liveness
   is_halting next_is_term bb_label base ps vs as ops ps' r ra rest mem0
   env ret srest labs0 ss.
    code_labels_agree prog lo /\ o2pc = build_offset_to_pc prog /\
    inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS /\
    (inst.inst_opcode = CODESIZE ==> allow_own) /\
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
    (if allow_own then label_flow_own_ok ctx else label_flow_ok ctx) /\
    (!dst x sz w off. inst.inst_opcode = CODECOPY /\
      inst.inst_operands = [dst; Var x; sz] /\ code_end_var fn x /\
      eval_operand (Var x) vs = SOME w /\ FLOOKUP lo "code_end" = SOME off ==>
      w2n (w - n2w off) < dimword (:256) DIV 2) /\
    sym_data_label prog env "code_end" /\
    (MEM (Label "runtime_begin") inst.inst_operands ==>
     sym_data_label prog env "runtime_begin") /\ asm_static_wf prog /\
    sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 ps as ss ==>
    !vs'. step_inst fuel ctx inst vs = OK vs' ==>
      ?n as' ss'.
        asm_steps lo o2pc prog n as = AsmOK as' /\
        fn_frame_inv ctx cp lo fn ra rest mem0 ps' vs' as' /\
        as'.as_pc = as.as_pc + LENGTH (execute_plan cp.cp_initial_fmp ops) /\
        sym_steps_mode allow_own prog env own n ss = SymOK ss' /\
        sym_frame_inv_own lo prog env own ctx cp fn ret srest labs0 ps' as' ss'
Proof
  rpt gen_tac >> strip_tac >> rename1 `MEM r cplan.cp_regions` >>
  gen_tac >> strip_tac >>
  drule_all_then strip_assume_tac gen_inst_frame_sim_deep_count_reloc >>
  `!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    (rpt strip_tac >>
     qpat_x_assum `!op. _ ==> IS_SOME (stack_get_depth _ _) \/ _` mp_tac >>
     simp[fnPlanLineageInventoryTheory.stack_get_depth_is_some,
          finite_mapTheory.FLOOKUP_DEF, COND_RAND]) >>
  `?ss'. sym_steps_mode allow_own prog env own
      (LENGTH (execute_plan cplan.cp_initial_fmp ops) -
       (if inst.inst_opcode = ASSERT_UNREACHABLE then 1 else 0)) ss = SymOK ss' /\
    sym_kinds_ok cplan fn ret srest ps' ss' /\
    (!b. context_spill_byte cplan b /\ ~closure_spill_byte ctx cplan fn.fn_name b ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP labs0 b)` by
    (Cases_on `inst.inst_opcode = BUMP` >> simp[]
     >- (drule_all_then strip_assume_tac bump_operand_shape >>
         qpat_assum `compute_operands inst = _` (fn eq =>
           qpat_assum `inst.inst_opcode = BUMP` (fn opc =>
             every_assum (assume_tac o PURE_REWRITE_RULE [eq, opc]))) >>
         `!n cs ss ss'. asm_sym_rel_own lo prog env own cs ss /\
           sym_steps_mode allow_own prog env own n ss = SymOK ss' ==>
           ?cs'. asm_steps lo (build_offset_to_pc prog) prog n cs = AsmOK cs' /\
             asm_sym_rel_own lo prog env own cs' ss'` by
           (rpt strip_tac >> drule_all asm_sym_steps_mode_sim >> simp[]) >>
         fs[sym_frame_inv_own_def] >>
         drule_at (Pat `fn_frame_inv _ _ _ _ _ _ _ _ _ _`)
           (REWRITE_RULE [asm_sym_rel_core_own]
             (Q.INST [`code_ok` |-> `\code. asm_data_env_lo_ok lo prog env own /\ code = own`]
               symBumpRunOwnTheory.sym_bump_inst_symbolic_run_mode_conditional)) >>
         disch_then (drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)) >>
         disch_then irule >> simp[] >> metis_tac[]) >>
     drule_all_then MATCH_ACCEPT_TAC symInstDispatchOwnTheory.sym_non_bump_inst_symbolic_run_own) >>
  fs[sym_frame_inv_own_def] >>
  drule_all_then strip_assume_tac asm_sym_steps_mode_sim >>
  gvs[] >> metis_tac[]
QED
