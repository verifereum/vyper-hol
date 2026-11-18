Theory symZeroInstSim
Ancestors
  symInstPieces genFrameSim venomWf stackPlanGen planExec codegenSymRel
  asmSymBridge asmSymSem venomInst genBlockSim stackModel stackPlanOps
  fnPlanLineageInventory deepResidualSim fnPlanPrefix
  symGeneratedAssignOwn symGeneratedZeroOwn

Theorem sym_generated_phi_sim:
  inst.inst_opcode = PHI /\ inst_wf inst /\
  codegen_ready_fn fn /\ fn_shape_ok fn /\ label_flow_ok ctx /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  generated_plan_state_wf_marked sb ps /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= qs.ps_alloc.sa_spill_base /\
  qs.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  EVERY (\s. case s of SOSpill off => off < dimword (:256)
    | SORestore off => off < dimword (:256) | _ => T) ops /\
  generate_inst_plan lv dfg cfg fn inst nl halt term lbl ps = SOME (ops,qs) /\
  asm_block_at prog as.as_pc (execute_plan cplan.cp_initial_fmp ops) /\
  sym_frame_inv prog env ctx cplan fn ret srest labs0 ps as ss ==>
  ?ss'. sym_steps prog env (LENGTH (execute_plan cplan.cp_initial_fmp ops)) ss = SymOK ss' /\
    sym_kinds_ok cplan fn ret srest qs ss' /\
    ss'.sym_base.as_pc = as.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp ops) /\
    (!b. ~closure_spill_byte ctx cplan fn.fn_name b ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >>
  drule codegenSymOwnRelTheory.label_flow_ok_imp_label_flow_own_ok >> strip_tac >>
  `sym_kinds_ok cplan fn ret srest ps ss /\ ss.sym_base.as_pc = as.as_pc` by
    (fs[sym_frame_inv_def] >> metis_tac[asmSymBridgeTheory.asm_sym_rel_pc]) >>
  drule_all (REWRITE_RULE [sym_steps_mode_def] (Q.INST
    [`allow_own` |-> `F`] symGeneratedZeroOwnTheory.sym_generated_phi_sim_mode)) >> simp[]
QED

Theorem sym_generated_nop_sim:
  inst.inst_opcode = NOP /\
  generate_inst_plan lv dfg cfg fn inst nl halt term lbl ps = SOME (ops,qs) /\
  sym_frame_inv prog env ctx cplan fn ret srest labs0 ps as ss ==>
  ?ss'. sym_steps prog env (LENGTH (execute_plan cplan.cp_initial_fmp ops)) ss = SymOK ss' /\
    sym_kinds_ok cplan fn ret srest qs ss' /\
    ss'.sym_base.as_pc = as.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp ops) /\
    (!b. ~closure_spill_byte ctx cplan fn.fn_name b ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >>
  `sym_kinds_ok cplan fn ret srest ps ss /\ ss.sym_base.as_pc = as.as_pc` by
    (fs[sym_frame_inv_def] >> metis_tac[asmSymBridgeTheory.asm_sym_rel_pc]) >>
  drule_all (REWRITE_RULE [sym_steps_mode_def] (Q.INST
    [`allow_own` |-> `F`] symGeneratedZeroOwnTheory.sym_generated_nop_sim_mode)) >> simp[]
QED

Theorem sym_generated_assign_sim:
  inst.inst_opcode = ASSIGN /\
  step_inst fuel ctx inst vs = OK vs' /\
  codegen_ready_fn fn /\ fn_shape_ok fn /\ MEM inst (fn_insts fn) /\
  dfg = dfg_build_function fn /\
  generated_plan_state_wf_marked sb ps /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= qs.ps_alloc.sa_spill_base /\
  qs.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack /\
  (!op. MEM op (compute_operands inst) /\ is_var_operand op ==>
    IS_SOME (stack_get_depth op ps.ps_stack) \/ IS_SOME (FLOOKUP ps.ps_spilled op)) /\
  EVERY (\op. op <> dead_stack_marker /\
    !at. operand_equiv dfg op at ==> at <> dead_stack_marker) (compute_operands inst) /\
  EVERY (\s. case s of SOSpill off => off < dimword (:256)
    | SORestore off => off < dimword (:256) | _ => T) ops /\
  generate_inst_plan lv dfg cfg fn inst nl halt term lbl ps = SOME (ops,qs) /\
  asm_block_at prog as.as_pc (execute_plan cplan.cp_initial_fmp ops) /\
  sym_frame_inv prog env ctx cplan fn ret srest labs0 ps as ss ==>
  ?ss'. sym_steps prog env (LENGTH (execute_plan cplan.cp_initial_fmp ops)) ss = SymOK ss' /\
    sym_kinds_ok cplan fn ret srest qs ss' /\
    ss'.sym_base.as_pc = as.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp ops) /\
    (!b. ~closure_spill_byte ctx cplan fn.fn_name b ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >>
  `sym_kinds_ok cplan fn ret srest ps ss /\ ss.sym_base.as_pc = as.as_pc` by
    (fs[sym_frame_inv_def] >> metis_tac[asmSymBridgeTheory.asm_sym_rel_pc]) >>
  drule_all (REWRITE_RULE [sym_steps_mode_def] (Q.INST
    [`allow_own` |-> `F`] symGeneratedAssignOwnTheory.sym_generated_assign_sim_mode)) >> simp[]
QED
