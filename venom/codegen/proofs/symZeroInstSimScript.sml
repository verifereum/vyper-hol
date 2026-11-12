Theory symZeroInstSim
Ancestors
  symInstPieces genFrameSim venomWf stackPlanGen planExec codegenSymRel
  asmSymBridge asmSymSem venomInst genBlockSim stackModel stackPlanOps
  fnPlanLineageInventory deepResidualSim fnPlanPrefix

Theorem sym_zero_spill_offsets[local]:
  EVERY (\s. case s of SOSpill off => off < dimword (:256)
    | SORestore off => off < dimword (:256) | _ => T) ops ==>
  !off. MEM (SOSpill off) ops ==> off < dimword (:256)
Proof
  simp[listTheory.EVERY_MEM] >> rpt strip_tac >>
  first_x_assum (qspec_then `SOSpill off` mp_tac) >> simp[]
QED

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
  drule_all sym_generated_phi_plan_applicability >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  gvs[codegen_ready_fn_def, unitShapeDefsTheory.fn_shape_ok_def,
    venomWfTheory.inst_wf_def, codegenSymRelTheory.sym_frame_inv_def,
    asmSymBridgeTheory.asm_sym_rel_def, listTheory.LENGTH_EQ_1] >>
  `!off. MEM (SOSpill off) ops ==> off < dimword (:256)` by
    metis_tac[sym_zero_spill_offsets] >>
  `asm_block_at prog ss.sym_base.as_pc (execute_plan cplan.cp_initial_fmp ops)` by simp[] >>
  drule_all (Q.INST [`R` |-> `closure_spill_byte ctx cplan fn.fn_name`] sym_phi_plan_sim) >>
  disch_then (qspec_then `env` mp_tac) >> simp[]
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
  strip_tac >> gvs[generate_inst_plan_def, is_pre_codegen_opcode_def,
    is_param_opcode_def, is_unlowered_fmp_opcode_def,
    is_unlowered_internal_call_opcode_def, is_raw_fmp_opcode_def] >>
  qexists `ss` >>
  gvs[execute_plan_def, sym_steps_def, sym_frame_inv_def,
    asmSymBridgeTheory.asm_sym_rel_def]
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
  strip_tac >> drule_all genBlockSimTheory.step_inst_assign_ok >> strip_tac >>
  Cases_on `emit_input_plan ASSIGN [op] nl ps` >>
  rename1 `emit_input_plan ASSIGN [op] nl ps = (iops,prepared)` >>
  Cases_on `reorder_plan dfg [op] prepared` >>
  rename1 `reorder_plan dfg [op] prepared = (rops,arranged)` >>
  drule_all genBlockSimTheory.assign_plan_decompose >>
  disch_then (qspecl_then [`lv`, `cfg`, `fn`, `halt`, `term`, `lbl`] strip_assume_tac) >>
  gvs[compute_operands_def, python_stack_operands_def,
    fnPlanLineageInventoryTheory.stack_get_depth_is_some] >>
  `is_var_operand op ==> MEM op ps.ps_stack \/ op IN FDOM ps.ps_spilled` by
    (Cases_on `op IN FDOM ps.ps_spilled` >> gvs[finite_mapTheory.FLOOKUP_DEF]) >>
  qmatch_asmsub_abbrev_tac `popmany_plan _ ps7` >>
  `ps7 = arranged with ps_stack := stack_push (Var out) (stack_pop 1 arranged.ps_stack)` by
    simp[Abbr `ps7`] >>
  drule_all (SRULE [] (Q.INST [`qs` |-> `release_dead_spills nl ps9`]
    sym_assign_plan_applicability)) >> strip_tac >>
  `ssa_form fn /\ label_positions_ok inst` by
    metis_tac[codegen_ready_fn_def, unitShapeDefsTheory.fn_shape_ok_def,
      listTheory.EVERY_MEM, unitShapeDefsTheory.inst_shape_ok_def] >>
  `spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\ plan_slots_bounded sb ps /\
    residual_budget_wf_marked sb [] ps` by
    metis_tac[generated_plan_state_wf_marked_def,
      generated_plan_state_wf_marked_residual_nil] >>
  qpat_x_assum `sym_frame_inv _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac (srw_ss()) [sym_frame_inv_def, asm_sym_rel_def] >> strip_tac >>
  `asm_block_at prog ss.sym_base.as_pc
    (execute_plan cplan.cp_initial_fmp (iops ++ rops ++ pops ++ opts))` by
    simp[listTheory.APPEND_ASSOC] >>
  `!off. MEM (SOSpill off) (pops ++ opts) ==> off < dimword (:256)` by
    (simp[listTheory.MEM_APPEND] >> metis_tac[sym_zero_spill_offsets]) >>
  `EVERY (\s. case s of SOSpill off => off < dimword (:256)
    | SORestore off => off < dimword (:256) | _ => T) (iops ++ rops)` by simp[] >>
  drule_at (Pat `inst.inst_outputs = _`)
    (PURE_REWRITE_RULE [listTheory.APPEND_ASSOC] sym_assign_plan_sim) >>
  disch_then (drule_at (Pat `reorder_plan _ _ _ = _`)) >>
  disch_then (drule_at (Pat `sym_kinds_ok _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `asm_block_at _ _ _`)) >>
  disch_then (drule_at (Pat `emit_input_plan _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `(if _ then _ else _) = (pops,_)`)) >>
  disch_then (drule_at (Pat `(if _ then _ else _) = (opts,_)`)) >>
  disch_then (drule_at (Pat `plan_slots_bounded _ _`)) >>
  disch_then (drule_at (Pat `MEM _ cplan.cp_regions`)) >>
  disch_then (qspecl_then [`release_dead_spills nl ps9`, `env`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >>
    FIRST [first_assum ACCEPT_TAC, REFL_TAC, all_tac] >>
    simp_tac (srw_ss()) [listTheory.MEM_APPEND] >> metis_tac[])) >>
  strip_tac >>
  qexists `ss'` >> simp[listTheory.APPEND_ASSOC] >>
  metis_tac[genFrameSimTheory.closure_spill_byte_own]
QED
