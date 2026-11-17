(* Generated PHI and empty NOP plans in either symbolic execution mode. *)
Theory symGeneratedZeroOwn
Ancestors
  symInstPieces symInstPhiOwn genFrameSim venomWf stackPlanGen planExec
  codegenSymRel asmSymSem venomInst genBlockSim stackModel stackPlanOps
  fnPlanLineageInventory deepResidualSim fnPlanPrefix

Theorem sym_generated_phi_sim_mode:
  inst.inst_opcode = PHI /\ inst_wf inst /\
  codegen_ready_fn fn /\ fn_shape_ok fn /\ label_flow_own_ok ctx /\
  MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
  generated_plan_state_wf_marked sb ps /\
  MEM r cplan.cp_regions /\ r.sr_fn_name = fn.fn_name /\
  r.sr_spill_base <= qs.ps_alloc.sa_spill_base /\
  qs.ps_alloc.sa_next_offset <= r.sr_spill_end /\
  EVERY (\s. case s of SOSpill off => off < dimword (:256)
    | SORestore off => off < dimword (:256) | _ => T) ops /\
  generate_inst_plan lv dfg cfg fn inst nl halt term lbl ps = SOME (ops,qs) /\
  asm_block_at prog as.as_pc (execute_plan cplan.cp_initial_fmp ops) /\
  sym_kinds_ok cplan fn ret srest ps ss /\ ss.sym_base.as_pc = as.as_pc ==>
  ?ss'. sym_steps_mode allow_own prog env own
      (LENGTH (execute_plan cplan.cp_initial_fmp ops)) ss = SymOK ss' /\
    sym_kinds_ok cplan fn ret srest qs ss' /\
    ss'.sym_base.as_pc = as.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp ops) /\
    (!b. ~closure_spill_byte ctx cplan fn.fn_name b ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >>
  drule_all sym_generated_phi_plan_applicability >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  gvs[codegen_ready_fn_def, unitShapeDefsTheory.fn_shape_ok_def,
    venomWfTheory.inst_wf_def, listTheory.LENGTH_EQ_1] >>
  `!off. MEM (SOSpill off) ops ==> off < dimword (:256)` by
    (rpt strip_tac >>
     qpat_x_assum `EVERY _ ops` mp_tac >>
     simp[listTheory.EVERY_MEM] >>
     disch_then (qspec_then `SOSpill off` mp_tac) >> simp[]) >>
  `asm_block_at prog ss.sym_base.as_pc (execute_plan cplan.cp_initial_fmp ops)` by simp[] >>
  drule_all (Q.INST [`R` |-> `closure_spill_byte ctx cplan fn.fn_name`]
    sym_phi_plan_sim_mode) >>
  disch_then (qspecl_then [`own`, `env`, `allow_own`] mp_tac) >> simp[]
QED

Theorem sym_generated_nop_sim_mode:
  inst.inst_opcode = NOP /\
  generate_inst_plan lv dfg cfg fn inst nl halt term lbl ps = SOME (ops,qs) /\
  sym_kinds_ok cplan fn ret srest ps ss /\ ss.sym_base.as_pc = as.as_pc ==>
  ?ss'. sym_steps_mode allow_own prog env own
      (LENGTH (execute_plan cplan.cp_initial_fmp ops)) ss = SymOK ss' /\
    sym_kinds_ok cplan fn ret srest qs ss' /\
    ss'.sym_base.as_pc = as.as_pc + LENGTH (execute_plan cplan.cp_initial_fmp ops) /\
    (!b. ~closure_spill_byte ctx cplan fn.fn_name b ==>
      FLOOKUP ss'.sym_mem_labels b = FLOOKUP ss.sym_mem_labels b)
Proof
  strip_tac >> gvs[generate_inst_plan_def, is_pre_codegen_opcode_def,
    is_param_opcode_def, is_unlowered_fmp_opcode_def,
    is_unlowered_internal_call_opcode_def, is_raw_fmp_opcode_def] >>
  qexists `ss` >> simp[execute_plan_def] >>
  irule sym_steps_mode_ok >> simp[asmSpliceTheory.sym_steps_def]
QED
