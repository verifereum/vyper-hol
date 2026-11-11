Theory acRuntimeStepProofs
Ancestors
  acRuntimeInvariantDefs acRuntimeInvariantProofs acChainProofs
  venomWf venomWfProps venomExecProofs venomExecProps venomExecSemantics
  venomInstProps venomState venomInst dfgDefs dfgAnalysisProps
  algebraicOptFreshnessProofs algebraicOptDominanceProofs basePtrProofs
  simplifyCfgAvailability finite_map list

Theorem ac_def_before_output_not_current:
  wf_function fn /\ wf_ssa fn /\ MEM bb fn.fn_blocks /\
  idx < LENGTH bb.bb_instructions /\ ac_def_before fn bb idx di /\
  MEM v di.inst_outputs ==>
  ~MEM v (EL idx bb.bb_instructions).inst_outputs
Proof
  rpt strip_tac >>
  `MEM di (fn_insts_blocks fn.fn_blocks)` by
    (fs[ac_def_before_def, unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >>
     metis_tac[EL_MEM]) >>
  `MEM (EL idx bb.bb_instructions) (fn_insts_blocks fn.fn_blocks)` by
    (simp[unitShapeDefsTheory.MEM_fn_insts_blocks_iff] >> metis_tac[EL_MEM]) >>
  `di = EL idx bb.bb_instructions` by
    (fs[wf_ssa_def] >> metis_tac[ssa_outputs_same_inst]) >>
  gvs[] >>
  gvs[ac_def_before_location]
QED

Theorem ac_def_before_operand_not_current:
  wf_function fn /\ wf_ssa fn /\ MEM bb fn.fn_blocks /\
  idx < LENGTH bb.bb_instructions /\ ac_def_before fn bb idx di /\
  di.inst_opcode <> PHI /\ MEM (Var v) di.inst_operands ==>
  ~MEM v (EL idx bb.bb_instructions).inst_outputs
Proof
  rpt strip_tac >>
  `?db j. MEM db fn.fn_blocks /\ j < LENGTH db.bb_instructions /\
          EL j db.bb_instructions = di` by
    (fs[ac_def_before_def] >> metis_tac[EL_MEM, MEM_EL]) >>
  `def_available_at fn db (SOME (EL j db.bb_instructions)) v` by
    (fs[wf_ssa_def, def_dominates_uses_def] >> metis_tac[EL_MEM]) >>
  drule_all ac_available_before_cursor >> strip_tac >>
  `ac_def_before fn bb idx inst` by
    (irule ac_def_before_trans >> metis_tac[]) >>
  metis_tac[ac_def_before_output_not_current]
QED

Theorem ac_current_operand_not_output:
  wf_function fn /\ wf_ssa fn /\ MEM bb fn.fn_blocks /\
  idx < LENGTH bb.bb_instructions /\
  (EL idx bb.bb_instructions).inst_opcode <> PHI /\
  MEM (Var v) (EL idx bb.bb_instructions).inst_operands ==>
  ~MEM v (EL idx bb.bb_instructions).inst_outputs
Proof
  rpt strip_tac >>
  `def_available_at fn bb (SOME (EL idx bb.bb_instructions)) v` by
    (fs[wf_ssa_def, def_dominates_uses_def] >> metis_tac[EL_MEM]) >>
  `get_instruction bb idx = SOME (EL idx bb.bb_instructions)` by
    simp[get_instruction_def] >>
  metis_tac[ao_ssa_producer_operand_not_output]
QED
