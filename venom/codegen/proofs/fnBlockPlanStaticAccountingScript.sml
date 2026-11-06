Theory fnBlockPlanStaticAccounting
Ancestors
  fnBlockPlanStaticBalance fnBlockPlanStaticBodyPrefix list venomWf
  asmIR stackPlanGen venomInst removeUnusedSsaProofs livenessTransferProofs

Definition instruction_correction_def:
  instruction_correction inst =
    if inst.inst_opcode = PHI \/ inst.inst_opcode = OFFSET \/
       is_param_opcode inst.inst_opcode \/ inst.inst_opcode = NOP
    then (0:int) else regular_correction inst (source_topics inst)
End

Theorem invoke_compute_operands_no_label[local]:
  inst.inst_opcode = INVOKE ==> ~MEM (Label l) (compute_operands inst)
Proof
  simp[compute_operands_def, get_non_label_operands_def, MEM_FILTER]
QED

Theorem generate_inst_plan_signed_balance:
  inst.inst_opcode <> JMP /\
  (inst.inst_opcode <> PHI ==> LENGTH (compute_operands inst) <= 16) /\
  LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack /\
  generate_inst_plan lv dfg cfg fn inst nl halting next_term lbl ps = SOME (ops,qs) ==>
  &(LENGTH qs.ps_stack) = (&(LENGTH ps.ps_stack):int) + trace_weight ops +
    instruction_correction inst
Proof
  strip_tac >>
  qpat_x_assum `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[generate_inst_plan_def] >>
  Cases_on `is_pre_codegen_opcode inst.inst_opcode` >> simp[] >>
  Cases_on `inst.inst_opcode = INVOKE /\ ~invoke_operands_wf inst` >> simp[] >>
  Cases_on `inst.inst_opcode = PHI` >> simp[]
  >- (strip_tac >> simp[instruction_correction_def] >>
      drule generate_phi_plan_signed_balance >> simp[]) >>
  Cases_on `inst.inst_opcode = OFFSET` >> simp[]
  >- (strip_tac >> simp[instruction_correction_def] >>
      drule generate_offset_plan_signed_balance >> simp[]) >>
  Cases_on `is_param_opcode inst.inst_opcode` >> simp[]
  >- (strip_tac >> gvs[instruction_correction_def, trace_weight_def]) >>
  Cases_on `inst.inst_opcode = NOP` >> simp[]
  >- (strip_tac >> gvs[instruction_correction_def, trace_weight_def]) >>
  strip_tac >> simp[instruction_correction_def] >>
  drule_at (Pat `generate_regular_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    generate_regular_inst_plan_signed_balance >>
  simp[invoke_compute_operands_no_label]
QED

Theorem regional_body_lower_inv_signed_balance:
  codegen_ready_fn fn /\ MEM bb.bb_label (cfg_analyze fn).cfg_dfs_pre /\
  lookup_block bb.bb_label fn.fn_blocks = SOME bb /\
  i < LENGTH bb.bb_instructions /\ inst = EL i bb.bb_instructions /\
  inst.inst_opcode <> JMP /\
  regional_body_lower_inv (liveness_analyze fn) (dfg_build_function fn) spill_base bb i ps /\
  generate_inst_plan (liveness_analyze fn) (dfg_build_function fn) cfg fn inst
    nl halting next_term bb.bb_label ps = SOME (ops,qs) ==>
  &(LENGTH qs.ps_stack) = (&(LENGTH ps.ps_stack):int) + trace_weight ops +
    instruction_correction inst
Proof
  strip_tac >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_mem] >>
  `MEM inst (fn_insts fn)` by
    (simp[fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
     metis_tac[EL_MEM]) >>
  `inst.inst_opcode <> PHI ==> LENGTH (compute_operands inst) <= 16` by
    (gvs[codegen_ready_fn_def, EVERY_MEM, codegen_ready_inst_def] >>
     metis_tac[EL_MEM]) >>
  `LENGTH (compute_operands inst) <=
    LENGTH (SND (emit_input_plan inst.inst_opcode (compute_operands inst) nl ps)).ps_stack` by
    (irule regional_body_lower_inv_input_capacity >> metis_tac[]) >>
  drule_at (Pat `generate_inst_plan _ _ _ _ _ _ _ _ _ _ = _`)
    generate_inst_plan_signed_balance >> simp[]
QED
