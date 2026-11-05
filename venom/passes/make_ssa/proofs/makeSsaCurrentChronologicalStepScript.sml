Theory makeSsaCurrentChronologicalStep
Ancestors
  makeSsaCurrentJointRuntime makeSsaCurrentOrdinary makeSsaCurrentSimDefs
  makeSsaCurrentDefs venomExecSemantics
  venomInst venomState stateFrame list alist finite_map combin

Theorem current_joint_assign_seed:
  i.inst_opcode = ASSIGN /\ i.inst_operands = [op] /\ i.inst_outputs = [x] /\
  j.inst_opcode = ASSIGN /\ j.inst_operands = rename_current_operands rs [op] /\
  j.inst_outputs = [y] /\
  current_joint_rel V Ms Mt rs
    (venomInst$operand_vars [op] ++ current_before_outputs [x] D) st st' /\
  current_write_compatible rs rt x y D /\
  current_origin_absent origin Ms /\ current_origin_absent origin Mt /\
  step_inst_base i st = OK after ==>
  ?value after'.
    step_inst_base j st' = OK after' /\
    current_joint_rel ((origin =+ SOME value) V)
      ((x,origin)::Ms) ((y,origin)::Mt) rt D after after' /\
    ALOOKUP ((x,origin)::Ms) x = SOME origin /\
    ALOOKUP ((y,origin)::Mt) (latest_current_name rt x) = SOME origin /\
    lookup_var x after = SOME value /\
    lookup_var (latest_current_name rt x) after' = SOME value
Proof
  strip_tac >>
  `eval_operand (HD (rename_current_operands rs [op])) st' = eval_operand op st` by
    (irule current_eval_operand_agree >> conj_tac
     >- metis_tac[current_joint_frame] >>
     drule current_joint_name_agree >>
     simp[current_name_agree_def] >> metis_tac[]) >>
  qpat_x_assum `step_inst_base i st = _` mp_tac >>
  asm_rewrite_tac[step_inst_base_def] >>
  Cases_on `eval_operand op st` >> simp[] >> strip_tac >> gvs[] >>
  rename1 `eval_operand op st = SOME value` >>
  qexistsl_tac [`value`, `update_var y value st'`] >>
  conj_tac
  >- (asm_rewrite_tac[step_inst_base_def] >>
      Cases_on `op` >> gvs[rename_current_operands_def]) >>
  `current_origin_realizes V Ms st /\ current_origin_realizes V Mt st'` by
    fs[current_joint_rel_def] >>
  `current_origin_realizes ((origin =+ SOME value) V)
     ((x,origin)::Ms) (update_var x value st)` by
    (irule current_origin_realizes_fresh_write >> simp[]) >>
  `current_origin_realizes ((origin =+ SOME value) V)
     ((y,origin)::Mt) (update_var y value st')` by
    (irule current_origin_realizes_fresh_write >> simp[]) >>
  gvs[current_write_compatible_def] >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  fs[current_joint_rel_def, update_var_def] >>
  simp[current_joint_rel_def, update_var_def, execution_frame_def] >>
  rpt strip_tac >> Cases_on `v = x` >>
  gvs[current_before_outputs_def, MEM_FILTER] >> metis_tac[]
QED
