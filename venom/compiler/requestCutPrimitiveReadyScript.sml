Theory requestCutPrimitiveReady
Ancestors
  stackPlanGen stackPlanTypes asmIR unitShapeDefs
  venomExecProofs venomExecSemantics venomState venomInst venomWf
  logEmitSim list rich_list words option
Libs
  stepInstBaseLib

(* Ordinary instruction evaluation is total on its actual stack operands.
   Parameters use the separate entry-frame transition. *)
Theorem request_cut_primitive_no_error:
  inst_wf inst /\ inst_shape_ok inst /\ codegen_ready_inst inst /\
  ~is_param_opcode inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  inst.inst_opcode <> PHI /\
  (inst.inst_opcode = RET ==> inst.inst_operands <> []) /\
  EVERY (\op. IS_SOME (eval_operand op s)) (compute_operands inst) ==>
  step_inst fuel C inst s <> Error err
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[step_inst_non_invoke] >>
  Cases_on `inst.inst_opcode = JNZ` >- suspend "branch" >>
  Cases_on `inst.inst_opcode = LOG` >- suspend "log" >>
  `~is_pre_codegen_opcode inst.inst_opcode /\
   inst.inst_opcode <> DJMP /\ inst.inst_opcode <> OFFSET` by
    fs[codegen_ready_inst_def, inst_shape_ok_def] >>
  `inst.inst_opcode <> JMP ==> IS_SOME (eval_operands inst.inst_operands s)` by
    (strip_tac >> fs[eval_operands_IS_SOME_EVERY, compute_operands_def, EVERY_MEM]) >>
  Cases_on `inst.inst_opcode = RET` >- suspend "ret" >>
  `inst.inst_opcode = NOP ==> inst.inst_operands = []` by fs[codegen_ready_inst_def] >>
  map_every (fn pat => qpat_x_assum pat kall_tac)
    [`EVERY _ (compute_operands inst)`, `inst_shape_ok inst`, `codegen_ready_inst inst`] >>
  Cases_on `inst.inst_opcode` >>
  gvs[is_pre_codegen_opcode_def, is_unlowered_fmp_opcode_def,
      is_unlowered_internal_call_opcode_def, is_raw_fmp_opcode_def, is_param_opcode_def] >>
  qpat_x_assum `inst_wf inst` mp_tac >>
  simp[inst_wf_def] >>
  strip_tac >>
  fs[LENGTH_EQ_NUM_compute] >>
  stepInstBaseLib.with_opcode_clause (fn cs => asm_simp_tac bool_ss cs) >>
  fs[exec_pure1_def, exec_pure2_def, exec_pure3_def] >>
  fs[exec_read0_def, exec_read1_def, exec_write2_def, exec_gas_def] >>
  fs[exec_ext_call_def, exec_delegatecall_def, exec_create_def] >>
  fs[eval_operands_IS_SOME_EVERY] >>
  fs[optionTheory.IS_SOME_EQ_NOT_NONE] >>
  strip_tac >> gvs[AllCaseEqs()]
QED

Resume request_cut_primitive_no_error[branch]:
  gvs[inst_wf_def, inst_shape_ok_def, label_positions_ok_def] >>
  `case c of Label _ => F | _ => T` by
    (Cases_on `c` >> gvs[is_label_operand_def]) >>
  fs[compute_operands_def, get_non_label_operands_def] >>
  Cases_on `eval_operand c s` >> gvs[] >>
  stepInstBaseLib.with_opcode_clause (fn cs => simp cs) >>
  IF_CASES_TAC >> simp[]
QED

Resume request_cut_primitive_no_error[log]:
  gvs[inst_wf_def, compute_operands_def] >>
  `EVERY (\op. IS_SOME (eval_operand op s)) (REVERSE rest)` by simp[EVERY_REVERSE] >>
  `LENGTH (REVERSE rest) = w2n tc + 2` by simp[] >>
  Cases_on `REVERSE rest` >> gvs[] >>
  Cases_on `t` >> gvs[] >>
  `IS_SOME (eval_operands t' s)` by simp[eval_operands_IS_SOME_EVERY] >>
  Cases_on `eval_operand h s` >> gvs[] >>
  Cases_on `eval_operand h' s` >> gvs[] >>
  Cases_on `eval_operands t' s` >> gvs[] >>
  stepInstBaseLib.with_opcode_clause (fn cs => simp (cs @ [eval_operand_def])) >>
  IF_CASES_TAC >> simp[]
QED

Resume request_cut_primitive_no_error[ret]:
  `IS_SOME (eval_operands inst.inst_operands s)` by simp[] >>
  Cases_on `eval_operands inst.inst_operands s` >> gvs[] >>
  `x <> []` by (strip_tac >> drule eval_operands_length >> gvs[]) >>
  Cases_on `x` >> gvs[] >>
  stepInstBaseLib.with_opcode_clause (fn cs => simp cs)
QED

Finalise request_cut_primitive_no_error
