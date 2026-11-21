(* Constructor exit code satisfies the shared O1 source-shape interface. *)
Theory ctorShapeProps
Ancestors
  ctorDecoderShape ctorRegisterShape loweringShapeProps loweringShapeDefs loweringShapeRules moduleLowering
  unitShapeDefs compileEnv emitHelper venomInst

Theorem compile_constructor_epilogue_shape_mode:
  !runtime_size immutables_len immutables_buf.
    shape_mode_step static F compiler_label (\st. plain_operand st immutables_buf)
      (compile_constructor_epilogue runtime_size immutables_len immutables_buf)
      (\x st. T)
Proof
  rpt gen_tac >> simp[compile_constructor_epilogue_def] >>
  IF_CASES_TAC
  >- (match_mp_tac shape_step_bind_mode >>
      qexists_tac `\v st. plain_operand st immutables_buf /\ plain_operand st v` >>
      conj_tac
      >- (ho_match_mp_tac shape_step_emit_op_guarded_mode >>
          conj_tac >- (rw[shape_mode_stable_def] >> metis_tac[plain_operand_mono_mode]) >>
          simp[label_or_plain_def,
            plain_operand_def, stackPlanTypesTheory.is_label_operand_def,
            lowered_inst_mode_ok_def, mk_inst_def, raw_opcode_ok_def,
            inst_shape_ok_def, label_positions_ok_def, inst_jump_labels_ok_def,
            is_read0_opcode_def, is_terminator_def, is_param_opcode_def]) >>
      qx_gen_tac `deploy_buf` >> simp[] >>
      match_mp_tac shape_step_bind_mode >>
      qexists_tac `\v st. (plain_operand st immutables_buf /\
                          plain_operand st deploy_buf) /\ plain_operand st v` >>
      conj_tac
      >- (ho_match_mp_tac shape_step_emit_op_guarded_mode >>
          conj_tac >- (rw[shape_mode_stable_def] >> metis_tac[plain_operand_mono_mode]) >>
          simp[label_or_plain_def, plain_operand_def,
            stackPlanTypesTheory.is_label_operand_def,
            lowered_inst_mode_ok_def, mk_inst_def, raw_opcode_ok_def,
            inst_shape_ok_def, label_positions_ok_def, inst_jump_labels_ok_def,
            is_read0_opcode_def, is_terminator_def, is_param_opcode_def] >>
          metis_tac[plain_operand_mono_mode, plain_operand_def]) >>
      qx_gen_tac `imm_dst` >> simp[] >>
      match_mp_tac shape_step_ignore_bind_mode >>
      qexists_tac `\u st. plain_operand st deploy_buf` >> conj_tac
      >- suspend "mcopy"
      >> gen_tac >> simp[] >> suspend "positive_copy") >>
  match_mp_tac shape_step_bind_mode >>
  qexists_tac `\buf st. plain_operand st buf.buf_operand` >> conj_tac
  >- (irule shape_step_conseq_mode >> irule_at Any compile_alloc_buffer_shape_mode >> simp[]) >>
  gen_tac >> simp[] >> match_mp_tac shape_step_bind_mode >>
  qexists_tac `\v st. plain_operand st v` >> conj_tac
  >- (irule shape_step_return_mode >> simp[]) >>
  gen_tac >> simp[] >> suspend "zero_copy"
QED

Resume compile_constructor_epilogue_shape_mode[mcopy]:
  `emit_void MCOPY [imm_dst; immutables_buf; Lit (n2w immutables_len)] =
   emit_inst MCOPY [imm_dst; immutables_buf; Lit (n2w immutables_len)] []`
    by simp[FUN_EQ_THM, emit_void_eq, emit_inst_eq] >>
  pop_assum SUBST1_TAC >> irule shape_step_conseq_mode >>
  irule_at Any shape_step_emit_inst_guarded_mode >>
  qexists_tac `\st. (plain_operand st immutables_buf /\
                      plain_operand st deploy_buf) /\ plain_operand st imm_dst` >>
  qexists_tac `compiler_label` >> simp[] >> conj_tac
  >- (rw[shape_mode_stable_def] >> metis_tac[plain_operand_mono_mode]) >>
  simp[label_or_plain_def, plain_operand_def,
       stackPlanTypesTheory.is_label_operand_def,
       lowered_inst_mode_ok_def, mk_inst_def, raw_opcode_ok_def,
       inst_shape_ok_def, label_positions_ok_def, inst_jump_labels_ok_def,
       is_read0_opcode_def, is_terminator_def, is_param_opcode_def]
QED

Resume compile_constructor_epilogue_shape_mode[positive_copy]:
  match_mp_tac shape_step_ignore_bind_mode >>
  qexists_tac `\u st. plain_operand st deploy_buf` >> conj_tac
  >- (irule shape_step_conseq_mode >>
      irule_at Any shape_step_emit_runtime_codecopy_mode >>
      qexists_tac `\st. T` >> qexists_tac `compiler_label` >>
      simp[shape_mode_stable_def, plain_operand_def,
           stackPlanTypesTheory.is_label_operand_def]) >>
  gen_tac >> simp[] >> irule shape_step_conseq_mode >>
  irule_at Any shape_step_emit_entry_return_mode >>
  qexists_tac `compiler_label` >>
  simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def]
QED

Resume compile_constructor_epilogue_shape_mode[zero_copy]:
  rename1 `emit_void CODECOPY [buf; Label "runtime_begin"; _]` >>
  match_mp_tac shape_step_ignore_bind_mode >>
  qexists_tac `\u st. plain_operand st buf` >> conj_tac
  >- (irule shape_step_conseq_mode >>
      irule_at Any shape_step_emit_runtime_codecopy_mode >>
      qexists_tac `\st. T` >> qexists_tac `compiler_label` >>
      simp[shape_mode_stable_def, plain_operand_def,
           stackPlanTypesTheory.is_label_operand_def]) >>
  gen_tac >> simp[] >> irule shape_step_conseq_mode >>
  irule_at Any shape_step_emit_entry_return_mode >>
  qexists_tac `compiler_label` >>
  simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def]
QED

Finalise compile_constructor_epilogue_shape_mode

Theorem compile_simple_deploy_shape_mode:
  !runtime_size immutables_len.
    shape_mode_step static F compiler_label (\st. T)
      (compile_simple_deploy runtime_size immutables_len) (\x st. T)
Proof
  rpt gen_tac >> simp[compile_simple_deploy_def] >>
  match_mp_tac shape_step_bind_mode >>
  qexists_tac `\buf st. plain_operand st buf.buf_operand` >> conj_tac
  >- simp[compile_alloc_buffer_shape_mode] >>
  gen_tac >> simp[] >> match_mp_tac shape_step_bind_mode >>
  qexists_tac `\v st. plain_operand st v` >> conj_tac
  >- (irule shape_step_return_mode >> simp[]) >>
  qx_gen_tac `buf` >> simp[] >>
  match_mp_tac shape_step_ignore_bind_mode >>
  qexists_tac `\u st. plain_operand st buf` >> conj_tac
  >- (irule shape_step_conseq_mode >>
      irule_at Any shape_step_emit_runtime_codecopy_mode >>
      qexists_tac `\st. T` >> qexists_tac `compiler_label` >>
      simp[shape_mode_stable_def, plain_operand_def,
           stackPlanTypesTheory.is_label_operand_def]) >>
  gen_tac >> simp[] >> irule shape_step_conseq_mode >>
  irule_at Any shape_step_emit_entry_return_mode >>
  qexists_tac `compiler_label` >>
  simp[plain_operand_def, stackPlanTypesTheory.is_label_operand_def]
QED

(* The static shape facts used by the existing clients. *)

Theorem compile_constructor_epilogue_shape:
  !runtime_size immutables_len immutables_buf.
    shape_step F compiler_label (\st. plain_operand st immutables_buf)
      (compile_constructor_epilogue runtime_size immutables_len immutables_buf)
      (\x st. T)
Proof
  ACCEPT_TAC (PURE_REWRITE_RULE
    [shape_mode_step_static]
    (Q.INST [`static` |-> `T`] compile_constructor_epilogue_shape_mode))
QED

Theorem compile_simple_deploy_shape:
  !runtime_size immutables_len.
    shape_step F compiler_label (\st. T)
      (compile_simple_deploy runtime_size immutables_len) (\x st. T)
Proof
  ACCEPT_TAC (PURE_REWRITE_RULE
    [shape_mode_step_static]
    (Q.INST [`static` |-> `T`] compile_simple_deploy_shape_mode))
QED
