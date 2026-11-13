Theory runtimeSymSrcEmission
Ancestors
  runtimeSymSrcInterfaces compileVyper string compileEnv emitHelper
  loweringShapeDefs venomInst list stackPlanTypes

Theorem runtime_sym_fresh_label_output:
  runtime_sym_label (fresh_label_output suffix n)
Proof
  simp[runtime_sym_label_def, fresh_label_output_def]
QED

Theorem runtime_sym_internal_label:
  runtime_sym_label (internal_fn_label id name tys ctor)
Proof
  simp[runtime_sym_label_def, internal_fn_label_def]
QED

Theorem runtime_sym_external_label:
  runtime_sym_label ("fn_" ++ name)
Proof
  simp[runtime_sym_label_def]
QED

Theorem runtime_sym_external_prefix_label:
  runtime_sym_label (external_prefix_label name k)
Proof
  simp[external_prefix_label_def, runtime_sym_label_def]
QED

Theorem runtime_sym_external_common_label:
  runtime_sym_label (external_common_label name)
Proof
  simp[external_common_label_def, runtime_sym_label_def]
QED

Theorem runtime_sym_fresh_var:
  fresh_var s = (v,s') ==>
  state_insts s' = state_insts s /\ ~is_label_operand (Var v)
Proof
  simp[fresh_var_def, state_insts_def, all_blocks_def, is_label_operand_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem runtime_sym_fresh_label:
  fresh_label suffix s = (l,s') ==>
  state_insts s' = state_insts s /\ runtime_sym_label l
Proof
  simp[compileEnvTheory.fresh_label_def] >> rpt strip_tac >> gvs[] >>
  simp[state_insts_def, all_blocks_def, runtime_sym_fresh_label_output]
QED

Theorem runtime_sym_emit_inst:
  runtime_sym_inst (mk_inst id opc ops outs) /\
  EVERY runtime_sym_inst (state_insts s) /\
  emit_inst opc ops outs s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  simp[emit_inst_def, comp_bind_def, comp_ignore_bind_def, fresh_id_def,
       emit_def, comp_return_def] >> rpt strip_tac >> gvs[] >>
  gvs[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND, EVERY_APPEND,
      runtime_sym_inst_def, mk_inst_def]
QED

Theorem runtime_sym_emit_op:
  opc <> CODESIZE /\ opc <> CODECOPY /\
  EVERY (\op. ~is_label_operand op) ops /\
  EVERY runtime_sym_inst (state_insts s) /\ emit_op opc ops s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_id_def,
       fresh_var_def, emit_def, comp_return_def] >> rpt strip_tac >> gvs[] >>
  simp[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND, EVERY_APPEND,
       is_label_operand_def] >>
  gvs[state_insts_def, all_blocks_def, EVERY_APPEND] >>
  gvs[runtime_sym_inst_def, mk_inst_def, EVERY_MEM, is_label_operand_def] >>
  metis_tac[runtime_sym_nonlabel_reserved]
QED

Theorem runtime_sym_emit_void:
  opc <> CODESIZE /\ opc <> CODECOPY /\
  EVERY (\op. ~is_label_operand op) ops /\
  EVERY runtime_sym_inst (state_insts s) /\ emit_void opc ops s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  simp[emit_void_def, comp_bind_def, comp_ignore_bind_def, fresh_id_def,
       emit_def, comp_return_def] >> rpt strip_tac >> gvs[] >>
  simp[state_insts_def, all_blocks_def, MAP_APPEND, FLAT_APPEND, EVERY_APPEND] >>
  gvs[state_insts_def, all_blocks_def, EVERY_APPEND] >>
  gvs[runtime_sym_inst_def, mk_inst_def, EVERY_MEM, is_label_operand_def] >>
  metis_tac[runtime_sym_nonlabel_reserved]
QED

(* Mixed operand lists cover branches and INVOKE: labels are permitted, but
   only outside the reserved assembler namespace. *)
Theorem runtime_sym_label_or_operand:
  (~is_label_operand op \/ ?l. op = Label l /\ runtime_sym_label l) ==>
  op <> Label "code_end" /\ op <> Label "runtime_begin"
Proof
  Cases_on `op` >> simp[is_label_operand_def, runtime_sym_label_def]
QED

Theorem runtime_sym_labeled_inst:
  opc <> CODESIZE /\ opc <> CODECOPY /\
  EVERY (\op. ~is_label_operand op \/
              ?l. op = Label l /\ runtime_sym_label l) ops ==>
  runtime_sym_inst (mk_inst id opc ops outs)
Proof
  simp[runtime_sym_inst_def, mk_inst_def, EVERY_MEM] >>
  metis_tac[runtime_sym_label_or_operand]
QED

Theorem runtime_sym_jump:
  runtime_sym_label l /\ EVERY runtime_sym_inst (state_insts s) /\
  emit_inst JMP [Label l] [] s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  rpt strip_tac >> irule runtime_sym_emit_inst >>
  goal_assum (drule_at Any) >> qexists `s.cs_next_id` >> simp[] >>
  irule runtime_sym_labeled_inst >> simp[]
QED

Theorem runtime_sym_jnz:
  ~is_label_operand op /\ runtime_sym_label yes /\ runtime_sym_label no /\
  EVERY runtime_sym_inst (state_insts s) /\
  emit_inst JNZ [op; Label yes; Label no] [] s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  rpt strip_tac >> irule runtime_sym_emit_inst >>
  goal_assum (drule_at Any) >> qexists `s.cs_next_id` >> simp[] >>
  irule runtime_sym_labeled_inst >> simp[]
QED

Theorem runtime_sym_jmp_if_not_terminated:
  runtime_sym_label l /\ EVERY runtime_sym_inst (state_insts s) /\
  emit_jmp_if_not_terminated l s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  simp[emit_jmp_if_not_terminated_def, comp_bind_def, comp_get_def] >>
  Cases_on `block_is_terminated s` >> simp[comp_return_def] >>
  metis_tac[runtime_sym_jump]
QED

Theorem runtime_sym_fresh_vars:
  !n s vs s'. fresh_vars n s = (vs,s') ==>
  state_insts s' = state_insts s
Proof
  Induct >> simp[fresh_vars_def, comp_return_def] >>
  rpt gen_tac >>
  simp[comp_bind_def, fresh_var_def] >>
  pairarg_tac >> simp[] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule >>
  gvs[comp_return_def, state_insts_def, all_blocks_def]
QED

Theorem runtime_sym_emit_multi_op:
  opc <> CODESIZE /\ opc <> CODECOPY /\
  EVERY (\op. ~is_label_operand op \/
              ?l. op = Label l /\ runtime_sym_label l) ops /\
  EVERY runtime_sym_inst (state_insts s) /\
  emit_multi_op opc ops n s = (vs,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\
  EVERY (\op. ~is_label_operand op) vs
Proof
  simp[emit_multi_op_def, comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  rpt strip_tac >> gvs[comp_return_def] >>
  drule runtime_sym_fresh_vars >> strip_tac >>
  simp[EVERY_MAP, is_label_operand_def] >>
  drule_at (Pat `emit_inst _ _ _ _ = _`) runtime_sym_emit_inst >>
  disch_then irule >> simp[] >>
  qexists `s.cs_next_id` >> irule runtime_sym_labeled_inst >> simp[]
QED
