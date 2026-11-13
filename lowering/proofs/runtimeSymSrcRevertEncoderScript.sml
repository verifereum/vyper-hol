Theory runtimeSymSrcRevertEncoder
Ancestors
  runtimeSymSrcInterfaces runtimeSymSrcEmission stmtLowering compileEnv venomInst stackPlanTypes

(* Equation-first interfaces keep the finite encoder traversal separate from
   the implementations of the emission primitives. *)
Theorem runtime_sym_encoder_op[local]:
  emit_op opc ops s = (v,s') ==>
  opc <> CODESIZE /\ opc <> CODECOPY /\
  EVERY (\op. ~is_label_operand op) ops /\
  EVERY runtime_sym_inst (state_insts s) ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  metis_tac[runtime_sym_emit_op]
QED

Theorem runtime_sym_encoder_void[local]:
  emit_void opc ops s = (u,s') ==>
  opc <> CODESIZE /\ opc <> CODECOPY /\
  EVERY (\op. ~is_label_operand op) ops /\
  EVERY runtime_sym_inst (state_insts s) ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  metis_tac[runtime_sym_emit_void]
QED

(* External contracts: compile_alloc_buffer and unwrap_value are context
   boundaries owned by C1.1.3.2. Their exact state/result obligations remain
   literal antecedents below; no expression-lowering fact is assumed. *)
Theorem runtime_sym_revert_encoder:
  (!n s b s'. EVERY runtime_sym_inst (state_insts s) /\
     compile_alloc_buffer n s = (b,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\
     ~is_label_operand b.buf_operand) /\
  (!ce v s op s'. runtime_sym_env ce /\ runtime_sym_value v /\
     EVERY runtime_sym_inst (state_insts s) /\
     unwrap_value ce v s = (op,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand op) ==>
  runtime_sym_env ce /\ runtime_sym_value msg /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_revert_with_reason ce msg ty msg_size s = (u,s') ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  simp[NoAsms, compile_revert_with_reason_def,
       comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >>
  rpt strip_tac >> gvs[] >>
  first_assum drule_all >> strip_tac >>
  rev_dxrule runtime_sym_encoder_void >> simp[is_label_operand_def] >> strip_tac >>
  rev_dxrule runtime_sym_encoder_op >> simp[is_label_operand_def] >> strip_tac >>
  first_assum drule_all >> strip_tac >>
  first_assum drule_all >> strip_tac >>
  ntac 5 (rev_dxrule runtime_sym_encoder_op >> simp[is_label_operand_def] >> strip_tac) >>
  rev_dxrule runtime_sym_encoder_void >> simp[is_label_operand_def] >> strip_tac >>
  qpat_assum `!n st b st'. EVERY _ _ /\ compile_alloc_buffer _ _ = _ ==> _`
    drule_all >> strip_tac >>
  rev_dxrule runtime_sym_encoder_void >> simp[is_label_operand_def] >> strip_tac >>
  ntac 8 (rev_dxrule runtime_sym_encoder_op >> simp[is_label_operand_def] >> strip_tac) >>
  rev_dxrule runtime_sym_encoder_void >> simp[is_label_operand_def] >> strip_tac >>
  rev_dxrule runtime_sym_encoder_op >> simp[is_label_operand_def] >> strip_tac >>
  rev_dxrule runtime_sym_encoder_void >> simp[is_label_operand_def] >> strip_tac >>
  ntac 4 (rev_dxrule runtime_sym_encoder_op >> simp[is_label_operand_def] >> strip_tac) >>
  rev_dxrule runtime_sym_encoder_void >> simp[is_label_operand_def] >> strip_tac >>
  rev_dxrule runtime_sym_encoder_op >> simp[is_label_operand_def] >> strip_tac >>
  rev_dxrule runtime_sym_encoder_void >> simp[is_label_operand_def] >> strip_tac >>
  ntac 3 (rev_dxrule runtime_sym_encoder_op >> simp[is_label_operand_def] >> strip_tac) >>
  drule_at (Pat `emit_inst _ _ _ _ = _`) runtime_sym_emit_inst >>
  disch_then irule >> simp[] >> qexists `s.cs_next_id` >>
  irule runtime_sym_labeled_inst >> simp[]
QED
