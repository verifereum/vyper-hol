Theory runtimeSymSrcOpenCalls
Ancestors
  runtimeSymSrcGeneratorContracts runtimeSymSrcEmission runtimeSymSrcInterfaces
  exprLowering compileEnv emitHelper loweringShapeDefs list venomInst stackPlanTypes

Theorem runtime_sym_call_op[local]:
  emit_op opc ops s = (v,s') ==>
  opc <> CODESIZE /\ opc <> CODECOPY /\
  EVERY (\op. ~is_label_operand op) ops /\
  EVERY runtime_sym_inst (state_insts s) ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  metis_tac[runtime_sym_emit_op]
QED

Theorem runtime_sym_acc:
  runtime_sym_lower_value_clause tops ==> runtime_sym_acc_clause tops
Proof
  rewrite_tac[runtime_sym_lower_value_clause_def, runtime_sym_acc_clause_def] >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `item` >> gvs[compile_acc_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  first_x_assum (qspecl_then [`cfn`, `ce`, `BaseT AddressT`, `e`, `s`] mp_tac) >>
  simp[] >> strip_tac >>
  all_tac
  >~ [`emit_inst INVALID [] [] s = ((),s')`] >-
     (conj_tac >- (irule runtime_sym_emit_inst >>
       goal_assum (drule_at Any) >>
       qexists `s.cs_next_id` >> simp[runtime_sym_inst_def, mk_inst_def]) >>
      simp[is_label_operand_def])
  >~ [`emit_op GT [cs_op; Lit 0w] st2 = (op,s')`] >-
     (dxrule runtime_sym_call_op >> simp[] >> strip_tac >>
      drule runtime_sym_call_op >> simp[is_label_operand_def]) >>
  drule runtime_sym_call_op >> simp[]
QED
