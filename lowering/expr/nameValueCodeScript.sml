(* TOP-LEVEL: generated SSA updates preserve earlier operands. *)
Theory nameValueCode
Ancestors
  abiFieldOperands abiStaticLoopCode ssaOperandFrame venomState

Theorem generated_update_before_operand:
  !var_base arg_op value ss.
    abi_operand_before var_base arg_op ==>
    eval_operand arg_op (update_var (STRING #"%" (toString var_base)) value ss) = eval_operand arg_op ss
Proof
  rpt gen_tac >> DISCH_TAC >> irule eval_operand_update_var_avoids >>
  qpat_x_assum `abi_operand_before _ _` (mp_tac o REWRITE_RULE [abi_operand_before_def]) >>
  disch_then (qspec_then `var_base` mp_tac) >> simp[compiler_var_name_def]
QED
