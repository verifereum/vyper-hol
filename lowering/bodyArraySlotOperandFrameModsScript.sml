Theory bodyArraySlotOperandFrameMods
Ancestors
  exprReasonOperand exprBopSimProps loweringPosts

Theorem array_slot_operand_frame_mods:
  well_typed_expr env obj /\
  (!id t. FLOOKUP env.var_types id = SOME t ==>
          ?x sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var x) sz)) /\
  compile_expr cenv ty obj sa = (LocatedValue t0 p,sm) /\
  wb_frame cenv mid fin sm s it /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  eval_operand p.ptr_operand s = SOME slot ==>
  eval_operand p.ptr_operand it = SOME slot
Proof
  strip_tac >>
  `!l. p.ptr_operand <> Label l` by
    (`reason_uniform_shape compile_expr cenv ty obj` by
       (irule compile_expr_reason_uniform >> qexists `env` >> simp[]) >>
     qpat_x_assum `reason_uniform_shape _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [reason_uniform_shape_def]) >>
     first_x_assum drule >> simp[reason_result_shape_def]) >>
  irule eval_operand_frame >> simp[] >>
  qexistsl [`sm`,`s`] >> fs[wb_frame_def]
QED
