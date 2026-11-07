Theory bodyPtrBytestringBuiltinsConcatProgramProbe
Ancestors bodyPtrBytestringBuiltinsConcatAdmissionProbe

(* A genuine source unit is required: body_inv fixes its actual context. *)
Definition concat_program_tops_def:
  concat_program_tops =
    [FunctionDecl External Nonpayable F F "f" [] [] NoneT
      [Expr concat_admission_expr]]
End

Theorem concat_program_not_supported:
  ~supported_program concat_program_tops
Proof
  EVAL_TAC
QED

Theorem concat_expression_not_supported:
  !tops. ~supported_expr tops concat_admission_expr
Proof
  EVAL_TAC >> simp[]
QED


(* Even though func is quantified separately, the runtime frame couples it
   back to the supported unit's context through alloca_room. *)
Theorem stmt_state_rel_function_lookup:
  !ctx func cenv cx es s.
    stmt_state_rel ctx func cenv cx es s ==>
    lookup_function func.fn_name ctx.ctx_functions = SOME func
Proof
  simp[exprLoweringPropsTheory.stmt_state_rel_def,
       exprLoweringPropsTheory.alloca_room_def]
QED
