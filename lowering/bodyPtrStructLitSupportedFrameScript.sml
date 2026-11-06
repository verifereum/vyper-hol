(* Finite supported-frame candidate data; no replacement body invariant. *)
Theory bodyPtrStructLitSupportedFrame
Ancestors bodyPtrStructLitWidenedCandidate bodySim supportedProgram
  compileVyper vyperAST supportedNames supportedExprs
Libs wordsLib

Definition structlit_supported_value_def:
  structlit_supported_value =
    Builtin (structlit_identity_type 33) (MakeArray NONE (Fixed 2))
      [Literal (BaseT (BytesT (Dynamic 33))) (BytesL []);
       Literal (BaseT (BytesT (Dynamic 1))) (BytesL [])]
End

Definition structlit_supported_call_def:
  structlit_supported_call =
    Call (structlit_identity_type 1) (IntCall (NONE,"structlit_probe")) [] NONE
End

Definition structlit_supported_expr_def:
  structlit_supported_expr =
    StructLit (StructT (NONE,"S")) (NONE,"S") [("x",structlit_supported_call)]
End

Definition structlit_supported_program_def:
  structlit_supported_program =
    [StructDecl "S" [("x",structlit_identity_type 1)];
     FunctionDecl Internal Pure F F "structlit_probe" [] []
       (structlit_identity_type 33)
       [Return (SOME structlit_supported_value)];
     FunctionDecl External Pure F F "structlit_caller" [] []
       (StructT (NONE,"S"))
       [Return (SOME structlit_supported_expr)]]
End

Theorem structlit_supported_headers_check:
  supported_declaration_headers structlit_supported_program
Proof
  EVAL_TAC
QED

Theorem structlit_supported_name_projections:
  ALL_DISTINCT (supported_function_names structlit_supported_program) /\
  ALL_DISTINCT (supported_event_names structlit_supported_program) /\
  EVERY (supported_function_header_names structlit_supported_program)
    structlit_supported_program
Proof
  simp[structlit_supported_program_def, supported_function_names_def,
       supported_event_names_def, supported_function_header_names_def,
       supported_function_bindings_def]
QED

Theorem structlit_supported_names_check:
  supported_declaration_names structlit_supported_program
Proof
  simp[supported_declaration_names_def, structlit_supported_name_projections] >>
  simp[supported_selectors_distinct_def, structlit_supported_program_def,
       classify_functions_def, classify_function_def, build_selectors_def]
QED

Theorem structlit_supported_program_rejected:
  ~supported_program structlit_supported_program
Proof
  rewrite_tac[supported_program_def] >>
  simp[structlit_supported_headers_check, structlit_supported_names_check] >>
  rewrite_tac[structlit_supported_program_def, listTheory.EVERY_DEF] >>
  EVAL_TAC
QED

Theorem structlit_supported_body_checks:
  supported_declaration_body structlit_supported_program
    (EL 1 structlit_supported_program) /\
  ~supported_declaration_body structlit_supported_program
    (EL 2 structlit_supported_program)
Proof
  conj_tac >> EVAL_TAC
QED

(* Struct fields must be pure in the supported-program whitelist; an
   internal call is an effect expression even when its callee is Pure. *)
Theorem structlit_supported_field_not_pure:
  !tops. ~supported_pure_expr tops structlit_supported_expr
Proof
  simp[structlit_supported_expr_def, structlit_supported_call_def,
       supported_pure_expr_def]
QED

Theorem structlit_supported_no_body_frame:
  !ctx cenv cx. ~body_inv structlit_supported_program ctx cenv cx
Proof
  simp[body_inv_def, structlit_supported_program_rejected]
QED
