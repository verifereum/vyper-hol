(* Concrete source-program linkage diagnostic; these definitions are fixture
   data, not replacement semantics or an assumed simulation invariant. *)
Theory bodyPtrStructLitProgramLink
Ancestors bodyPtrStructLitCalleeFixture bodySim supportedProgram
  supportedDecls supportedTypes

Definition structlit_link_call_def:
  structlit_link_call =
    Call (structlit_callee_type 1) (IntCall (NONE,"structlit_probe")) [] NONE
End

Definition structlit_link_program_def:
  structlit_link_program =
    [FunctionDecl Internal Pure F F "structlit_probe" [] []
       (structlit_callee_type 33)
       [Return (SOME (structlit_callee_expr F))];
     FunctionDecl External Pure F F "structlit_caller" [] []
       (structlit_callee_type 1)
       [Return (SOME structlit_link_call)]]
End

Theorem structlit_link_not_supported:
  ~supported_program structlit_link_program
Proof
  EVAL_TAC
QED

Theorem structlit_link_not_headers:
  ~supported_declaration_headers structlit_link_program
Proof
  EVAL_TAC
QED

(* The obstruction is independent of policy, names, caller or source context:
   supported internal returns only admit scalar tuple elements. *)
Theorem structlit_callee_return_unsupported:
  !tops n. ~supported_function_return tops Internal (structlit_callee_type n)
Proof
  simp[structlit_callee_type_def, supported_function_return_def,
       supported_return_type_def, supported_value_type_def,
       supported_scalar_type_def, supported_word_type_def,
       supported_string_type_def]
QED

(* No expression-frame premise for this module can instantiate the body
   judgment: failure is earlier than source evaluation or gas exemptions. *)
Theorem structlit_link_no_body_frame:
  !ctx cenv cx. ~body_inv structlit_link_program ctx cenv cx
Proof
  simp[body_inv_def, structlit_link_not_supported]
QED
