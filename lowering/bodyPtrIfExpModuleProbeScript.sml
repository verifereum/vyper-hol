Theory bodyPtrIfExpModuleProbe
Ancestors
  bodyPtrIfExpHeaderProbe supportedProgram

(* Concrete module fixture for the admission experiment only; this is not
   a replacement simulation contract or an admissible machine frame. *)
Definition header_probe_tops_def:
  header_probe_tops =
    [FunctionDecl Internal Pure F F "helper" [] [] header_probe_ty
      [Return (SOME header_probe_expr)]]
End

Theorem header_probe_module_rejected:
  ~supported_program header_probe_tops
Proof
  EVAL_TAC
QED

Theorem header_probe_module_header_rejected:
  ~supported_declaration_headers header_probe_tops /\
  ~supported_return_type header_probe_tops header_probe_ty
Proof
  EVAL_TAC
QED
