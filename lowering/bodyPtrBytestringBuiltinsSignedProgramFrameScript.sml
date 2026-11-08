Theory bodyPtrBytestringBuiltinsSignedProgramFrame
Ancestors
  bodyPtrBytestringBuiltinsSignedProgram bodySim supportedExprForms supportedDecls
  bodyPtrBytestringBuiltinsRuntime bodyPtrBytestringBuiltinsSourceFrame

(* Source context shares the program used to derive the installed code. *)
Definition signed_program_cx_def:
  signed_program_cx = order_runtime_cx with
    sources := [(order_runtime_cx.txn.target, [(NONE, signed_program_tops)])]
End

Theorem signed_program_unsupported:
  ~supported_program signed_program_tops
Proof
  EVAL_TAC
QED

Theorem signed_program_body_inv_obstruction:
  !ctx cenv cx. ~body_inv signed_program_tops ctx cenv cx
Proof
  simp[body_inv_def, signed_program_unsupported]
QED

(* Slice is absent from the supported builtin whitelist, independently of
   operands or types; this exclusion is not a signed-conversion restriction. *)
Theorem signed_program_slice_form_excluded:
  !tops ty n es. ~supported_builtin_form tops ty (Slice n) es
Proof
  EVAL_TAC >> simp[]
QED

Theorem signed_program_header_admitted:
  supported_declaration_headers signed_program_tops
Proof
  EVAL_TAC
QED

Theorem signed_program_tail_forms_admitted:
  supported_type_builtin_form signed_program_tops (BaseT (IntT 256))
    Convert (BaseT (IntT 256)) [Name (BaseT (BytesT (Dynamic 1))) "b"] /\
  supported_type_builtin_form signed_program_tops (BaseT (UintT 256))
    Convert (BaseT (UintT 256))
    [TypeBuiltin (BaseT (IntT 256)) Convert (BaseT (IntT 256))
      [Name (BaseT (BytesT (Dynamic 1))) "b"]]
Proof
  EVAL_TAC
QED
