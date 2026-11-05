Theory bodyPtrBopInProgramProbe
Ancestors
  bodyPtrBopInSourceFrame bodyPtrBopInProbe compileVyper supportedProgram
  venomMemProps words

(* A real source function keeps the tested expression inside the lowered unit,
   rather than adding an unrelated function to the context after lowering. *)
Definition probe_program_def:
  probe_program = [FunctionDecl External View F F "probe" [] [] (BaseT BoolT)
    [Return (SOME probe_expr)]]
End

Theorem probe_program_unsupported:
  ~supported_program probe_program
Proof
  EVAL_TAC >> simp[dimword_def, dimindex_256]
QED

Theorem probe_program_has_no_body_frame:
  !ctx cenv cx. ~body_inv probe_program ctx cenv cx
Proof
  simp[bodySimTheory.body_inv_def, probe_program_unsupported]
QED
