(* A real returning source function, not a patched context function. *)
Theory bodyPtrBopInUnequalEntry
Ancestors
  bodyPtrBopInUnequalProbe bodyPtrBopInSourceFrame
  compileVyper supportedProgram words

Theorem unequal_membership_program_unsupported:
  ~supported_program
    [FunctionDecl External View F F "probe" [] [] (BaseT BoolT)
      [Return (SOME (Builtin (BaseT BoolT) (Bop In)
        [Literal (BaseT (StringT 1)) (StringL "a");
         Builtin (ArrayT (BaseT (StringT 1)) (Fixed 1))
           (MakeArray (SOME (BaseT (StringT 1))) (Fixed 1))
           [Literal (BaseT (StringT 1)) (StringL "b")]]))]]
Proof
  EVAL_TAC
QED
