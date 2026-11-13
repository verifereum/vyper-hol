(* TOP-LEVEL: the actual remaining field compiler discharges the preceding
   child's continuation obligation from the enclosing continuation. *)
Theory typedFieldsContinuation
Ancestors
  typedCopyContinuations typedCopyCut context compileEnv fragExec

Theorem compile_typed_copy_fields_continuation =
  REWRITE_RULE [compiler_cut_continuation_def]
    (CONJUNCT1 (CONJUNCT2 compiler_cut_continuation_typed_copy_mutual));
