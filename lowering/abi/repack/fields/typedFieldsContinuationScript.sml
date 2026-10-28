(* TOP-LEVEL: the actual remaining field compiler discharges the preceding
   child's continuation obligation from the enclosing continuation. *)
Theory typedFieldsContinuation
Ancestors
  typedCopyContinuations typedCopyCut context compileEnv fragExec

Theorem compile_typed_copy_fields_continuation =
  REWRITE_RULE [compiler_cut_continuation_def]
    (CONJUNCT1 (CONJUNCT2 compiler_cut_continuation_typed_copy_mutual));

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed tuple field continuation transport: " ^ name)
  end) (DB.thms "typedFieldsContinuation")
