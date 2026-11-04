(* Counted memory-safe conditional and direct control statement interface. *)
Theory stmtControlMemory
Ancestors
  stmtSimJumpMem stmtRaiseMemory stmtIfMemory stmtAssertMemory

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_CONTROL_KERNEL_AUDIT OK\n"
     else raise Fail "body control inherited admission"
  end) [compile_break_frag_mem, compile_continue_frag_mem,
        compile_if_stmt_frag_mem, compile_raise_frag_mem,
        compile_assert_frag_mem];
