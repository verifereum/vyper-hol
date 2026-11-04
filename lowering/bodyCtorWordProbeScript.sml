(* Diagnostic only: no claim of a constructor body memory consumer. *)
Theory bodyCtorWordProbe
Ancestors
  immutableWordExecution context exprLoweringProps venomExecSemantics
  venomState venomInst finite_map bodySim

Theorem body_ctor_word_none_equation:
  compile_imm_load_word T NONE off = emit_op ILOAD [off]
Proof
  simp[compile_imm_load_word_def]
QED

Theorem body_ctor_word_some_equation:
  compile_imm_load_word T (SOME region) off =
    do addr <- emit_op ADD [off; region]; emit_op ILOAD [addr] od
Proof
  simp[compile_imm_load_word_def]
QED

Theorem body_ctor_word_none_run:
  eval_operand off s = SOME a ==>
  run_inst_seq [mk_inst id ILOAD [off] [out]] s =
    OK (update_var out (mload (w2n a) s) s)
Proof
  simp[mk_inst_def, run_inst_seq_def, step_inst_base_opcode_eqs, exec_read1_def]
QED

Theorem body_ctor_word_some_run:
  eval_operand off s = SOME a /\ eval_operand region s = SOME b ==>
  run_inst_seq
    [mk_inst id ADD [off; region] [tmp];
     mk_inst (id+1) ILOAD [Var tmp] [out]] s =
  OK (update_var out (mload (w2n (a+b)) s) (update_var tmp (a+b) s))
Proof
  simp[mk_inst_def, run_inst_seq_def, step_inst_base_opcode_eqs,
       exec_pure2_def, exec_read1_def, eval_operand_def, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE, mload_def]
QED

Theorem body_ctor_word_read_alloca_frame:
  (update_var out w (update_var tmp a s)).vs_alloca_next = s.vs_alloca_next /\
  (update_var out w (update_var tmp a s)).vs_allocas = s.vs_allocas
Proof
  simp[update_var_def]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_CTOR_WORD_PROBE_AUDIT OK\n"
     else raise Fail "constructor word probe inherited admission"
  end) [body_ctor_word_none_equation, body_ctor_word_some_equation,
        body_ctor_word_none_run, body_ctor_word_some_run, body_ctor_word_read_alloca_frame];

(* The actual body invariant rules out the diagnostic constructor branch. *)
Theorem body_ctor_word_unreachable:
  body_inv tops ctx cenv cx ==> ~cenv.ce_is_ctor
Proof
  simp[body_inv_def]
QED

val () =
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag body_ctor_word_unreachable)
  in if null axioms andalso null (Thm.hyp body_ctor_word_unreachable) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_CTOR_UNREACHABLE_AUDIT OK\n"
     else raise Fail "constructor reachability probe inherited admission"
  end;
