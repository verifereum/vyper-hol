(*
 * Statement Lowering Properties
 *
 * The single-instruction statements: compile_pass_correct,
 * compile_break_correct, compile_continue_correct.  The statement judgment
 * for every outcome is stmt_frag (stmtSim and the theories after it).
 *
 * Source: vyperInterpreterScript.sml (eval_stmt/eval_stmts)
 * Target: venomExecSemanticsScript.sml (run_block/run_function)
 * Lowering: stmtLoweringScript.sml (compile_stmt/compile_stmts)
 *)

Theory stmtLoweringProps
Ancestors
  list fragExec
  stmtLowering exprLoweringProps exprLowering emitHelper emitHelperProps
  compileEnv venomExecSemantics venomExecProps venomInst venomState
  vyperInterpreter vyperState
Libs
  monadsyntax

(* ===== Per-Statement Lemmas ===== *)

(* --- Pass: no-op --- *)
Theorem compile_pass_correct:
  ∀ func cenv cx lctx ty es ss st.
    state_rel func cenv cx es ss ∧
    compile_stmt cenv lctx ty Pass st = ((), st')
    ⇒
    st' = st ∧
    state_rel func cenv cx es ss
Proof
  rw[compile_stmt_def, comp_return_def, comp_bind_def, comp_ignore_bind_def]
QED

(* --- Break: jumps to exit label --- *)
Theorem compile_break_correct:
  ∀ cenv exit_lbl incr_lbl ty ss st st'.
    compile_stmt cenv (InLoop exit_lbl incr_lbl) ty Break st = ((), st')
    ⇒
    run_inst_seq (emitted_insts st st') ss =
      OK (jump_to exit_lbl ss)
Proof
  rw[compile_stmt_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
     fresh_id_def, emit_def, venomInstTheory.mk_inst_def, comp_return_def, comp_bind_def, comp_ignore_bind_def]
  >> simp[emitted_insts_def, rich_listTheory.DROP_APPEND1,
          rich_listTheory.DROP_LENGTH_NIL, comp_return_def, comp_bind_def, comp_ignore_bind_def]
  >> simp[run_inst_seq_def, step_inst_base_def, comp_return_def, comp_bind_def, comp_ignore_bind_def]
QED

(* --- Continue: jumps to increment label --- *)
Theorem compile_continue_correct:
  ∀ cenv exit_lbl incr_lbl ty ss st st'.
    compile_stmt cenv (InLoop exit_lbl incr_lbl) ty Continue st = ((), st')
    ⇒
    run_inst_seq (emitted_insts st st') ss =
      OK (jump_to incr_lbl ss)
Proof
  rw[compile_stmt_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
     fresh_id_def, emit_def, venomInstTheory.mk_inst_def, comp_return_def, comp_bind_def, comp_ignore_bind_def]
  >> simp[emitted_insts_def, rich_listTheory.DROP_APPEND1,
          rich_listTheory.DROP_LENGTH_NIL, comp_return_def, comp_bind_def, comp_ignore_bind_def]
  >> simp[run_inst_seq_def, step_inst_base_def, comp_return_def, comp_bind_def, comp_ignore_bind_def]
QED

(* Every theorem here is closed. *)
val () = List.app
  (fn (name,th) =>
    let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
      if null (Thm.hyp th) andalso null axioms andalso
         List.all (fn oracle => oracle = "DISK_THM") oracles then ()
      else raise Fail ("statement lowering proof is not closed: " ^ name)
    end)
  (DB.thms "stmtLoweringProps");
