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

Theorem compile_load_tuple_elements_no_gas:
  !tys cenv bop off sa elems sb.
    compile_load_tuple_elements cenv bop tys off sa = (elems, sb) ==>
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sb) /\
    sb.cs_current_bb = sa.cs_current_bb
Proof
  Induct
  >- simp[compile_load_tuple_elements_def, comp_return_def, emitted_insts_def] >>
  rpt gen_tac >>
  simp[compile_load_tuple_elements_def, comp_bind_def, LET_THM] >>
  rpt (pairarg_tac >> simp[]) >> simp[comp_return_def] >> strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[] >>
  rename1 `emit_op ADD _ sa = (pv, sm)` >>
  rename1 `emit_op MLOAD _ sm = (v, sh)` >>
  rename1 `compile_load_tuple_elements _ _ _ _ sh = (rest, sf)` >>
  `sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm` by
    metis_tac[emit_op_extends] >>
  `sh.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sh` by
    metis_tac[emit_op_extends] >>
  `emitted_insts sa sh = emitted_insts sa sm ++ emitted_insts sm sh` by
    metis_tac[emitted_insts_append] >>
  `sh.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sh` by
    metis_tac[APPEND_ASSOC] >>
  `emitted_insts sa sf = emitted_insts sa sh ++ emitted_insts sh sf` by
    metis_tac[emitted_insts_append] >>
  conj_tac >- metis_tac[APPEND_ASSOC] >>
  conj_tac
  >- (simp[] >>
      qpat_x_assum `emit_op ADD _ _ = _` (strip_assume_tac o MATCH_MP emitted_insts_emit_op_local) >>
      qpat_x_assum `emit_op MLOAD _ _ = _` (strip_assume_tac o MATCH_MP emitted_insts_emit_op_local) >>
      simp[venomInstTheory.mk_inst_def]) >>
  imp_res_tac exprLoweringPropsTheory.emit_op_same_blocks >>
  gvs[same_blocks_def]
QED

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
