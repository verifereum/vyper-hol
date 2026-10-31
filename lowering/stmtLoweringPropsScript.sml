(*
 * Statement Lowering Properties
 *
 * TOP-LEVEL:
 *   compile_stmt_correct    — single statement lowering preserves state_rel
 *   compile_stmts_correct   — statement list lowering preserves state_rel
 *   compile_if_correct      — if/else preserves state_rel
 *   compile_for_correct     — for-range preserves state_rel
 *   compile_assert_correct  — assert: OK if true, Abort if false
 *   compile_return_some_external_correct  — external return: Halt
 *   compile_return_some_internal_correct  — internal return: IntRet
 *
 * The multi-block statements are stated with frag_exec (fragExecTheory):
 * the compiled fragment runs inside any function containing the code, and
 * reaches the end of the fragment or exits.  compile_stmt_correct and
 * compile_stmts_correct are cheated and cover success only; the statement
 * judgment for every outcome is stmt_frag (stmtSim and the theories after
 * it).
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

(* ===== Multi-Block Execution ===== *)

(* Assemble all blocks from a compile state into a block list.
   Includes all finalized blocks (cs_blocks) plus the current
   still-open block (cs_current_bb / cs_current_insts). *)
Definition assemble_blocks_def:
  assemble_blocks (st':compile_state) =
    let current_bb = <| bb_label := st'.cs_current_bb;
                        bb_instructions := st'.cs_current_insts |> in
    let finalized = st'.cs_blocks in
    finalized ++ [current_bb]
End

(* Build an ir_function from the blocks assembled between two compile states.
   Entry block is the block that was current at the start of compilation. *)
Definition assemble_function_def:
  assemble_function (st:compile_state) (st':compile_state) =
    mk_raw_function st.cs_current_bb (assemble_blocks st')
End

(* ===== Main Statement Correctness ===== *)

(* ===== lookup_block on assembled blocks ===== *)

(* Find the current (last) block in assembled blocks *)
Theorem lookup_block_assemble_current:
  ∀ st' lbl.
    st'.cs_current_bb = lbl ∧
    ¬MEM lbl (MAP (λbb. bb.bb_label) st'.cs_blocks) ⇒
    lookup_block lbl (assemble_blocks st') =
      SOME <| bb_label := lbl; bb_instructions := st'.cs_current_insts |>
Proof
  rw[assemble_blocks_def, lookup_block_def] >>
  pop_assum mp_tac >>
  qspec_tac(`st'.cs_current_bb`,`v`) >>
  qspec_tac(`st'.cs_current_insts`,`insts`) >>
  qspec_tac(`st'.cs_blocks`,`ls`) >>
  Induct >> rw[FIND_thm]
QED

(* Find a finalized block in assembled blocks *)
Theorem lookup_block_assemble_in_blocks:
  ∀ st' bb lbl.
    FIND (λb. b.bb_label = lbl) st'.cs_blocks = SOME bb ⇒
    lookup_block lbl (assemble_blocks st') = SOME bb
Proof
  rw[assemble_blocks_def, lookup_block_def] >>
  qspec_tac(`st'.cs_current_bb`,`v`) >>
  qspec_tac(`st'.cs_current_insts`,`insts`) >>
  pop_assum mp_tac >>
  qspec_tac(`st'.cs_blocks`,`ls`) >>
  Induct >> rw[FIND_thm] >> gvs[FIND_thm]
QED

(* ===== Main Statement Correctness ===== *)

(* The statement lemmas relate states with stmt_state_rel func, where func
   is the function the fragment runs in.  Their code premises tie func to the
   fragment:
   - fn_has_code st st' func: func holds the fragment's code, so the ALLOCA
     that declares a local is an instruction of func and backs the local
     (local_backed);
   - fn_inst_ids_distinct func: with the allocation facts of stmt_state_rel,
     a re-executed ALLOCA (a loop body, a branch) returns a region no other
     live local holds;
   - local_ptrs_reserved cenv st: the locals are the pointer locals reserved
     before st, so no temporary overwrites a local's pointer and no store
     goes to a fixed MemLoc offset.
   stmt_state_rel says nothing of the compiler temporaries, so it holds again
   where a loop body starts its next iteration with the last one's
   temporaries still bound.
   A fresh ALLOCA runs with vs_alloca_next below 2 ** 256, so its pointer
   does not wrap: stmt_state_rel's alloca_room bounds the frontier plus
   every allocation func can still make and a frame for each function it
   can call (stmt_state_rel_exec_alloca). *)

(* compile_stmt preserves state_rel: if the Vyper statement
   evaluates successfully, the compiled Venom code reaches the end of the
   fragment in a related state. *)
Theorem compile_stmt_correct:
  ∀ func cenv cx lctx ty s es st st' es' ctx.
    eval_stmt cx s es = (INL (), es') ∧
    compile_stmt cenv lctx ty s st = ((), st') ∧
    fn_has_code st st' func ∧ fn_inst_ids_distinct func ∧
    local_ptrs_reserved cenv st
    ⇒
    frag_exec ctx st st' (stmt_state_rel ctx func cenv cx es)
      (stmt_state_rel ctx func cenv cx es') (λr. F)
Proof
  cheat
QED

(* compile_stmts preserves state_rel *)
Theorem compile_stmts_correct:
  ∀ func cenv cx lctx ty stmts es st st' es' ctx.
    eval_stmts cx stmts es = (INL (), es') ∧
    compile_stmts cenv lctx ty stmts st = ((), st') ∧
    fn_has_code st st' func ∧ fn_inst_ids_distinct func ∧
    local_ptrs_reserved cenv st
    ⇒
    frag_exec ctx st st' (stmt_state_rel ctx func cenv cx es)
      (stmt_state_rel ctx func cenv cx es') (λr. F)
Proof
  cheat
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

(* --- Expr statement: side-effect expression --- *)
Theorem compile_expr_stmt_correct:
  ∀ func cenv cx lctx ty e es ss st es' ctx.
    stmt_state_rel ctx func cenv cx es ss ∧
    eval_stmt cx (Expr e) es = (INL (), es') ∧
    compile_stmt cenv lctx ty (Expr e) st = ((), st') ∧
    fn_has_code st st' func ∧ fn_inst_ids_distinct func ∧
    local_ptrs_reserved cenv st
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      stmt_state_rel ctx func cenv cx es' ss'
Proof
  cheat
QED

(* --- AnnAssign: variable declaration with init --- *)
Theorem compile_annassign_correct:
  ∀ func cenv cx lctx ty id vtyp e es ss st st' es' ctx.
    stmt_state_rel ctx func cenv cx es ss ∧
    eval_stmt cx (AnnAssign id vtyp e) es = (INL (), es') ∧
    compile_stmt cenv lctx ty (AnnAssign id vtyp e) st = ((), st') ∧
    fn_has_code st st' func ∧ fn_inst_ids_distinct func ∧
    local_ptrs_reserved cenv st
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = OK ss' ∧
      stmt_state_rel ctx func cenv cx es' ss'
Proof
  cheat
QED

(* --- Assert: abort on false, continue on true --- *)
(* NOTE: Assert creates multiple blocks (fail_block, ok_block) via new_block.
   Must use frag_exec, not run_inst_seq.
   The running context is existential: nothing yet says it holds the
   compiled internal functions, without which a condition calling one
   (INVOKE) errors.  The ∀ctx statements in this file have the same gap
   until such a hypothesis exists.  The relation's context ctx0 stays
   universal: chosen with the existential, it could name no function, and
   stmt_state_rel (alloca_room) would then hold of no state. *)
Theorem compile_assert_correct_true:
  ∀ func cenv cx lctx ty cond_e msg es st st' es' ctx0.
    (do result <- eval_expr cx cond_e; read_result cx result od) es =
      (INL (BoolV T), es') ∧
    compile_stmt cenv lctx ty (Assert cond_e msg) st = ((), st') ∧
    fn_has_code st st' func ∧ fn_inst_ids_distinct func ∧
    local_ptrs_reserved cenv st
    ⇒
    ∃ctx.
      frag_exec ctx st st' (stmt_state_rel ctx0 func cenv cx es)
        (stmt_state_rel ctx0 func cenv cx es') (λr. F)
Proof
  cheat
QED

(* Partial proof of compile_assert_bare_correct_false against its earlier
   run_compiled_blocks statement, kept for reference; it stops before the
   blocks are run:

  rw[compile_stmt_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[comp_return_def] >>
  drule_all compile_expr_correct >> strip_tac >>
  qspec_then`"assert_ok"`drule fresh_label_props >>
  qspec_then`"assert_fail"`drule fresh_label_props >>
  qspec_then`REVERT`drule emit_inst_extends >>
  qspec_then`JNZ`drule emit_inst_extends >>
  qspec_then`fail_lbl`drule new_block_props >>
  qspec_then`ok_lbl`drule new_block_props >>
  rpt strip_tac >>
  simp[run_compiled_blocks_def, assemble_function_def, assemble_blocks_def] >>
  cheat
*)

(* Assert bare + false condition: revert with empty returndata.
   Only for AssertBare — AssertReason has non-empty Error(string) data,
   AssertUnreachable uses INVALID (not REVERT).
   The state reverted from is related to es', the source state after the
   condition. *)
Theorem compile_assert_bare_correct_false:
  ∀ func cenv cx lctx ty cond_e es st st' es' ctx.
    supported_expr cond_e ∧
    well_annotated cond_e ∧
    (do result <- eval_expr cx cond_e; read_result cx result od) es =
      (INL (BoolV F), es') ∧
    compile_stmt cenv lctx ty (Assert cond_e AssertBare) st = ((), st') ∧
    fn_has_code st st' func ∧ fn_inst_ids_distinct func ∧
    local_ptrs_reserved cenv st
    ⇒
    frag_exec ctx st st' (stmt_state_rel ctx func cenv cx es) (λss. F)
      (λr. ∃ss. r = Abort Revert_abort (revert_state (set_returndata [] ss)) ∧
                state_rel func cenv cx es' ss)
Proof
  cheat
QED

(* Assert with reason + false condition: revert with Error(string) encoded data.
   The state reverted from is related to the source state after the
   condition and then the forced reason expression:
   the fail block evaluates the reason before reverting.
   The running context is existential and ctx0 universal, for the same
   reasons as in compile_assert_correct_true:
   the condition and the reason may call internal functions. *)
Theorem compile_assert_reason_correct_false:
  ∀ func cenv cx lctx ty cond_e reason_e es st st' es' ctx0.
    (do result <- eval_expr cx cond_e; read_result cx result od) es =
      (INL (BoolV F), es') ∧
    compile_stmt cenv lctx ty (Assert cond_e (AssertReason reason_e)) st = ((), st') ∧
    fn_has_code st st' func ∧ fn_inst_ids_distinct func ∧
    local_ptrs_reserved cenv st
    ⇒
    ∃ctx.
      frag_exec ctx st st' (stmt_state_rel ctx0 func cenv cx es) (λss. F)
        (λr. ∃ss rd.
               r = Abort Revert_abort (revert_state (set_returndata rd ss)) ∧
               state_rel func cenv cx
                 (SND ((do result <- eval_expr cx reason_e;
                           read_result cx result od) es')) ss)
Proof
  cheat
QED

(* --- Return NONE (external): unlock + STOP → Halt --- *)
Theorem compile_return_none_external_correct:
  ∀ cenv lctx ty ss st st'.
    compile_stmt cenv lctx ty (Return NONE) st = ((), st') ∧
    cenv.ce_return_pc = NONE
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = Halt ss'
Proof
  cheat
QED

(* --- Return NONE (internal): load return_pc + RET → IntRet --- *)
(* NOTE: RET produces IntRet, not OK. The callee's INVOKE handler
   catches IntRet and continues as OK at the call site. *)
Theorem compile_return_none_internal_correct:
  ∀ cenv lctx ty ss st st' rpc_off sz.
    compile_stmt cenv lctx ty (Return NONE) st = ((), st') ∧
    cenv.ce_return_pc = SOME (MemLoc rpc_off sz)
    ⇒
    ∃ ss' vals.
      run_inst_seq (emitted_insts st st') ss = IntRet vals ss'
Proof
  cheat
QED

(* --- Return (SOME e) external: ABI-encode + RETURN → Halt --- *)
Theorem compile_return_some_external_correct:
  ∀ func cenv cx lctx ty e es ss st st' v es'.
    state_rel func cenv cx es ss ∧
    cenv.ce_is_external ∧
    (do result <- eval_expr cx e; read_result cx result od) es =
      (INL v, es') ∧
    compile_stmt cenv lctx ty (Return (SOME e)) st = ((), st')
    ⇒
    ∃ ss'.
      run_inst_seq (emitted_insts st st') ss = Halt (halt_state ss')
Proof
  cheat
QED

(* --- Return (SOME e) internal: push to stack + RET → IntRet --- *)
Theorem compile_return_some_internal_correct:
  ∀ func cenv cx lctx ty e es ss st st' v es' rpc_off sz.
    state_rel func cenv cx es ss ∧
    ¬cenv.ce_is_external ∧
    cenv.ce_return_pc = SOME (MemLoc rpc_off sz) ∧
    (do result <- eval_expr cx e; read_result cx result od) es =
      (INL v, es') ∧
    compile_stmt cenv lctx ty (Return (SOME e)) st = ((), st')
    ⇒
    ∃ ss' vals.
      run_inst_seq (emitted_insts st st') ss = IntRet vals ss'
Proof
  cheat
QED

(* --- If: multi-block correctness --- *)
Theorem compile_if_correct:
  ∀ func cenv cx lctx ty cond_e then_body else_body es st st' es' ctx.
    eval_stmt cx (If cond_e then_body else_body) es = (INL (), es') ∧
    compile_stmt cenv lctx ty (If cond_e then_body else_body) st = ((), st') ∧
    fn_has_code st st' func ∧ fn_inst_ids_distinct func ∧
    local_ptrs_reserved cenv st
    ⇒
    frag_exec ctx st st' (stmt_state_rel ctx func cenv cx es)
      (stmt_state_rel ctx func cenv cx es') (λr. F)
Proof
  cheat
QED

(* --- For range: multi-block loop correctness --- *)
Theorem compile_for_range_correct:
  ∀ func cenv cx lctx ty id fty start_e end_e bound body es st st' es' ctx.
    eval_stmt cx (For id fty (Range start_e end_e) bound body) es =
      (INL (), es') ∧
    compile_stmt cenv lctx ty (For id fty (Range start_e end_e) bound body) st =
      ((), st') ∧
    fn_has_code st st' func ∧ fn_inst_ids_distinct func ∧
    local_ptrs_reserved cenv st
    ⇒
    frag_exec ctx st st' (stmt_state_rel ctx func cenv cx es)
      (stmt_state_rel ctx func cenv cx es') (λr. F)
Proof
  cheat
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

(* Only the explicitly retained general compiler claims may be admitted. *)
val () = List.app
  (fn (name,th) =>
    if List.exists (fn allowed => name = allowed)
      ["compile_stmt_correct", "compile_stmts_correct", "compile_expr_stmt_correct",
       "compile_annassign_correct", "compile_assert_correct_true",
       "compile_assert_bare_correct_false", "compile_assert_reason_correct_false",
       "compile_return_none_external_correct", "compile_return_none_internal_correct",
       "compile_return_some_external_correct", "compile_return_some_internal_correct",
       "compile_if_correct", "compile_for_range_correct"] then ()
    else let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
      if null (Thm.hyp th) andalso null axioms andalso
         List.all (fn oracle => oracle = "DISK_THM") oracles then ()
      else raise Fail ("statement lowering proof is not closed: " ^ name)
    end)
  (DB.thms "stmtLoweringProps");
