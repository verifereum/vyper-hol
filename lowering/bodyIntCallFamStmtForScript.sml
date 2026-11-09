(* Seam 2 joint induction, a family leaf of the stmt step: For. *)
Theory bodyIntCallFamStmtFor
Ancestors
  bodyIntCallJointContract bodySim loweringPosts compileEnv bodyIntCallFamStmtForEntry bodyIntCallFamStmtForScope bodyIntCallFamStmtForResources bodyIntCallFamStmtForFrontier bodyIntCallFamStmtForTransport bodyIntCallFamStmtForPop bodyIntCallFamStmtForArrayFrame bodyIntCallFamStmtForRound

(* Re-entry uses the original compile state, not the body's allocation
   frontier.  Only the static operand reservations need to be re-established. *)
Theorem intcall_joint_res_reentry:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sb s /\
  local_ptrs_reserved ce sa /\
  (!op x. fp.jc_reserved op /\ op = Var x ==> not_fresh_at sa x) ==>
  intcall_joint_res fp ce env es sa s
Proof
  simp[intcall_joint_res_def] >> strip_tac >>
  `ce.ce_return_pc = fp.jc_root_ce.ce_return_pc /\
   ce.ce_return_buf = fp.jc_root_ce.ce_return_buf` by
    fs[same_frame_def, compile_env_component_equality] >>
  `ret_pc_ok ce sa s` by
    (fs[ret_pc_ok_def, intcall_frame_ok_def] >> metis_tac[]) >>
  `return_buf_frame fp.jc_rb ce sa s` by
    (Cases_on `fp.jc_rb`
     >- gvs[return_buf_frame_def] >>
     rename1 `fp.jc_rb = SOME rb` >> PairCases_on `rb` >>
     gvs[return_buf_frame_def] >>
     fs[intcall_frame_ok_def] >> metis_tac[]) >>
  simp[] >> metis_tac[]
QED

Theorem intcall_for_body_size:
  !x ty it n ss. list_size stmt_size ss < stmt_size (For x ty it n ss)
Proof
  simp[vyperASTTheory.stmt_size_def]
QED

Theorem intcall_for_stmt_step:
  (!e. intcall_expr_producer fp e /\ intcall_forced_producer fp e /\
       intcall_map_producer fp e) /\
  (!ss. list_size stmt_size ss < stmt_size st ==>
         intcall_stmts_producer fp ss) /\
  (?x ty it n body. st = For x ty it n body) ==>
  intcall_stmts_producer fp [st]
Proof
  cheat
QED
