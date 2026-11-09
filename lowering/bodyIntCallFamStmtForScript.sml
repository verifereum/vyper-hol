(* Seam 2 joint induction, a family leaf of the stmt step: For. *)
Theory bodyIntCallFamStmtFor
Ancestors
  bodyIntCallJointContract bodySim loweringPosts compileEnv bodyIntCallFamStmtForEntry bodyIntCallFamStmtForScope bodyIntCallFamStmtForResources bodyIntCallFamStmtForFrontier bodyIntCallFamStmtForTransport bodyIntCallFamStmtForPop bodyIntCallFamStmtForArrayFrame bodyIntCallFamStmtForRound stmtSimForLoop stmtSimProps stmtSimDeclStore fragGasMode intCallFrame venomState finite_map

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

(* Internal returns clear scopes; abort exits do not inspect them. *)
Theorem intcall_stmt_exit_scopes[simp]:
  intcall_stmt_exit fp res (ee with scopes := scs) r <=>
  intcall_stmt_exit fp res ee r
Proof
  simp[intcall_stmt_exit_def]
QED

(* The condition/store prefix enters the body with the original fp origin. *)
Theorem intcall_for_range_entry:
  for_code fp.jc_func ce bc ty stmts id tyv p sz ainst cv ev dv nv
    cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa cc /\
  declare_local ce id fty sd = (bc,sd') /\ ce.ce_alloca_locals /\
  FLOOKUP ce.ce_vars id = NONE /\ id NOTIN FDOM env.var_types /\
  lookup_scopes id es.scopes = NONE /\
  evaluate_type (get_tenv fp.jc_cx) fty = SOME tyv /\
  value_has_type tyv (IntV (n1 + &k)) /\ type_memory_bytes ce fty < 2 ** 64 /\
  sa.cs_next_var <= sb0.cs_next_var /\
  (!x. not_fresh_at sa x ==> x <> dv) /\
  not_local_ptr bc (FEMPTY :: es.scopes) p /\
  cc.vs_current_bb = cond_lbl /\ cc.vs_inst_idx = 0 /\ ~cc.vs_halted /\
  lookup_var cv cc = SOME (i2w (n1 + &k)) /\
  lookup_var ev cc = SOME (i2w n2) /\ lookup_var p cc = SOME w /\
  FLOOKUP cc.vs_allocas ainst.inst_id = SOME (w2n w,sz) /\
  n1 <= n2 /\ k < Num (n2 - n1) /\ Num (n2 - n1) < dimword (:256) ==>
  ?s2. gas_marked_path F fp.jc_ctx fp.jc_func cc 0 (OK s2) /\
    intcall_joint_res fp bc (extend_local env id fty F)
      (es with scopes :=
        (FEMPTY |+ (id, <|assignable := F; type := tyv;
                          value := IntV (n1 + &k); popped := []|>)) :: es.scopes)
      sb0 s2 /\
    ~s2.vs_halted /\ s2.vs_current_bb = sb0.cs_current_bb /\
    s2.vs_inst_idx = LENGTH sb0.cs_current_insts /\
    (!x. x <> dv ==> lookup_var x s2 = lookup_var x cc) /\
    s2.vs_allocas = cc.vs_allocas /\ cc.vs_alloca_next <= s2.vs_alloca_next
Proof
  strip_tac >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es cc` by
    fs[intcall_joint_res_def] >>
  `bc.ce_module_vars = ce.ce_module_vars /\ bc.ce_module = ce.ce_module /\
   bc.ce_is_ctor = ce.ce_is_ctor /\ bc.ce_imm_alloca = ce.ce_imm_alloca` by
    fs[for_code_def, compile_env_component_equality] >>
  qhdtm_assum `for_code` mp_tac >>
  rewrite_tac[for_code_def] >> strip_tac >>
  `not_local_ptr ce es.scopes dv` by metis_tac[] >>
  drule_all intcall_for_body_entry_frame >> strip_tac >>
  `cc.vs_alloca_next <= s2.vs_alloca_next` by
    (drule intcall_marked_path_frontier_mono >> simp[]) >>
  `allocas_above fp.jc_lo s2` by
    (fs[intcall_joint_res_def, allocas_above_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `!a z. fp.jc_prot a z ==>
    mem_bytes_at a z s2.vs_memory = mem_bytes_at a z cc.vs_memory` by
    (rpt strip_tac >> first_x_assum irule >> disj1_tac >>
     fs[intcall_frame_ok_def, intcall_joint_res_def, allocas_above_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  qexists_tac `s2` >> simp[] >>
  irule intcall_for_declared_entry >>
  metis_tac[]
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
