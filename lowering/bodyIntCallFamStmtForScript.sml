(* Seam 2 joint induction, a family leaf of the stmt step: For. *)
Theory bodyIntCallFamStmtFor
Ancestors
  bodyIntCallJointContract bodySim loweringPosts compileEnv bodyIntCallFamStmtForEntry bodyIntCallFamStmtForScope bodyIntCallFamStmtForResources bodyIntCallFamStmtForFrontier bodyIntCallFamStmtForTransport bodyIntCallFamStmtForPop bodyIntCallFamStmtForArrayFrame bodyIntCallFamStmtForRound stmtForRangeMemoryLoop stmtSimForLoop stmtSimProps stmtSimDeclStore fragGasMode intCallFrame venomState finite_map

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

(* Returns and aborts bypass the loop's Break/Continue handler. *)
Theorem intcall_stmt_exit_no_loop_control:
  intcall_stmt_exit fp res ee r ==>
  ?ex. res = INR ex /\ ex <> BreakException /\ ex <> ContinueException
Proof
  Cases_on `res` >> simp[intcall_stmt_exit_def, exprSimDefsTheory.expr_exit_def] >>
  rename1 `INR ex` >> Cases_on `ex` >>
  Cases_on `r` >> simp[exprSimDefsTheory.expr_exit_def]
QED

(* Source cleanup preserves the joint exit without changing its memory origin. *)
Theorem intcall_for_round_exit_cleanup:
  intcall_stmt_exit fp res ee r /\
  eval_stmts fp.jc_cx stmts
    (es with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tyv;
                        value := v; popped := []|>)) :: es.scopes) = (res,ee) ==>
  ee.scopes <> [] /\ ?ex. res = INR ex /\
    ex <> BreakException /\ ex <> ContinueException /\
    intcall_stmt_exit fp (INR ex) (ee with scopes := TL ee.scopes) r
Proof
  strip_tac >>
  `ee.scopes <> []` by
    (drule vyperEvalPreservesScopesTheory.eval_stmts_preserves_scopes_len >>
     simp[] >> strip_tac >> Cases_on `ee.scopes` >> gvs[]) >>
  drule intcall_stmt_exit_no_loop_control >> strip_tac >> gvs[]
QED

(* One resource boundary for all three nonexceptional body outcomes. *)
Theorem intcall_for_body_pop_resources:
  !fp ce env es sa s ce' env' ee sb t id fty tyv v body env_b bindings res.
  intcall_joint_res fp ce env es sa s /\
  intcall_joint_res fp ce' env' ee sb t /\
  cenv_top_ext ce ce' ee.scopes /\ local_ptrs_reserved ce sb /\
  id NOTIN FDOM env.var_types /\ lookup_scopes id es.scopes = NONE /\
  evaluate_type (get_tenv fp.jc_cx) fty = SOME tyv /\ value_has_type tyv v /\
  type_stmts (extend_local env id fty F) fp.jc_ret_ty body = SOME env_b /\
  call_evaluation_safe fp.jc_cx (int_calls_stmts body) /\
  supported_program fp.jc_tops /\ get_module_code fp.jc_cx NONE = SOME fp.jc_tops /\
  supported_stmts fp.jc_tops bindings body /\
  eval_stmts fp.jc_cx body
    (es with scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tyv;
                        value := v; popped := []|>)) :: es.scopes) = (res,ee) /\
  (res = INL () \/ res = INR ContinueException \/ res = INR BreakException) ==>
  ee.scopes <> [] /\
  intcall_joint_res fp ce env (ee with scopes := TL ee.scopes) sb t
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qmatch_asmsub_abbrev_tac `eval_stmts _ _ entry = (res,ee)` >>
  `vyperEvalPreservesScopes$preserves_scopes_dom entry ee` by
    metis_tac[vyperEvalPreservesScopesTheory.eval_stmts_preserves_scopes_dom] >>
  `ee.scopes <> []` by
    fs[vyperEvalPreservesScopesTheory.preserves_scopes_dom_def, Abbr `entry`] >>
  namedCases_on `ee.scopes` ["", "sc rest"] >- gvs[] >> simp[] >>
  `expr_sim_inv ce fp.jc_cx env (ee with scopes := rest)` by
    (irule intcall_for_expr_sim_inv_pop >>
     fs[intcall_joint_res_def, Abbr `entry`] >> metis_tac[]) >>
  irule intcall_joint_res_pop_top_ext >>
  conj_tac
  >- (qexists_tac `sc` >> simp[] >> suspend "nonshadowing") >>
  fs[intcall_joint_res_def] >> metis_tac[]
QED
Resume intcall_for_body_pop_resources[nonshadowing]:
  rpt strip_tac >> Cases_on `n = id`
  >- (gvs[] >>
      irule vyperEvalPreservesScopesTheory.lookup_scopes_none_map_fdom >>
      qexists_tac `es.scopes` >>
      fs[vyperEvalPreservesScopesTheory.preserves_scopes_dom_def, Abbr `entry`]) >>
  drule (cj 1 vyperEvalPreservesScopesTheory.eval_stmts_new_in_head_not_in_tail) >>
  disch_then (qspec_then `n` mp_tac) >>
  simp[Abbr `entry`, FDOM_FUPDATE]
QED
Finalise intcall_for_body_pop_resources

(* The loop's increment writes only its two reserved-against temporaries. *)
Theorem intcall_for_increment_resources:
  lookup_block lbl fp.jc_func.fn_blocks =
    SOME <|bb_label := lbl; bb_instructions :=
      [mk_inst i1 ADD [Var cv; Lit 1w] [nv];
       mk_inst i2 ASSIGN [Var nv] [cv];
       mk_inst i3 JMP [Label cond_lbl] []]|> /\
  t.vs_current_bb = lbl /\ t.vs_inst_idx = 0 /\ ~t.vs_halted /\
  lookup_var cv t = SOME c /\
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa t /\
  not_local_ptr ce es.scopes cv /\ not_local_ptr ce es.scopes nv /\
  (!op. fp.jc_reserved op ==> op <> Var cv /\ op <> Var nv) ==>
  gas_marked_path F fp.jc_ctx fp.jc_func t 0
    (OK (jump_to cond_lbl (update_var cv (c + 1w) (update_var nv (c + 1w) t)))) /\
  intcall_joint_res fp ce env es sa
    (jump_to cond_lbl (update_var cv (c + 1w) (update_var nv (c + 1w) t)))
Proof
  strip_tac >> conj_tac
  >- (irule gas_marked_path_from_mem >>
      irule stmtForRangeMemoryPartsTheory.for_incr_zero_path_mem >> simp[] >>
      metis_tac[]) >>
  simp[bodyIntCallJointStmtJumpTheory.intcall_joint_res_jump_to] >>
  metis_tac[intcall_joint_res_update_var]
QED

(* Route a popped body's landing, then advance unless it broke. *)
Theorem intcall_for_body_finish_resources:
  for_code fp.jc_func ce bc ty stmts id tyv p sz ainst cv ev dv nv
    cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
  stmt_lands (InLoop exit_lbl incr_lbl) sb1 res t /\ ~t.vs_halted /\
  (res = INL () ==> ~block_is_terminated sb1) /\
  intcall_frame_ok fp /\ intcall_joint_res fp ce env ee sb1 t /\
  not_local_ptr ce ee.scopes cv /\ not_local_ptr ce ee.scopes nv /\
  (!op. fp.jc_reserved op ==> op <> Var cv /\ op <> Var nv) /\
  lookup_var cv t = SOME c ==>
  ?u. gas_marked_path F fp.jc_ctx fp.jc_func t 0 (OK u) /\
    intcall_joint_res fp ce env ee sb1 u /\ ~u.vs_halted /\
    u.vs_inst_idx = 0 /\
    (res = INR BreakException ==> u.vs_current_bb = exit_lbl) /\
    (res <> INR BreakException ==>
      u.vs_current_bb = cond_lbl /\ lookup_var cv u = SOME (c + 1w)) /\
    (!x. x <> cv /\ x <> nv ==> lookup_var x u = lookup_var x t) /\
    u.vs_allocas = t.vs_allocas /\ u.vs_alloca_next = t.vs_alloca_next
Proof
  strip_tac >> drule_all for_body_route_mem >>
  disch_then (qspec_then `fp.jc_ctx` strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `u = land` >>
  `gas_marked_path F fp.jc_ctx fp.jc_func t 0 (OK u)` by
    metis_tac[gas_marked_path_from_mem] >>
  `intcall_joint_res fp ce env ee sb1 u /\
   lookup_var cv u = SOME c /\ u.vs_allocas = t.vs_allocas /\
   u.vs_alloca_next = t.vs_alloca_next /\
   (!x. lookup_var x u = lookup_var x t)` by
    (gvs[Abbr `land`] >> Cases_on `res = INL ()` >>
     simp[bodyIntCallJointStmtJumpTheory.intcall_joint_res_jump_to] >>
     fs[jump_to_def, lookup_var_def]) >>
  Cases_on `res = INR BreakException`
  >- (qexists_tac `u` >> simp[]) >>
  `gas_marked_path F fp.jc_ctx fp.jc_func u 0
     (OK (jump_to cond_lbl (update_var cv (c + 1w) (update_var nv (c + 1w) u)))) /\
   intcall_joint_res fp ce env ee sb1
     (jump_to cond_lbl (update_var cv (c + 1w) (update_var nv (c + 1w) u)))` by
    (irule intcall_for_increment_resources >> fs[for_code_def] >> metis_tac[]) >>
  qexists_tac `jump_to cond_lbl (update_var cv (c + 1w) (update_var nv (c + 1w) u))` >>
  conj_tac
  >- (qpat_assum `gas_marked_path _ _ _ t _ _`
        (mp_then Any mp_tac gas_marked_path_then) >>
      disch_then drule >> simp[]) >>
  simp[] >>
  fs[jump_to_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >> gvs[]
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
