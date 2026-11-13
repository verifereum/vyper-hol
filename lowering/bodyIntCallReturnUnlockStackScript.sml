(* Stack-return resource boundary, with the exact optional release. *)
Theory bodyIntCallReturnUnlockStack
Ancestors
  bodyIntCallJointContract bodyIntCallFamStmtReturnStackEndpoint
  bodyIntCallForcingReadOnly ctorReturnFrame compileEnv loweringStateRelDefs
  exprLoweringProps loweringPosts fragExec stmtSimReturn stmtLowering
  bodyIntCallFamStmtReturnStackRun venomExecSemantics venomState
  externalReturnSelectedSuffix stmtLoweringMono bodySim

Theorem intcall_stack_unlock_exit_frame:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  0 < fp.jc_root_ce.ce_returns_count /\
  t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  intret_vals_match fp.jc_ret_tv v ws /\
  LENGTH ws = fp.jc_root_ce.ce_returns_count ==>
  intcall_stmt_exit fp (INR (ReturnException v)) es
    (IntRet <|iret_values := ws; iret_adopt_fmp := NONE|>
      (return_unlock_state fp.jc_root_ce t))
Proof
  strip_tac >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es t` by
    (irule forcing_readonly_state_rel >> qexistsl_tac [`t.vs_inst_idx`, `s`, `sa`] >>
     fs[intcall_joint_res_def, intcall_expr_res_def]) >>
  `state_rel fp.jc_func fp.jc_root_ce fp.jc_cx (es with scopes := []) t` by
    (irule constructor_exit_state_rel >> qexists_tac `ce` >>
     fs[intcall_joint_res_def, intcall_expr_res_def, stmt_state_rel_def, state_rel_gas_obs]) >>
  `fp.jc_rb = NONE` by
    (fs[intcall_frame_ok_def] >> Cases_on `fp.jc_rb` >> gvs[]) >>
  simp[intcall_stmt_exit_def] >> disj2_tac >>
  conj_tac
  >- (simp[intret_q_def] >> qexists_tac `t` >>
      simp[result_rel_def, state_rel_gas_obs]) >>
  simp[eval_operand_return_unlock] >> conj_tac
  >- (qpat_x_assum `t = _` SUBST1_TAC >> fs[intcall_joint_res_def, intcall_expr_res_def]) >>
  rpt strip_tac >>
  `eval_operand op t = eval_operand op s` by
    (fs[intcall_frame_ok_def] >>
     first_x_assum drule >> strip_tac >> gvs[] >>
     simp[eval_operand_def] >> first_x_assum irule >>
     fs[intcall_joint_res_def, intcall_expr_res_def]) >>
  fs[intcall_joint_res_def, intcall_expr_res_def]
QED

Theorem return_unlock_load_append:
  !ce s vars k.
    (return_unlock_state ce s) with
      <|vs_vars := vars; vs_inst_idx := (return_unlock_state ce s).vs_inst_idx + k|> =
    return_unlock_state ce
      (s with <|vs_vars := vars; vs_inst_idx := s.vs_inst_idx + k|>)
Proof
  rpt gen_tac >> qabbrev_tac `info = ce.ce_nonreentrant` >> PairCases_on `info` >>
  Cases_on `info0` >> Cases_on `info2` >> Cases_on `info3` >>
  simp[return_unlock_state_def, tstore_def, sstore_def, arithmeticTheory.ADD_CLAUSES]
QED

Theorem stack_return_unlocked_suffix:
  compile_internal_return ce (SOME src) rpc n ty sty tys buf sa = ((),sb) /\
  0 < n /\ fn_has_code sa sb func /\
  ~u.vs_halted /\ u = return_unlock_state ce s /\
  u.vs_current_bb = sa.cs_current_bb /\
  u.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. rpc = Var x ==> not_fresh_at sa x) /\
  eval_operand src u = SOME w /\ eval_operand rpc u = SOME pc ==>
  ?k t. gas_path ctx func u k
      (IntRet <|iret_values := if tys = [] then [w]
                             else tuple_words ce w tys 0 s.vs_memory;
                iret_adopt_fmp := NONE|> (return_unlock_state ce t)) /\
    t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> Cases_on `tys = []`
  >- (gvs[compile_internal_return_def] >>
      `gas_path ctx func (return_unlock_state ce s)
         (LENGTH (FILTER (\i. i.inst_opcode = GAS) []))
         (IntRet <|iret_values := [w]; iret_adopt_fmp := NONE|>
           ((return_unlock_state ce s) with vs_inst_idx :=
             (return_unlock_state ce s).vs_inst_idx + LENGTH ([]:instruction list)))` by
        (irule emitted_seq_values_ret_path >> simp[run_inst_seq_def] >>
         qexistsl_tac [`[src]`, `pc`, `rpc`, `sa`, `sb`, `sa`] >>
         simp[run_inst_seq_def, eval_operands_def]) >>
      qpat_x_assum `(return_unlock_state ce s).vs_inst_idx = _`
        (SUBST_ALL_TAC o SYM) >>
      qexistsl_tac [`0`, `s`] >> gvs[]) >>
  qpat_x_assum `compile_internal_return _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_internal_return_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_load_tuple_elements ce src tys 0 sa = (ops,sm)` >>
  drule_all compile_load_tuple_elements_run >> strip_tac >>
  `eval_operand rpc t = SOME pc` by
    (`eval_operand rpc t = eval_operand rpc u` suffices_by simp[] >>
     irule eval_operand_old_vars >> simp[] >> qexists_tac `sa` >> gvs[]) >>
  `sm.cs_current_bb = sa.cs_current_bb /\
   t.vs_current_bb = u.vs_current_bb /\ ~t.vs_halted` by gvs[same_blocks_def] >>
  drule_all emitted_seq_values_ret_path >>
  disch_then (qspec_then `ctx` assume_tac) >>
  qexistsl_tac [`LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sm))`,
    `s with <|vs_vars := t.vs_vars;
              vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts sa sm)|>`] >>
  gvs[lookup_var_def, GSYM return_unlock_load_append]
QED

Theorem compile_unlock_stack_ret_path:
  compile_return_unlock ce sa = ((),sm) /\
  compile_internal_return ce (SOME src) rpc n ty sty tys buf sm = ((),sb) /\
  0 < n /\ fn_has_code sa sb func /\
  ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. rpc = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME w /\ eval_operand rpc s = SOME pc ==>
  ?k t. gas_path ctx func s k
      (IntRet <|iret_values := if tys = [] then [w]
                             else tuple_words ce w tys 0 s.vs_memory;
                iret_adopt_fmp := NONE|> (return_unlock_state ce t)) /\
    t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >> drule compile_return_unlock_shape >> strip_tac >>
  `cs_extends sm sb` by
    (`ci_mono sm (SND (compile_internal_return ce (SOME src) rpc n ty sty tys buf sm))`
       by simp[cj 1 ci_mono_return_helpers] >> gvs[ci_mono_def]) >>
  drule_all fn_has_code_split >> strip_tac >>
  qsuff_tac `?k r. gas_path ctx func s k r /\ exit_result r /\
    ?t. r = IntRet <|iret_values := if tys = [] then [w]
                         else tuple_words ce w tys 0 s.vs_memory;
                    iret_adopt_fmp := NONE|> (return_unlock_state ce t) /\
      t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)`
  >- metis_tac[] >>
  ho_match_mp_tac (GEN_ALL return_normalizing_prefix_path) >>
  qexistsl_tac [`sm`, `sa`, `\u. u = return_unlock_state ce s`] >>
  simp[] >> conj_tac
  >- (irule compile_return_unlock_frag >> simp[]) >>
  rpt strip_tac >>
  `?k t. gas_path ctx func (return_unlock_state ce s) k
      (IntRet <|iret_values := if tys = [] then [w]
                             else tuple_words ce w tys 0 s.vs_memory;
                iret_adopt_fmp := NONE|> (return_unlock_state ce t)) /\
    t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s)` by
    (irule stack_return_unlocked_suffix >>
     simp[] >> goal_assum (drule_at (Pat `compile_internal_return _ _ _ _ _ _ _ _ _ = _`)) >>
     fs[not_fresh_at_def, eval_operand_return_unlock]) >>
  qexists_tac `k` >> goal_assum (drule_at Any) >>
  simp[exit_result_def] >> qexists_tac `t` >>
  fs[not_fresh_at_def]
QED

Theorem intcall_stack_return_unlock_endpoint:
  intcall_frame_ok fp /\ intcall_joint_res fp ce env es sa s /\
  0 < fp.jc_root_ce.ce_returns_count /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv fp.jc_cx) /\
  value_has_type fp.jc_ret_tv v /\
  expr_val_rel fp.jc_cx fp.jc_ret_ty v op s /\
  expr_val_at ce fp.jc_cx fp.jc_ret_ty spre sa es v op s /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  compile_internal_return_from_env ce fp.jc_ret_ty sty op fp.jc_rpc sa = ((),sb) /\
  fn_has_code sa sb fp.jc_func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?k r. gas_path fp.jc_ctx fp.jc_func s k r /\ exit_result r /\
    intcall_stmt_exit fp (INR (ReturnException v)) es r
Proof
  strip_tac >>
  `ce.ce_returns_count = fp.jc_root_ce.ce_returns_count /\
   ce.ce_struct_fields = fp.jc_root_ce.ce_struct_fields /\
   ce.ce_nonreentrant = fp.jc_root_ce.ce_nonreentrant` by
    fs[intcall_joint_res_def, intcall_expr_res_def, same_frame_def,
       compile_env_component_equality] >>
  `fp.jc_rb = NONE` by
    (fs[intcall_frame_ok_def] >> Cases_on `fp.jc_rb` >> gvs[]) >>
  `ce.ce_return_buf = NONE` by
    fs[intcall_joint_res_def, intcall_expr_res_def, return_buf_frame_def] >>
  `(!x. fp.jc_rpc = Var x ==> not_fresh_at sa x) /\
   eval_operand fp.jc_rpc s = SOME fp.jc_pc` by
    (fs[intcall_joint_res_def, intcall_expr_res_def, intcall_frame_ok_def] >> metis_tac[]) >>
  `?w. eval_operand op s = SOME w` by fs[expr_val_rel_def] >>
  `evaluate_type (get_tenv fp.jc_cx) fp.jc_ret_ty = SOME fp.jc_ret_tv /\
   0 < returns_stack_count
     (\name. MAP (FST o SND) (get_struct_fields ce.ce_struct_fields name))
     fp.jc_ret_ty /\ stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s` by
    fs[intcall_frame_ok_def, intcall_joint_res_def, intcall_expr_res_def] >>
  `~s.vs_call_ctx.cc_static` by fs[stmt_state_rel_def, state_rel_def] >>
  drule_all stack_return_operand_layout >> simp[] >> strip_tac >>
  qpat_x_assum `compile_internal_return_from_env _ _ _ _ _ _ = _` mp_tac >>
  simp[compile_internal_return_from_env_def, comp_bind_def, comp_return_def,
       comp_ignore_bind_def] >> pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_return_unlock ce sa = (unit,sm)` >> Cases_on `unit` >>
  drule_all compile_unlock_stack_ret_path >>
  disch_then (qspec_then `fp.jc_ctx` strip_assume_tac) >>
  qexists_tac `k` >> goal_assum (drule_at Any) >> simp[exit_result_def] >>
  `!z. return_unlock_state ce z = return_unlock_state fp.jc_root_ce z` by
    simp[return_unlock_state_def] >> simp[] >>
  irule intcall_stack_unlock_exit_frame >> simp[] >>
  metis_tac[intcall_frame_ok_def]
QED
