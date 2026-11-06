(* Same-witness memory preservation for word forcing. *)
Theory bodyIntCallJointWordForce
Ancestors
  exprSimMemoryRead exprSimMemoryPath exprSimUnwrapProps exprSimProps exprSimMemorySource
  exprLoweringProps exprSimUnwrap loweringPosts gasSummary fragGasMode fragGasPath
  valueEncodingProps venomState compileEnv vyperState exprLowering
  emitHelper emitHelperProps context freshWrites venomInst venomExecSemantics

Theorem unwrap_memory_word_joint_read:
  unwrap_value cenv (LocatedValue ty p) sm = (op,sb) /\
  p.ptr_location = LocMemory /\ is_word_type (expr_type e) /\
  fn_has_code sm sb func /\ local_ptrs_reserved cenv sm /\
  sa.cs_next_var <= sm.cs_next_var /\
  vv_post ctx func cenv cx e es sa sm s0 ee tv (LocatedValue ty p) s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?v u. gas_marked_exec F (ctx,func) (read_result cx tv) (ee,s)
          [] (INL v) ee (OK u) /\
    expr_post ctx func cenv cx e es sa sb s0 ee v op u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    u.vs_memory = s.vs_memory
Proof
  strip_tac >>
  `ty = expr_type e /\ ?w v. eval_operand p.ptr_operand s = SOME w /\
     read_result cx tv ee = (INL v,ee) /\
     (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt ==>
       mem_word_at (w2n w) s.vs_memory = typed_val_to_w256 tvt v)` by
    gvs[vv_post_def, vv_holds_def] >>
  `vv_post ctx func cenv cx e es sa sm s0 ee (Value v) (LocatedValue ty p) s` by
    metis_tac[vv_post_read_result] >>
  gvs[unwrap_memory_compile] >>
  qabbrev_tac `u = (update_var (STRING #"%" (toString sm.cs_next_var))
     (mload (w2n w) s) s) with vs_inst_idx := SUC s.vs_inst_idx` >>
  `eval_operand op u = SOME (mload (w2n w) s) /\
   u.vs_current_bb = sb.cs_current_bb /\
   u.vs_inst_idx = LENGTH sb.cs_current_insts /\
   (!x w'. not_fresh_at sm x /\ lookup_var x s = SOME w' ==>
      lookup_var x u = SOME w') /\
   u.vs_allocas = s.vs_allocas /\ u.vs_memory = s.vs_memory` by
    (qunabbrev_tac `u` >> irule emit_mload_endpoint >>
     simp[] >> qexists_tac `p.ptr_operand` >> simp[]) >>
  qexistsl_tac [`v`, `u`] >> reverse conj_tac
  >- (simp[] >> irule expr_post_of_vv_post_load >>
      goal_assum (drule_at Any) >> simp[] >> conj_tac
      >- (rpt strip_tac >> fs[GSYM mem_word_at_eq_mload]) >>
      conj_tac
      >- (simp[Abbr `u`, stmt_state_rel_inst_idx] >>
          irule stmt_state_rel_update_var >>
          `stmt_state_rel ctx func cenv cx ee s` by fs[vv_post_def] >>
          simp[] >> irule local_ptrs_reserved_fresh >>
          qexists_tac `sm` >> simp[]) >>
      qexistsl_tac [`p`, `s`, `sm`, `expr_type e`] >> simp[]) >>
  simp[gas_marked_exec_def] >>
  drule_all emit_mload_marked_path >>
  simp[Abbr `u`] >> metis_tac[read_result_gas_obs]
QED

Theorem unwrap_stack_joint_read:
  unwrap_value cenv (StackValue ty arg) sm = (op,sb) /\
  vv_post ctx func cenv cx e es sa sm s0 ee tv (StackValue ty arg) s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?v u. gas_marked_exec F (ctx,func) (read_result cx tv) (ee,s)
          [] (INL v) ee (OK u) /\
    expr_post ctx func cenv cx e es sa sb s0 ee v op u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    u.vs_memory = s.vs_memory
Proof
  strip_tac >> gvs[unwrap_value_def, comp_return_def] >>
  `?v. read_result cx tv ee = (INL v,ee)` by
    fs[vv_post_def, vv_holds_def] >>
  drule vv_post_read_result >>
  disch_then (fn th => fs[th]) >>
  qexistsl_tac [`v`, `s`] >> simp[] >> conj_tac
  >- (simp[gas_marked_exec_def] >> conj_tac
      >- metis_tac[read_result_gas_obs] >>
      simp[gas_marked_path_def] >> irule (cj 1 gas_path_rules) >> simp[]) >>
  irule expr_post_of_vv_post_stack >> goal_assum (drule_at Any)
QED

(* Concrete endpoint facts are independent of the opcode and input operands. *)
Theorem joint_emit_op_endpoint:
  emit_op opc args sa = (op,sb) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  let u = (update_var (STRING #"%" (toString sa.cs_next_var)) w s)
            with vs_inst_idx := SUC s.vs_inst_idx in
    eval_operand op u = SOME w /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x w'. not_fresh_at sa x /\ lookup_var x s = SOME w' ==>
             lookup_var x u = SOME w') /\
    u.vs_allocas = s.vs_allocas /\ u.vs_memory = s.vs_memory
Proof
  simp[emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
       comp_ignore_bind_def, comp_return_def, emit_def] >>
  rpt strip_tac >> gvs[eval_operand_def, update_var_def, lookup_var_def,
                        not_fresh_at_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac[arithmeticTheory.LESS_EQ_REFL]
QED

Theorem joint_word_load_path:
  emit_op opc args sm = (op,sb) /\ fn_has_code sm sb func /\
  opc <> INVOKE /\ opc <> GAS /\ ~is_terminator opc /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  vv_post ctx func cenv cx e es sa sm s0 ee (Value v) (LocatedValue ty p) s /\
  is_word_type (expr_type e) /\
  (!tvt. evaluate_type (get_tenv cx) (expr_type e) = SOME tvt ==>
     w = typed_val_to_w256 tvt v) /\
  (!out. step_inst_base (mk_inst sm.cs_next_id opc args [out]) s =
     OK (update_var out w s)) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    expr_post ctx func cenv cx e es sa sb s0 ee v op u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\ u.vs_memory = s.vs_memory
Proof
  strip_tac >>
  qabbrev_tac `u = (update_var (STRING #"%" (toString sm.cs_next_var)) w s)
     with vs_inst_idx := SUC s.vs_inst_idx` >>
  `eval_operand op u = SOME w /\
   u.vs_current_bb = sb.cs_current_bb /\
   u.vs_inst_idx = LENGTH sb.cs_current_insts /\
   (!x w'. not_fresh_at sm x /\ lookup_var x s = SOME w' ==>
      lookup_var x u = SOME w') /\
   u.vs_allocas = s.vs_allocas /\ u.vs_memory = s.vs_memory` by
    (drule_all joint_emit_op_endpoint >>
     disch_then (qspec_then `w` mp_tac) >>
     simp_tac bool_ss [LET_THM] >> strip_tac >>
     fs[Abbr `u`]) >>
  qexists_tac `u` >> simp[] >> conj_tac
  >- (pure_rewrite_tac[gas_marked_path_def, COND_CLAUSES] >>
      qunabbrev_tac `u` >> irule emit_op_zero_path >>
      simp[] >> qexistsl_tac [`args`, `op`, `opc`, `sb`] >> simp[]) >>
  irule expr_post_of_vv_post_load >> goal_assum (drule_at Any) >>
  simp[] >> conj_tac
  >- (simp[Abbr `u`, stmt_state_rel_inst_idx] >>
      irule stmt_state_rel_update_var >>
      `stmt_state_rel ctx func cenv cx ee s` by fs[vv_post_def] >>
      simp[] >> irule local_ptrs_reserved_fresh >>
      qexists_tac `sm` >> simp[]) >>
  qexistsl_tac [`p`, `s`, `sm`, `ty`] >> simp[]
QED

Theorem joint_storage_word_load:
  emit_op (if tr then TLOAD else SLOAD) [p.ptr_operand] sm = (op,sb) /\
  fn_has_code sm sb func /\ local_ptrs_reserved cenv sm /\
  sa.cs_next_var <= sm.cs_next_var /\ is_word_type (expr_type e) /\
  vv_post ctx func cenv cx e es sa sm s0 ee (Value v) (LocatedValue ty p) s /\
  eval_operand p.ptr_operand s = SOME w /\
  storage_holds cx tr (expr_type e) (Value v) w ee s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    expr_post ctx func cenv cx e es sa sb s0 ee v op u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\ u.vs_memory = s.vs_memory
Proof
  strip_tac >> irule joint_word_load_path >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`[p.ptr_operand]`, `if tr then TLOAD else SLOAD`] >>
  qexistsl_tac [`p`, `sm`, `ty`, `if tr then tload w s else sload w s`] >> simp[] >>
  conj_tac
  >- (Cases_on `tr` >> rpt strip_tac >>
      simp[step_inst_base_def, exec_read1_def]) >>
  conj_tac
  >- (rpt strip_tac >> irule storage_holds_load >>
      simp[] >> qexistsl_tac [`cx`, `ee`, `expr_type e`] >> simp[]) >>
  Cases_on `tr` >> simp[is_terminator_def]
QED

Theorem joint_runtime_immutable_word_load:
  emit_op DLOAD [p.ptr_operand] sm = (op,sb) /\
  fn_has_code sm sb func /\ local_ptrs_reserved cenv sm /\
  sa.cs_next_var <= sm.cs_next_var /\ is_word_type (expr_type e) /\
  vv_post ctx func cenv cx e es sa sm s0 ee (Value v) (LocatedValue ty p) s /\
  eval_operand p.ptr_operand s = SOME w /\ ~cenv.ce_is_ctor /\
  immutable_holds cenv cx (expr_type e) (Value v) w ee s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u. gas_marked_path F ctx func s 0 (OK u) /\
    expr_post ctx func cenv cx e es sa sb s0 ee v op u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\ u.vs_memory = s.vs_memory
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx ee s` by fs[vv_post_def] >>
  drule_all immutable_holds_dload >> strip_tac >>
  irule joint_word_load_path >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`[p.ptr_operand]`, `DLOAD`, `p`, `sm`, `ty`] >>
  simp[is_terminator_def] >> rpt strip_tac >>
  drule step_DLOAD >> disch_then (qspecl_then [`sm.cs_next_id`, `out`] mp_tac) >>
  simp[]
QED

Theorem unwrap_storage_word_joint_read:
  unwrap_value cenv (LocatedValue ty p) sm = (op,sb) /\
  (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
  is_word_type (expr_type e) /\ fn_has_code sm sb func /\
  local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
  vv_post ctx func cenv cx e es sa sm s0 ee tv (LocatedValue ty p) s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?v u. gas_marked_exec F (ctx,func) (read_result cx tv) (ee,s)
          [] (INL v) ee (OK u) /\
    expr_post ctx func cenv cx e es sa sb s0 ee v op u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    u.vs_memory = s.vs_memory
Proof
  strip_tac >>
  `ty = expr_type e /\ ?w. eval_operand p.ptr_operand s = SOME w /\
    storage_holds cx (p.ptr_location = LocTransient) ty tv w ee s` by
    gvs[vv_post_def, vv_holds_def] >>
  `?v. read_result cx tv ee = (INL v,ee)` by fs[storage_holds_def] >>
  `vv_post ctx func cenv cx e es sa sm s0 ee (Value v) (LocatedValue ty p) s` by
    metis_tac[vv_post_read_result] >>
  `storage_holds cx (p.ptr_location = LocTransient) ty (Value v) w ee s` by
    gvs[storage_holds_def, read_result_def, return_def] >>
  `emit_op (if p.ptr_location = LocTransient then TLOAD else SLOAD)
    [p.ptr_operand] sm = (op,sb)` by
    gvs[unwrap_value_def, compile_ptr_load_def] >>
  qpat_x_assum `ty = expr_type e` SUBST_ALL_TAC >>
  drule_all joint_storage_word_load >> strip_tac >>
  qexistsl_tac [`v`, `u`] >> simp[gas_marked_exec_def] >>
  metis_tac[read_result_gas_obs]
QED
