(* Immutable word reads at the common held-argument endpoint. *)
Theory bodyIntCallHeldImmutableWord
Ancestors
  bodyIntCallHeldRead bodyIntCallHeldArgs exprSimCopy exprSimAttribute exprSimUnwrap
  exprSimBopRestWordTail exprSimBopRestWordLoadPath exprSimStorageCopy
  context venomState compileEnv loweringPosts exprLoweringProps immutableCopyExecution

Theorem held_immutable_word_read:
  immutable_holds ce cx ty raw w es s /\ is_word_type ty /\
  stmt_state_rel ctx func ce cx es s ==>
  ?v. read_result cx raw es = (INL v,es) /\
    !tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
      immutable_copy_read ce.ce_is_ctor w s = typed_val_to_w256 tv v
Proof
  strip_tac >> drule immutable_holds_read >> strip_tac >>
  `immutable_holds ce cx ty (Value v) w es s` by
    (qpat_x_assum `immutable_holds _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[immutable_holds_def] >> strip_tac >>
     qexistsl_tac [`name`, `off`, `itv`, `iv`, `k`, `tvt`, `v`] >>
     asm_rewrite_tac[vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
     gvs[]) >>
  qexists_tac `v` >> simp[] >> rpt strip_tac >>
  Cases_on `ce.ce_is_ctor`
  >- (drule_all immutable_holds_iload >> simp[immutable_copy_read_def]) >>
  drule_all immutable_holds_dload >> simp[immutable_copy_read_def]
QED

Theorem held_immutable_word_load_run:
  compile_imm_load_word ce.ce_is_ctor ce.ce_imm_alloca src sm = (op,sn) /\
  copy_old_operand sm src /\ eval_operand src s = SOME w /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sm ==>
  ?u. copy_runtime_frame sm s sn u /\
    eval_operand op u = SOME (immutable_copy_read ce.ce_is_ctor w s) /\
    u.vs_memory = s.vs_memory
Proof
  strip_tac >> Cases_on `ce.ce_is_ctor` >> fs[]
  >- (`!region. ce.ce_imm_alloca = SOME region ==>
         eval_operand region s = SOME 0w /\ copy_old_operand sm region` by
        (gvs[stmt_state_rel_def, immutable_base_zero_def,
             local_ptrs_reserved_def, copy_old_operand_def] >> metis_tac[]) >>
      drule_all copy_ctor_load >> metis_tac[]) >>
  drule_all copy_runtime_load >> metis_tac[]
QED

Theorem held_immutable_word_load_path:
  compile_imm_load_word ce.ce_is_ctor ce.ce_imm_alloca src sm = (op,sn) /\
  copy_old_operand sm src /\ eval_operand src s = SOME w /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sm /\
  fn_has_code sm sn func /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    eval_operand op t = SOME (immutable_copy_read ce.ce_is_ctor w s) /\
    ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
    t.vs_inst_idx = LENGTH sn.cs_current_insts /\
    (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!x w'. not_fresh_at sm x /\ lookup_var x s = SOME w' ==>
      lookup_var x t = SOME w')
Proof
  strip_tac >> drule_all held_immutable_word_load_run >> strip_tac >>
  `context$compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca LocCode src sm = (op,sn)` by
    simp[compile_ptr_load_def] >>
  `run_inst_seq (emitted_insts sm sn) s = OK u` by gvs[copy_runtime_frame_def] >>
  `gas_marked_path F ctx func s 0
      (OK (u with vs_inst_idx := LENGTH sn.cs_current_insts)) /\
   u.vs_current_bb = sn.cs_current_bb /\ ~u.vs_halted` by
    (irule rest_word_ptr_load_marked >> simp[] >>
     goal_assum (drule_at (Pat `context$compile_ptr_load _ _ _ _ _ = _`)) >> simp[]) >>
  `u = s with vs_vars := u.vs_vars` by
    (drule_at (Pat `context$compile_ptr_load _ _ _ _ _ = _`)
       rest_word_ptr_load_run_frame >> simp[] >>
     disch_then drule >> simp[]) >>
  qexists_tac `u with vs_inst_idx := LENGTH sn.cs_current_insts` >>
  simp[eval_operand_def, lookup_var_def] >> conj_tac
  >- gvs[venom_state_component_equality] >>
  gvs[copy_runtime_frame_def, lookup_var_def]
QED

Theorem intcall_held_immutable_word_read:
  unwrap_value ce (LocatedValue sty p) sm = (op,sn) /\
  is_word_type sty /\ p.ptr_location = LocCode /\
  vv_holds ce cx ty raw (LocatedValue sty p) es s /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sm /\
  fn_has_code sm sn func /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?v t. gas_marked_exec F (ctx,func) (read_result cx raw) (es,s)
          [] (INL v) es (OK t) /\
    expr_val_rel cx ty v op t /\ ~t.vs_halted /\
    t.vs_current_bb = sn.cs_current_bb /\
    t.vs_inst_idx = LENGTH sn.cs_current_insts /\
    (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!x w. not_fresh_at sm x /\ lookup_var x s = SOME w ==>
           lookup_var x t = SOME w)
Proof
  strip_tac >>
  `ty = sty /\ ?w. eval_operand p.ptr_operand s = SOME w /\
      immutable_holds ce cx ty raw w es s` by gvs[vv_holds_def] >>
  gvs[] >> drule_all held_immutable_word_read >> strip_tac >>
  `compile_imm_load_word ce.ce_is_ctor ce.ce_imm_alloca p.ptr_operand sm = (op,sn)` by
    gvs[exprLoweringTheory.unwrap_value_def, compile_ptr_load_def] >>
  `copy_old_operand sm p.ptr_operand` by simp[copy_old_operand_def] >>
  drule_all held_immutable_word_load_path >> strip_tac >>
  qexistsl_tac [`v`, `t`] >> fs[] >> conj_tac
  >- (simp[gasSummaryTheory.gas_marked_exec_def] >>
      drule exprSimMemorySourceTheory.read_result_gas_obs >> simp[]) >>
  simp[expr_val_rel_def] >> gvs[]
QED

Theorem intcall_held_immutable_word_read_with_tail:
  unwrap_value ce (LocatedValue sty p) sm = (op,sn) /\
  is_word_type sty /\ p.ptr_location = LocCode /\
  intcall_held_args ce cx a sm es s H /\ MEM (ty,raw,LocatedValue sty p) H /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sm /\
  fn_has_code sm sn func /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?v t. gas_marked_exec F (ctx,func) (read_result cx raw) (es,s)
          [] (INL v) es (OK t) /\
    expr_val_rel cx ty v op t /\ ~t.vs_halted /\
    t.vs_current_bb = sn.cs_current_bb /\
    t.vs_inst_idx = LENGTH sn.cs_current_insts /\
    (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!x w. not_fresh_at sm x /\ lookup_var x s = SOME w ==>
           lookup_var x t = SOME w) /\
    intcall_held_args ce cx a sn es t H
Proof
  strip_tac >> drule_all intcall_held_args_member >> strip_tac >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sm x` by
    gvs[vv_operand_def] >>
  drule_all intcall_held_immutable_word_read >> strip_tac >>
  `sm.cs_next_id <= sn.cs_next_id /\ sm.cs_next_var <= sn.cs_next_var` by
    (mp_tac (Q.SPECL [`ce`, `LocatedValue sty p`, `sm`] ci_mono_unwrap_value) >>
     simp[ci_mono_def]) >>
  qexistsl_tac [`v`, `t`] >> fs[] >>
  irule intcall_held_args_readonly_tail >>
  gvs[stmt_state_rel_def, state_rel_def] >> metis_tac[]
QED
