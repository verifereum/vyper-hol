(* Runtime DLOAD is a readonly step, separate from fresh arithmetic. *)
Theory bodyIntCallFamAggSubscriptArrayRun
Ancestors
  bodyIntCallFamAggSubscriptReadOnly exprSimSubscriptArrayFramed
  bodyIntCallJointContract emitHelperProps context venomState venomInst
  compileEnv exprLoweringProps fragGasFresh varsExt exprSimArrayIndex freshWrites
  exprSimUnopProps fragExec fragGasMode

Theorem intcall_runtime_load_landing:
  intcall_frame_ok fp /\
  intcall_expr_cont fp ce env es0 sa s0 es si s /\
  sa.cs_next_var <= si.cs_next_var /\
  compile_imm_load_word F imm base_op si = (op,sb) /\
  eval_operand base_op s = SOME b /\ fn_has_code si sb fp.jc_func ==>
  ?t. run_inst_seq (emitted_insts si sb) s = OK t /\
    eval_operand op t = SOME (word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP (w2n b) s.vs_data_section ++ REPLICATE 32 0w))) /\
    (t with vs_vars := s.vs_vars) = s /\
    (!x. not_fresh_at si x ==> lookup_var x t = lookup_var x s) /\
    gas_marked_path F fp.jc_ctx fp.jc_func s 0
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    intcall_expr_cont fp ce env es0 sa s0 es sb
      (t with vs_inst_idx := LENGTH sb.cs_current_insts)
Proof
  strip_tac >>
  drule_all compile_imm_load_word_runtime_run >> strip_tac >>
  qmatch_asmsub_abbrev_tac `run_inst_seq _ s = OK t` >>
  `!x. not_fresh_at si x ==> lookup_var x t = lookup_var x s` by
    (rpt strip_tac >> simp[Abbr `t`] >>
     gvs[] >> drule moduleLoweringPropsTheory.lookup_var_update_not_fresh >> simp[]) >>
  `(t with vs_vars := s.vs_vars) = s` by
    simp[Abbr `t`, update_var_def] >>
  `eval_operand op t = SOME (word_of_bytes T (0w:bytes32)
      (TAKE 32 (DROP (w2n b) s.vs_data_section ++ REPLICATE 32 0w)))` by
    simp[Abbr `t`, eval_operand_def, lookup_var_def,
      update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  qexists_tac `t` >> asm_rewrite_tac [] >>
  irule intcall_readonly_run_landing >> simp[] >>
  qexists_tac `si` >> simp[] >>
  qpat_x_assum `compile_imm_load_word _ _ _ _ = _` mp_tac >>
  simp[compile_imm_load_word_runtime] >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  gvs[same_blocks_def, mk_inst_def, is_terminator_def]
QED

Theorem intcall_fixed_array_subscript_landing:
  intcall_frame_ok fp /\
  intcall_expr_cont fp ce env es0 sa0 s0 es sa s /\
  sa0.cs_next_var <= sa.cs_next_var /\
  compile_array_subscript base_op idx_op F cnt ws esz sgn loader sa = (op,sb) /\
  fn_has_code sa sb fp.jc_func /\
  (!z. base_op = Var z ==> not_fresh_at sa z) /\
  (!z. idx_op = Var z ==> not_fresh_at sa z) /\
  eval_operand base_op s = SOME b /\ eval_operand idx_op s = SOME i /\
  idx_in_range sgn i (n2w cnt) ==>
  ?t. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK t) /\
    intcall_expr_cont fp ce env es0 sa0 s0 es sb t /\
    eval_operand op t = SOME (b + i * n2w esz) /\
    t.vs_memory = s.vs_memory /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!z v. not_fresh_at sa z /\ lookup_var z s = SOME v ==>
       lookup_var z t = SOME v)
Proof
  strip_tac >>
  `~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
   s.vs_inst_idx = LENGTH sa.cs_current_insts /\
   local_ptrs_reserved ce sa /\
   stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s` by
    fs[intcall_expr_cont_def, intcall_expr_res_def] >>
  `eval_operand base_op (drop_fresh sa s) = SOME b /\
   eval_operand idx_op (drop_fresh sa s) = SOME i` by
    metis_tac[eval_operand_drop_fresh] >>
  `fresh_vars_wrt sa (drop_fresh sa s)` by simp[fresh_vars_wrt_drop_fresh] >>
  `array_len_ok F cnt loader base_op (drop_fresh sa s) (n2w cnt)` by
    simp[array_len_ok_static] >>
  drule_all compile_array_subscript_ok >> strip_tac >>
  `straight_fresh (compile_array_subscript base_op idx_op F cnt ws esz sgn loader)` by
    simp[straight_fresh_compile_array_subscript] >>
  drule_all straight_fresh_clean_success_path >>
  disch_then (qspec_then `fp.jc_ctx` strip_assume_tac) >>
  drule_all straight_fresh_run_post >> strip_tac >>
  `writes_fresh sa (emitted_insts sa sb)` by metis_tac[straight_fresh_def] >>
  drule_all run_inst_seq_writes_fresh >> strip_tac >>
  drule_all intcall_straight_fresh_run_landing >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >>
  fs[venom_state_component_equality]
QED

Theorem intcall_array_check_ptr_landing:
  intcall_frame_ok fp /\
  intcall_expr_cont fp ce env es0 sa0 s0 es sa s /\
  sa0.cs_next_var <= sa.cs_next_var /\
  comp_ignore_bind (array_bounds_check idx_op len_op sgn)
    (array_elem_ptr base_op idx_op dyn ws esz) sa = (op,sb) /\
  fn_has_code sa sb fp.jc_func /\
  (!z. base_op = Var z ==> not_fresh_at sa z) /\
  (!z. idx_op = Var z ==> not_fresh_at sa z) /\
  (!z. len_op = Var z ==> not_fresh_at sa z) /\
  eval_operand base_op s = SOME b /\ eval_operand idx_op s = SOME i /\
  eval_operand len_op s = SOME len /\ idx_in_range sgn i len ==>
  ?t. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK t) /\
    intcall_expr_cont fp ce env es0 sa0 s0 es sb t /\
    eval_operand op t = SOME ((if dyn then b + n2w ws else b) + i * n2w esz) /\
    t.vs_memory = s.vs_memory /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!z v. not_fresh_at sa z /\ lookup_var z s = SOME v ==>
       lookup_var z t = SOME v)
Proof
  strip_tac >>
  `~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
   s.vs_inst_idx = LENGTH sa.cs_current_insts /\
   local_ptrs_reserved ce sa /\
   stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s` by
    fs[intcall_expr_cont_def, intcall_expr_res_def] >>
  `eval_operand base_op (drop_fresh sa s) = SOME b /\
   eval_operand idx_op (drop_fresh sa s) = SOME i /\
   eval_operand len_op (drop_fresh sa s) = SOME len` by
    metis_tac[eval_operand_drop_fresh] >>
  `fresh_vars_wrt sa (drop_fresh sa s)` by simp[fresh_vars_wrt_drop_fresh] >>
  drule_all array_check_ptr_run >> strip_tac >>
  `straight_fresh (comp_ignore_bind (array_bounds_check idx_op len_op sgn)
      (array_elem_ptr base_op idx_op dyn ws esz))` by
    simp[straight_fresh_array_check_ptr] >>
  drule_all straight_fresh_clean_success_path >>
  disch_then (qspec_then `fp.jc_ctx` strip_assume_tac) >>
  drule_all straight_fresh_run_post >> strip_tac >>
  `writes_fresh sa (emitted_insts sa sb)` by metis_tac[straight_fresh_def] >>
  drule_all run_inst_seq_writes_fresh >> strip_tac >>
  drule_all intcall_straight_fresh_run_landing >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >>
  fs[venom_state_component_equality]
QED

Theorem intcall_runtime_array_subscript_landing:
  intcall_frame_ok fp /\
  intcall_expr_cont fp ce env es0 sa0 s0 es sa s /\
  sa0.cs_next_var <= sa.cs_next_var /\
  compile_array_subscript base_op idx_op T cnt ws esz sgn
    (compile_imm_load_word F imm) sa = (op,sb) /\
  fn_has_code sa sb fp.jc_func /\
  (!z. base_op = Var z ==> not_fresh_at sa z) /\
  (!z. idx_op = Var z ==> not_fresh_at sa z) /\
  eval_operand base_op s = SOME b /\ eval_operand idx_op s = SOME i /\
  idx_in_range sgn i (word_of_bytes T (0w:bytes32)
    (TAKE 32 (DROP (w2n b) s.vs_data_section ++ REPLICATE 32 0w))) ==>
  ?t. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK t) /\
    intcall_expr_cont fp ce env es0 sa0 s0 es sb t /\
    eval_operand op t = SOME (b + n2w ws + i * n2w esz) /\
    t.vs_memory = s.vs_memory /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    (!z v. not_fresh_at sa z /\ lookup_var z s = SOME v ==>
       lookup_var z t = SOME v)
Proof
  simp[compile_array_subscript_split, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_imm_load_word F imm base_op sa = (lop,sm)` >>
  `straight_fresh (comp_ignore_bind (array_bounds_check idx_op lop sgn)
      (array_elem_ptr base_op idx_op T ws esz))` by
    simp[straight_fresh_array_check_ptr] >>
  `cs_extends sa sm /\ sa.cs_next_var < sm.cs_next_var /\
   (!z. lop = Var z ==> not_fresh_at sm z)` by
    (qpat_x_assum `compile_imm_load_word _ _ _ _ = _` mp_tac >>
     simp[compile_imm_load_word_runtime] >> strip_tac >>
     drule emit_op_extends >> strip_tac >>
     drule emitted_insts_emit_op >> strip_tac >>
     gvs[not_fresh_at_def] >>
     irule cs_extends_same_block >>
     gvs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND3]) >>
  `cs_extends sm sb` by metis_tac[straight_fresh_cs_extends] >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all intcall_runtime_load_landing >> strip_tac >>
  qmatch_asmsub_abbrev_tac `run_inst_seq _ s = OK t` >>
  `eval_operand base_op t = SOME b /\ eval_operand idx_op t = SOME i` by
    (conj_tac >- (Cases_on `base_op` >>
       gvs[eval_operand_def, venom_state_component_equality]) >>
     Cases_on `idx_op` >> gvs[eval_operand_def, venom_state_component_equality]) >>
  `(!z. base_op = Var z ==> not_fresh_at sm z) /\
   (!z. idx_op = Var z ==> not_fresh_at sm z)` by
    metis_tac[not_fresh_at_mono, arithmeticTheory.LESS_IMP_LESS_OR_EQ] >>
  `sa0.cs_next_var <= sm.cs_next_var` by decide_tac >>
  qmatch_asmsub_abbrev_tac `eval_operand lop t = SOME len` >>
  `eval_operand base_op (t with vs_inst_idx := LENGTH sm.cs_current_insts) = SOME b /\
   eval_operand idx_op (t with vs_inst_idx := LENGTH sm.cs_current_insts) = SOME i /\
   eval_operand lop (t with vs_inst_idx := LENGTH sm.cs_current_insts) = SOME len` by simp[] >>
  drule_all intcall_array_check_ptr_landing >> strip_tac >>
  drule_all gas_marked_path_then >> simp[] >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >>
  fs[venom_state_component_equality] >> rpt strip_tac >>
  `not_fresh_at sm z` by
    (irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  first_x_assum irule >> gvs[lookup_var_def]
QED
