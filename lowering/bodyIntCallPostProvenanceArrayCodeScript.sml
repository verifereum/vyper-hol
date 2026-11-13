(* Immutable array header observations in constructor and runtime modes. *)
Theory bodyIntCallPostProvenanceArrayCode
Ancestors
  bodyIntCallPostProvenanceArrayImmutableFrame exprSimSubscriptArraySuffix
  bodyIntCallHeldImmutableWord targetSubscriptMemory immutableCopyExecution
  context emitHelper compileEnv exprLoweringProps loweringStateRelDefs
  bodyPtrSignedConvertSourceFrame venomState exprSimCopy
  freshWrites exprBopSimProps fragGasMode exprSimArrayIndex exprSimUnopProps fragExec

Theorem immutable_array_length_read:
  stmt_state_rel ctx fn ce cx es s /\
  immutable_holds ce cx (ArrayT et (Dynamic cap)) r w es s /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  read_result cx r es = (INL (ArrayV av),es) /\
  value_has_type (ArrayTV etv (Dynamic cap)) (ArrayV av) ==>
  immutable_copy_read ce.ce_is_ctor w s =
    n2w (array_length (ArrayTV etv (Dynamic cap)) av)
Proof
  strip_tac >> Cases_on `ce.ce_is_ctor`
  >- (drule_all immutable_holds_ctor_memory >> strip_tac >>
      gvs[vyperValueTheory.evaluate_type_def] >>
      drule_all target_memory_array_header >>
      simp[immutable_copy_read_def]) >>
  drule_all framed_array_code_length_view >>
  simp[immutable_copy_read_def]
QED

Theorem immutable_loader_compile[local]:
  compile_imm_load_word ctor imm src sa = (dst,sb) ==>
  cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
  (!x. dst = Var x ==> not_fresh_at sb x)
Proof
  Cases_on `ctor` >> Cases_on `imm` >>
  simp[contextTheory.compile_imm_load_word_def, emit_op_def, comp_bind_def,
       fresh_var_def, fresh_id_def, comp_ignore_bind_def, comp_return_def,
       emit_def] >>
  strip_tac >> gvs[cs_extends_def, not_fresh_at_def,
                   rich_listTheory.IS_PREFIX_APPEND] >> simp[]
QED

Theorem immutable_loader_landing[local]:
  compile_imm_load_word ce.ce_is_ctor ce.ce_imm_alloca src sa = (op,sb) /\
  copy_old_operand sa src /\ eval_operand src s = SOME b /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sa /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    eval_operand op t = SOME (immutable_copy_read ce.ce_is_ctor b s) /\
    stmt_state_rel ctx func ce cx es t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x v. not_fresh_at sa x /\ lookup_var x s = SOME v ==>
           lookup_var x t = SOME v) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas
Proof
  strip_tac >> drule_all held_immutable_word_load_path >> strip_tac >>
  `t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|>` by
    gvs[venom_state_component_equality] >>
  `stmt_state_rel ctx func ce cx es t` by
    (irule stmt_state_rel_readonly_vars_pc >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  qexists `t` >> simp[] >> gvs[venom_state_component_equality]
QED

Theorem code_dynamic_array_path[local]:
  compile_imm_load_word ce.ce_is_ctor ce.ce_imm_alloca base_op sa = (len_op,sm) /\
  comp_ignore_bind (array_bounds_check idx_op len_op sgn)
    (array_elem_ptr base_op idx_op T ws esz) sm = (dst,sb) /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  local_ptrs_reserved ce sa /\ stmt_state_rel ctx func ce cx es s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. base_op = Var x ==> not_fresh_at sa x) /\
  (!x. idx_op = Var x ==> not_fresh_at sa x) /\
  (!l. base_op <> Label l) /\ (!l. idx_op <> Label l) /\
  eval_operand base_op s = SOME b /\ eval_operand idx_op s = SOME i /\
  idx_in_range sgn i (immutable_copy_read ce.ce_is_ctor b s) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    eval_operand dst t = SOME (b + n2w ws + i * n2w esz) /\
    stmt_state_rel ctx func ce cx es t /\
    (!x v. not_fresh_at sa x /\ lookup_var x s = SOME v ==> lookup_var x t = SOME v) /\
    (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==> FLOOKUP t.vs_allocas aid = SOME a) /\
    t.vs_memory = s.vs_memory /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> drule immutable_loader_compile >> strip_tac >>
  `local_ptrs_reserved ce sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!x. base_op = Var x ==> not_fresh_at sm x) /\
   (!x. idx_op = Var x ==> not_fresh_at sm x)` by metis_tac[not_fresh_at_mono] >>
  `copy_old_operand sa base_op` by simp[copy_old_operand_def] >>
  drule_all immutable_loader_landing >> strip_tac >>
  `eval_operand base_op t = SOME b /\ eval_operand idx_op t = SOME i` by
    (conj_tac >> irule eval_operand_frame >> simp[] >> qexistsl [`sa`,`s`] >> simp[]) >>
  drule_all target_array_check_ptr_path >> strip_tac >>
  qexists `t'` >> conj_tac
  >- (qpat_x_assum `gas_marked_path F ctx func s 0 (OK t)` mp_tac >>
      qpat_x_assum `gas_marked_path F ctx func t 0 (OK t')` mp_tac >>
      metis_tac[gas_marked_path_then, arithmeticTheory.ADD_CLAUSES]) >>
  simp[] >> rpt strip_tac >>
  `not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >> metis_tac[]
QED

Theorem code_dynamic_array_abort_path[local]:
  compile_imm_load_word ce.ce_is_ctor ce.ce_imm_alloca base_op sa = (len_op,sm) /\
  comp_ignore_bind (array_bounds_check idx_op len_op sgn)
    (array_elem_ptr base_op idx_op T ws esz) sm = (dst,sb) /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  local_ptrs_reserved ce sa /\ stmt_state_rel ctx func ce cx es s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. base_op = Var x ==> not_fresh_at sa x) /\
  (!x. idx_op = Var x ==> not_fresh_at sa x) /\
  (!l. idx_op <> Label l) /\
  eval_operand base_op s = SOME b /\ eval_operand idx_op s = SOME i /\
  ~idx_in_range sgn i (immutable_copy_read ce.ce_is_ctor b s) ==>
  ?t. gas_marked_path F ctx func s 0 (Abort Revert_abort t)
Proof
  strip_tac >> drule immutable_loader_compile >> strip_tac >>
  `!x. idx_op = Var x ==> not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >>
  `copy_old_operand sa base_op` by simp[copy_old_operand_def] >>
  drule_all immutable_loader_landing >> strip_tac >>
  `eval_operand idx_op t = SOME i` by
    (irule eval_operand_frame >> simp[] >> qexistsl [`sa`,`s`] >> simp[]) >>
  drule_all target_array_check_ptr_abort_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexists `t'` >>
  qpat_x_assum `gas_marked_path F ctx func s 0 (OK t)` mp_tac >>
  qpat_x_assum `gas_marked_path F ctx func t 0 (Abort Revert_abort t')` mp_tac >>
  metis_tac[gas_marked_path_then, arithmeticTheory.ADD_CLAUSES]
QED

Theorem code_array_subscript_path:
  compile_array_subscript base_op idx_op dyn cnt ws esz sgn
    (compile_imm_load_word ce.ce_is_ctor ce.ce_imm_alloca) sa = (dst,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved ce sa /\
  stmt_state_rel ctx func ce cx es s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. base_op = Var x ==> not_fresh_at sa x) /\
  (!x. idx_op = Var x ==> not_fresh_at sa x) /\
  (!l. base_op <> Label l) /\ (!l. idx_op <> Label l) /\
  eval_operand base_op s = SOME b /\ eval_operand idx_op s = SOME i /\
  idx_in_range sgn i (if dyn then immutable_copy_read ce.ce_is_ctor b s else n2w cnt) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    eval_operand dst t = SOME ((if dyn then b + n2w ws else b) + i * n2w esz) /\
    stmt_state_rel ctx func ce cx es t /\
    (!x v. not_fresh_at sa x /\ lookup_var x s = SOME v ==> lookup_var x t = SOME v) /\
    (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==> FLOOKUP t.vs_allocas aid = SOME a) /\
    t.vs_memory = s.vs_memory /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  reverse (Cases_on `dyn`) >>
  simp[compile_array_subscript_split, comp_bind_def, comp_return_def]
  >- (strip_tac >>
      `eval_operand (Lit (n2w cnt)) s = SOME (n2w cnt)` by simp[eval_operand_def] >>
      `!x. Lit (n2w cnt) = Var x ==> not_fresh_at sa x` by simp[] >>
      drule_all target_array_check_ptr_path >> simp[]) >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_imm_load_word _ _ base_op sa = (len_op,sm)` >>
  drule immutable_loader_compile >> strip_tac >>
  `straight_fresh (comp_ignore_bind (array_bounds_check idx_op len_op sgn)
     (array_elem_ptr base_op idx_op T ws esz))` by
    simp[straight_fresh_array_check_ptr] >>
  drule_all straight_fresh_cs_extends >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all code_dynamic_array_path >> simp[]
QED

Theorem code_array_subscript_abort_path:
  compile_array_subscript base_op idx_op dyn cnt ws esz sgn
    (compile_imm_load_word ce.ce_is_ctor ce.ce_imm_alloca) sa = (dst,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved ce sa /\
  stmt_state_rel ctx func ce cx es s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. base_op = Var x ==> not_fresh_at sa x) /\
  (!x. idx_op = Var x ==> not_fresh_at sa x) /\ (!l. idx_op <> Label l) /\
  eval_operand base_op s = SOME b /\ eval_operand idx_op s = SOME i /\
  ~idx_in_range sgn i (if dyn then immutable_copy_read ce.ce_is_ctor b s else n2w cnt) ==>
  ?t. gas_marked_path F ctx func s 0 (Abort Revert_abort t)
Proof
  reverse (Cases_on `dyn`) >>
  simp[compile_array_subscript_split, comp_bind_def, comp_return_def]
  >- (strip_tac >>
      `eval_operand (Lit (n2w cnt)) s = SOME (n2w cnt)` by simp[eval_operand_def] >>
      `!x. Lit (n2w cnt) = Var x ==> not_fresh_at sa x` by simp[] >>
      drule_all target_array_check_ptr_abort_path >> simp[]) >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_imm_load_word _ _ base_op sa = (len_op,sm)` >>
  drule immutable_loader_compile >> strip_tac >>
  `straight_fresh (comp_ignore_bind (array_bounds_check idx_op len_op sgn)
     (array_elem_ptr base_op idx_op T ws esz))` by
    simp[straight_fresh_array_check_ptr] >>
  drule_all straight_fresh_cs_extends >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all code_dynamic_array_abort_path >> simp[]
QED
