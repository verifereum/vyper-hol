(* Counted successful array suffix at the resource-preserving endpoint. *)
Theory bodyIntCallFamAggSubscriptArraySuffix
Ancestors
  bodyIntCallFamAggSubscriptArrayRun exprSimSubscriptArraySuffix
  exprOperandVar bodyIntCallJointContract exprSimSubscriptArrayFramed

Theorem intcall_framed_array_valid_suffix:
  ((?ty. vv_location (FST (compile_expr ce ty obj sa)) = SOME LocCode) \/
   (?n. bd = Fixed n)) /\
  expr_body_pre ce fp.jc_cx env (Subscript ann obj idx) es /\
  expr_body_pre ce fp.jc_cx env obj es /\ expr_type obj = ArrayT et bd /\
  post_value_type ce obj = expr_type obj /\
  eval_expr fp.jc_cx obj es = (INL r,t) /\
  ee.scopes = t.scopes /\ ee.immutables = t.immutables /\ ee.gas_obs = [] /\
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) /\
  ((~ce.ce_is_ctor /\ p.ptr_location = LocCode) \/
   ((?n. bd = Fixed n) /\
    (!tv. evaluate_type (get_tenv fp.jc_cx) et = SOME tv ==> dynarray_free tv) /\
    p.ptr_location = LocMemory)) /\
  local_ptrs_reserved ce sc /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sc x) /\
  (!l. p.ptr_operand <> Label l) /\
  (!x. iop = Var x ==> not_fresh_at sc x) /\ (!l. iop <> Label l) /\
  compile_array_subscript p.ptr_operand iop
    (case bd of Fixed _ => F | Dynamic _ => T)
    (case bd of Fixed n => n | Dynamic _ => 0)
    (word_scale p.ptr_location) (elem_size_in_location ce p.ptr_location et)
    (is_signed_type (expr_type idx))
    (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca p.ptr_location) sc = (dst,sd) /\
  fn_has_code sc sd fp.jc_func /\ ~s.vs_halted /\
  s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts /\
  stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx ee s /\
  vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx obj es sa sc s0 ee r
    (LocatedValue (ArrayT et bd) p) s /\
  evaluate_type (get_tenv fp.jc_cx) et = SOME etv /\
  evaluate_type (get_tenv fp.jc_cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  read_result fp.jc_cx r ee = (INL (ArrayV av),ee) /\
  val_wf (ArrayTV etv bd) (ArrayV av) /\
  value_has_type (ArrayTV etv bd) (ArrayV av) /\
  eval_operand p.ptr_operand s = SOME w /\ eval_operand iop s = SOME iw /\
  i = (if is_signed_type (expr_type idx) then w2i iw else &(w2n iw)) /\
  array_length (ArrayTV etv bd) av < dimword (:256) /\
  (!al. av = SArrayV al ==> ?n. bd = Fixed n) /\
  (!q. (!x z. not_fresh_at sc x /\ lookup_var x s = SOME z ==> lookup_var x q = SOME z) /\
       (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
       q.vs_memory = s.vs_memory /\ stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx ee q ==>
       vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx obj es sa sd s0 ee r
         (LocatedValue (ArrayT et bd) p) q) /\
  intcall_frame_ok fp /\ intcall_expr_cont fp ce env es sa s0 ee sc s /\
  sa.cs_next_var <= sc.cs_next_var /\ valid_index (ArrayTV etv bd) av i ==>
  ?q. gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK q) /\
    intcall_expr_cont fp ce env es sa s0 ee sd q /\
    vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx obj es sa sd s0 ee r
      (LocatedValue (ArrayT et bd) p) q /\
    eval_operand p.ptr_operand q = SOME w /\
    eval_operand dst q = SOME (w + n2w
      ((case bd of Fixed _ => 0 | Dynamic _ => 32) + Num i * type_memory_size etv)) /\
    (!x. dst = Var x ==> not_fresh_at sd x)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then assume_tac array_index_word_bounds >>
  `type_memory_bytes ce et = type_memory_size etv` by
    (irule exprSimHypsTheory.expr_sim_inv_memory_size >>
     goal_assum (drule_at Any) >> qexistsl_tac [`env`,`es`] >>
     fs[exprSimHypsDefsTheory.expr_body_pre_def]) >>
  `iw = n2w (Num i)` by
    (qpat_x_assum `valid_index _ _ _` mp_tac >>
     qpat_x_assum `i = _` mp_tac >> rpt (pop_assum kall_tac) >>
     Cases_on `is_signed_type (expr_type idx)` >>
     simp[integer_wordTheory.w2i_def] >>
     Cases_on `word_msb iw` >> simp[] >> rw[] >> gvs[]) >>
  qpat_x_assum `i = _` kall_tac >>
  `!x. dst = Var x ==> not_fresh_at sd x` by
    (drule (cj 3 compiler_subscript_ops_var) >> simp[]) >>
  Cases_on `bd`
  >- suspend "fixed" >>
  suspend "dynamic"
QED

Resume intcall_framed_array_valid_suffix[fixed]:
  `array_length (ArrayTV etv (Fixed n)) av = n` by
    (Cases_on `av` >>
     gvs[vyperTypingTheory.value_has_type_def, vyperValueOperationTheory.array_length_def]) >>
  fs[Excl "valid_index_def"] >>
  drule_all intcall_fixed_array_subscript_landing >> strip_tac >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx ee t'` by
    fs[intcall_expr_cont_def, intcall_expr_res_def] >>
  `vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx obj es sa sd s0 ee r
      (LocatedValue (ArrayT et (Fixed n)) p) t'` by
    (first_x_assum irule >> simp[]) >>
  `eval_operand p.ptr_operand t' = SOME w` by
    (Cases_on `p.ptr_operand` >> gvs[venomStateTheory.eval_operand_def] >>
     first_x_assum irule >> metis_tac[]) >>
  qexists_tac `t'` >>
  gvs[compileEnvTheory.elem_size_in_location_def, compileEnvTheory.is_slot_addressed_def,
      GSYM wordsTheory.word_mul_n2w]
QED

Resume intcall_framed_array_valid_suffix[dynamic]:
  fs[Excl "valid_index_def"] >>
  `immutable_holds ce fp.jc_cx (ArrayT et (Dynamic n)) r w ee s` by
    (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[loweringPostsTheory.vv_post_def, loweringPostsTheory.vv_holds_def]) >>
  drule_all_then assume_tac framed_array_code_length_view >>
  `compile_ptr_load F ce.ce_imm_alloca LocCode = compile_imm_load_word F ce.ce_imm_alloca` by
    simp[FUN_EQ_THM, contextTheory.compile_ptr_load_def] >>
  gvs[Excl "valid_index_def"] >>
  `idx_in_range (is_signed_type (expr_type idx)) (n2w (Num i))
     (word_of_bytes T (0w:bytes32)
       (TAKE 32 (DROP (w2n w) s.vs_data_section ++ REPLICATE 32 0w)))` by simp[] >>
  drule_all intcall_runtime_array_subscript_landing >> strip_tac >>
  `stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx ee t'` by
    fs[intcall_expr_cont_def, intcall_expr_res_def] >>
  `vv_post fp.jc_ctx fp.jc_func ce fp.jc_cx obj es sa sd s0 ee r
      (LocatedValue (ArrayT et (Dynamic n)) p) t'` by
    (first_x_assum irule >> simp[]) >>
  `eval_operand p.ptr_operand t' = SOME w` by
    (Cases_on `p.ptr_operand` >> gvs[venomStateTheory.eval_operand_def] >>
     first_x_assum irule >> metis_tac[]) >>
  qexists_tac `t'` >>
  gvs[compileEnvTheory.elem_size_in_location_def, compileEnvTheory.is_slot_addressed_def,
      compileEnvTheory.word_scale_def, wordsTheory.word_mul_n2w,
      wordsTheory.word_add_n2w, wordsTheory.WORD_ADD_ASSOC] >>
  simp[GSYM wordsTheory.word_add_n2w, wordsTheory.WORD_ADD_ASSOC] >>
  simp[AC wordsTheory.WORD_ADD_ASSOC wordsTheory.WORD_ADD_COMM]
QED

Finalise intcall_framed_array_valid_suffix

(* Failure has no normal endpoint obligations. *)
Theorem intcall_framed_array_invalid_suffix:
  expr_body_pre ce cx env obj es /\ expr_type obj = ArrayT et bd /\
  eval_expr cx obj es = (INL r,t) /\
  ee.scopes = t.scopes /\ ee.immutables = t.immutables /\
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) /\
  ((~ce.ce_is_ctor /\ p.ptr_location = LocCode) \/
   ((?n. bd = Fixed n) /\ p.ptr_location = LocMemory)) /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sc x) /\
  (!x. iop = Var x ==> not_fresh_at sc x) /\
  compile_array_subscript p.ptr_operand iop
    (case bd of Fixed _ => F | Dynamic _ => T)
    (case bd of Fixed n => n | Dynamic _ => 0)
    (word_scale p.ptr_location) (elem_size_in_location ce p.ptr_location et)
    (is_signed_type (expr_type idx))
    (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca p.ptr_location) sc = (dst,sd) /\
  fn_has_code sc sd func /\ ~s.vs_halted /\
  s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts /\
  stmt_state_rel ctx func ce cx ee s /\
  vv_post ctx func ce cx obj es sa sc s0 ee r
    (LocatedValue (ArrayT et bd) p) s /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  read_result cx r ee = (INL (ArrayV av),ee) /\
  value_has_type (ArrayTV etv bd) (ArrayV av) /\
  eval_operand p.ptr_operand s = SOME w /\ eval_operand iop s = SOME iw /\
  i = (if is_signed_type (expr_type idx) then w2i iw else &(w2n iw)) /\
  array_length (ArrayTV etv bd) av < dimword (:256) /\
  (!al. av = SArrayV al ==> ?n. bd = Fixed n) /\
  ~valid_index (ArrayTV etv bd) av i ==>
  gas_summary_at F (ctx,func) []
    (select_result cx (ArrayT et bd) r (ValueSubscript (IntV i))) (ee,s)
    P (\res ee' outcome. expr_exit res outcome)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then assume_tac array_index_word_bounds >>
  drule_all_then assume_tac framed_array_select_error >>
  Cases_on `bd`
  >- suspend "fixed" >>
  suspend "dynamic"
QED

Resume intcall_framed_array_invalid_suffix[fixed]:
  `array_length (ArrayTV etv (Fixed n)) av = n` by
    (Cases_on `av` >>
     gvs[vyperTypingTheory.value_has_type_def, vyperValueOperationTheory.array_length_def]) >>
  fs[Excl "valid_index_def"] >>
  drule_all fixed_array_subscript_counted_oob >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  irule select_result_counted_summary >> simp[] >>
  goal_assum (drule_at Any) >>
  qexists_tac `INR (Error (RuntimeError "evaluate_subscripts array_index"))` >>
  metis_tac[exprSimDefsTheory.expr_exit_def, fragExecTheory.exit_result_def]
QED

Resume intcall_framed_array_invalid_suffix[dynamic]:
  fs[Excl "valid_index_def"] >>
  `immutable_holds ce cx (ArrayT et (Dynamic n)) r w ee s` by
    (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[loweringPostsTheory.vv_post_def, loweringPostsTheory.vv_holds_def]) >>
  drule_all_then assume_tac framed_array_code_length_view >>
  `compile_ptr_load F ce.ce_imm_alloca LocCode = compile_imm_load_word F ce.ce_imm_alloca` by
    simp[FUN_EQ_THM, contextTheory.compile_ptr_load_def] >>
  gvs[Excl "valid_index_def"] >>
  `~idx_in_range (is_signed_type (expr_type idx)) iw
     (word_of_bytes T (0w:bytes32)
       (TAKE 32 (DROP (w2n w) s.vs_data_section ++ REPLICATE 32 0w)))` by simp[] >>
  drule_all runtime_array_subscript_counted_oob >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  irule select_result_counted_summary >> simp[] >>
  goal_assum (drule_at Any) >>
  simp[exprSimDefsTheory.expr_exit_def, fragExecTheory.exit_result_def]
QED

Finalise intcall_framed_array_invalid_suffix
