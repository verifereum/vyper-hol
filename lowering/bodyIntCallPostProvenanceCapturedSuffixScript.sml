(* Checked selection from an owned memory snapshot, including dynamic arrays. *)
Theory bodyIntCallPostProvenanceCapturedSuffix
Ancestors
  bodyIntCallPostProvenanceCaptured targetSubscriptMemory
  exprSimSubscriptArraySuffix exprSimSubscriptArrayFramed exprSimHash
  exprLoweringProps emitHelperProps context compileEnv loweringPosts
  venomState venomInst finite_map freshWrites loweringStateRelDefs
  valueEncodingProps valueEncodingDefs exprSimAggregateEncoding exprSimProps
  vyperInterpreter vyperState exprSimSubscriptArraySource vyperValueOperation
  vyperTyping words integer_word valueTypingMemoryProps

Theorem intcall_owned_memory_value_post:
  post_value_type ce e = expr_type e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  val_wf tv v /\ value_has_type tv v /\
  read_result cx raw ee = (INL v,ee) /\
  val_in_memory tv v (w2n w) t.vs_memory /\ eval_operand dst t = SOME w /\
  FLOOKUP t.vs_allocas aid = SOME (b,sz) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  b <= w2n w /\ w2n w + val_footprint tv v <= b + sz /\
  (!n lb lsz. local_region ce ee.scopes t n lb lsz ==>
     b + sz <= lb \/ lb + lsz <= b) /\
  stmt_state_rel ctx func ce cx ee t /\ wb_frame ce es ee sa s0 t /\
  (~expr_has_effect e ==> pure_frame ce func es sa s0 t) ==>
  vv_post ctx func ce cx e es sa sb s0 ee raw
    (LocatedValue (expr_type e) (mk_ptr dst LocMemory)) t /\
  intcall_vv_provenance ce cx (expr_type e) sa sb ee raw
    (LocatedValue (expr_type e) (mk_ptr dst LocMemory)) t
Proof
  strip_tac >> reverse conj_tac
  >- (irule intcall_fresh_selection_provenance >>
      goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  irule vv_post_frame_intro >> simp[mk_ptr_def] >>
  conj_tac
  >- (simp[vv_holds_def, mk_ptr_def] >>
      strip_tac >> irule val_in_memory_word_type >>
      goal_assum (drule_at Any) >> simp[] >>
      qexistsl_tac [`expr_type e`, `get_tenv cx`] >> simp[]) >>
  simp[vv_at_def, mk_ptr_def] >> rpt strip_tac >> gvs[] >>
  disj1_tac >>
  qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem intcall_owned_array_element_post:
  post_value_type ce e = expr_type e /\ expr_type e = et /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  val_wf (ArrayTV etv bd) (ArrayV av) /\ val_wf etv v /\ value_has_type etv v /\
  array_index (ArrayTV etv bd) av i = SOME v /\
  val_in_memory (ArrayTV etv bd) (ArrayV av) (w2n w) t.vs_memory /\
  eval_operand dst t = SOME
    (w + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 32) + Num i * type_memory_size etv)) /\
  FLOOKUP t.vs_allocas aid = SOME (b,sz) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\ b <= w2n w /\
  w2n w + type_memory_size (ArrayTV etv bd) <= b + sz /\ b + sz < dimword (:256) /\
  (!n lb lsz. local_region ce ee.scopes t n lb lsz ==>
     b + sz <= lb \/ lb + lsz <= b) /\
  stmt_state_rel ctx func ce cx ee t /\ wb_frame ce es ee sa s0 t /\
  (~expr_has_effect e ==> pure_frame ce func es sa s0 t) ==>
  vv_post ctx func ce cx e es sa sb s0 ee (Value v)
    (LocatedValue et (mk_ptr dst LocMemory)) t /\
  intcall_vv_provenance ce cx et sa sb ee (Value v)
    (LocatedValue et (mk_ptr dst LocMemory)) t
Proof
  strip_tac >>
  `sub_layout (ArrayTV etv bd) (ArrayV av) 0 (ArrayTV etv bd) (ArrayV av)` by
    simp[sub_layout_def] >>
  drule_all sub_layout_array_element >> simp[] >> strip_tac >>
  qmatch_asmsub_abbrev_tac `sub_layout _ _ j etv v` >>
  `j + type_memory_size etv <= type_memory_size (ArrayTV etv bd)` by
    gvs[sub_layout_def] >>
  `w2n (w + n2w j) = w2n w + j` by
    (irule exprSimAttributePropsTheory.field_ptr_w2n >>
     qexistsl_tac [`0`, `type_memory_size (ArrayTV etv bd)`] >>
     simp[] >> gvs[]) >>
  `val_in_memory etv v (w2n (w + n2w j)) t.vs_memory` by
    (gvs[sub_layout_def] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `val_footprint etv v <= type_memory_size etv` by simp[val_footprint_le] >>
  qpat_assum `expr_type e = et` (fn th => rewrite_tac[GSYM th]) >>
  irule intcall_owned_memory_value_post >>
  goal_assum (drule_at Any) >>
  simp[read_result_def, return_def] >>
  qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >>
  conj_tac >- first_assum ACCEPT_TAC >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem intcall_captured_array_suffix_summary:
  post_value_type ce e = expr_type e /\ expr_type e = et /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  val_wf (ArrayTV etv bd) (ArrayV av) /\ value_has_type (ArrayTV etv bd) (ArrayV av) /\
  val_in_memory (ArrayTV etv bd) (ArrayV av) (w2n w) s.vs_memory /\
  array_length (ArrayTV etv bd) av < dimword (:256) /\
  (!al. av = SArrayV al ==> ?n. bd = Fixed n) /\
  compile_array_subscript base_op idx
    (case bd of Fixed _ => F | Dynamic _ => T)
    (case bd of Fixed n => n | Dynamic _ => 0) 32 (type_memory_size etv) sgn
    (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca LocMemory) sm = (dst,sb) /\
  fn_has_code sm sb func /\ local_ptrs_reserved ce sm /\
  (!z. base_op = Var z ==> not_fresh_at sm z) /\ (!l. base_op <> Label l) /\
  (!z. idx = Var z ==> not_fresh_at sm z) /\ (!l. idx <> Label l) /\
  eval_operand base_op s = SOME w /\ eval_operand idx s = SOME iw /\
  i = (if sgn then w2i iw else &(w2n iw)) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\ ee.gas_obs = [] /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\ b <= w2n w /\
  w2n w + type_memory_size (ArrayTV etv bd) <= b + sz /\ b + sz < dimword (:256) /\
  (!n lb lsz. local_region ce ee.scopes s n lb lsz ==>
     b + sz <= lb \/ lb + lsz <= b) /\
  stmt_state_rel ctx func ce cx ee s /\ wb_frame ce es ee sa s0 s /\
  sa.cs_next_var <= sm.cs_next_var /\
  (~expr_has_effect e ==> pure_frame ce func es sa s0 s) ==>
  gas_summary_at F (ctx,func) []
    (select_result cx (ArrayT et bd) (Value (ArrayV av)) (ValueSubscript (IntV i))) (ee,s)
    (\res ee' t. ?child. res = INL child /\
      vv_post ctx func ce cx e es sa sb s0 ee' child
        (LocatedValue et (mk_ptr dst LocMemory)) t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      intcall_vv_provenance ce cx et sa sb ee' child
        (LocatedValue et (mk_ptr dst LocMemory)) t)
    (\res ee' outcome. expr_exit res outcome)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `n2w (array_length (ArrayTV etv bd) av) =
    (if (case bd of Fixed _ => F | Dynamic _ => T) then mload (w2n w) s
     else n2w (case bd of Fixed n => n | Dynamic _ => 0))` by
    (Cases_on `bd`
     >- (Cases_on `av` >> gvs[vyperTypingTheory.value_has_type_def,
           vyperValueOperationTheory.array_length_def]) >>
     drule_all target_memory_array_header >> simp[]) >>
  drule_all array_index_word_bounds >> strip_tac >>
  Cases_on `valid_index (ArrayTV etv bd) av i`
  >- suspend "success" >>
  drule_all evaluate_array_subscript_oob >> strip_tac >>
  `select_result cx (ArrayT et bd) (Value (ArrayV av)) (ValueSubscript (IntV i)) ee =
    (INR (Error (RuntimeError "evaluate_subscripts array_index")),ee)` by
    (drule select_value_result >> simp[bind_def, lift_sum_def, raise_def]) >>
  `~idx_in_range sgn iw (if (case bd of Fixed _ => F | Dynamic _ => T)
    then mload (w2n w) s else n2w (case bd of Fixed n => n | Dynamic _ => 0))` by metis_tac[] >>
  drule_all target_memory_array_abort_path >>
  strip_tac >>
  irule select_result_counted_summary >> simp[] >>
  goal_assum (drule_at Any) >>
  simp[exprSimDefsTheory.expr_exit_def, fragExecTheory.exit_result_def]
QED

Resume intcall_captured_array_suffix_summary[success]:
  drule vyperArrayTheory.array_index_valid >> pure_rewrite_tac[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  rename1 `array_index (ArrayTV etv bd) av i = SOME v` >>
  `value_has_type etv v` by metis_tac[vyperAssignPreservesTypeTheory.array_index_has_type,
    vyperTypingTheory.evaluate_type_well_formed] >>
  `val_wf etv v` by metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  `iw = n2w (Num i)` by
    (qpat_x_assum `valid_index _ _ _` mp_tac >> qpat_x_assum `i = _` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `sgn` >>
     simp[integer_wordTheory.w2i_def] >> Cases_on `word_msb iw` >> simp[] >> rw[] >> gvs[]) >>
  `idx_in_range sgn iw (if (case bd of Fixed _ => F | Dynamic _ => T)
    then mload (w2n w) s else n2w (case bd of Fixed n => n | Dynamic _ => 0))` by metis_tac[] >>
  drule_all target_memory_array_path >> strip_tac >>
  qpat_x_assum `i = if _ then _ else _` kall_tac >>
  `wb_frame ce es ee sa s0 t` by
    (irule exprSimWordArgsTheory.wb_frame_readonly_tail >>
     goal_assum (drule_at Any) >> simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  `~expr_has_effect e ==> pure_frame ce func es sa s0 t` by
    (strip_tac >> irule pure_frame_mem_tail >> qexists_tac `s` >> simp[]) >>
  `!n lb lsz. local_region ce ee.scopes t n lb lsz ==> b + sz <= lb \/ lb + lsz <= b` by
    (rpt strip_tac >> qpat_x_assum `!n lb lsz. local_region _ _ s _ _ _ ==> _` irule >>
     qexists_tac `n` >> irule local_region_frame >>
     conj_tac >- (qexists_tac `func` >>
       qpat_x_assum `stmt_state_rel _ _ _ _ _ s` mp_tac >> simp[stmt_state_rel_def, state_rel_def]) >>
     qexistsl_tac [`sm`, `ee.scopes`, `t`] >> simp[]) >>
  `eval_operand dst t = SOME
    (w + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 32) + Num i * type_memory_size etv))` by
    (qpat_x_assum `eval_operand dst t = _` mp_tac >>
     qpat_x_assum `iw = _` (fn th => rewrite_tac[th]) >>
     rpt (pop_assum kall_tac) >> Cases_on `bd` >>
     simp[wordsTheory.word_mul_n2w, GSYM wordsTheory.word_add_n2w,
       wordsTheory.WORD_ADD_ASSOC] >> wordsLib.WORD_DECIDE_TAC) >>
  `vv_post ctx func ce cx e es sa sb s0 ee (Value v) (LocatedValue et (mk_ptr dst LocMemory)) t /\
   intcall_vv_provenance ce cx et sa sb ee (Value v) (LocatedValue et (mk_ptr dst LocMemory)) t` by
    (irule intcall_owned_array_element_post >> goal_assum (drule_at Any) >> simp[] >>
     qexists_tac `aid` >> goal_assum (drule_at Any) >>
     qexistsl_tac [`av`, `bd`, `i`, `w`] >> gvs[]) >>
  `select_result cx (ArrayT et bd) (Value (ArrayV av)) (ValueSubscript (IntV i)) ee = (INL (Value v),ee)` by
    (irule (cj 1 select_value_read) >> goal_assum (drule_at Any) >>
     simp[evaluate_array_subscript_result]) >>
  irule select_result_counted_summary >> simp[] >> goal_assum (drule_at Any) >>
  qexists_tac `t` >> simp[] >>
  `ee with gas_obs := [] = ee` by
    (Cases_on `ee` >> gvs[vyperStateTheory.evaluation_state_component_equality]) >> simp[]
QED

Finalise intcall_captured_array_suffix_summary
