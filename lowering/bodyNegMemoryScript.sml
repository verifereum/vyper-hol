(* Actual Neg opcode suffix; independent of source numeric correctness. *)
Theory bodyNegMemory
Ancestors
  bodyMemoryDefs exprSimUnop bodyFieldMemory emitHelperProps
  fragExecMem instMemFrontier allocaHistoryFragment
  exprLoweringProps emitHelper venomInst venomState words list rich_list
  compileEnv fragExec exprSim valueEncoding vyperValue vyperAST venomExecSemantics
  loweringSlice exprLowering vyperState freshWrites varsExt integer_word

Theorem body_neg_no_ranges_seq[local]:
  !is s. EVERY (\i. !q. inst_mem_below_frontier i q) is ==>
         run_inst_seq_mem_ok is s
Proof
  Induct >> simp[run_inst_seq_mem_ok_def] >> rpt strip_tac >>
  Cases_on `step_inst_base h s` >> simp[]
QED

Theorem body_neg_prefix_mem_ok:
  compile_neg x ty sm = (dst,sn) ==>
  run_inst_seq_mem_ok (emitted_insts sm sn) s
Proof
  strip_tac >> irule body_neg_no_ranges_seq >>
  gvs[compile_neg_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_var_def, fresh_id_def, emit_def,
      emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_APPEND, DROP_LENGTH_TOO_LONG] >>
  rpt strip_tac >> irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem body_neg_emitted:
  compile_neg x ty sm = (dst,sn) ==>
  emitted_insts sm sn =
    [mk_inst sm.cs_next_id SGT [x; Lit (FST (type_bounds ty))]
       ["%" ++ toString sm.cs_next_var];
     mk_inst (sm.cs_next_id + 1) ASSERT [Var ("%" ++ toString sm.cs_next_var)] [];
     mk_inst (sm.cs_next_id + 2) SUB [Lit 0w; x]
       ["%" ++ toString (sm.cs_next_var + 1)]]
Proof
  strip_tac >>
  gvs[compile_neg_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_var_def, fresh_id_def, emit_def,
      emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_APPEND, DROP_LENGTH_TOO_LONG]
QED

Theorem body_neg_straight_fresh[local]:
  straight_fresh (compile_neg x ty)
Proof
  Cases_on `type_bounds ty` >> simp[compile_neg_def] >>
  irule straight_fresh_bind >> conj_tac
  >- (gen_tac >> BETA_TAC >> irule straight_fresh_ignore_bind >>
      simp[straight_fresh_emit_void, straight_fresh_emit_op, fresh_write_op_def]) >>
  simp[straight_fresh_emit_op, fresh_write_op_def]
QED

Theorem body_neg_shape:
  compile_neg x ty sm = (dst,sn) ==>
  sn.cs_blocks = sm.cs_blocks /\ sn.cs_current_bb = sm.cs_current_bb /\
  sn.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sn /\
  sm.cs_next_var <= sn.cs_next_var /\
  writes_fresh sm (emitted_insts sm sn) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             ~is_ext_call_op i.inst_opcode) (emitted_insts sm sn)
Proof
  strip_tac >> mp_tac body_neg_straight_fresh >>
  rewrite_tac[straight_fresh_def] >> disch_then drule >> strip_tac >>
  simp[] >> gvs[writes_fresh_def, EVERY_MEM] >>
  metis_tac[fresh_write_op_simple]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_NEG_PREFIX_MEMORY_AUDIT OK\n"
     else raise Fail "Neg prefix inherited admission"
  end) [body_neg_prefix_mem_ok, body_neg_emitted, body_neg_shape];

Theorem body_neg_history:
  compile_neg x ty sm = (dst,sn) /\ fn_has_code sm sn func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  run_inst_seq (emitted_insts sm sn) s = OK t ==>
  alloca_history func (t with vs_inst_idx := LENGTH sn.cs_current_insts)
Proof
  rpt strip_tac >> drule body_neg_shape >> strip_tac >>
  `(?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sm sn ++ rest) /\
    s.vs_inst_idx + LENGTH (emitted_insts sm sn) = LENGTH sn.cs_current_insts /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sn)` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
     simp[] >> gvs[EVERY_MEM]) >>
  drule_all alloca_history_run_inst_seq >> simp[]
QED

Theorem body_neg_state_post:
  compile_neg x ty sm = (dst,sn) /\
  local_ptrs_reserved cenv sm /\ stmt_state_rel ctx func cenv cx es s /\
  run_inst_seq (emitted_insts sm sn) s = OK q ==>
  stmt_state_rel ctx func cenv cx es q /\
  (!z v. not_fresh_at sm z /\ lookup_var z s = SOME v ==>
         lookup_var z q = SOME v) /\
  q.vs_memory = s.vs_memory /\ q.vs_allocas = s.vs_allocas /\
  q.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> drule body_neg_shape >> strip_tac >>
  drule_all run_inst_seq_writes_fresh >> strip_tac >>
  conj_tac
  >- (qpat_x_assum `q = _` (fn th => once_rewrite_tac[th]) >>
      irule stmt_state_rel_vars_frame >> simp[] >> rpt strip_tac >>
      `not_fresh_at sm p` by
        (gvs[local_ptrs_reserved_def, not_fresh_at_def] >> metis_tac[]) >>
      simp[lookup_var_def]) >>
  qpat_x_assum `q = _` (fn th => once_rewrite_tac[th]) >>
  simp[lookup_var_def]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_NEG_PRESERVATION_MEMORY_AUDIT OK\n"
     else raise Fail "Neg preservation inherited admission"
  end) [body_neg_history, body_neg_state_post];

Theorem body_neg_result:
  compile_neg x ty sm = (dst,sn) ==>
  dst = Var ("%" ++ toString (sm.cs_next_var + 1))
Proof
  strip_tac >>
  gvs[compile_neg_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_var_def, fresh_id_def, emit_def]
QED

Theorem body_neg_old_operand[local]:
  (!z. x = Var z ==> not_fresh_at sm z) ==>
  eval_operand x (update_var ("%" ++ toString sm.cs_next_var) v s) =
  eval_operand x s
Proof
  Cases_on `x` >> simp[eval_operand_def, lookup_var_update_var] >>
  rpt strip_tac >> gvs[not_fresh_at_def] >> metis_tac[]
QED

Theorem body_neg_run:
  compile_neg x ty sm = (dst,sn) /\
  (!z. x = Var z ==> not_fresh_at sm z) /\ eval_operand x s = SOME w ==>
  (word_gt w (FST (type_bounds ty)) ==>
    ?t. run_inst_seq (emitted_insts sm sn) s = OK t /\
        eval_operand dst t = SOME (0w - w)) /\
  (~word_gt w (FST (type_bounds ty)) ==>
    run_inst_seq (emitted_insts sm sn) s =
      Abort Revert_abort (revert_state (set_returndata []
        (update_var ("%" ++ toString sm.cs_next_var) 0w s))))
Proof
  strip_tac >> drule body_neg_emitted >> strip_tac >>
  drule body_neg_result >> strip_tac >>
  `!v. eval_operand x (update_var ("%" ++ toString sm.cs_next_var) v s) = SOME w`
    by (gen_tac >> drule body_neg_old_operand >> simp[]) >>
  `step_inst_base
     (mk_inst sm.cs_next_id SGT [x; Lit (FST (type_bounds ty))]
       ["%" ++ toString sm.cs_next_var]) s =
    OK (update_var ("%" ++ toString sm.cs_next_var)
      (bool_to_word (word_gt w (FST (type_bounds ty)))) s)` by
    (irule step_SGT >> simp[eval_operand_lit]) >>
  `!v. step_inst_base
    (mk_inst (sm.cs_next_id + 2) SUB [Lit 0w; x]
      ["%" ++ toString (sm.cs_next_var + 1)])
    (update_var ("%" ++ toString sm.cs_next_var) v s) =
    OK (update_var ("%" ++ toString (sm.cs_next_var + 1)) (0w - w)
      (update_var ("%" ++ toString sm.cs_next_var) v s))` by
    (gen_tac >> irule step_SUB >> simp[eval_operand_lit]) >>
  gvs[] >> simp[run_inst_seq_def] >>
  conj_tac >> strip_tac >>
  simp[bool_to_word_def, run_inst_seq_def, step_ASSERT_ok, step_ASSERT_revert,
       step_SUB, eval_operand_lit, eval_operand_def, lookup_var_update_var]
QED

Theorem body_neg_frag_mem_at:
  compile_neg x ty sm = (dst,sn) /\ local_ptrs_reserved cenv sm /\
  fn_has_code sm sn func /\ fn_inst_ids_distinct func /\
  (!z. x = Var z ==> not_fresh_at sm z) /\
  (~word_gt w (FST (type_bounds ty)) ==> !q. R (Abort Revert_abort q)) ==>
  frag_exec_mem ctx sm sn
    (\s. s = entry /\ stmt_state_rel ctx func cenv cx es s /\
         eval_operand x s = SOME w /\ alloca_history func s)
    (\s. word_gt w (FST (type_bounds ty)) /\
         stmt_state_rel ctx func cenv cx es s /\
         eval_operand dst s = SOME (0w - w) /\
         (!z v. not_fresh_at sm z /\ lookup_var z entry = SOME v ==>
                lookup_var z s = SOME v) /\
         s.vs_memory = entry.vs_memory /\ s.vs_allocas = entry.vs_allocas /\
         s.vs_alloca_next = entry.vs_alloca_next /\ alloca_history func s) R
Proof
  strip_tac >> drule body_neg_shape >> strip_tac >>
  qabbrev_tac `P = \s. s = entry /\ stmt_state_rel ctx func cenv cx es s /\
    eval_operand x s = SOME w /\ alloca_history func s /\ ~s.vs_halted /\
    s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts` >>
  `frag_exec_mem ctx sm sn P
    (\s. word_gt w (FST (type_bounds ty)) /\
         stmt_state_rel ctx func cenv cx es s /\
         eval_operand dst s = SOME (0w - w) /\
         (!z v. not_fresh_at sm z /\ lookup_var z entry = SOME v ==>
                lookup_var z s = SOME v) /\
         s.vs_memory = entry.vs_memory /\ s.vs_allocas = entry.vs_allocas /\
         s.vs_alloca_next = entry.vs_alloca_next /\ alloca_history func s) R`
    suffices_by (simp[frag_exec_mem_def, Abbr `P`] >> metis_tac[]) >>
  irule frag_exec_mem_run_inst_seq >> simp[IS_PREFIX_APPEND3] >>
  reverse conj_tac >- (gvs[EVERY_MEM] >> metis_tac[]) >>
  gen_tac >> strip_tac >> gvs[Abbr `P`] >>
  conj_tac >- metis_tac[body_neg_prefix_mem_ok] >>
  drule_all body_neg_run >> strip_tac >>
  Cases_on `word_gt w (FST (type_bounds ty))`
  >- (gvs[] >> drule_all body_neg_state_post >> strip_tac >>
      `alloca_inv entry` by gvs[stmt_state_rel_def] >>
      drule_all body_neg_history >> strip_tac >>
      gvs[stmt_state_rel_inst_idx, lookup_var_def, eval_operand_def]) >>
  gvs[] >> disj2_tac >> metis_tac[]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_NEG_EXECUTION_MEMORY_AUDIT OK\n"
     else raise Fail "Neg execution inherited admission"
  end) [body_neg_result, body_neg_run, body_neg_frag_mem_at];
