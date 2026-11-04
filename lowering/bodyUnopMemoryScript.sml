(* Actual Boolean unary suffix execution for recursive body memory proofs. *)
Theory bodyUnopMemory
Ancestors
  bodyMemoryDefs exprSimUnop bodyFieldMemory emitHelperProps
  fragExecMem instMemFrontier allocaHistoryFragment
  exprLoweringProps emitHelper venomInst venomState words list rich_list
  compileEnv fragExec exprSim valueEncoding vyperValue vyperAST venomExecSemantics
  loweringSlice exprLowering vyperState exprSimHyps vyperExprNoControl
  builtinSimple builtinProps freshWrites varsExt vyperTyping vyperValueOperation integer_word
  exprSimOperators

Theorem body_iszero_prefix_mem_ok:
  emit_op ISZERO ops sm = (dst,sn) ==>
  run_inst_seq_mem_ok (emitted_insts sm sn) s
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  simp[run_inst_seq_mem_ok_last] >>
  irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem body_iszero_run:
  emit_op ISZERO [x] sm = (dst,sn) /\ eval_operand x s = SOME w ==>
  run_inst_seq (emitted_insts sm sn) s =
    OK (update_var (STRING #"%" (toString sm.cs_next_var))
                   (bool_to_word (w = 0w)) s)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  simp[run_inst_seq_def] >> drule step_ISZERO >> simp[]
QED

Theorem body_iszero_history:
  emit_op ISZERO ops sm = (dst,sn) /\ fn_has_code sm sn func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  run_inst_seq (emitted_insts sm sn) s = OK t ==>
  alloca_history func (t with vs_inst_idx := LENGTH sn.cs_current_insts)
Proof
  rpt strip_tac >>
  `(?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sm sn ++ rest) /\
    s.vs_inst_idx + LENGTH (emitted_insts sm sn) = LENGTH sn.cs_current_insts /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sn)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def, fresh_id_def, fresh_var_def, emit_def,
         emitted_insts_def, fn_has_code_def, IS_PREFIX_APPEND] >>
     simp[DROP_APPEND, DROP_LENGTH_TOO_LONG, mk_inst_def, is_terminator_def]) >>
  drule_all alloca_history_run_inst_seq >> simp[]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_ISZERO_SUFFIX_MEMORY_AUDIT OK\n"
     else raise Fail "iszero suffix memory inherited admission"
  end) [body_iszero_prefix_mem_ok, body_iszero_run, body_iszero_history];

Theorem body_iszero_state_post:
  emit_op ISZERO [x] sm = (dst,sn) /\ eval_operand x s = SOME w /\
  local_ptrs_reserved cenv sm /\ stmt_state_rel ctx func cenv cx es s ==>
  ?q. run_inst_seq (emitted_insts sm sn) s = OK q /\
      stmt_state_rel ctx func cenv cx es q /\
      eval_operand dst q = SOME (bool_to_word (w = 0w)) /\
      (!z v. not_fresh_at sm z /\ lookup_var z s = SOME v ==>
             lookup_var z q = SOME v) /\
      q.vs_memory = s.vs_memory /\ q.vs_allocas = s.vs_allocas /\
      q.vs_alloca_next = s.vs_alloca_next
Proof
  rpt strip_tac >> drule_all body_iszero_run >> strip_tac >>
  qabbrev_tac `out = STRING #"%" (toString sm.cs_next_var)` >>
  `not_local_ptr cenv es.scopes out` by
    (simp[Abbr `out`] >> irule local_ptrs_reserved_fresh >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  qexists_tac `update_var out (bool_to_word (w = 0w)) s` >>
  simp[Abbr `out`] >> conj_tac
  >- (irule stmt_state_rel_update_var >> simp[]) >>
  `dst = Var (STRING #"%" (toString sm.cs_next_var))` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_var_def, fresh_id_def, emit_def] >>
  gvs[] >>
  simp[eval_operand_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[not_fresh_at_def]
QED

val () =
  let val th = body_iszero_state_post
      val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_ISZERO_STATE_POST_MEMORY_AUDIT OK\n"
     else raise Fail "iszero state post inherited admission"
  end;

Theorem body_iszero_frag_mem_at:
  emit_op ISZERO [x] sm = (dst,sn) /\ local_ptrs_reserved cenv sm /\
  fn_has_code sm sn func /\ fn_inst_ids_distinct func ==>
  frag_exec_mem ctx sm sn
    (\s. s = entry /\ stmt_state_rel ctx func cenv cx es s /\
         eval_operand x s = SOME w /\ alloca_history func s)
    (\s. stmt_state_rel ctx func cenv cx es s /\
         eval_operand dst s = SOME (bool_to_word (w = 0w)) /\
         (!z v. not_fresh_at sm z /\ lookup_var z entry = SOME v ==>
                lookup_var z s = SOME v) /\
         s.vs_memory = entry.vs_memory /\ s.vs_allocas = entry.vs_allocas /\
         s.vs_alloca_next = entry.vs_alloca_next /\ alloca_history func s) R
Proof
  rpt strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  qabbrev_tac `P = \s. s = entry /\ stmt_state_rel ctx func cenv cx es s /\
    eval_operand x s = SOME w /\ alloca_history func s /\ ~s.vs_halted /\
    s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts` >>
  `frag_exec_mem ctx sm sn P
    (\s. stmt_state_rel ctx func cenv cx es s /\
         eval_operand dst s = SOME (bool_to_word (w = 0w)) /\
         (!z v. not_fresh_at sm z /\ lookup_var z entry = SOME v ==>
                lookup_var z s = SOME v) /\
         s.vs_memory = entry.vs_memory /\ s.vs_allocas = entry.vs_allocas /\
         s.vs_alloca_next = entry.vs_alloca_next /\ alloca_history func s) R`
    suffices_by (simp[frag_exec_mem_def, Abbr `P`] >> metis_tac[]) >>
  irule frag_exec_mem_run_inst_seq >> fs[same_blocks_def] >>
  simp[IS_PREFIX_APPEND3, mk_inst_def, is_terminator_def] >>
  gen_tac >> strip_tac >> gvs[Abbr `P`] >>
  conj_tac
  >- (simp[GSYM mk_inst_def, run_inst_seq_mem_ok_last] >>
      irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  disj1_tac >> drule_all body_iszero_state_post >> strip_tac >>
  `alloca_inv entry` by gvs[stmt_state_rel_def] >>
  drule_all body_iszero_history >> strip_tac >>
  qexists_tac `q` >>
  fs[GSYM mk_inst_def, stmt_state_rel_inst_idx, lookup_var_def] >>
  qpat_x_assum `run_inst_seq _ _ = OK q` mp_tac >>
  qpat_x_assum `alloca_history func (q with vs_inst_idx := _)` mp_tac >>
  simp[]
QED

val () =
  let val th = body_iszero_frag_mem_at
      val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_ISZERO_FRAGMENT_MEMORY_AUDIT OK\n"
     else raise Fail "iszero fragment inherited admission"
  end;

Theorem body_not_bool_tail_mem[local]:
  emit_op ISZERO [x] sm = (op,sb) /\ local_ptrs_reserved cenv sm /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  expr_type e = BaseT BoolT /\ sa.cs_next_var <= sm.cs_next_var /\
  expr_post ctx func cenv cx e es sa sm s0 es' (BoolV b) x entry /\
  alloca_history func entry /\ s0.vs_alloca_next <= entry.vs_alloca_next ==>
  frag_exec_mem ctx sm sb (\s. s = entry)
    (\s. expr_post ctx func cenv cx (Builtin (BaseT BoolT) Not [e]) es
           sa sb s0 es' (BoolV (~b)) op s /\
         s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s) R
Proof
  rpt strip_tac >>
  `stmt_state_rel ctx func cenv cx es' entry /\
   eval_operand x entry = SOME (bool_to_word b)` by
    (Cases_on `b` >>
     gvs[expr_post_def, expr_val_rel_def, vyperValueTheory.evaluate_type_def,
         typed_val_to_w256_def, val_to_w256_def, is_word_type_def, bool_to_word_def]) >>
  drule_all body_iszero_frag_mem_at >>
  disch_then (qspecl_then [`bool_to_word b`, `es'`, `entry`, `cx`, `ctx`, `R`] mp_tac) >>
  disch_then (mp_tac o MATCH_MP frag_exec_mem_weaken) >>
  disch_then irule >> simp[] >> rpt strip_tac >>
  irule expr_post_unop >> simp[is_word_type_def] >>
  conj_tac
  >- (Cases_on `b` >>
      gvs[expr_val_rel_def, vyperValueTheory.evaluate_type_def,
          is_word_type_def, typed_val_to_w256_def, val_to_w256_def,
          bool_to_word_def]) >>
  qexistsl_tac [`sm`, `entry`, `BoolV b`, `x`] >> simp[]
QED

Theorem compile_not_bool_sim_mem:
  expr_type e = BaseT BoolT /\
  expr_sim_mem ctx func cenv cx (BaseT BoolT) e es /\
  (!v es1. (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es1) ==>
             ?b. v = BoolV b) ==>
  expr_sim_mem ctx func cenv cx ty (Builtin (BaseT BoolT) Not [e]) es
Proof
  strip_tac >> simp[expr_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  drule lower_value_not >> strip_tac >> gvs[] >>
  `cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var` by
    (drule (cj 2 compile_expr_grows) >> simp[]) >>
  `cs_extends s1 sb` by metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `builtin_args_length_ok Not 1 /\ Not <> Len` by
    simp[vyperContextTheory.builtin_args_length_ok_def] >>
  drule_all eval_expr_unop_cases >> strip_tac
  >- (qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
      disch_then (qspecl_then [`sa`, `s1`, `x`, `INR exc`, `es'`, `s0`] mp_tac) >>
      (impl_tac >- gvs[]) >>
      disch_then (mp_tac o MATCH_MP frag_exec_mem_weaken) >>
      disch_then (qspecl_then
        [`\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\ alloca_history func s`,
         `\s. F`, `expr_exit res`] mp_tac) >>
      (impl_tac >- gvs[]) >> strip_tac >>
      irule frag_exec_mem_exit_prefix >> qexists_tac `s1` >> simp[]) >>
  qpat_x_assum `!v es1. _ ==> ?b. _` drule >> strip_tac >> gvs[] >>
  `unop_result cx (BaseT BoolT) Not [BaseT BoolT] (BoolV b) es' =
   INL (BoolV (~b))` by
    simp[unop_result_def, vyperContextTheory.evaluate_builtin_def] >>
  gvs[] >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`sa`, `s1`, `x`, `INL (BoolV b)`, `es'`, `s0`] mp_tac) >>
  (impl_tac >- simp[expr_res_ok_def]) >>
  disch_then (mp_tac o MATCH_MP frag_exec_mem_pre_exit_c) >>
  disch_then (qspecl_then
    [`\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\ alloca_history func s`,
     `expr_exit (INL (BoolV (~b)))`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (fn th => irule (MATCH_MP frag_exec_mem_then th)) >>
  simp[] >> rpt strip_tac >> gvs[] >>
  irule body_not_bool_tail_mem >> simp[] >> qexists_tac `x` >> simp[]
QED

Theorem body_expr_vv_sim_mem_stack:
  expr_sim_mem ctx func cenv cx ty e es /\
  (!sa. ?t op sb. compile_expr cenv ty e sa = (StackValue t op,sb)) /\
  (!tv es'. eval_expr cx e es = (INL tv,es') ==> ?v. tv = Value v) ==>
  expr_vv_sim_mem ctx func cenv cx ty e es
Proof
  strip_tac >> rw[expr_vv_sim_mem_def] >>
  qpat_x_assum `!sa. ?t op sb. _` (qspec_then `sa` strip_assume_tac) >> gvs[] >>
  `lower_value compile_expr cenv ty e sa = (op,sb)` by
    simp[lower_value_def, comp_bind_def, unwrap_value_def, comp_return_def] >>
  Cases_on `res`
  >- (rename1 `eval_expr cx e es = (INL raw,es')` >>
      `?v. raw = Value v` by metis_tac[] >> gvs[] >>
      qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
      disch_then (qspecl_then [`sa`, `sb`, `op`, `INL v`, `es'`, `s0`] mp_tac) >>
      simp[vyperStateTheory.bind_def, read_result_def,
           vyperStateTheory.return_def, expr_res_ok_def] >>
      strip_tac >> irule frag_exec_mem_conseq >> first_x_assum (irule_at Any) >>
      rpt strip_tac >>
      gvs[expr_post_def, vv_post_def, vv_holds_def, vv_at_def,
          read_result_def, vyperStateTheory.return_def] >>
      first_assum ACCEPT_TAC) >>
  rename1 `eval_expr cx e es = (INR exc,es')` >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`sa`, `sb`, `op`, `INR exc`, `es'`, `s0`] mp_tac) >>
  (impl_tac >- gvs[vyperStateTheory.bind_def, expr_res_ok_def, expr_vv_res_ok_def]) >>
  strip_tac >> irule frag_exec_mem_conseq >> first_x_assum (irule_at Any) >>
  simp[] >> rpt gen_tac >>
  Cases_on `exc` >> Cases_on `r` >> simp[expr_exit_def] >>
  rename1 `Error err` >> Cases_on `err` >> simp[expr_exit_def]
QED

Theorem compile_not_bool_vv_sim_mem:
  expr_type e = BaseT BoolT /\
  expr_sim_mem ctx func cenv cx (BaseT BoolT) e es /\
  (!v es1. (do r <- eval_expr cx e; read_result cx r od) es = (INL v,es1) ==>
             ?b. v = BoolV b) ==>
  expr_vv_sim_mem ctx func cenv cx ty (Builtin (BaseT BoolT) Not [e]) es
Proof
  strip_tac >> irule body_expr_vv_sim_mem_stack >>
  conj_tac >- simp[compile_not_abs_stack] >>
  conj_tac >- metis_tac[eval_expr_builtin_value] >>
  irule compile_not_bool_sim_mem >> simp[]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_NOT_BOOL_COMPOSITION_MEMORY_AUDIT OK\n"
     else raise Fail "Boolean Not composition inherited admission"
  end) [body_not_bool_tail_mem, compile_not_bool_sim_mem,
        body_expr_vv_sim_mem_stack, compile_not_bool_vv_sim_mem];

Theorem body_unop_no_ranges_seq[local]:
  !is s. EVERY (\i. !q. inst_mem_below_frontier i q) is ==>
         run_inst_seq_mem_ok is s
Proof
  Induct >> simp[run_inst_seq_mem_ok_def] >> rpt strip_tac >>
  Cases_on `step_inst_base h s` >> simp[]
QED

Theorem body_abs_prefix_mem_ok:
  compile_builtin_abs x sm = (dst,sn) ==>
  run_inst_seq_mem_ok (emitted_insts sm sn) s
Proof
  strip_tac >> irule body_unop_no_ranges_seq >>
  gvs[builtinSimpleTheory.compile_builtin_abs_def,
      builtinSimpleTheory.compile_select_def,
      comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, fresh_var_def, fresh_id_def, emit_def,
      emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[DROP_APPEND, DROP_LENGTH_TOO_LONG] >>
  rpt strip_tac >> irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem body_abs_shape[local]:
  compile_builtin_abs x sm = (dst,sn) ==>
  sn.cs_blocks = sm.cs_blocks /\ sn.cs_current_bb = sm.cs_current_bb /\
  sn.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sn /\
  sm.cs_next_var <= sn.cs_next_var /\
  writes_fresh sm (emitted_insts sm sn) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
             ~is_ext_call_op i.inst_opcode) (emitted_insts sm sn)
Proof
  strip_tac >> mp_tac (Q.SPEC `x` straight_fresh_abs) >>
  rewrite_tac[straight_fresh_def] >> disch_then drule >> strip_tac >>
  simp[] >> gvs[writes_fresh_def, EVERY_MEM] >>
  metis_tac[fresh_write_op_simple]
QED

Theorem body_abs_run[local]:
  compile_builtin_abs x sm = (dst,sn) /\ eval_operand x s = SOME w /\
  (!z. x = Var z ==> not_fresh_at sm z) ==>
  (w <> INT_MINw ==>
   ?q. run_inst_seq (emitted_insts sm sn) s = OK q /\
       eval_operand dst q = SOME (if word_msb w then 0w - w else w)) /\
  (w = INT_MINw ==>
   ?q. run_inst_seq (emitted_insts sm sn) s = Abort Revert_abort q)
Proof
  strip_tac >> drule body_abs_shape >> strip_tac >>
  `eval_operand x (drop_fresh sm s) = SOME w` by
    metis_tac[eval_operand_drop_fresh] >>
  `fresh_vars_wrt sm (drop_fresh sm s)` by simp[fresh_vars_wrt_drop_fresh] >>
  drule_all compile_builtin_abs_run >> strip_tac >>
  `vars_ext_result (run_inst_seq (emitted_insts sm sn) (drop_fresh sm s))
                   (run_inst_seq (emitted_insts sm sn) s)` by
    (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh, EVERY_MEM] >>
     gvs[EVERY_MEM]) >>
  conj_tac >> strip_tac >> gvs[vars_ext_result_def] >>
  gvs[vars_ext_def] >> drule eval_operand_vars_ext >>
  disch_then (qspec_then `dst` mp_tac) >> simp[] >>
  qpat_x_assum `t' = _` (fn th => once_rewrite_tac[th]) >> simp[]
QED

Theorem body_abs_history[local]:
  compile_builtin_abs x sm = (dst,sn) /\ fn_has_code sm sn func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  run_inst_seq (emitted_insts sm sn) s = OK t ==>
  alloca_history func (t with vs_inst_idx := LENGTH sn.cs_current_insts)
Proof
  rpt strip_tac >> drule body_abs_shape >> strip_tac >>
  `(?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sm sn ++ rest) /\
    s.vs_inst_idx + LENGTH (emitted_insts sm sn) = LENGTH sn.cs_current_insts /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sn)` by
    (gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
     simp[] >>
     gvs[EVERY_MEM]) >>
  drule_all alloca_history_run_inst_seq >> simp[]
QED

Theorem body_abs_state_post[local]:
  compile_builtin_abs x sm = (dst,sn) /\
  local_ptrs_reserved cenv sm /\ stmt_state_rel ctx func cenv cx es s /\
  run_inst_seq (emitted_insts sm sn) s = OK q ==>
  stmt_state_rel ctx func cenv cx es q /\
  (!z v. not_fresh_at sm z /\ lookup_var z s = SOME v ==>
         lookup_var z q = SOME v) /\
  q.vs_memory = s.vs_memory /\ q.vs_allocas = s.vs_allocas /\
  q.vs_alloca_next = s.vs_alloca_next
Proof
  strip_tac >> drule body_abs_shape >> strip_tac >>
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

Theorem body_abs_frag_mem_at[local]:
  compile_builtin_abs x sm = (dst,sn) /\ local_ptrs_reserved cenv sm /\
  fn_has_code sm sn func /\ fn_inst_ids_distinct func /\
  (!z. x = Var z ==> not_fresh_at sm z) /\
  (w = INT_MINw ==> !q. R (Abort Revert_abort q)) ==>
  frag_exec_mem ctx sm sn
    (\s. s = entry /\ stmt_state_rel ctx func cenv cx es s /\
         eval_operand x s = SOME w /\ alloca_history func s)
    (\s. w <> INT_MINw /\ stmt_state_rel ctx func cenv cx es s /\
         eval_operand dst s = SOME (if word_msb w then 0w - w else w) /\
         (!z v. not_fresh_at sm z /\ lookup_var z entry = SOME v ==>
                lookup_var z s = SOME v) /\
         s.vs_memory = entry.vs_memory /\ s.vs_allocas = entry.vs_allocas /\
         s.vs_alloca_next = entry.vs_alloca_next /\ alloca_history func s) R
Proof
  strip_tac >> drule body_abs_shape >> strip_tac >>
  qabbrev_tac `P = \s. s = entry /\ stmt_state_rel ctx func cenv cx es s /\
    eval_operand x s = SOME w /\ alloca_history func s /\ ~s.vs_halted /\
    s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts` >>
  `frag_exec_mem ctx sm sn P
    (\s. w <> INT_MINw /\ stmt_state_rel ctx func cenv cx es s /\
         eval_operand dst s = SOME (if word_msb w then 0w - w else w) /\
         (!z v. not_fresh_at sm z /\ lookup_var z entry = SOME v ==>
                lookup_var z s = SOME v) /\
         s.vs_memory = entry.vs_memory /\ s.vs_allocas = entry.vs_allocas /\
         s.vs_alloca_next = entry.vs_alloca_next /\ alloca_history func s) R`
    suffices_by (simp[frag_exec_mem_def, Abbr `P`] >> metis_tac[]) >>
  irule frag_exec_mem_run_inst_seq >> simp[IS_PREFIX_APPEND3] >>
  reverse conj_tac >- (gvs[EVERY_MEM] >> metis_tac[]) >>
  gen_tac >> strip_tac >> gvs[Abbr `P`] >>
  conj_tac >- metis_tac[body_abs_prefix_mem_ok] >>
  drule_all body_abs_run >> strip_tac >>
  Cases_on `w = INT_MINw`
  >- (gvs[] >> disj2_tac >> metis_tac[]) >>
  gvs[] >>
  drule_all body_abs_state_post >> strip_tac >>
  `alloca_inv entry` by gvs[stmt_state_rel_def] >>
  drule_all body_abs_history >> strip_tac >>
  gvs[stmt_state_rel_inst_idx, lookup_var_def, eval_operand_def]
QED

Theorem body_abs_tail_mem[local]:
  compile_builtin_abs x sm = (op,sb) /\ local_ptrs_reserved cenv sm /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!z. x = Var z ==> not_fresh_at sm z) /\
  value_has_type (BaseTV (IntT 256)) v1 /\ expr_type e = BaseT (IntT 256) /\
  sa.cs_next_var <= sm.cs_next_var /\
  expr_post ctx func cenv cx e es sa sm s0 es' v1 x entry /\
  alloca_history func entry /\ s0.vs_alloca_next <= entry.vs_alloca_next /\
  res = unop_result cx (BaseT (IntT 256)) Abs [expr_type e] v1 es' ==>
  frag_exec_mem ctx sm sb (\s. s = entry)
    (\s. ?v. res = INL v /\
         expr_post ctx func cenv cx (Builtin (BaseT (IntT 256)) Abs [e]) es
           sa sb s0 es' v op s /\
         s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s)
    (expr_exit res)
Proof
  strip_tac >> Cases_on `v1` >> gvs[value_has_type_def] >>
  rename1 `within_int_bound _ i` >>
  drule int256_abs_bound >> strip_tac >> drule_all abs_i2w >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es' entry /\
   eval_operand x entry = SOME (integer_word$i2w i : bytes32)` by
    gvs[expr_post_def, expr_val_rel_def, vyperValueTheory.evaluate_type_def,
        typed_val_to_w256_def, val_to_w256_def, is_word_type_def] >>
  `i2w i = (INT_MINw : bytes32) ==>
   !q. expr_exit (unop_result cx (BaseT (IntT 256)) Abs [expr_type e] (IntV i) es')
          (Abort Revert_abort q)` by
    (strip_tac >> gvs[unop_result_def, vyperContextTheory.evaluate_builtin_def,
       vyperASTTheory.type_to_int_bound_def, vyperValueOperationTheory.bounded_int_op_def,
       expr_exit_def]) >>
  drule_all body_abs_frag_mem_at >>
  disch_then (qspecl_then
    [`es'`, `entry`, `cx`, `ctx`] mp_tac) >>
  disch_then (mp_tac o MATCH_MP frag_exec_mem_weaken) >>
  disch_then irule >> simp[] >> rpt strip_tac >>
  Cases_on `i = INT_MIN (:256)`
  >- gvs[unop_result_def, vyperContextTheory.evaluate_builtin_def,
         vyperASTTheory.type_to_int_bound_def, vyperValueOperationTheory.bounded_int_op_def] >>
  simp[unop_result_def, vyperContextTheory.evaluate_builtin_def,
       vyperASTTheory.type_to_int_bound_def, vyperValueOperationTheory.bounded_int_op_def] >>
  irule expr_post_unop >> simp[is_word_type_def] >>
  conj_tac
  >- gvs[expr_val_rel_def, vyperValueTheory.evaluate_type_def,
         typed_val_to_w256_def, val_to_w256_def, is_word_type_def] >>
  qexistsl_tac [`sm`, `entry`, `IntV i`, `x`] >> simp[]
QED

Theorem compile_abs_sim_mem:
  expr_type e = BaseT (IntT 256) /\ expr_body_pre cenv cx env e es /\
  expr_sim_mem ctx func cenv cx ty e es ==>
  expr_sim_mem ctx func cenv cx ty (Builtin (BaseT (IntT 256)) Abs [e]) es
Proof
  strip_tac >> simp[expr_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  drule lower_value_abs >> strip_tac >>
  `cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var /\
   (!z. x = Var z ==> not_fresh_at s1 z)` by
    (drule expr_body_pre_lower_value_word_shape >>
     disch_then drule >> simp[is_word_type_def]) >>
  `cs_extends s1 sb` by
    (drule_at Any straight_fresh_cs_extends >> simp[straight_fresh_abs]) >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `builtin_args_length_ok Abs 1 /\ Abs <> Len` by
    simp[vyperContextTheory.builtin_args_length_ok_def] >>
  drule_all eval_expr_unop_cases >> strip_tac
  >- (qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
      disch_then (qspecl_then [`sa`, `s1`, `x`, `INR exc`, `es'`, `s0`] mp_tac) >>
      (impl_tac >- gvs[]) >>
      disch_then (mp_tac o MATCH_MP frag_exec_mem_weaken) >>
      disch_then (qspecl_then
        [`\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\ alloca_history func s`,
         `\s. F`, `expr_exit res`] mp_tac) >>
      (impl_tac >- gvs[]) >> strip_tac >>
      irule frag_exec_mem_exit_prefix >> qexists_tac `s1` >> simp[]) >>
  `value_has_type (BaseTV (IntT 256)) v1` by
    (drule expr_body_pre_word_value >>
     simp[is_word_type_def, vyperValueTheory.evaluate_type_def]) >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`sa`, `s1`, `x`, `INL v1`, `es'`, `s0`] mp_tac) >>
  (impl_tac >- simp[expr_res_ok_def]) >>
  disch_then (mp_tac o MATCH_MP frag_exec_mem_pre_exit_c) >>
  disch_then (qspecl_then
    [`\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\ alloca_history func s`,
     `expr_exit res`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (fn th => irule (MATCH_MP frag_exec_mem_then th)) >>
  simp[] >> rpt strip_tac >> gvs[] >>
  irule body_abs_tail_mem >> simp[] >> qexistsl_tac [`v1`, `x`] >> simp[]
QED

Theorem compile_abs_vv_sim_mem:
  expr_type e = BaseT (IntT 256) /\ expr_body_pre cenv cx env e es /\
  expr_sim_mem ctx func cenv cx ty e es ==>
  expr_vv_sim_mem ctx func cenv cx ty (Builtin (BaseT (IntT 256)) Abs [e]) es
Proof
  strip_tac >> irule body_expr_vv_sim_mem_stack >>
  conj_tac >- simp[compile_not_abs_stack] >>
  conj_tac >- metis_tac[eval_expr_builtin_value] >>
  irule compile_abs_sim_mem >> simp[] >> qexists_tac `env` >> simp[]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_ABS_MEMORY_AUDIT OK\n"
     else raise Fail "Abs memory inherited admission"
  end) [body_abs_prefix_mem_ok, body_abs_shape, body_abs_run,
        body_abs_history, body_abs_state_post, body_abs_frag_mem_at,
        body_abs_tail_mem, compile_abs_sim_mem, compile_abs_vv_sim_mem];

Theorem body_not_prefix_mem_ok:
  emit_op NOT ops sm = (dst,sn) ==>
  run_inst_seq_mem_ok (emitted_insts sm sn) s
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  simp[run_inst_seq_mem_ok_last] >>
  irule below_frontier_no_ranges >> simp[mk_inst_def]
QED

Theorem body_not_run:
  emit_op NOT [x] sm = (dst,sn) /\ eval_operand x s = SOME w ==>
  run_inst_seq (emitted_insts sm sn) s =
    OK (update_var (STRING #"%" (toString sm.cs_next_var)) (word_1comp w) s)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  simp[run_inst_seq_def] >> drule step_NOT >> simp[]
QED

Theorem body_not_history:
  emit_op NOT ops sm = (dst,sn) /\ fn_has_code sm sn func /\
  fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  run_inst_seq (emitted_insts sm sn) s = OK t ==>
  alloca_history func (t with vs_inst_idx := LENGTH sn.cs_current_insts)
Proof
  rpt strip_tac >>
  `(?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sm sn ++ rest) /\
    s.vs_inst_idx + LENGTH (emitted_insts sm sn) = LENGTH sn.cs_current_insts /\
    EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sm sn)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def,
         comp_return_def, fresh_id_def, fresh_var_def, emit_def,
         emitted_insts_def, fn_has_code_def, IS_PREFIX_APPEND] >>
     simp[DROP_APPEND, DROP_LENGTH_TOO_LONG, mk_inst_def, is_terminator_def]) >>
  drule_all alloca_history_run_inst_seq >> simp[]
QED

Theorem body_not_state_post:
  emit_op NOT [x] sm = (dst,sn) /\ eval_operand x s = SOME w /\
  local_ptrs_reserved cenv sm /\ stmt_state_rel ctx func cenv cx es s ==>
  ?q. run_inst_seq (emitted_insts sm sn) s = OK q /\
      stmt_state_rel ctx func cenv cx es q /\
      eval_operand dst q = SOME (word_1comp w) /\
      (!z v. not_fresh_at sm z /\ lookup_var z s = SOME v ==>
             lookup_var z q = SOME v) /\
      q.vs_memory = s.vs_memory /\ q.vs_allocas = s.vs_allocas /\
      q.vs_alloca_next = s.vs_alloca_next
Proof
  rpt strip_tac >> drule_all body_not_run >> strip_tac >>
  qabbrev_tac `out = STRING #"%" (toString sm.cs_next_var)` >>
  `not_local_ptr cenv es.scopes out` by
    (simp[Abbr `out`] >> irule local_ptrs_reserved_fresh >>
     metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  qexists_tac `update_var out (word_1comp w) s` >>
  simp[Abbr `out`] >> conj_tac
  >- (irule stmt_state_rel_update_var >> simp[]) >>
  `dst = Var (STRING #"%" (toString sm.cs_next_var))` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_var_def, fresh_id_def, emit_def] >>
  gvs[] >>
  simp[eval_operand_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[not_fresh_at_def]
QED

Theorem body_not_frag_mem_at:
  emit_op NOT [x] sm = (dst,sn) /\ local_ptrs_reserved cenv sm /\
  fn_has_code sm sn func /\ fn_inst_ids_distinct func ==>
  frag_exec_mem ctx sm sn
    (\s. s = entry /\ stmt_state_rel ctx func cenv cx es s /\
         eval_operand x s = SOME w /\ alloca_history func s)
    (\s. stmt_state_rel ctx func cenv cx es s /\
         eval_operand dst s = SOME (word_1comp w) /\
         (!z v. not_fresh_at sm z /\ lookup_var z entry = SOME v ==>
                lookup_var z s = SOME v) /\
         s.vs_memory = entry.vs_memory /\ s.vs_allocas = entry.vs_allocas /\
         s.vs_alloca_next = entry.vs_alloca_next /\ alloca_history func s) R
Proof
  rpt strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  qabbrev_tac `P = \s. s = entry /\ stmt_state_rel ctx func cenv cx es s /\
    eval_operand x s = SOME w /\ alloca_history func s /\ ~s.vs_halted /\
    s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts` >>
  `frag_exec_mem ctx sm sn P
    (\s. stmt_state_rel ctx func cenv cx es s /\
         eval_operand dst s = SOME (word_1comp w) /\
         (!z v. not_fresh_at sm z /\ lookup_var z entry = SOME v ==>
                lookup_var z s = SOME v) /\
         s.vs_memory = entry.vs_memory /\ s.vs_allocas = entry.vs_allocas /\
         s.vs_alloca_next = entry.vs_alloca_next /\ alloca_history func s) R`
    suffices_by (simp[frag_exec_mem_def, Abbr `P`] >> metis_tac[]) >>
  irule frag_exec_mem_run_inst_seq >> fs[same_blocks_def] >>
  simp[IS_PREFIX_APPEND3, mk_inst_def, is_terminator_def] >>
  gen_tac >> strip_tac >> gvs[Abbr `P`] >>
  conj_tac
  >- (simp[GSYM mk_inst_def, run_inst_seq_mem_ok_last] >>
      irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  disj1_tac >> drule_all body_not_state_post >> strip_tac >>
  `alloca_inv entry` by gvs[stmt_state_rel_def] >>
  drule_all body_not_history >> strip_tac >>
  qexists_tac `q` >>
  fs[GSYM mk_inst_def, stmt_state_rel_inst_idx, lookup_var_def] >>
  qpat_x_assum `run_inst_seq _ _ = OK q` mp_tac >>
  qpat_x_assum `alloca_history func (q with vs_inst_idx := _)` mp_tac >>
  simp[]
QED

Theorem body_not_uint256_tail_mem[local]:
  emit_op NOT [x] sm = (op,sb) /\ local_ptrs_reserved cenv sm /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  value_has_type (BaseTV (UintT 256)) v1 /\ expr_type e = BaseT (UintT 256) /\
  sa.cs_next_var <= sm.cs_next_var /\
  expr_post ctx func cenv cx e es sa sm s0 es' v1 x entry /\
  alloca_history func entry /\ s0.vs_alloca_next <= entry.vs_alloca_next /\
  res = unop_result cx (BaseT (UintT 256)) Not [expr_type e] v1 es' ==>
  frag_exec_mem ctx sm sb (\s. s = entry)
    (\s. ?v. res = INL v /\
         expr_post ctx func cenv cx (Builtin (BaseT (UintT 256)) Not [e]) es
           sa sb s0 es' v op s /\
         s0.vs_alloca_next <= s.vs_alloca_next /\ alloca_history func s)
    (expr_exit res)
Proof
  strip_tac >> Cases_on `v1` >> gvs[value_has_type_def] >>
  rename1 `expr_post _ _ _ _ _ _ _ _ _ _ (IntV i) _ _` >>
  `stmt_state_rel ctx func cenv cx es' entry /\
   eval_operand x entry = SOME (integer_word$i2w i : bytes32)` by
    gvs[expr_post_def, expr_val_rel_def, vyperValueTheory.evaluate_type_def,
        typed_val_to_w256_def, val_to_w256_def, is_word_type_def] >>
  drule_all body_not_frag_mem_at >>
  disch_then (qspecl_then
    [`integer_word$i2w i : bytes32`, `es'`, `entry`, `cx`, `ctx`,
     `expr_exit (unop_result cx (BaseT (UintT 256)) Not [expr_type e] (IntV i) es')`] mp_tac) >>
  disch_then (mp_tac o MATCH_MP frag_exec_mem_weaken) >>
  disch_then irule >> simp[] >> rpt strip_tac >>
  gvs[unop_result_def, vyperContextTheory.evaluate_builtin_def,
       vyperASTTheory.type_to_int_bound_def, expr_exit_def] >>
  irule expr_post_unop >> simp[is_word_type_def] >>
  conj_tac
  >- (gvs[expr_val_rel_def, vyperValueTheory.evaluate_type_def,
          typed_val_to_w256_def, val_to_w256_def, is_word_type_def] >>
      `~(i < 0)` by intLib.ARITH_TAC >>
      simp[integer_wordTheory.i2w_pos, integer_wordTheory.i2w_def]) >>
  qexistsl_tac [`sm`, `entry`, `IntV i`, `x`] >> simp[]
QED

Theorem compile_not_uint256_sim_mem:
  is_uint256_type (expr_type e) /\ expr_body_pre cenv cx env e es /\
  expr_sim_mem ctx func cenv cx (expr_type e) e es ==>
  expr_sim_mem ctx func cenv cx ty (Builtin (expr_type e) Not [e]) es
Proof
  strip_tac >>
  `expr_type e = BaseT (UintT 256)` by
    (Cases_on `expr_type e` >> gvs[] >> rename1 `BaseT bt` >> Cases_on `bt` >> gvs[]) >>
  simp[expr_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  drule lower_value_not >> strip_tac >>
  gvs[compile_invert_def] >>
  `cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var /\
   (!z. x = Var z ==> not_fresh_at s1 z)` by
    (drule expr_body_pre_lower_value_word_shape >>
     disch_then drule >> simp[is_word_type_def]) >>
  `cs_extends s1 sb` by metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `builtin_args_length_ok Not 1 /\ Not <> Len` by
    simp[vyperContextTheory.builtin_args_length_ok_def] >>
  drule_all eval_expr_unop_cases >> strip_tac
  >- (qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
      disch_then (qspecl_then [`sa`, `s1`, `x`, `INR exc`, `es'`, `s0`] mp_tac) >>
      (impl_tac >- gvs[]) >>
      disch_then (mp_tac o MATCH_MP frag_exec_mem_weaken) >>
      disch_then (qspecl_then
        [`\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\ alloca_history func s`,
         `\s. F`, `expr_exit res`] mp_tac) >>
      (impl_tac >- gvs[]) >> strip_tac >>
      irule frag_exec_mem_exit_prefix >> qexists_tac `s1` >> simp[]) >>
  `value_has_type (BaseTV (UintT 256)) v1` by
    (drule expr_body_pre_word_value >>
     simp[is_word_type_def, vyperValueTheory.evaluate_type_def]) >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`sa`, `s1`, `x`, `INL v1`, `es'`, `s0`] mp_tac) >>
  (impl_tac >- simp[expr_res_ok_def]) >>
  disch_then (mp_tac o MATCH_MP frag_exec_mem_pre_exit_c) >>
  disch_then (qspecl_then
    [`\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s /\ alloca_history func s`,
     `expr_exit res`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (fn th => irule (MATCH_MP frag_exec_mem_then th)) >>
  simp[] >> rpt strip_tac >> gvs[] >>
  irule body_not_uint256_tail_mem >> simp[] >> qexistsl_tac [`v1`, `x`] >> simp[]
QED

Theorem compile_not_uint256_vv_sim_mem:
  is_uint256_type (expr_type e) /\ expr_body_pre cenv cx env e es /\
  expr_sim_mem ctx func cenv cx (expr_type e) e es ==>
  expr_vv_sim_mem ctx func cenv cx ty (Builtin (expr_type e) Not [e]) es
Proof
  strip_tac >> irule body_expr_vv_sim_mem_stack >>
  conj_tac >- simp[compile_not_abs_stack] >>
  conj_tac >- metis_tac[eval_expr_builtin_value] >>
  irule compile_not_uint256_sim_mem >> simp[] >> qexists_tac `env` >> simp[]
QED

val () = List.app (fn th =>
  let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "BODY_NOT_UINT256_MEMORY_AUDIT OK\n"
     else raise Fail "uint256 Not memory inherited admission"
  end) [body_not_prefix_mem_ok, body_not_run, body_not_history,
        body_not_state_post, body_not_frag_mem_at, body_not_uint256_tail_mem,
        compile_not_uint256_sim_mem, compile_not_uint256_vv_sim_mem];
