(*
 * The exits of the full body induction (bodySimFullMain) that compile to
 * no operand of their own: break, continue, bare and unreachable raise,
 * and the unreachable assertion.  Each target path is one zero-GAS jump,
 * abort, or the condition's joint path followed by them, so the source
 * marks, the target execution, the memory checks and the pointer ghosts
 * share the one witness gas_outcome_full asks for.
 *
 * TOP-LEVEL:
 *   emit_jmp_origin_ptr, emit_jnz_origin_ptr, emit_abort_origin_ptr
 *     -- the emitted control instructions as zero-mark joint paths
 *   compile_loop_jump_frag_full -- break and continue
 *   compile_raise_frag_full     -- bare and unreachable raise
 *   compile_assert_frag_full    -- bare and unreachable assertion
 *   body_break_case_full, body_continue_case_full,
 *   body_raise_bare_case_full, body_raise_unreachable_case_full,
 *   body_assert_unreachable_case_full
 *)
Theory bodyFullExits
Ancestors
  bodyFullPreds bodySimFull gasOutcomeFull fragGasOriginPtr fragGasOriginPtrExec
  fragGasOrigin vyperContext vyperTypeCallGraph gasSummary
  fragGasPathPtr gasShadow gasShadowState bodyPtrDefs bodyMemoryDefs
  stmtSimAssertProps stmtSimIfProps
  stmtSimDefs stmtSimProps exprSimDefs loweringPosts gasContext
  gasExemptCert gasCount gasEvents stmtLowering exprLowering compileEnv
  emitHelper emitHelperProps exprLoweringProps fragExec memSafeRun
  ptrSafeRun ptrDiscipline codegenRel contextCodegenRel instMemFrontier
  unitTransformDefs allocaHistory bodySim rich_list exprSimHyps bodySimStmtCases
  bodyExprPreFacts supportedStmts supportedExprs supportedStmtTraverse
  supportedExprTraverse vyperTypeSystem vyperInterpreter vyperState
  vyperAST venomInst venomState venomExecSemantics venomExecProps list
Libs
  monadsyntax

val _ = Parse.hide "body";

(* ===== Zero-mark joint edges of emitted control instructions ===== *)

(* The gas, memory and pointer facts of one emitted control instruction at
   its block position, as a zero-mark joint edge. *)
val ctrl_edge_tac =
  simp[gas_origin_ptr_edge_def, gas_origin_edge_def, gas_path_ptr_edge_def] >>
  conj_tac >> qexists_tac `0` >> simp[] >> metis_tac[];

Theorem emit_jmp_origin_ptr:
  emit_inst JMP [Label lbl] [] sa = ((), sb) /\ fn_has_code sa sb func /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted ==>
  gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
    (s, G, tn) [] (OK (jump_to lbl s), G, tn)
Proof
  strip_tac >> drule emit_inst_extends >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sa.cs_current_insts) =
    SOME (mk_inst sa.cs_next_id JMP [Label lbl] [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `ptr_safe_step D lo 0 ctx func PG G tn
     (mk_inst sa.cs_next_id JMP [Label lbl] []) s` by
    (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
          mk_inst_def, source_memory_write_ranges_def,
          source_memory_read_ranges_def, op_taint_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke] >>
     simp[mk_inst_def, step_jmp_behavior, jump_to_def]) >>
  qabbrev_tac `i = mk_inst sa.cs_next_id JMP [Label lbl] []` >>
  `!fuel. step_inst fuel ctx i s = OK (jump_to lbl s)` by
    simp[Abbr `i`, step_inst_non_invoke, mk_inst_def, step_jmp_behavior] >>
  `gas_events_step 0 ctx func.fn_name i s = [] /\
   gas_count_step 0 ctx i s = 0 /\ mem_safe_step 0 ctx i s /\
   is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE` by
    simp[Abbr `i`, gas_events_step_def, gas_count_step_def, mk_inst_def,
         mem_safe_step_non_invoke, inst_mem_below_frontier_def,
         inst_dload_in_section_def, source_memory_read_ranges_def,
         source_memory_write_ranges_def, is_terminator_def] >>
  `~(jump_to lbl s).vs_halted` by simp[jump_to_def] >>
  `gas_origin_ptr_edge (D, lo, explicit, ctx, func, PG)
     (s, G, tn) [] (OK (jump_to lbl s), G, tn)` by ctrl_edge_tac >>
  metis_tac[gas_origin_ptr_path_rules, APPEND]
QED

Theorem emit_jnz_origin_ptr:
  emit_inst JNZ [op; Label lt; Label lf] [] sa = ((), sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  eval_operand op s = SOME (if b then 1w else 0w) /\ op_taint tn op = {} /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted ==>
  gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
    (s, G, tn) [] (OK (jump_to (if b then lt else lf) s), G, tn)
Proof
  strip_tac >> drule emit_inst_extends >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sa.cs_current_insts) =
    SOME (mk_inst sa.cs_next_id JNZ [op; Label lt; Label lf] [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `!fuel. step_inst fuel ctx
      (mk_inst sa.cs_next_id JNZ [op; Label lt; Label lf] []) s =
      OK (jump_to (if b then lt else lf) s)` by
    (simp[step_inst_non_invoke, mk_inst_def] >>
     drule step_jnz_behavior >>
     disch_then (qspecl_then [`lt`, `lf`, `sa.cs_next_id`] mp_tac) >>
     simp[mk_inst_def] >> Cases_on `b` >> simp[]) >>
  `ptr_safe_step D lo 0 ctx func PG G tn
     (mk_inst sa.cs_next_id JNZ [op; Label lt; Label lf] []) s` by
    (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
          source_memory_write_ranges_def, source_memory_read_ranges_def,
          mk_inst_def] >>
     simp[GSYM mk_inst_def, jump_to_def] >>
     qx_gen_tac `x` >> Cases_on `x = op` >> gvs[op_taint_def] >>
     Cases_on `x` >> simp[]) >>
  qabbrev_tac `i = mk_inst sa.cs_next_id JNZ [op; Label lt; Label lf] []` >>
  `gas_events_step 0 ctx func.fn_name i s = [] /\
   gas_count_step 0 ctx i s = 0 /\ mem_safe_step 0 ctx i s /\
   is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE` by
    simp[Abbr `i`, gas_events_step_def, gas_count_step_def, mk_inst_def,
         mem_safe_step_non_invoke, inst_mem_below_frontier_def,
         inst_dload_in_section_def, source_memory_read_ranges_def,
         source_memory_write_ranges_def, is_terminator_def] >>
  `~(jump_to (if b then lt else lf) s).vs_halted` by simp[jump_to_def] >>
  `gas_origin_ptr_edge (D, lo, explicit, ctx, func, PG)
     (s, G, tn) [] (OK (jump_to (if b then lt else lf) s), G, tn)` by
    ctrl_edge_tac >>
  metis_tac[gas_origin_ptr_path_rules, APPEND]
QED

(* ptr_inst_ok_abort_zero at any reserved bound. *)
Theorem ptr_inst_ok_abort_at[local]:
  ((opc = REVERT /\ ops = [Lit 0w; Lit 0w]) \/ (opc = INVALID /\ ops = [])) /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s ==>
  ptr_inst_ok D lo fuel ctx fn G tn (mk_inst id opc ops []) s
Proof
  rpt strip_tac >> gvs[]
  >- (qspecl_then [`id`, `s`] strip_assume_tac step_revert_zero >>
      gvs[mk_inst_def, ptr_inst_ok_def, step_inst_non_invoke] >>
      simp[access_ok_def, taint_ok_def, op_taint_def,
           source_memory_write_ranges_def, source_memory_read_ranges_def,
           memory_range_of_operands_def, eval_operand_def,
           about_to_revert_def] >>
      metis_tac[op_taint_def]) >>
  qspecl_then [`id`, `s`] strip_assume_tac step_invalid >>
  gvs[mk_inst_def, ptr_inst_ok_def, step_inst_non_invoke] >>
  simp[access_ok_def, taint_ok_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def]
QED

Theorem emit_abort_origin_ptr:
  emit_inst opc ops [] sa = ((), sb) /\ fn_has_code sa sb func /\
  ((opc = REVERT /\ ops = [Lit 0w; Lit 0w]) \/ (opc = INVALID /\ ops = [])) /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  step_inst_base (mk_inst sa.cs_next_id opc ops []) s = Abort a t ==>
  gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
    (s, G, tn) [] (Abort a t, G, tn)
Proof
  strip_tac >> drule emit_inst_extends >> strip_tac >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sa.cs_current_insts) =
    SOME (mk_inst sa.cs_next_id opc ops [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `ptr_inst_ok D lo 0 ctx func G tn (mk_inst sa.cs_next_id opc ops []) s` by
    (irule ptr_inst_ok_abort_at >> simp[]) >>
  qabbrev_tac `i = mk_inst sa.cs_next_id opc ops []` >>
  `i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS` by
    gvs[Abbr `i`, mk_inst_def] >>
  `ptr_safe_step D lo 0 ctx func PG G tn i s` by
    simp[ptr_safe_step_def] >>
  `!fuel. step_inst fuel ctx i s = Abort a t` by
    simp[step_inst_non_invoke] >>
  `gas_events_step 0 ctx func.fn_name i s = [] /\
   gas_count_step 0 ctx i s = 0 /\ mem_safe_step 0 ctx i s` by
    gvs[Abbr `i`, gas_events_step_def, gas_count_step_def, mk_inst_def,
        mem_safe_step_non_invoke, inst_mem_below_frontier_def,
        inst_dload_in_section_def, source_memory_read_ranges_def,
        source_memory_write_ranges_def, memory_range_of_operands_def,
        eval_operand_def] >>
  irule (cj 3 gas_origin_ptr_path_rules) >> simp[exit_result_def] >>
  simp[gas_origin_ptr_edge_def, gas_origin_edge_def, gas_path_ptr_edge_def] >>
  conj_tac >> qexists_tac `0` >> simp[exit_result_def]
QED

(* ===== Posts at a jump ===== *)

Theorem ghost_inv_at_jump_to[local]:
  ghost_inv_at D lo d cenv cx (es with gas_obs := gs) G tn (jump_to l s) <=>
  ghost_inv_at D lo d cenv cx es G tn s
Proof
  simp[ghost_inv_at_def, jump_to_def, ptr_covers_def, stor_taint_ok_at_def,
       lookup_var_def, allocas_from_def] >>
  Cases_on `d` >> TRY (PairCases_on `x`) >>
  simp[return_buf_ptr_def, ptr_covers_def, lookup_var_def]
QED

(* ===== Break and continue ===== *)

Theorem compile_loop_jump_frag_full:
  !D lo d ctx shadow_ctx PG func shadow_func cx lctx RetQ cenv ty st es.
    (st = Break \/ st = Continue) ==>
    stmt_frag_full (D, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ty st) (stmt_env cenv lctx ty st)
      (eval_stmt cx st) es
Proof
  rpt gen_tac >> disch_then (DISJ_CASES_THEN SUBST_ALL_TAC) >> (
  pure_rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `lctx`
  >- (gvs[gas_admissible_def] >>
      first_x_assum (qspec_then `es.gas_obs` mp_tac) >>
      simp[Once evaluate_def, raise_def, stmt_res_ok_def]) >>
  rename1 `InLoop ex inc` >>
  qmatch_goalsub_abbrev_tac `eval_stmt cx st` >>
  qabbrev_tac `lbl = if st = Break then ex else inc` >>
  qabbrev_tac `exc = if st = Break then BreakException
                     else ContinueException` >>
  `eval_stmt cx st = raise exc` by
    (gvs[Abbr `exc`, Abbr `st`] >> simp[FUN_EQ_THM, Once evaluate_def]) >>
  `cenv' = cenv /\ emit_inst JMP [Label lbl] [] sa = ((), sb)` by
    (qpat_x_assum `stmt_env _ _ _ _ sa = _` mp_tac >>
     gvs[Abbr `lbl`, Abbr `st`] >>
     simp[stmt_env_def, declare_stmt_local_def, comp_ignore_bind_def,
          comp_bind_def, compile_stmt_def, comp_return_def] >>
     pairarg_tac >> simp[]) >>
  `allocas_from lo s0` by fs[ghost_inv_at_def] >>
  drule emit_inst_extends >> strip_tac >>
  `return_buf_frame d cenv sb s0` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`, `sa`, `s0`] >>
     simp[]) >>
  `alloca_history func (jump_to lbl s0)` by
    (irule alloca_history_jump >> qexists_tac `s0` >> simp[jump_to_def]) >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) (jump_to lbl s0)` by
    (simp[stmt_state_rel_jump_to] >> drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`]
       mp_tac) >>
     simp[stmt_state_rel_inst_idx]) >>
  pure_rewrite_tac[gas_outcome_full_def] >>
  qexists_tac `[]` >> disj1_tac >>
  qexistsl_tac [`INR exc`, `es`, `OK (jump_to lbl s0)`, `G0`, `tn0`] >>
  conj_tac >- simp[gas_explicit_def, raise_def] >>
  conj_tac >- (irule emit_jmp_origin_ptr >> simp[] >> metis_tac[]) >>
  disj1_tac >> simp[] >> qexists_tac `cenv` >>
  simp[stmt_lands_def, cenv_top_ext_refl, ghost_inv_at_jump_to,
       return_buf_frame_jump_to] >>
  gvs[Abbr `lbl`, Abbr `exc`, Abbr `st`, jump_to_def, lookup_var_def])
QED

Theorem body_break_case_full:
  !cx. body_stmt_full_ok cx Break
Proof
  rw[body_stmt_full_ok_def, gas_shadow_stmt_def] >>
  irule compile_loop_jump_frag_full >> simp[]
QED

Theorem body_continue_case_full:
  !cx. body_stmt_full_ok cx Continue
Proof
  rw[body_stmt_full_ok_def, gas_shadow_stmt_def] >>
  irule compile_loop_jump_frag_full >> simp[]
QED

(* ===== Raise with no reason ===== *)

Theorem compile_raise_frag_full:
  !D lo d ctx shadow_ctx PG func shadow_func cx lctx RetQ cenv ty rk es.
    (rk = RaiseBare \/ rk = RaiseUnreachable) ==>
    stmt_frag_full (D, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Raise rk)) (stmt_env cenv lctx ty (Raise rk))
      (eval_stmt cx (Raise rk)) es
Proof
  rpt gen_tac >> disch_then (DISJ_CASES_THEN SUBST_ALL_TAC) >> (
  pure_rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ _ sa = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  qmatch_goalsub_abbrev_tac `emit_inst opc ops [] sa` >>
  Cases_on `emit_inst opc ops [] sa` >> rename1 `_ = (u, sm)` >>
  Cases_on `u` >> simp[] >> strip_tac >> gvs[] >>
  fs[markerTheory.Abbrev_def] >>
  `allocas_from lo s0` by fs[ghost_inv_at_def] >>
  pure_rewrite_tac[gas_outcome_full_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[Once evaluate_def, raise_def, gas_explicit_def] >>
  qmatch_goalsub_abbrev_tac `AssertException msg` >>
  fs[markerTheory.Abbrev_def] >>
  `?a t. step_inst_base (mk_inst sa.cs_next_id opc ops []) s0 = Abort a t /\
         expr_exit (INR (AssertException msg) : unit + exception) (Abort a t)` by
    (simp[expr_exit_def] >> metis_tac[step_revert_zero, step_invalid]) >>
  qexistsl_tac [`INR (AssertException msg)`, `es`, `Abort a t`, `G0`, `tn0`] >>
  simp[exit_result_def, stmt_exit_ptr_def] >>
  irule emit_abort_origin_ptr >> simp[] >> metis_tac[])
QED

Theorem body_raise_bare_case_full:
  !cx. body_stmt_full_ok cx (Raise RaiseBare)
Proof
  rw[body_stmt_full_ok_def, gas_shadow_stmt_def,
     gas_shadow_raise_reason_def] >>
  irule compile_raise_frag_full >> simp[]
QED

Theorem body_raise_unreachable_case_full:
  !cx. body_stmt_full_ok cx (Raise RaiseUnreachable)
Proof
  rw[body_stmt_full_ok_def, gas_shadow_stmt_def,
     gas_shadow_raise_reason_def] >>
  irule compile_raise_frag_full >> simp[]
QED

(* ===== Assertion with no reason ===== *)

(* The assertion's suffix after the condition compiles alike on both sides,
   so the shadow condition ends at the same operand and a shadow state. *)
Theorem assert_shadow_prefix[local]:
  fresh_label "assert_ok" s1 = (ok,s2) /\
  fresh_label "assert_fail" s2 = (fl,s3) /\
  emit_inst JNZ [op; Label ok; Label fl] [] s3 = ((),s4) /\
  new_block fl s4 = (s4.cs_current_bb,s5) /\
  emit_inst opc ops [] s5 = ((),s6) /\
  new_block ok s6 = (s6.cs_current_bb,sb) /\
  fresh_label "assert_ok" t1 = (ok',t2) /\
  fresh_label "assert_fail" t2 = (fl',t3) /\
  emit_inst JNZ [op'; Label ok'; Label fl'] [] t3 = ((),t4) /\
  new_block fl' t4 = (t4.cs_current_bb,t5) /\
  emit_inst opc ops [] t5 = ((),t6) /\
  new_block ok' t6 = (t6.cs_current_bb,tb) /\
  gas_shadow_state sb tb ==>
  op' = op /\ gas_shadow_state s1 t1
Proof
  simp[fresh_label_def, emit_inst_def, comp_bind_def, fresh_id_def, emit_def,
       new_block_def] >>
  strip_tac >> gvs[gas_shadow_state_def, gas_shadow_block_def,
    gas_shadow_inst_def, mk_inst_def]
QED

Theorem compile_assert_frag_full:
  !D lo d ctx shadow_ctx PG func shadow_func cx lctx RetQ cenv ty e ak es.
    (ak = AssertBare \/ ak = AssertUnreachable) /\
    expr_type e = BaseT BoolT /\
    expr_sim_full (D, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx (BaseT BoolT) e es ==>
    stmt_frag_full (D, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assert e ak))
      (stmt_env cenv lctx ty (Assert (gas_shadow_expr e) ak))
      (eval_stmt cx (Assert e ak)) es
Proof
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 (DISJ_CASES_THEN SUBST_ALL_TAC)
    strip_assume_tac) >> (
  pure_rewrite_tac[stmt_frag_full_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ (Assert e _) _ = _`
    (mp_then Any mp_tac compile_assert_parts) >> simp[] >> strip_tac >>
  qpat_x_assum `stmt_env _ _ _ (Assert (gas_shadow_expr e) _) _ = _`
    (mp_then Any mp_tac compile_assert_parts) >> simp[] >>
  disch_then (qx_choosel_then [`op'`, `t1`, `ok'`, `t2`, `fl'`, `t3`, `t4`,
    `t5`, `t6`] strip_assume_tac) >>
  drule_all assert_shadow_prefix >> strip_tac >> gvs[] >>
  `cs_extends sa s1 /\ cs_extends shadow_sa t1` by
    metis_tac[compile_expr_grows] >>
  drule_all assert_compiler_code >> strip_tac >>
  qpat_x_assum `cs_extends shadow_sa t1` assume_tac >>
  drule_all assert_compiler_code >> strip_tac >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[assert_expr_admissible] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sa x` by metis_tac[ret_pc_ok_def] >>
  qpat_x_assum `expr_sim_full _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[expr_sim_full_def] >>
  disch_then (qspecl_then [`sa`, `s1`, `shadow_sa`, `t1`, `op`, `s0`, `G0`,
    `tn0`] mp_tac) >>
  simp[] >> strip_tac >>
  qpat_x_assum `gas_outcome_full _ _ (bind _ _) _ _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [gas_outcome_full_def])
  >- suspend "normal"
  >- suspend "exception" >>
  simp[gas_outcome_full_def] >> qexists_tac `marks` >> disj2_tac >>
  metis_tac[assert_expr_exempt])
QED

Resume compile_assert_frag_full[exception]:
  markerLib.RESUME_TAC >> (
  gvs[] >> Cases_on `res` >- gvs[expr_exit_def] >>
  rename1 `expr_exit (INR err) r` >>
  pure_rewrite_tac[gas_outcome_full_def] >>
  qexists_tac `marks` >> disj1_tac >>
  qexistsl_tac [`INR err`, `ee`, `r`, `G'`, `tn'`] >>
  conj_tac
  >- (gen_tac >> simp[eval_assert_bind] >>
      asm_simp_tac (srw_ss()) [Once bind_def]) >>
  simp[] >> disj2_tac >> simp[stmt_exit_ptr_def] >>
  metis_tac[expr_exit_INR_type])
QED

Resume compile_assert_frag_full[normal]:
  markerLib.RESUME_TAC >> (
  gvs[] >>
  `~t.vs_halted` by
    (drule gas_origin_ptr_path_exec >> simp[exit_result_def] >> metis_tac[]) >>
  `?b. v = BoolV b` by
    (qmatch_asmsub_abbrev_tac `eval_stmt cx (Assert e ak)` >>
     Cases_on `eval_stmt cx (Assert e ak)
       (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` >>
     drule_all gas_admissible_result >> strip_tac >>
     drule_at (Pat `eval_stmt _ _ _ = _`) eval_assert_forced_ok >>
     disch_then (qspec_then `lctx` mp_tac) >>
     (impl_tac >- simp[Abbr `ak`]) >> strip_tac >>
     qpat_x_assum `!tail. _ = _` (qspec_then `[]` assume_tac) >>
     gvs[bind_def]) >>
  `eval_operand op t = SOME (if b then 1w else 0w)` by
    gvs[expr_post_def, expr_val_rel_def, evaluate_type_def, is_word_type_def,
        typed_val_to_w256_def, val_to_w256_def] >>
  `op_taint tn' op = {}` by gvs[ptr_val_ok_def] >>
  `allocas_from lo t` by fs[ghost_inv_at_def] >>
  `gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (s0,G0,tn0) marks (OK (jump_to (if b then ok else fl) t),G',tn')` by
    (`gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (t,G',tn') [] (OK (jump_to (if b then ok else fl) t),G',tn')` by
       (irule emit_jnz_origin_ptr >> simp[] >>
        qexistsl_tac [`op`, `s3`, `s4`] >> simp[]) >>
     metis_tac[gas_origin_ptr_path_append, APPEND_NIL]) >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` kall_tac >>
  Cases_on `b`
  >- suspend "true"
  >> suspend "false")
QED

Resume compile_assert_frag_full[true]:
  markerLib.RESUME_TAC >> (
  gvs[] >>
  `sa.cs_next_var <= sb.cs_next_var` by
    gvs[cs_extends_def] >>
  drule assert_success_post_mem >> simp[] >>
  disch_then (qspecl_then [`sb`, `lctx`, `d`] mp_tac) >> simp[] >>
  strip_tac >>
  qabbrev_tac `t' = jump_to sb.cs_current_bb t` >>
  `stmt_state_rel ctx func cenv cx (ee with gas_obs := []) t'` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`t'.vs_gas_readings`, `t'.vs_inst_idx`, `[]`]
       mp_tac) >>
     simp[stmt_state_rel_inst_idx]) >>
  qunabbrev_tac `t'` >>
  pure_rewrite_tac[gas_outcome_full_def] >>
  qexists_tac `marks` >> disj1_tac >>
  qexistsl_tac [`INL ()`, `ee`, `OK (jump_to sb.cs_current_bb t)`, `G'`,
                `tn'`] >>
  conj_tac
  >- (gen_tac >> simp[eval_assert_bind] >>
      asm_simp_tac (srw_ss()) [Once bind_def, return_def]) >>
  simp[] >> disj1_tac >> qexists_tac `cenv` >>
  gvs[ghost_inv_at_jump_to, ghost_kept_at_def])
QED

Resume compile_assert_frag_full[false]:
  markerLib.RESUME_TAC >> (
  gvs[] >>
  qmatch_goalsub_abbrev_tac `eval_stmt cx (Assert e ak)` >>
  qmatch_asmsub_abbrev_tac `emit_inst opc ops [] s5` >>
  `?a u. step_inst_base (mk_inst s5.cs_next_id opc ops [])
      (jump_to fl t) = Abort a u /\
    expr_exit (INR (AssertException
      (if ak = AssertBare then "" else "UNREACHABLE")) : unit + exception)
      (Abort a u)` by
    (simp[Abbr `ak`, Abbr `opc`, Abbr `ops`, expr_exit_def] >>
     metis_tac[step_revert_zero, step_invalid]) >>
  `gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (jump_to fl t,G',tn') [] (Abort a u,G',tn')` by
    (irule emit_abort_origin_ptr >>
     simp[jump_to_def, Abbr `opc`, Abbr `ops`] >>
     fs[allocas_from_def, jump_to_def] >> metis_tac[]) >>
  pure_rewrite_tac[gas_outcome_full_def] >>
  qexists_tac `marks` >> disj1_tac >>
  qexistsl_tac [`INR (AssertException
      (if ak = AssertBare then "" else "UNREACHABLE"))`, `ee`, `Abort a u`,
      `G'`, `tn'`] >>
  conj_tac
  >- (gen_tac >> simp[Abbr `ak`, eval_assert_bind] >>
      asm_simp_tac (srw_ss()) [Once bind_def, raise_def]) >>
  conj_tac >- metis_tac[gas_origin_ptr_path_append, APPEND_NIL] >>
  disj2_tac >> simp[exit_result_def, stmt_exit_ptr_def])
QED

Finalise compile_assert_frag_full

Theorem body_assert_unreachable_case_full:
  !cx e.
    body_expr_full_ok cx e ==> body_stmt_full_ok cx (Assert e AssertUnreachable)
Proof
  rw[body_stmt_full_ok_def, gas_shadow_stmt_def,
     gas_shadow_assert_reason_def] >>
  `supported_expr tops e` by
    gvs[supported_stmt_def, supportedExprsTheory.supported_expr_def] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `cx_tops cx = tops` by (drule cx_tops_module >> simp[]) >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[type_stmt_def, stmt_exprs_ok_def, supported_stmt_expr_exists_def,
         supported_assert_exists_def, int_calls_stmt_def,
         int_calls_assert_reason_def, body_inv_def] >>
     qexists_tac `[]` >> simp[]) >>
  irule compile_assert_frag_full >> gvs[type_stmt_def] >>
  fs[body_expr_full_ok_def]
QED
