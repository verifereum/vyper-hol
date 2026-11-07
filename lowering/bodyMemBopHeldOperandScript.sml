(* Compiler boundaries for sequential bytestring digest operands. *)
Theory bodyMemBopHeldOperand
Ancestors
  bodyMemBopHeldHash bodyMemBopHeldFacts exprBopLowering
  exprLoweringProps exprOperandVar exprLowering compileEnv emitHelper
  list rich_list fragExec exprSimMemDefs exprSimSource gasSummary
  fragGasPathMem fragGasPath gasOutcome fragGasMode vyperInterpreter vyperState
  vyperValue venomState loweringPosts exprSimProps exprSimHash
  exprBopSimProps bodyMemBiKeccakBounds vyperTyping
  vyperEvalExprPreservesScopesDom venomExecSemantics venomInst
  emitHelperProps valueEncoding fragExecMem instMemFrontier venomMemDefs
  fragGasSeqMem allocaHistoryFragment rich_list
Libs
  pairLib

Theorem held_lower_value_compare:
  (bop = Eq \/ bop = NotEq) /\
  is_bytestring_type (expr_type e1) /\ expr_type e2 = expr_type e1 ==>
  lower_value compile_expr cenv ty (Builtin ann (Bop bop) [e1;e2]) sa =
  (let (h1,s1) =
     (case bytestring_literal_hash e1 of
        SOME h => (Lit h,sa)
      | NONE => let (p,sm) = lower_value compile_expr cenv (expr_type e1) e1 sa in
                compile_bytestring_hash p sm) in
   let (h2,s2) =
     (case bytestring_literal_hash e2 of
        SOME h => (Lit h,s1)
      | NONE => let (p,sm) = lower_value compile_expr cenv (expr_type e2) e2 s1 in
                compile_bytestring_hash p sm) in
   if bop = Eq then emit_op EQ [h1;h2] s2
   else let (q,sm) = emit_op EQ [h1;h2] s2 in emit_op ISZERO [q] sm)
Proof
  strip_tac >>
  simp[Once lower_value_def, comp_bind_def, compile_expr_bop] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       compile_builtin_dispatch_body_def, lower_value_child_call] >>
  Cases_on `bytestring_literal_hash e1` >>
  Cases_on `bytestring_literal_hash e2` >>
  rpt (pairarg_tac >> gvs[]) >>
  rw[] >> gvs[as_stack_val_pair, unwrap_value_def, comp_return_def] >>
  RULE_ASSUM_TAC (CONV_RULE (DEPTH_CONV ETA_CONV)) >> gvs[]
QED

Theorem held_hash_compiler:
  compile_bytestring_hash p sa = (h,sb) ==>
  ci_mono sa sb /\ (!z. h = Var z ==> not_fresh_at sb z)
Proof
  simp[compile_bytestring_hash_def, comp_bind_def, comp_return_def,
       comp_ignore_bind_def, emit_op_def, fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[] >>
  simp[ci_mono_def, cs_extends_def, not_fresh_at_def,
       rich_listTheory.IS_PREFIX_APPEND, GSYM APPEND_ASSOC]
QED

Theorem held_digest_operand_compiler:
  (case bytestring_literal_hash e of
     SOME w => (Lit w,sa)
   | NONE => let (p,sm) = lower_value compile_expr cenv (expr_type e) e sa in
             compile_bytestring_hash p sm) = (h,sb) ==>
  ci_mono sa sb /\ (!z. h = Var z ==> not_fresh_at sb z) /\
  (local_ptrs_reserved cenv sa ==> local_ptrs_reserved cenv sb)
Proof
  Cases_on `bytestring_literal_hash e`
  >- (simp[] >> pairarg_tac >> strip_tac >> gvs[] >>
      drule held_hash_compiler >> strip_tac >>
      `ci_mono sa (SND (lower_value compile_expr cenv (expr_type e) e sa))` by
        (irule ci_mono_lower_value_cfn >> simp[compile_expr_ci_mono]) >>
      gvs[] >>
      `ci_mono sa sb` by
        (fs[ci_mono_def] >> metis_tac[cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS]) >>
      metis_tac[compiler_ci_mono_reserved]) >>
  simp[] >> strip_tac >> gvs[] >>
  simp[ci_mono_def, cs_extends_refl]
QED

Theorem held_compare_tail_compiler:
  (if bop = Eq then emit_op EQ [h1;h2] sa
   else let (q,sm) = emit_op EQ [h1;h2] sa in emit_op ISZERO [q] sm) = (op,sb) ==>
  ci_mono sa sb
Proof
  Cases_on `bop = Eq` >> simp[]
  >- metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  `ci_mono sa sm` by metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `ci_mono sm sb` by metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  fs[ci_mono_def] >> metis_tac[cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem held_digest_runtime_cut:
  lower_value compile_expr cenv (expr_type e) e sa = (p,sm) /\
  compile_bytestring_hash p sm = (h,sb) /\
  cs_extends start sa /\ cs_extends sb last_st /\
  fn_has_code start last_st func /\ local_ptrs_reserved cenv sa ==>
  ci_mono sa sm /\ ci_mono sm sb /\
  local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv sb /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  (!z. h = Var z ==> not_fresh_at sb z)
Proof
  strip_tac >>
  `ci_mono sa (SND (lower_value compile_expr cenv (expr_type e) e sa))` by
    (irule ci_mono_lower_value_cfn >> simp[compile_expr_ci_mono]) >>
  gvs[] >> drule held_hash_compiler >> strip_tac >>
  `local_ptrs_reserved cenv sm` by metis_tac[compiler_ci_mono_reserved] >>
  `local_ptrs_reserved cenv sb` by metis_tac[compiler_ci_mono_reserved] >>
  fs[ci_mono_def] >> metis_tac[fn_has_code_mid, cs_extends_trans]
QED

Theorem held_compare_cuts:
  (case bytestring_literal_hash e1 of
     SOME w => (Lit w,sa)
   | NONE => let (p,sm) = lower_value compile_expr cenv (expr_type e1) e1 sa in
             compile_bytestring_hash p sm) = (h1,s1) /\
  (case bytestring_literal_hash e2 of
     SOME w => (Lit w,s1)
   | NONE => let (p,sm) = lower_value compile_expr cenv (expr_type e2) e2 s1 in
             compile_bytestring_hash p sm) = (h2,s2) /\
  (if bop = Eq then emit_op EQ [h1;h2] s2
   else let (q,sm) = emit_op EQ [h1;h2] s2 in emit_op ISZERO [q] sm) = (op,sb) /\
  local_ptrs_reserved cenv sa /\ fn_has_code sa sb func ==>
  ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 sb /\
  local_ptrs_reserved cenv s1 /\ local_ptrs_reserved cenv s2 /\
  fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\ fn_has_code s2 sb func /\
  (!z. h1 = Var z ==> not_fresh_at s1 z) /\
  (!z. h2 = Var z ==> not_fresh_at s2 z)
Proof
  strip_tac >>
  drule_all held_digest_operand_compiler >> strip_tac >>
  drule_all held_compare_tail_compiler >> strip_tac >>
  `ci_mono sa s1 /\ (!z. h1 = Var z ==> not_fresh_at s1 z) /\
   local_ptrs_reserved cenv s1` by
    metis_tac[held_digest_operand_compiler] >>
  `ci_mono s1 s2 /\ (!z. h2 = Var z ==> not_fresh_at s2 z) /\
   local_ptrs_reserved cenv s2` by
    metis_tac[held_digest_operand_compiler] >>
  fs[ci_mono_def] >> metis_tac[fn_has_code_split, cs_extends_trans]
QED

Theorem held_digest_operand_outcome:
  expr_body_pre cenv cx env e es /\ is_bytestring_type (expr_type e) /\
  expr_sim_mem ctx func cenv cx (expr_type e) e es /\
  (case bytestring_literal_hash e of
     SOME w => (Lit w,sa)
   | NONE => let (p,sm) = lower_value compile_expr cenv (expr_type e) e sa in
             compile_bytestring_hash p sm) = (h,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  gas_admissible (vyperState$bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\ alloca_history func s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (vyperState$bind (eval_expr cx e) (read_result cx)) (es,s0)
    (\res ee t. ?v bs. res = INL v /\
      (v = BytesV bs \/ ?str. v = StringV str /\ bs = MAP (n2w o ORD) str) /\
      eval_operand h t = SOME (word_of_bytes_be (Keccak_256_w64 bs):bytes32) /\
      stmt_state_rel ctx func cenv cx ee t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
             lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
               FLOOKUP t.vs_allocas aid = SOME b) /\
      (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
        aid < sa.cs_next_id /\
        (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
                   off + sz <= b \/ b + sz' <= off) ==>
        mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz s0.vs_memory) /\
      locals_kept cenv es s0 t /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ ~t.vs_halted /\
      s0.vs_alloca_next <= t.vs_alloca_next)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >> Cases_on `bytestring_literal_hash e`
  >- suspend "runtime" >>
  Cases_on `e` >> gvs[bytestring_literal_hash_def] >>
  rename1 `Literal ann lit` >> Cases_on `lit` >>
  gvs[bytestring_literal_hash_def] >> suspend "literal"
QED

Resume held_digest_operand_outcome[literal]:
  markerLib.RESUME_TAC >> rpt strip_tac >> simp[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_at_def] >>
  simp[gas_marked_exec_def, gas_marked_path_def,
       Once evaluate_def, bind_def, read_result_def, return_def,
       vyperValueOperationTheory.evaluate_literal_def, eval_operand_def] >>
  qrefinel [`_`, `es`, `OK s0`] >>
  simp[gas_path_mem_rules] >> metis_tac[]
QED

Resume held_digest_operand_outcome[runtime]:
  gvs[] >> pairarg_tac >> gvs[] >>
  `ci_mono sa sm /\ ci_mono sm sb /\
   local_ptrs_reserved cenv sm /\ fn_has_code sa sm func /\
   fn_has_code sm sb func` by
    (metis_tac[held_digest_runtime_cut, cs_extends_refl]) >>
  qpat_x_assum `expr_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_mem_def]) >>
  disch_then (qspecl_then [`sa`, `sm`, `p`, `s0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  simp[gas_outcome_def] >> strip_tac
  >- (fs[gas_summary_at_def] >>
      Cases_on `?u. r = OK u /\ ?v. res = INL v /\
        expr_post ctx func cenv cx e es sa sm s0 (es_end with gas_obs := []) v p u /\
        expr_store_bound cx (expr_type e) v p u /\
        u.vs_current_bb = sm.cs_current_bb /\
        u.vs_inst_idx = LENGTH sm.cs_current_insts /\
        alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next`
      >- (gvs[] >> suspend "runtime_normal") >>
      qexists_tac `marks` >> disj1_tac >>
      simp[gas_summary_at_def] >> metis_tac[]) >>
  metis_tac[]
QED

Resume held_digest_operand_outcome[runtime_normal]:
  `~t.vs_halted` by
    (fs[gas_marked_exec_def, gas_marked_path_def] >>
     drule gas_path_mem_exec >> metis_tac[gas_path_normal]) >>
  `vyperState$bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v, es_end with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     strip_tac >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM es_end.scopes` by
    (qpat_x_assum `vyperState$bind _ _ _ = _` mp_tac >>
     simp[vyperStateTheory.bind_def, AllCaseEqs()] >> strip_tac >>
     imp_res_tac read_result_state >> gvs[] >>
     drule eval_expr_preserves_scopes_dom >> simp[]) >>
  `?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
        value_has_type tv v` by
    (qpat_x_assum `vyperState$bind _ _ _ = _` mp_tac >>
     simp[vyperStateTheory.bind_def, AllCaseEqs()] >> strip_tac >>
     imp_res_tac read_result_state >> gvs[] >>
     `expr_body_pre cenv cx env e
       (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
     drule_all expr_body_pre_runtime_typed >> strip_tac >>
     first_x_assum (irule_at Any) >> metis_tac[]) >>
  `?bs b. (v = BytesV bs \/ ?str. v = StringV str /\
                   bs = MAP (n2w o ORD) str) /\
    eval_operand p t = SOME (n2w b) /\
    mem_word_at b t.vs_memory = n2w (LENGTH bs) /\
    mem_bytes_at (b + 32) (LENGTH bs) t.vs_memory = bs /\
    b + 32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
    b + 32 <= t.vs_alloca_next /\
    (LENGTH bs = 0 \/ b + 32 + LENGTH bs <= t.vs_alloca_next)` by
    (Cases_on `expr_type e` >> gvs[is_bytestring_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >> gvs[is_bytestring_type_def]
     >~ [`BytesT bd`]
     >- (Cases_on `bd` >> gvs[is_bytestring_type_def, evaluate_type_def] >>
         Cases_on `v` >> gvs[value_has_type_def] >>
         drule_at (Pos hd) keccak_dynamic_post_bounds >> simp[evaluate_type_def] >> strip_tac >>
         goal_assum (drule_at Any) >> simp[]) >>
     gvs[evaluate_type_def] >> Cases_on `v` >> gvs[value_has_type_def] >>
     drule_at (Pos hd) keccak_string_post_bounds >> simp[evaluate_type_def] >> strip_tac >>
     goal_assum (drule_at Any) >> simp[]) >>
  `!z. p = Var z ==> not_fresh_at sm z` by
    metis_tac[compile_lower_value_var] >>
  `stmt_state_rel ctx func cenv cx (es_end with gas_obs := []) t` by
    fs[expr_post_def] >>
  drule_at (Pos hd) held_hash_counted_nofresh >>
  disch_then (drule_at (Pat `mem_bytes_at _ _ _ = _`)) >>
  simp[] >> disch_then drule_all >> strip_tac >>
  qexists_tac `marks` >> disj1_tac >>
  qexistsl_tac [`INL v`, `es_end`, `OK t'`] >>
  (conj_tac
   >- (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
       simp[gas_marked_exec_def, gas_marked_path_def] >> strip_tac >>
       simp[] >> metis_tac[gas_path_mem_then, arithmeticTheory.ADD_CLAUSES])) >>
  simp[] >>
  `!z. not_fresh_at sa z ==> not_fresh_at sm z` by
    (fs[ci_mono_def, not_fresh_at_def] >> decide_tac) >>
  fs[expr_post_def, locals_kept_def] >>
  asm_rewrite_tac[]
QED

Finalise held_digest_operand_outcome

Theorem held_compare_run_nofresh:
  (if bop = Eq then emit_op EQ [h1;h2] sa
   else let (q,sm) = emit_op EQ [h1;h2] sa in emit_op ISZERO [q] sm) = (op,sb) /\
  eval_operand h1 s = SOME w1 /\ eval_operand h2 s = SOME w2 ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand op t = SOME (bool_to_word (if bop = Eq then w1 = w2 else w1 <> w2)) /\
    (t with vs_vars := s.vs_vars) = s /\
    (!z. not_fresh_at sa z ==> lookup_var z t = lookup_var z s)
Proof
  Cases_on `bop = Eq` >>
  simp[emit_op_def, fresh_id_def, fresh_var_def, emit_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >> strip_tac >> gvs[] >>
  `!k. LENGTH sa.cs_current_insts - (LENGTH sa.cs_current_insts + k) = 0`
    by decide_tac >>
  simp[emitted_insts_def, DROP_APPEND, run_inst_seq_def,
       step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def, exec_pure1_def,
       bind_outputs_def] >>
  simp[eval_operand_def, lookup_var_update_var, update_var_def, bool_to_word_def] >>
  rpt strip_tac >> gvs[not_fresh_at_def, lookup_var_def,
                       finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem held_compare_shape:
  (if bop = Eq then emit_op EQ [h1;h2] sa
   else let (q,sm) = emit_op EQ [h1;h2] sa in emit_op ISZERO [q] sm) = (op,sb) ==>
  same_blocks sa sb /\ sb.cs_current_bb = sa.cs_current_bb /\
  LENGTH sb.cs_current_insts = LENGTH sa.cs_current_insts +
    LENGTH (emitted_insts sa sb) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb) /\
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = [] /\
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  Cases_on `bop = Eq` >>
  simp[comp_bind_def, comp_return_def, comp_ignore_bind_def,
       emit_op_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[] >>
  `!k. LENGTH sa.cs_current_insts - (LENGTH sa.cs_current_insts + k) = 0`
    by decide_tac >>
  simp[same_blocks_def, emitted_insts_def, DROP_APPEND, mk_inst_def,
       is_terminator_def] >>
  irule run_inst_seq_mem_ok_every >>
  simp[below_frontier_no_ranges, memSafeRunTheory.inst_dload_in_section_other]
QED

Theorem held_compare_counted_nofresh:
  (if bop = Eq then emit_op EQ [h1;h2] sa
   else let (q,sm) = emit_op EQ [h1;h2] sa in emit_op ISZERO [q] sm) = (op,sb) /\
  eval_operand h1 s = SOME w1 /\ eval_operand h2 s = SOME w2 /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_path_mem ctx func s 0 (OK t) /\
    eval_operand op t = SOME (bool_to_word (if bop = Eq then w1 = w2 else w1 <> w2)) /\
    stmt_state_rel ctx func cenv cx es t /\
    (!z. not_fresh_at sa z ==> lookup_var z t = lookup_var z s) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ alloca_history func t /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    t.vs_current_bb = sb.cs_current_bb /\ ~t.vs_halted
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all held_compare_run_nofresh >> strip_tac >>
  drule held_compare_shape >> disch_then (qspec_then `s` strip_assume_tac) >>
  `(?bb rest. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
      DROP s.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest) /\
    s.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts` by
    (conj_tac
     >- (fs[fn_has_code_def, same_blocks_def, IS_PREFIX_APPEND] >>
         qpat_x_assum `LENGTH sb.cs_current_insts = _` kall_tac >>
         simp[DROP_APPEND, emitted_insts_def] >> metis_tac[]) >>
     decide_tac) >>
  `isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)` by
    simp[IS_PREFIX_APPEND] >>
  drule_all run_inst_seq_gas_path_mem >> simp[] >> strip_tac >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    fs[EVERY_MEM] >>
  drule_all alloca_history_run_inst_seq >> simp[] >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es t` by
    (irule hash_readonly_state_rel >> goal_assum (drule_at Any) >> simp[]) >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  gvs[venom_state_component_equality, stmt_state_rel_inst_idx,
      eval_operand_def, lookup_var_def]
QED
