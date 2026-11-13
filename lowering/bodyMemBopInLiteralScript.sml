(* Memory case of the body induction (bodyMemory's body_mem_mutual): in and
   not in on an array literal. *)
Theory bodyMemBopInLiteral
Ancestors
  bodyMemoryPreds exprSimBopInLiteralWord compileEnv
  bodyArgsMemory bodyUnopFragMemory exprSimMemoryStack
  exprSimHypsDefs exprSimWordArgs exprLoweringProps gasSummary gasOutcome
  gasSummaryCompose gasExemptCert fragGasFresh freshWrites
  vyperAST exprSimUnopProps fragExec
  gasStorage vyperStorageFootprint vyperStorageTrace

Theorem body_literal_operands_mem_ok[local]:
  !cx e1 a t n elems.
    body_exprs_mem_ok cx [e1; Builtin a (MakeArray t n) elems] /\
    builtin_args_length_ok (MakeArray t n) (LENGTH elems) ==>
    body_exprs_mem_ok cx (e1::elems)
Proof
  simp[body_exprs_mem_ok_def] >>
  metis_tac[body_make_array_children_mem_ok]
QED

Theorem body_literal_mem_typing[local]:
  expr_body_pre cenv cx env
    (Builtin ann (Bop bop) [e1; Builtin a (MakeArray t n) elems]) es /\
  (bop = In \/ bop = NotIn) ==>
  is_word_type (expr_type e1) /\
  builtin_args_length_ok (MakeArray t n) (LENGTH elems)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all literal_body_typing >> strip_tac >>
  conj_tac
  >- (`well_typed_binop ann bop (expr_type e1) a` by
        (gvs[exprSimHypsDefsTheory.expr_body_pre_def, vyperTypeSystemTheory.well_typed_expr_def,
             vyperTypeSystemTheory.well_typed_builtin_app_def,
             vyperASTTheory.expr_type_def]) >>
      gvs[] >> metis_tac[membership_checker_lowering_boundary]) >>
  gvs[exprSimHypsDefsTheory.expr_body_pre_def, vyperTypeSystemTheory.well_typed_expr_def] >>
  qpat_x_assum `well_typed_builtin_app _ (MakeArray _ _) _`
    (mp_then Any mp_tac
       vyperTypeBuiltinsTheory.well_typed_builtin_app_length) >> simp[]
QED

Theorem literal_typed_args_ready_mem[local]:
  (bop = In \/ bop = NotIn) /\
  body_exprs_mem_ok cx [e1; Builtin a (MakeArray t n) elems] /\
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env
    (Builtin ann (Bop bop) [e1; Builtin a (MakeArray t n) elems]) es ==>
  typed_args_ready_mem ctx func cenv cx expr_type
    (expr_sim_inv cenv cx env) (e1::elems)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all body_literal_mem_typing >> strip_tac >>
  irule typed_args_ready_mem_of_body >>
  simp[] >> conj_tac
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      `MEM e (e1::elems)` by simp[] >> conj_tac
      >- (drule_all literal_body_operand_pre >> simp[]) >>
      drule_all literal_operand_word_type >> simp[]) >>
  metis_tac[body_literal_operands_mem_ok]
QED

Theorem literal_straight_success_mem[local]:
  straight_fresh m /\ m sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel H ctx func cenv cx es s0 /\
  alloca_history func s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) (drop_fresh sa s0) = OK u /\
  eval_operand op u = SOME w ==>
  ?s. gas_marked_path T ctx func s0 0 (OK s) /\
      stmt_state_rel H ctx func cenv cx es s /\ eval_operand op s = SOME w /\
      (!z v. not_fresh_at sa z /\ lookup_var z s0 = SOME v ==>
             lookup_var z s = SOME v) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
               FLOOKUP s.vs_allocas aid = SOME b) /\
      s.vs_memory = s0.vs_memory /\ ~s.vs_halted /\
      s.vs_current_bb = sb.cs_current_bb /\
      s.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func s /\ s.vs_alloca_next = s0.vs_alloca_next /\
      s.vs_accounts = s0.vs_accounts /\ s.vs_transient = s0.vs_transient /\
      s.vs_requests = s0.vs_requests /\ s.vs_call_ctx = s0.vs_call_ctx
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all fragGasFreshTheory.straight_fresh_clean_success_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all fragGasFreshTheory.straight_fresh_run_post >> strip_tac >>
  `writes_fresh sa (emitted_insts sa sb) /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    metis_tac[freshWritesTheory.straight_fresh_def] >>
  drule fragGasFreshTheory.writes_fresh_path_opcodes >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s0` by
    metis_tac[writes_fresh_mem_ok] >>
  drule_all fragGasFreshTheory.straight_fresh_code_prefix >> strip_tac >>
  `?rest. DROP s0.vs_inst_idx bb.bb_instructions = emitted_insts sa sb ++ rest`
    by fs[rich_listTheory.IS_PREFIX_APPEND] >>
  `s0.vs_inst_idx + LENGTH (emitted_insts sa sb) = LENGTH sb.cs_current_insts`
    by simp[] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb)` by fs[listTheory.EVERY_MEM] >>
  drule_all fragGasSeqMemTheory.run_inst_seq_gas_path_mem >>
  disch_then (qspec_then `ctx` assume_tac) >>
  `alloca_inv s0` by fs[exprLoweringPropsTheory.stmt_state_rel_def] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    fs[listTheory.EVERY_MEM] >>
  drule_all allocaHistoryFragmentTheory.alloca_history_run_inst_seq >>
  disch_tac >>
  drule_all freshWritesTheory.run_inst_seq_writes_fresh >> strip_tac >>
  `t.vs_alloca_next = s0.vs_alloca_next` by
    (qpat_x_assum `t = _` (fn th => once_rewrite_tac [th]) >> simp[]) >>
  `t.vs_accounts = s0.vs_accounts /\ t.vs_transient = s0.vs_transient /\
   t.vs_requests = s0.vs_requests /\ t.vs_call_ctx = s0.vs_call_ctx` by
    (qpat_x_assum `t = _` (fn th => once_rewrite_tac [th]) >> simp[]) >>
  drule fragGasFreshTheory.writes_fresh_gas_count >> disch_tac >>
  qexists_tac `t with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  gvs[fragGasModeTheory.gas_marked_path_def, arithmeticTheory.ADD_COMM]
QED

Theorem literal_typed_fragment_success_mem[local]:
  (bop = In \/ bop = NotIn) /\
  (if bop = In then compile_list_membership_in needle xs
   else compile_list_membership_notin needle xs) sa = (op,sb) /\
  is_word_type ty /\ evaluate_type tenv ty = SOME tv /\
  value_has_type tv v /\ EVERY (value_has_type tv) vs /\
  EVERY (\x. !z. x = Var z ==> not_fresh_at sa z) (needle::xs) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  stmt_state_rel H ctx func cenv cx ee s0 /\ alloca_history func s0 /\
  LIST_REL (\x v. eval_operand x s0 = SOME (typed_val_to_w256 tv v)) xs vs /\
  eval_operand needle s0 = SOME (typed_val_to_w256 tv v) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?s. gas_marked_path T ctx func s0 0 (OK s) /\
      stmt_state_rel H ctx func cenv cx ee s /\
      eval_operand op s = SOME (bool_to_word (if bop = In then MEM v vs else ~MEM v vs)) /\
      (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==> lookup_var z s = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
      s.vs_memory = s0.vs_memory /\ ~s.vs_halted /\
      s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func s /\ s.vs_alloca_next = s0.vs_alloca_next /\
      s.vs_accounts = s0.vs_accounts /\ s.vs_transient = s0.vs_transient /\
      s.vs_requests = s0.vs_requests /\ s.vs_call_ctx = s0.vs_call_ctx
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `fresh_vars_wrt sa (drop_fresh sa s0)` by
    simp[varsExtTheory.fresh_vars_wrt_drop_fresh] >>
  `LIST_REL (\x v. eval_operand x (drop_fresh sa s0) = SOME (typed_val_to_w256 tv v)) xs vs` by
    (irule (iffRL literal_typed_operands_drop_fresh) >> gvs[]) >>
  `eval_operand needle (drop_fresh sa s0) = SOME (typed_val_to_w256 tv v)` by
    (gvs[] >> drule freshWritesTheory.eval_operand_drop_fresh >> simp[]) >>
  drule_all literal_typed_run >> strip_tac >>
  `straight_fresh (if bop = In then compile_list_membership_in needle xs
                   else compile_list_membership_notin needle xs)` by
    (Cases_on `bop = In` >> simp[literal_membership_straight]) >>
  drule_all literal_straight_success_mem >> simp[]
QED

Theorem literal_typed_continuation_summary_mem[local]:
  (bop = In \/ bop = NotIn) /\
  (if bop = In then compile_list_membership_in needle xs
   else compile_list_membership_notin needle xs) sm = (op,sb) /\
  is_word_type et /\ evaluate_type (get_tenv cx) et = SOME tv /\
  value_has_type tv v /\ EVERY (value_has_type tv) vs /\
  EVERY (\x. !z. x = Var z ==> not_fresh_at sm z) (needle::xs) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sm /\ alloca_history func t0 /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_state_rel H ctx func cenv cx (ee with gas_obs := []) t0 /\
     storage_well_formed_on cx (ee with gas_obs := []) (FST H)) /\
  valid_horizon cx st0 H0 ee.storage_trace /\
  LIST_REL (\x v. eval_operand x t0 = SOME (typed_val_to_w256 tv v)) xs vs /\
  eval_operand needle t0 = SOME (typed_val_to_w256 tv v) /\
  wb_frame cenv es (ee with gas_obs := []) sa s0 t0 /\
  (~expr_has_effect e1 /\ EVERY ($~ o expr_has_effect) elems ==>
   pure_frame cenv func es sa s0 t0) /\
  sa.cs_next_var <= sm.cs_next_var /\
  ~t0.vs_halted /\ t0.vs_current_bb = sm.cs_current_bb /\
  t0.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  gas_summary_at T (ctx,func) []
    (vyperState$return (BoolV (if bop = In then MEM v vs else ~MEM v vs)))
    (ee with gas_obs := [],t0)
    (\res fin s. !H. valid_horizon cx st0 H fin.storage_trace ==>
      ?w. res = INL w /\
      expr_post H ctx func cenv cx
        (Builtin (BaseT BoolT) (Bop bop) [e1; Builtin a (MakeArray t n) elems])
        es sa sb s0 fin w op s /\
      expr_store_bound cx (BaseT BoolT) w op s /\
      s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func s /\ s.vs_alloca_next = t0.vs_alloca_next)
    (\res fin r. !H. valid_horizon cx st0 H fin.storage_trace ==> expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `wb_frame _ _ (_ with gas_obs := _) _ _ _`
    (assume_tac o REWRITE_RULE [exprSimWordArgsTheory.wb_frame_gas_obs]) >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (qspec_then `H0` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  drule_all literal_typed_fragment_success_mem >> strip_tac >>
  `wb_frame cenv es ee sa s0 s` by
    (irule exprSimWordArgsTheory.wb_frame_readonly_tail >>
     goal_assum (drule_at Any) >> qexists_tac `sm` >> simp[]) >>
  `~expr_has_effect e1 /\ EVERY ($~ o expr_has_effect) elems ==>
   pure_frame cenv func es sa s0 s` by
    (strip_tac >> irule exprSimPropsTheory.pure_frame_mem_tail >>
     qexists_tac `t0` >> fs[]) >>
  rewrite_tac[gasSummaryTheory.gas_summary_at_def] >>
  qexistsl_tac [`INL (BoolV (if bop = In then MEM v vs else ~MEM v vs))`, `ee`, `OK s`] >>
  conj_tac
  >- simp[gasSummaryTheory.gas_marked_exec_def, gasSummaryTheory.gas_explicit_def,
           vyperStateTheory.return_def] >>
  disj1_tac >> qexists_tac `s` >> conj_tac >- REFL_TAC >>
  BETA_TAC >> gen_tac >> strip_tac >>
  `valid_horizon cx st0 H ee.storage_trace` by
    (qpat_x_assum `valid_horizon cx st0 H (ee with gas_obs := []).storage_trace`
       mp_tac >> simp[]) >>
  qpat_x_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `stmt_state_rel H ctx func cenv cx (ee with gas_obs := []) s` by
    (mp_tac (Q.INST [`u` |-> `s`, `s` |-> `t0`, `es` |-> `ee with gas_obs := []`]
               (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``] stmt_state_rel_fields_transport)) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  qexists_tac `BoolV (if bop = In then MEM v vs else ~MEM v vs)` >>
  rpt conj_tac
  >- REFL_TAC
  >- (irule exprSimWordArgsTheory.expr_post_word_intro >>
      simp[vyperASTTheory.expr_type_def, is_word_type_def,
           loweringSliceTheory.word_value_def, valueEncodingTheory.val_to_w256_def,
           venomExecSemanticsTheory.bool_to_word_def] >>
      rpt conj_tac >>
      Cases_on `if bop = In then MEM v vs else ~MEM v vs` >>
      fs[venomExecSemanticsTheory.bool_to_word_def,
         exprSimWordArgsTheory.wb_frame_gas_obs])
  >- simp[exprSimMemDefsTheory.expr_store_bound_word, is_word_type_def]
  >> first_assum ACCEPT_TAC
QED

Theorem literal_expr_sim_mem[local]:
  (bop = In \/ bop = NotIn) /\
  body_exprs_mem_ok cx [e1; Builtin a (MakeArray t n) elems] /\
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env
    (Builtin ann (Bop bop) [e1; Builtin a (MakeArray t n) elems]) es ==>
  expr_sim_mem ctx func cenv cx ty
    (Builtin ann (Bop bop) [e1; Builtin a (MakeArray t n) elems]) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all body_literal_mem_typing >> strip_tac >>
  drule_all literal_body_evaluate_types >> strip_tac >>
  drule_all literal_body_typing >> strip_tac >>
  qpat_x_assum `ann = BaseT BoolT` SUBST_ALL_TAC >>
  qpat_x_assum `a = ArrayT _ _` SUBST_ALL_TAC >>
  qpat_x_assum `t = SOME _` SUBST_ALL_TAC >>
  `is_ArrayT (ArrayT (expr_type e1) n)` by simp[is_ArrayT_def] >>
  `wb_args_shape cenv expr_type (e1::elems)` by metis_tac[literal_args_shape] >>
  `typed_args_ready_mem ctx func cenv cx expr_type
     (expr_sim_inv cenv cx env) (e1::elems)` by
    (drule_all literal_typed_args_ready_mem >> simp[]) >>
  rewrite_tac[exprSimMemDefsTheory.expr_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  drule_all literal_lower_value >> strip_tac >>
  drule_all lower_word_args_shape_ready >> strip_tac >>
  `cs_extends sm sb` by metis_tac[literal_membership_straight, straight_fresh_cs_extends] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `EVERY (\x. !z. x = Var z ==> not_fresh_at sm z) (needle::xs)` by
    (gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  `!ee gs. expr_sim_inv cenv cx env ee ==>
      expr_sim_inv cenv cx env (ee with gas_obs := gs)` by simp[] >>
  drule_all lower_typed_args_sim_mem >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      drule_all literal_body_action_flat >> disch_then (fn th => rewrite_tac[th]) >>
      irule gas_bad_storage_at_bind_left >> conj_tac >>
      FIRST [first_assum ACCEPT_TAC, simp[storage_trace_frame_return]])
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (mp_tac o REWRITE_RULE [gas_summary_at_def]) >>
      disch_then (qx_choosel_then [`res`, `es_end`, `r`]
        (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
      (reverse (Cases_on `storage_trace_domain cx st0 es_end.storage_trace`)
       >- (qexists_tac `marks` >> disj1_tac >>
           drule_all literal_body_action_flat >>
           disch_then (fn th => rewrite_tac[th]) >>
           irule gas_bad_storage_at_bind_left >>
           conj_tac
           >- simp[storage_trace_frame_return] >>
           drule_all_then ACCEPT_TAC gas_bad_storage_at_counted_prefix)) >>
      `valid_horizon cx st0 (storage_trace_horizon es_end.storage_trace)
         es_end.storage_trace` by
        (qpat_assum `storage_trace_domain _ _ _`
           (ACCEPT_TAC o REWRITE_RULE [storage_trace_domain_def])) >>
      qpat_x_assum `(?t. r = OK t /\ _) \/ _`
        (DISJ_CASES_THEN2 (qx_choose_then `tt` strip_assume_tac) strip_assume_tac)
      >- suspend "normal"
      >> suspend "exit") >>
  suspend "exempt"
QED

Resume literal_expr_sim_mem[normal]:
  qpat_x_assum `(\res ee t. _) _ _ _` (assume_tac o SIMP_RULE (srw_ss()) []) >>
  qpat_assum `!H. valid_horizon _ _ H es_end.storage_trace ==> ?vs. _`
    (drule_then (qx_choose_then `vs` strip_assume_tac)) >>
  qpat_x_assum `res = INL vs` SUBST_ALL_TAC >>
  qpat_x_assum `r = OK tt` SUBST_ALL_TAC >>
  qpat_x_assum `!H. valid_horizon _ _ H es_end.storage_trace ==> ?vs. _`
    (assume_tac o SIMP_RULE (srw_ss()) []) >>
  `!H. valid_horizon cx st0 H es_end.storage_trace ==>
     stmt_state_rel H ctx func cenv cx (es_end with gas_obs := []) tt /\
     storage_well_formed_on cx (es_end with gas_obs := []) (FST H)` by
    (rpt strip_tac >>
     qpat_x_assum `!H. valid_horizon _ _ H es_end.storage_trace ==> typed_args_post _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     fs[exprSimPrecompilesTheory.typed_args_post_def]) >>
  qpat_x_assum `!H. valid_horizon _ _ H es_end.storage_trace ==> typed_args_post _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    kall_tac >>
  `~tt.vs_halted` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     disch_then (mp_tac o CONJUNCT2) >>
     disch_then (mp_tac o MATCH_MP fragGasModeTheory.gas_marked_path_exec) >>
     disch_then (mp_tac o MATCH_MP fragGasPathTheory.gas_path_normal) >> simp[]) >>
  qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
  disch_then (mp_tac o CONJUNCT1) >>
  disch_then (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  `!e. MEM e (e1::elems) ==> MEM e (e1::elems)` by simp[] >>
  `expr_sim_inv cenv cx env
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  drule_all literal_eval_exprs_typed >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `vs`
  >- (qpat_x_assum `typed_args_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
      simp[exprSimPrecompilesTheory.typed_args_post_def]) >>
  rename1 `typed_args_post _ _ _ _ _ _ _ _ _ _ _ (hv::tv0) _` >>
  qpat_assum `typed_args_post _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE (srw_ss())
       [exprSimPrecompilesTheory.typed_args_post_def]) >>
  qpat_x_assum `EVERY (value_has_type _) (_::_)`
    (strip_assume_tac o REWRITE_RULE [listTheory.EVERY_DEF]) >>
  `eval_operand needle tt = SOME (typed_val_to_w256 tv hv)` by
    (qpat_x_assum `eval_operand needle tt = _` mp_tac >> simp[]) >>
  `LIST_REL (\x v. eval_operand x tt = SOME (typed_val_to_w256 tv v)) xs tv0` by
    (fs[listTheory.LIST_REL_EL_EQN, listTheory.EL_ZIP, listTheory.EVERY_EL] >>
     rpt strip_tac >> first_x_assum drule >> simp[] >> metis_tac[]) >>
  `wb_frame cenv es (es_end with gas_obs := []) sa s0 tt` by
    (qpat_assum `wb_frame _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [exprSimWordArgsTheory.wb_frame_gas_obs]) >>
     simp[exprSimWordArgsTheory.wb_frame_gas_obs]) >>
  `~expr_has_effect e1 /\ EVERY ($~ o expr_has_effect) elems ==>
   pure_frame cenv func es sa s0 tt` by
    (strip_tac >>
     qpat_x_assum `_ ==> pure_frame cenv func es sa s0 tt` irule >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `?H. valid_horizon cx st0 H es_end.storage_trace` by
    (qexists_tac `storage_trace_horizon es_end.storage_trace` >>
     first_assum ACCEPT_TAC) >>
  qpat_x_assum `typed_args_ready_mem _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `wb_args_shape _ _ _` kall_tac >>
  drule_all literal_typed_continuation_summary_mem >>
  disch_then (qspecl_then
    [`SOME (expr_type e1)`, `n`, `ArrayT (expr_type e1) n`]
    (fn th => qx_choosel_then [`res2`, `es2`, `r2`]
       (CONJUNCTS_THEN2 assume_tac assume_tac)
       (REWRITE_RULE [gas_summary_at_def] th))) >>
  qexists_tac `marks` >> disj2_tac >> disj1_tac >>
  drule_all literal_body_action_flat >> disch_then (fn th => rewrite_tac[th]) >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`res2`, `es2`, `r2`] >> conj_tac
  >- (irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
               |> REWRITE_RULE [listTheory.APPEND_NIL]) >>
      qpat_assum `gas_marked_exec _ _ _ _ _ (INL _) _ _` (irule_at Any) >>
      simp[]) >>
  qpat_x_assum `(?t. r2 = OK t /\ _) \/ _`
    (DISJ_CASES_THEN2 (qx_choose_then `uu` strip_assume_tac) strip_assume_tac)
  >- (disj1_tac >> qexists_tac `uu` >> conj_tac >- first_assum ACCEPT_TAC >>
      BETA_TAC >> qx_gen_tac `H1` >> BETA_TAC >> strip_tac >>
      qpat_x_assum `(\res fin s. _) _ _ _` (mp_tac o BETA_RULE) >>
      disch_then (qspec_then `H1` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
      qexists_tac `w` >> rpt conj_tac >>
      FIRST [first_assum ACCEPT_TAC,
             (simp[vyperASTTheory.expr_type_def] >> NO_TAC), decide_tac]) >>
  disj2_tac >> conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `(\res fin r. _) _ _ _` (assume_tac o BETA_RULE) >>
  BETA_TAC >> first_assum ACCEPT_TAC
QED
Resume literal_expr_sim_mem[exit]:
  `wb_args_exit res r` by
    (qpat_assum `(\res ee r. _) _ _ _` (mp_tac o BETA_RULE) >>
     disch_then (qspec_then `storage_trace_horizon es_end.storage_trace` mp_tac) >>
     (impl_tac >- simp[]) >> disch_then ACCEPT_TAC) >>
  Cases_on `res`
  >- (qpat_x_assum `wb_args_exit (INL _) _` mp_tac >> simp[wb_args_exit_def]) >>
  qexists_tac `marks` >> disj2_tac >> disj1_tac >>
  drule_all literal_body_action_flat >> disch_then (fn th => rewrite_tac[th]) >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INR y`, `es_end`, `r`] >> conj_tac
  >- (irule gas_marked_exec_bind_exception >> first_assum ACCEPT_TAC) >>
  disj2_tac >> conj_tac >- first_assum ACCEPT_TAC >>
  BETA_TAC >> gen_tac >> BETA_TAC >> strip_tac >>
  qpat_x_assum `wb_args_exit (INR _) _` mp_tac >> simp[wb_args_exit_def]
QED
Resume literal_expr_sim_mem[exempt]:
  qexists_tac `marks` >> disj2_tac >> disj2_tac >>
  drule_all literal_body_action_flat >> disch_then (fn th => rewrite_tac[th]) >>
  rewrite_tac[vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_assoc,
              vyperStateTheory.bind_return] >>
  irule_at Any gas_exempt_cert_error_values >>
  goal_assum (drule_at Any) >> simp[vyperStateTheory.ignore_bind_def]
QED
Finalise literal_expr_sim_mem

Theorem body_bop_in_literal_mem_case:
  !cx ty bop e1 a t n elems.
    (bop = In \/ bop = NotIn) /\
    body_exprs_mem_ok cx [e1; Builtin a (MakeArray t n) elems] ==>
    body_expr_mem_ok cx
      (Builtin ty (Bop bop) [e1; Builtin a (MakeArray t n) elems])
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[body_expr_mem_ok_def] >> rpt gen_tac >> strip_tac >>
  (conj_asm1_tac
   >- (irule literal_expr_sim_mem >> metis_tac[])) >>
  `ty = BaseT BoolT` by metis_tac[literal_body_typing] >>
  irule body_expr_vv_sim_mem_stack_word >>
  simp[vyperASTTheory.expr_type_def, is_word_type_def, exprSimOperatorsTheory.compile_bop_stack] >>
  metis_tac[exprLoweringPropsTheory.eval_expr_builtin_value]
QED
