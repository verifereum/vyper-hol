(* Memory case of the body induction (bodyMemory's body_mem_mutual): in and
   not in on an array literal. *)
Theory bodyMemBopInLiteral
Ancestors
  bodyMemoryPreds exprSimBopInLiteralWord compileEnv
  bodyArgsMemory bodyUnopFragMemory exprSimMemoryStack
  exprSimHypsDefs exprSimWordArgs exprLoweringProps gasSummary gasOutcome
  gasSummaryCompose gasExemptCert fragGasFresh freshWrites
  vyperAST exprSimUnopProps fragExec

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
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 /\
  alloca_history func s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) (drop_fresh sa s0) = OK u /\
  eval_operand op u = SOME w ==>
  ?s. gas_marked_path T ctx func s0 0 (OK s) /\
      stmt_state_rel ctx func cenv cx es s /\ eval_operand op s = SOME w /\
      (!z v. not_fresh_at sa z /\ lookup_var z s0 = SOME v ==>
             lookup_var z s = SOME v) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
               FLOOKUP s.vs_allocas aid = SOME b) /\
      s.vs_memory = s0.vs_memory /\ ~s.vs_halted /\
      s.vs_current_bb = sb.cs_current_bb /\
      s.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func s /\ s.vs_alloca_next = s0.vs_alloca_next
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
  stmt_state_rel ctx func cenv cx ee s0 /\ alloca_history func s0 /\
  LIST_REL (\x v. eval_operand x s0 = SOME (typed_val_to_w256 tv v)) xs vs /\
  eval_operand needle s0 = SOME (typed_val_to_w256 tv v) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?s. gas_marked_path T ctx func s0 0 (OK s) /\
      stmt_state_rel ctx func cenv cx ee s /\
      eval_operand op s = SOME (bool_to_word (if bop = In then MEM v vs else ~MEM v vs)) /\
      (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==> lookup_var z s = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP s.vs_allocas aid = SOME b) /\
      s.vs_memory = s0.vs_memory /\ ~s.vs_halted /\
      s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func s /\ s.vs_alloca_next = s0.vs_alloca_next
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
  stmt_state_rel ctx func cenv cx (ee with gas_obs := []) t0 /\
  LIST_REL (\x v. eval_operand x t0 = SOME (typed_val_to_w256 tv v)) xs vs /\
  eval_operand needle t0 = SOME (typed_val_to_w256 tv v) /\
  wb_frame cenv es sa s0 t0 /\ sa.cs_next_var <= sm.cs_next_var /\
  ~t0.vs_halted /\ t0.vs_current_bb = sm.cs_current_bb /\
  t0.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  gas_summary_at T (ctx,func) []
    (vyperState$return (BoolV (if bop = In then MEM v vs else ~MEM v vs)))
    (ee with gas_obs := [],t0)
    (\res fin s. ?w. res = INL w /\
      expr_post ctx func cenv cx
        (Builtin (BaseT BoolT) (Bop bop) [e1; Builtin a (MakeArray t n) elems])
        es sa sb s0 fin w op s /\
      expr_store_bound cx (BaseT BoolT) w op s /\
      s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func s /\ s.vs_alloca_next = t0.vs_alloca_next)
    (\res fin r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all literal_typed_fragment_success_mem >> strip_tac >>
  simp[gasSummaryTheory.gas_summary_at_def] >>
  qexistsl_tac [`INL (BoolV (if bop = In then MEM v vs else ~MEM v vs))`, `ee`, `OK s`] >>
  conj_tac
  >- simp[gasSummaryTheory.gas_marked_exec_def, gasSummaryTheory.gas_explicit_def,
           vyperStateTheory.return_def] >>
  disj1_tac >> simp[exprSimMemDefsTheory.expr_store_bound_word, is_word_type_def] >>
  irule exprSimWordArgsTheory.expr_post_word_intro >>
  simp[vyperASTTheory.expr_type_def, is_word_type_def,
       loweringSliceTheory.word_value_def, valueEncodingTheory.val_to_w256_def,
       venomExecSemanticsTheory.bool_to_word_def] >>
  conj_tac
  >- (Cases_on `if bop = In then MEM v vs else ~MEM v vs` >>
      simp[venomExecSemanticsTheory.bool_to_word_def]) >>
  irule exprSimWordArgsTheory.wb_frame_readonly_tail >> goal_assum (drule_at Any) >>
  qexists_tac `sm` >> simp[]
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
  `is_ArrayT a` by simp[is_ArrayT_def] >>
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
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [gas_summary_at_def])
      >- suspend "normal"
      >> suspend "exit") >>
  suspend "exempt"
QED

Resume literal_expr_sim_mem[normal]:
  qpat_x_assum `(\rr ee t. _) _ _ _` (strip_assume_tac o BETA_RULE) >>
  gnvs[] >>
  `~t'.vs_halted` by
    metis_tac[gas_marked_exec_def, fragGasModeTheory.gas_marked_path_exec,
              fragGasPathTheory.gas_path_normal] >>
  qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
  disch_then (mp_tac o CONJUNCT1) >>
  disch_then (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  `!e. MEM e (e1::elems) ==> MEM e (e1::elems)` by simp[] >>
  `expr_sim_inv cenv cx env
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  drule_all literal_eval_exprs_typed >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `vs` >- gvs[exprSimPrecompilesTheory.typed_args_post_def] >>
  gnvs[exprSimPrecompilesTheory.typed_args_post_def] >>
  `LIST_REL (\x v. eval_operand x t' = SOME (typed_val_to_w256 tv v)) xs t` by
    (fs[listTheory.LIST_REL_EL_EQN, listTheory.EL_ZIP, listTheory.EVERY_EL] >>
     rpt strip_tac >> first_x_assum drule >> simp[] >>
     metis_tac[]) >>
  qpat_x_assum `typed_args_ready_mem _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `wb_args_shape _ _ _` kall_tac >>
  `stmt_state_rel ctx func cenv cx (es_end with gas_obs := []) t'` by fs[] >>
  `EVERY (\x. !z. x = Var z ==> not_fresh_at sm z) (needle::xs)` by
    (simp[] >> metis_tac[]) >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ _ /\ _` strip_assume_tac >>
  qpat_x_assum `value_has_type _ _ /\ _` strip_assume_tac >>
  drule_all literal_typed_continuation_summary_mem >>
  disch_then (qspecl_then
    [`SOME (expr_type e1)`, `n`, `elems`, `e1`, `ArrayT (expr_type e1) n`] mp_tac) >>
  rewrite_tac[gas_summary_at_def] >>
  disch_then (qx_choose_then `res` (qx_choose_then `es_end'`
    (qx_choose_then `r` (map_every assume_tac o CONJUNCTS)))) >>
  qexists_tac `marks` >> disj1_tac >>
  drule_all literal_body_action_flat >> disch_then (fn th => rewrite_tac[th]) >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`res`, `es_end'`, `r`] >> conj_tac
  >- (irule (Q.INST [`right` |-> `[]`] gas_marked_exec_bind_normal
               |> REWRITE_RULE [listTheory.APPEND_NIL]) >>
      qpat_assum `gas_marked_exec _ _ _ _ _ (INL _) _ _` (irule_at Any) >>
      gvs[]) >> gvs[vyperASTTheory.expr_type_def]
QED
Resume literal_expr_sim_mem[exit]:
  Cases_on `res` >- gvs[wb_args_exit_def] >>
  qexists_tac `marks` >> disj1_tac >>
  drule_all literal_body_action_flat >> disch_then (fn th => rewrite_tac[th]) >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INR y`, `es_end`, `r`] >> conj_tac
  >- (irule gas_marked_exec_bind_exception >> first_assum ACCEPT_TAC) >>
  disj2_tac >> gvs[wb_args_exit_def]
QED
Resume literal_expr_sim_mem[exempt]:
  qexists_tac `marks` >> disj2_tac >>
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
  cheat
QED
