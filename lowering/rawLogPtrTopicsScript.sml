(* RawLog topic prefixes reuse the typed-word pointer simulation. *)
Theory rawLogPtrTopics
Ancestors
  bodyPtrPreds bodyPtrDefs bodySim bodySimMain bodyWordArgsReady
  bodySimRawLogTopics bodySimRawLogBodySource exprSimRawLog
  typedWordArgsSimPtr typedWordArgsReadyPtr typedWordArgsPostPtr
  exprSimPrecompiles exprSimWordArgs exprSimHyps exprSimHypsDefs
  exprLoweringProps gasSummaryComposePtr gasSummary vyperAST vyperState vyperValue compileEnv list

Theorem raw_log_body_topics_sim_ptr:
  body_inv tops ctx cenv cx /\ body_exprs_ptr_ok cx topics /\
  (!e s. MEM e topics /\ expr_sim_inv cenv cx env s ==>
     expr_body_pre cenv cx env e s /\ expr_type e = BaseT (BytesT (Fixed 32))) /\
  expr_sim_inv cenv cx env es /\
  lower_word_args cenv expr_type topics sa = (ops,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  stmt_state_rel ctx func cenv cx es s0 /\ ghost_inv d cenv cx es G0 tn0 s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_exprs cx topics) (es,s0,G0,tn0)
    (\rr ee G tn t. ?vs. rr = INL vs /\
       typed_args_post_ptr d ctx func cenv cx es sa s0 G0 tn0 ee topics ops vs G tn t /\
       t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\rr ee ghosts r. wb_args_exit rr r)
Proof
  strip_tac >>
  `typed_args_ready ctx func cenv cx expr_type (expr_sim_inv cenv cx env) topics` by
    (irule body_word_args_ready >> reverse conj_tac >- metis_tac[] >>
     rpt strip_tac >>
     res_tac >> simp[is_word_type_def]) >>
  `ptr_args_ready d ctx PG func cenv cx expr_type (expr_sim_inv cenv cx env) topics` by
    (irule body_exprs_ptr_ok_ready >> metis_tac[]) >>
  `wb_args_shape cenv expr_type topics` by
    (irule typed_stack_args_shape >> qexistsl_tac [`cx`, `env`, `es`] >>
     simp[] >> rpt strip_tac >> res_tac >> simp[is_word_type_def]) >>
  irule lower_typed_args_sim_ptr >> simp[] >>
  qexists_tac `expr_sim_inv cenv cx env` >> simp[] >>
  qexists_tac `expr_type` >> simp[]
QED

Theorem raw_log_topics_marked_post_ptr:
  body_inv tops ctx cenv cx /\
  (!e s. MEM e topics /\ expr_sim_inv cenv cx env s ==>
     expr_body_pre cenv cx env e s /\ expr_type e = BaseT (BytesT (Fixed 32))) /\
  expr_sim_inv cenv cx env es /\
  gas_marked_exec_ptr D (ctx,func) PG (eval_exprs cx topics) (es,s0,G0,tn0)
    marks (INL vs) ee G tn r /\
  typed_args_post_ptr d ctx func cenv cx es sa s0 G0 tn0
    (ee with gas_obs := []) topics ops vs G tn t ==>
  expr_sim_inv cenv cx env (ee with gas_obs := []) /\
  wb_args_post ctx func cenv cx es sa s0 (ee with gas_obs := []) ops vs t /\
  ghost_inv d cenv cx (ee with gas_obs := []) G tn t /\
  EVERY (\op. op_taint tn op = {}) ops /\
  ghost_kept cenv es sa G0 tn0 s0 G tn
Proof
  strip_tac >> drule gas_marked_exec_ptr_exec >> strip_tac >>
  fs[typed_args_post_ptr_def] >>
  `body_exprs_ok cx topics` by metis_tac[body_sim_mutual] >>
  drule_all raw_log_topics_marked_post >> simp[]
QED

Theorem raw_log_marked_data_ready_ptr:
  body_inv tops ctx cenv cx /\
  body_exprs_ptr_ok cx
    [Builtin ann (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics; data] /\
  LENGTH topics <= n /\
  expr_sim_inv cenv cx env es /\
  expr_sim_inv cenv cx env (ee with gas_obs := []) /\
  (!s. expr_sim_inv cenv cx env s ==> expr_body_pre cenv cx env data s) /\
  gas_marked_exec_ptr D (ctx,func) PG (eval_exprs cx topics) (es,s0,G0,tn0)
    marks (INL vs) ee G tn (OK t) ==>
  expr_sim_ptr d ctx PG func cenv cx (expr_type data) data (ee with gas_obs := []) /\
  expr_vv_sim_ptr d ctx PG func cenv cx (expr_type data) data (ee with gas_obs := [])
Proof
  strip_tac >>
  `eval_exprs cx topics
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL vs, ee with gas_obs := [])` by
    (fs[gas_marked_exec_ptr_def] >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  drule_all raw_log_literal_read_success >>
  simp[bind_def, AllCaseEqs()] >> strip_tac >>
  `body_expr_ptr_ok cx data` by
    (qpat_x_assum `!ann'. _` (qspec_then `ann` strip_assume_tac) >>
     gvs[body_exprs_ptr_ok_def] >> metis_tac[]) >>
  `expr_body_pre cenv cx env data (ee with gas_obs := [])` by
    (first_x_assum irule >> simp[]) >>
  qpat_x_assum `body_expr_ptr_ok cx data`
    (assume_tac o PURE_REWRITE_RULE [body_expr_ptr_ok_def]) >>
  metis_tac[]
QED
