(* Dynamic RawLog: source composition over checked topic and data paths. *)
Theory rawLogPtrDynamicSim
Ancestors
  rawLogPtrTopics rawLogPtrCompose bodyPtrHashBuiltinsSuffix
  bodyPtrWordBuiltinsWitnessCompose gasOutcomeMarkedPtr bodyPtrPreds bodyPtrDefs
  bodySimCallRawLog bodySimRawLogBodySource bodySimRawLogTopics bodySimRawLogSource
  bodySimRawLogTails bodySimMain bodySim exprSimHyps exprSimHypsDefs
  exprSimRawLog exprLowering exprLoweringProps exprSimPrecompiles
  exprSimWordArgs exprSimDefs exprSimHash loweringPosts exprOperandVar exprSimSource
  gasSummaryComposePtr gasExemptCert fragGasPathPtr fragExec vyperAST vyperState
  vyperInterpreter vyperValue vyperTypeSystem vyperContext vyperEvent
  compileEnv context emitHelper emitHelperProps venomState venomInst
  venomExecSemantics list finite_map words
Libs pairLib

Theorem raw_log_dynamic_frag_ptr:
  body_inv tops ctx cenv cx /\ body_exprs_ptr_ok cx args /\
  expr_body_pre cenv cx env (Call ann RawLog args dflt) es /\
  (?a elem bd topics data cap.
    args = [Builtin a (MakeArray elem bd) topics; data] /\
    expr_type data = BaseT (BytesT (Dynamic cap))) /\
  compile_expr cenv ty (Call ann RawLog args dflt) sa = (StackValue ann (Lit 0w),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx (Call ann RawLog args dflt)) (read_result cx))
    expr_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\ ghost_inv d cenv cx es G0 tn0 s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (bind (eval_expr cx (Call ann RawLog args dflt)) (read_result cx)) (es,s0,G0,tn0)
    (\rr ee G tn t. ?v. rr = INL v /\
      expr_post ctx func cenv cx (Call ann RawLog args dflt) es sa sb s0 ee v (Lit 0w) t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx ee G tn t /\
      ptr_val_ok cx (expr_type (Call ann RawLog args dflt)) v (Lit 0w) G tn t /\
      (~is_word_type (expr_type (Call ann RawLog args dflt)) ==>
        ptr_buf_ok cenv (Call ann RawLog args dflt) (Lit 0w) G t) /\
      ghost_kept cenv es sa G0 tn0 s0 G tn)
    (\rr ee gt r. expr_exit rr r)
Proof
  strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  drule raw_log_body_pre_shape >> strip_tac >> gvs[] >>
  drule_all raw_log_literal_typed >> strip_tac >> gvs[] >>
  `body_exprs_ptr_ok cx topics` by
    (qpat_assum `body_exprs_ptr_ok cx [_;_]`
       (strip_assume_tac o REWRITE_RULE [body_exprs_ptr_ok_def]) >>
     qpat_x_assum `body_expr_ptr_ok cx (Builtin _ _ _)`
       (strip_assume_tac o PURE_REWRITE_RULE [body_expr_ptr_ok_def]) >>
     first_x_assum irule >> simp[] >> metis_tac[]) >>
  `!arg s. MEM arg topics /\ expr_sim_inv cenv cx env s ==>
     expr_body_pre cenv cx env arg s /\ expr_type arg = BaseT (BytesT (Fixed 32))` by
    (rpt gen_tac >> strip_tac >> conj_tac
     >- (qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
         qpat_x_assum `MEM arg topics` mp_tac >>
         qpat_x_assum `expr_sim_inv _ _ _ s` mp_tac >>
         rpt (pop_assum kall_tac) >> rpt strip_tac >>
         drule expr_body_pre_raw_log_arg >>
         disch_then (qspec_then
           `Builtin (ArrayT (BaseT (BytesT (Fixed 32))) (Dynamic n))
             (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics` mp_tac) >>
         simp[] >> strip_tac >>
         first_x_assum (qspec_then `s` mp_tac) >> simp[] >> strip_tac >>
         drule expr_body_pre_builtin_arg >> disch_then irule >> simp[]) >>
     fs[EVERY_MEM, MEM_MAP] >> metis_tac[]) >>
  `wb_args_shape cenv expr_type topics` by
    (irule typed_stack_args_shape >> qexistsl_tac [`cx`, `env`, `es`] >>
     simp[] >> rpt strip_tac >> res_tac >> simp[is_word_type_def]) >>
  suspend "stages"
QED

Resume raw_log_dynamic_frag_ptr[stages]:
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_raw_log_stages] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `lower_word_args cenv expr_type topics sa = (ops,sm)` >>
  rename1 `lower_value compile_expr cenv _ data sm = (data_op,sn)` >>
  rename1 `emit_op MLOAD [data_op] sn = (len_op,sl)` >>
  rename1 `emit_op ADD [data_op; Lit 32w] sl = (ptr_op,sp)` >>
  rename1 `emit_inst LOG _ [] sp = ((),sb)` >>
  `!s. expr_sim_inv cenv cx env s ==> expr_body_pre cenv cx env data s` by
    (qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     metis_tac[expr_body_pre_raw_log_arg, MEM]) >>
  qmatch_asmsub_abbrev_tac `expr_body_pre cenv cx env call es` >>
  qpat_x_assum `well_typed_expr env (Builtin _ _ _)` kall_tac >>
  qpat_x_assum `well_typed_expr env data` kall_tac >>
  qpat_x_assum `EVERY _ (MAP expr_type topics)` kall_tac >>
  drule_all lower_word_args_shape_ready >> strip_tac >>
  `cs_extends sm sn /\ sm.cs_next_var <= sn.cs_next_var /\
   sm.cs_next_id <= sn.cs_next_id` by
    (drule (cj 2 exprLoweringPropsTheory.compile_expr_grows) >> simp[]) >>
  `cs_extends sn sl /\ cs_extends sl sp /\ cs_extends sp sb` by
    (qpat_x_assum `emit_op MLOAD _ _ = _` mp_tac >>
     qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
     qpat_x_assum `emit_inst LOG _ _ _ = _` mp_tac >>
     simp[emit_op_def, emit_inst_def, comp_bind_def, comp_return_def, comp_ignore_bind_def,
          fresh_var_def, fresh_id_def, emit_def, cs_extends_def] >>
     rpt strip_tac >> gvs[] >> simp[cs_extends_def, rich_listTheory.IS_PREFIX_APPEND]) >>
  `cs_extends sm sb /\ cs_extends sn sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sm func /\ fn_has_code sm sn func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  `local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv sn` by
    metis_tac[local_ptrs_reserved_next_var, arithmeticTheory.LESS_EQ_TRANS] >>
  `!z. data_op = Var z ==> not_fresh_at sn z` by
    (drule exprOperandVarTheory.compile_lower_value_var >> simp[]) >>
  `~cx.txn.is_static` by fs[stmt_state_rel_def, state_rel_def] >>
  suspend "topics"
QED

Resume raw_log_dynamic_frag_ptr[topics]:
  simp[Abbr `call`] >>
  drule_all raw_log_forced_source_eval >>
  simp[SF ETA_ss] >> disch_then (fn th => rewrite_tac[th]) >>
  irule gas_outcome_ptr_bind >>
  conj_tac
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_values >>
      goal_assum (drule_at Any) >> fs[]) >>
  conj_tac
  >- (rpt strip_tac >> irule gas_exempt_cert_error_values >> simp[]) >>
  suspend "topics_outcome"
QED

Resume raw_log_dynamic_frag_ptr[topics_outcome]:
  `(\(rr:value list + exception) (ee:evaluation_state) (gt:(string |-> (num # num)) # taint) r.
       ?exc. rr = INR exc /\ expr_exit (INR exc : value + exception) r) =
   (\rr ee gt r. wb_args_exit rr r)` by
    (simp[FUN_EQ_THM] >> Cases >> simp[wb_args_exit_def]) >>
  BETA_TAC >> asm_rewrite_tac[] >>
  drule_all raw_log_body_topics_sim_ptr >>
  disch_then (qspec_then `PG` assume_tac) >>
  irule gas_outcome_ptr_marked_conseq >>
  first_assum (irule_at Any) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  suspend "data" 
QED

Resume raw_log_dynamic_frag_ptr[data]:
  drule_all raw_log_topics_marked_post_ptr >> strip_tac >>
  drule_all raw_log_marked_data_ready_ptr >> strip_tac >>
  `stmt_state_rel ctx func cenv cx (mid with gas_obs := []) t` by
    fs[wb_args_post_def] >>
  `~t.vs_halted` by
    (drule gas_marked_exec_ptr_exec >> strip_tac >>
     qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gasSummaryTheory.gas_marked_exec_def,
          fragGasModeTheory.gas_marked_path_def] >> strip_tac >>
     drule fragGasPathTheory.gas_path_normal >> simp[]) >>
  `expr_body_pre cenv cx env data (mid with gas_obs := [])` by metis_tac[] >>
  drule expr_body_pre_gas_admissible >> strip_tac >>
  `lower_value compile_expr cenv (expr_type data) data sm = (data_op,sn)` by simp[] >>
  irule hash_expr_sim_ptr_suffix >>
  simp[] >>
  qexistsl_tac [`cenv`, `d`, `data_op`, `sm`, `sn`, `expr_type data`] >>
  simp[] >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    (qpat_x_assum `sa.cs_next_var <= sm.cs_next_var` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  reverse conj_tac
  >- (rpt conj_tac
      >- metis_tac[]
      >- metis_tac[] >>
      qpat_x_assum `!d. expr_sim_ptr _ _ _ _ _ _ _ _ _ /\ _`
        (qspec_then `d` strip_assume_tac) >> fs[stmt_state_rel_gas_obs, stmtFragPtrTheory.ghost_inv_gas_obs]) >>
  rpt gen_tac >> strip_tac >>
  suspend "tail"
QED

Resume raw_log_dynamic_frag_ptr[tail]:
  qmatch_goalsub_abbrev_tac `expr_post ctx func cenv cx call` >>
  `expr_body_pre cenv cx env data (mid with gas_obs := gs)` by fs[] >>
  drule_all (SRULE [SF ETA_ss] expr_body_pre_base_result) >> strip_tac >>
  `?bs. v = BytesV bs` by
    (qpat_x_assum `!v'. INL v = _ ==> _` mp_tac >>
     simp[] >> Cases_on `v` >> simp[vyperTypingTheory.value_has_type_def]) >>
  gvs[] >>
  `MAP FDOM es.scopes = MAP FDOM (mid with gas_obs := []).scopes` by
    (drule gas_marked_exec_ptr_exec >> strip_tac >>
     qpat_assum `gas_marked_exec _ _ (eval_exprs _ _) _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[gasSummaryTheory.gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[] >>
     disch_then (mp_then Any mp_tac
       vyperEvalExprPreservesScopesDomTheory.eval_exprs_preserves_scopes_dom) >> simp[]) >>
  drule_all raw_log_data_post_transport_ptr >> strip_tac >>
  `evaluate_type (get_tenv cx) (expr_type data) =
     SOME (BaseTV (BytesT (Dynamic cap)))` by
    (`expr_body_pre cenv cx env data mid` by metis_tac[] >>
     qpat_assum `expr_body_pre _ _ _ data _`
       (mp_then Any mp_tac expr_body_pre_type_evaluates) >>
     simp[vyperValueTheory.evaluate_type_def, AllCaseEqs()]) >>
  drule_all raw_log_dynamic_data_view >> strip_tac >>
  `~is_word_type (expr_type data)` by simp[is_word_type_def] >>
  `evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic cap))) =
    SOME (BaseTV (BytesT (Dynamic cap)))` by
    (qpat_assum `evaluate_type _ (expr_type data) = _` mp_tac >>
     qpat_assum `expr_type data = _` (fn th => pure_rewrite_tac[th]) >>
     disch_then ACCEPT_TAC) >>
  `~is_word_type (BaseT (BytesT (Dynamic cap)))` by simp[is_word_type_def] >>
  `post_value_type cenv data = expr_type data` by
    (irule loweringPostsTheory.post_value_type_bytestring >>
     qpat_assum `expr_type data = _`
       (fn th => simp[th, compileEnvTheory.is_bytestring_type_def])) >>
  qpat_x_assum `post_value_type cenv data = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  drule_all bodyPtrHashBuiltinsCasesTheory.hash_dynamic_bytes_operand >> strip_tac >>
  gvs[] >>
  fs[ptr_covers_def] >>
  `w = n2w b` by fs[eval_operand_def] >>
  `b < dimword (:256)` by decide_tac >>
  gvs[wordsTheory.w2n_n2w] >>
  suspend "tail_ready"
QED

Resume raw_log_dynamic_frag_ptr[tail_ready]:
  `fn_has_code sn sb func` by metis_tac[fn_has_code_split] >>
  `EVERY (\op. !z. op = Var z ==> not_fresh_at sn z) ops` by
    (qpat_assum `EVERY (\x. (!z. x = Var z ==> _) /\ _) ops` mp_tac >>
     qpat_assum `sm.cs_next_var <= sn.cs_next_var` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[EVERY_MEM, not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `LENGTH ops < dimword (:256)` by (simp[dimword_def] >> decide_tac) >>
  `~t'.vs_call_ctx.cc_static` by
    (qpat_assum `expr_post _ _ _ _ data _ _ _ _ _ _ _ t'` mp_tac >>
     rewrite_tac[expr_post_def, stmt_state_rel_def, state_rel_def] >>
     strip_tac >> fs[]) >>
  `mem_word_at b t'.vs_memory = n2w (LENGTH bs)` by fs[valueEncodingPropsTheory.mem_word_at_eq_mload] >>
  `stmt_state_rel ctx func cenv cx ee t'` by fs[expr_post_def] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x` by
    (rpt strip_tac >> irule stmtFragPtrTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[] >> metis_tac[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x` by
    (rpt strip_tac >> irule stmtFragPtrTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[] >> metis_tac[]) >>
  `b + 32 + LENGTH bs <= b' + sz'` by decide_tac >>
  `!i. b <= i /\ i < b + 32 + LENGTH bs ==> i NOTIN tn'.t_mem` by
    (qpat_assum `!i. b <= i /\ i < b + (LENGTH bs + 32) ==> _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     disch_tac >> gen_tac >> disch_tac >> first_x_assum irule >> decide_tac) >>
  qpat_assum `emit_inst LOG _ _ _ = _` mp_tac >>
  qpat_assum `LENGTH ops = LENGTH topics` (fn th => pure_rewrite_tac[GSYM th]) >>
  strip_tac >>
  drule_all (SRULE [APPEND] rawLogPtrDynamicTailTheory.raw_log_dynamic_tail_ptr) >>
  disch_then (qspecl_then [`cx_dead cx`, `PG`,
    `ee.logs ++ [encode_raw_event_values cx.txn.target vs bs]`] strip_assume_tac) >>
  `expr_type call = NoneT` by simp[Abbr `call`, expr_type_def] >>
  `post_value_type cenv call = expr_type call` by simp[Abbr `call`] >>
  `sa.cs_next_var <= sn.cs_next_var` by decide_tac >>
  `!x. Var p = Var x ==> not_fresh_at sn x` by simp[] >>
  drule_all (SRULE [APPEND] raw_log_dynamic_counted_post_ptr) >>
  strip_tac >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule (SRULE [SF ETA_ss] forced_eval_expr_preserves_scopes_dom) >> simp[] >> metis_tac[]) >>
  `sa.cs_next_id <= sn.cs_next_id` by decide_tac >>
  `ghost_kept cenv es sa G0 tn0 s0 G'' tn''` by
    (drule_all wordArgsPtrTheory.ghost_kept_wb_trans >> simp[]) >>
  suspend "summary"
QED

Resume raw_log_dynamic_frag_ptr[summary]:
  qexists_tac `[]` >> irule raw_log_tail_summary_ptr >>
  simp[] >>
  first_assum (irule_at Any) >>
  simp[] >>
  qexistsl_tac [`t'' with vs_inst_idx := LENGTH sb.cs_current_insts`, `bs`] >>
  simp[dest_BytesV_def, is_word_type_def, ptr_val_ok_def] >>
  `ee with gas_obs := [] = ee` by simp[vyperStateTheory.evaluation_state_component_equality] >>
  `LENGTH vs = LENGTH topics` by fs[wb_args_post_def, LIST_REL_EL_EQN] >>
  simp[GSYM vyperStateTheory.evaluation_state_updates_eq_literal, ptr_mem_ok_def,
    evaluate_type_def, ptr_buf_ok_def, lowered_value_type_def, Abbr `call`,
    expr_type_def] >>
  reverse conj_tac
  >- simp[type_memory_bytes_def, ptrDisciplineTheory.op_taint_def,
          valueEncodingTheory.val_in_memory_def, val_footprint_def,
          valueEncodingTheory.type_memory_size_def] >>
  `sb.cs_current_bb = sn.cs_current_bb /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sn sb)` by
    (qpat_x_assum `emit_op MLOAD _ _ = _` mp_tac >>
     qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
     qpat_x_assum `emit_inst LOG _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[emit_op_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_var_def, fresh_id_def, emit_def] >>
     rpt strip_tac >> gvs[] >>
     pure_rewrite_tac[emitted_insts_def] >> simp[NoAsms] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC] >>
     pure_rewrite_tac[rich_listTheory.DROP_LENGTH_APPEND] >>
     simp[NoAsms, mk_inst_def, is_terminator_def]) >>
  drule_all bodyPtrHashBuiltinsCursorTheory.hash_run_inst_seq_current_bb >> simp[]
QED

Finalise raw_log_dynamic_frag_ptr
