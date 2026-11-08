(* Fixed32 RawLog: allocation precedes evaluation of the data operand. *)
Theory rawLogPtrFixedSim
Ancestors
  rawLogPtrTopics rawLogPtrCompose rawLogPtrFixed bodyPtrHashBuiltinsSuffix
  stmtReasonLitFragMemory
  bodyPtrHashBuiltinsAllocFrame bodyPtrWordBuiltinsWitnessCompose gasOutcomeMarkedPtr
  bodyPtrPreds bodyPtrDefs bodySimCallRawLog bodySimRawLogBodySource
  bodySimRawLogTopics bodySimRawLogSource bodySimRawLogTails bodySimMain bodySim
  exprSimHyps exprSimHypsDefs exprSimRawLog exprLowering exprLoweringProps
  exprSimPrecompiles exprSimWordArgs exprSimDefs exprSimHash loweringPosts
  exprOperandVar exprSimSource gasSummaryComposePtr gasExemptCert fragGasPathPtr
  fragExec vyperAST vyperState vyperInterpreter vyperValue vyperTypeSystem
  vyperContext vyperEvent compileEnv context emitHelper emitHelperProps
  venomState venomInst venomExecSemantics list finite_map words
Libs pairLib

Theorem raw_log_fixed32_body_frag_ptr:
  body_inv tops ctx cenv cx /\ body_exprs_ptr_ok cx args /\
  expr_body_pre cenv cx env (Call ann RawLog args dflt) es /\
  (?a elem bd topics data.
    args = [Builtin a (MakeArray elem bd) topics; data] /\
    expr_type data = BaseT (BytesT (Fixed 32))) /\
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

Resume raw_log_fixed32_body_frag_ptr[stages]:
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_raw_log_stages] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `lower_word_args cenv expr_type topics sa = (ops,sm)` >>
  rename1 `compile_alloc_buffer 32 sm = (buf,sk)` >>
  rename1 `lower_value compile_expr cenv _ data sk = (data_op,sn)` >>
  rename1 `emit_void MSTORE _ sn = (u,sp)` >>
  rename1 `emit_inst LOG _ [] sp = (u,sb)` >>
  `!s. expr_sim_inv cenv cx env s ==> expr_body_pre cenv cx env data s` by
    (qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     metis_tac[expr_body_pre_raw_log_arg, MEM]) >>
  qmatch_asmsub_abbrev_tac `expr_body_pre cenv cx env call es` >>
  qpat_x_assum `well_typed_expr env (Builtin _ _ _)` kall_tac >>
  qpat_x_assum `well_typed_expr env data` kall_tac >>
  qpat_x_assum `EVERY _ (MAP expr_type topics)` kall_tac >>
  drule_all lower_word_args_shape_ready >> strip_tac >>
  `cs_extends sm sk /\ sm.cs_next_var <= sk.cs_next_var /\
   sm.cs_next_id <= sk.cs_next_id` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, emit_op_def, emit_inst_def,
       comp_bind_def, comp_return_def, comp_ignore_bind_def,
       fresh_var_def, fresh_id_def, emit_def, cs_extends_def] >>
     rpt strip_tac >> gvs[] >> simp[cs_extends_def, rich_listTheory.IS_PREFIX_APPEND]) >>
  `cs_extends sk sn /\ sk.cs_next_var <= sn.cs_next_var /\
   sk.cs_next_id <= sn.cs_next_id` by
    (drule (cj 2 exprLoweringPropsTheory.compile_expr_grows) >> simp[]) >>
  suspend "frames"
QED

Resume raw_log_fixed32_body_frag_ptr[frames]:
  `cs_extends sn sp /\ cs_extends sp sb` by
    (qpat_x_assum `emit_void MSTORE _ _ = _` mp_tac >>
     qpat_x_assum `emit_inst LOG _ _ _ = _` mp_tac >>
     simp[emit_void_def, emit_inst_def, comp_bind_def, comp_return_def,
       fresh_id_def, emit_def, cs_extends_def] >>
     rpt strip_tac >> gvs[] >> simp[cs_extends_def, rich_listTheory.IS_PREFIX_APPEND]) >>
  `cs_extends sm sb /\ cs_extends sk sb /\ cs_extends sn sb` by
    metis_tac[cs_extends_trans] >>
  `fn_has_code sa sm func /\ fn_has_code sm sk func /\ fn_has_code sk sn func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  `local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv sk /\
   local_ptrs_reserved cenv sn` by
    metis_tac[local_ptrs_reserved_next_var, arithmeticTheory.LESS_EQ_TRANS] >>
  `~cx.txn.is_static` by fs[stmt_state_rel_def, state_rel_def] >>
  simp[Abbr `call`] >>
  drule_all raw_log_forced_source_eval >>
  simp[SF ETA_ss] >> disch_then (fn th => rewrite_tac[th]) >>
  irule gas_outcome_ptr_bind >>
  conj_tac
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_values >>
      goal_assum (drule_at Any) >> fs[]) >>
  conj_tac
  >- (rpt strip_tac >> irule gas_exempt_cert_error_values >> simp[]) >>
  suspend "topics"
QED

Resume raw_log_fixed32_body_frag_ptr[topics]:
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
  suspend "allocation"
QED

Resume raw_log_fixed32_body_frag_ptr[allocation]:
  drule_all raw_log_topics_marked_post_ptr >> strip_tac >>
  drule_all raw_log_marked_data_ready_ptr >> strip_tac >>
  `stmt_state_rel ctx func cenv cx (mid with gas_obs := []) t /\
   wb_frame cenv es sa s0 t` by fs[wb_args_post_def] >>
  `~t.vs_halted` by
    (drule gas_marked_exec_ptr_exec >> strip_tac >>
     qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gasSummaryTheory.gas_marked_exec_def,
          fragGasModeTheory.gas_marked_path_def] >> strip_tac >>
     drule fragGasPathTheory.gas_path_normal >> simp[]) >>
  `32 < dimword (:256)` by simp[dimword_def] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule stmtFragPtrTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[] >> metis_tac[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule stmtFragPtrTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[] >> metis_tac[]) >>
  drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  drule_all hash_literal_alloc_buffer_frame >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  suspend "allocation_path"
QED

Resume raw_log_fixed32_body_frag_ptr[allocation_path]:
  `p = STRING #"%" (toString sm.cs_next_var) /\
   emit_inst ALLOCA [Lit (n2w 32)] [p]
     (sm with cs_next_var := sm.cs_next_var + 1) = ((),sk) /\
   sk.cs_current_bb = sm.cs_current_bb /\
   LENGTH sk.cs_current_insts = SUC (LENGTH sm.cs_current_insts) /\
   emitted_insts sm sk = [mk_inst sm.cs_next_id ALLOCA [Lit (n2w 32)] [p]]` by
    (qpat_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     qpat_assum `buf.buf_operand = Var p` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[compile_alloc_buffer_def, emit_op_def, emit_inst_def,
       comp_bind_def, comp_return_def, comp_ignore_bind_def,
       fresh_var_def, fresh_id_def, emit_def] >> rpt strip_tac >> gvs[] >>
     simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND]) >>
  `fn_has_code (sm with cs_next_var := sm.cs_next_var + 1) sk func` by
    (qpat_assum `fn_has_code sm sk func` mp_tac >>
     simp[NoAsms, fn_has_code_def, emitted_blocks_def]) >>
  `step_inst_base (mk_inst sm.cs_next_id ALLOCA [Lit (n2w 32)] [p]) t = OK t'` by
    (qpat_assum `run_inst_seq _ t = OK t'` mp_tac >>
     qpat_assum `emitted_insts sm sk = _` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `p = _` (fn th => pure_rewrite_tac[th]) >>
     rpt (pop_assum kall_tac) >>
     simp[run_inst_seq_def, AllCaseEqs()]) >>
  qpat_x_assum `p = _` SUBST_ALL_TAC >>
  qpat_assum `emit_inst ALLOCA _ _ _ = _`
    (mp_then Any mp_tac assignTuplePtrAllocTheory.emit_alloca_zero_path_ptr) >>
  simp[] >>
  disch_then drule_all >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `cx_dead cx`] strip_assume_tac) >>
  `gas_path_ptr (cx_dead cx) 0 ctx func PG G tn t 0 G1 tn1
     (OK (t' with vs_inst_idx := LENGTH sk.cs_current_insts))` by fs[] >>
  suspend "allocated_post"
QED

Resume raw_log_fixed32_body_frag_ptr[allocated_post]:
  `wb_frame cenv es sa s0 t'` by
    (irule wb_frame_readonly_tail >> qexistsl_tac [`sm`, `t`] >> simp[]) >>
  `wb_frame cenv (mid with gas_obs := []) sm t t'` by
    (simp[wb_frame_def] >>
     irule exprSimPropsTheory.locals_kept_mem_tail >>
     qexists_tac `t` >> simp[]) >>
  suspend "allocated_topics"
QED

Resume raw_log_fixed32_body_frag_ptr[allocated_topics]:
  `wb_args_post ctx func cenv cx es sa s0 (mid with gas_obs := []) ops vs t'` by
    (simp[wb_args_post_def] >>
     qpat_assum `wb_args_post _ _ _ _ _ _ _ _ _ _ t`
       (strip_assume_tac o REWRITE_RULE [wb_args_post_def]) >>
     fs[LIST_REL_EL_EQN, EVERY_EL] >> rpt strip_tac >>
     rename1 `i < LENGTH topics` >>
     `eval_operand (EL i ops) t = SOME (val_to_w256 (EL i vs)) /\
      (!z. EL i ops = Var z ==> not_fresh_at sm z) /\
      (!l. EL i ops <> Label l)` by metis_tac[] >>
     Cases_on `EL i ops` >> gvs[eval_operand_def] >>
     irule wb_frame_vars >> goal_assum (drule_at Any) >> simp[]) >>
  `EVERY (\op. op_taint tn1 op = {}) ops` by
    (fs[EVERY_MEM] >> rpt strip_tac >>
     `op_taint tn1 op = op_taint tn op` by
       (qpat_assum `ghost_kept cenv _ sm G tn t G1 tn1`
          (mp_then Any mp_tac wordArgsPtrTheory.ghost_kept_operand) >>
        disch_then irule >> metis_tac[]) >> metis_tac[]) >>
  `MAP FDOM es.scopes = MAP FDOM (mid with gas_obs := []).scopes` by
    (drule gas_marked_exec_ptr_exec >> strip_tac >>
     qpat_assum `gas_marked_exec _ _ (eval_exprs _ _) _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[gasSummaryTheory.gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[] >>
     disch_then (mp_then Any mp_tac
       vyperEvalExprPreservesScopesDomTheory.eval_exprs_preserves_scopes_dom) >> simp[]) >>
  `ghost_kept cenv es sa G0 tn0 s0 G1 tn1` by
    (drule_all wordArgsPtrTheory.ghost_kept_wb_trans >> simp[]) >>
  suspend "data"
QED

Resume raw_log_fixed32_body_frag_ptr[data]:
  qpat_x_assum `G1 = _` SUBST_ALL_TAC >>
  qpat_x_assum `tn1 = _` SUBST_ALL_TAC >>
  irule gas_outcome_ptr_prefix >>
  first_assum (irule_at Any) >>
  `expr_body_pre cenv cx env data (mid with gas_obs := [])` by metis_tac[] >>
  drule expr_body_pre_gas_admissible >> strip_tac >>
  `lower_value compile_expr cenv (expr_type data) data sk = (data_op,sn)` by simp[] >>
  irule hash_expr_sim_ptr_suffix >>
  simp[] >>
  conj_tac
  >- (drule fragGasPathPtrTheory.gas_path_ptr_erase >> strip_tac >>
      drule fragGasPathTheory.gas_path_normal >> simp[]) >>
  qexistsl_tac [`cenv`, `d`, `data_op`, `sk`, `sn`, `expr_type data`] >>
  simp[] >>
  reverse conj_tac
  >- (rpt conj_tac
      >- (rpt strip_tac >> irule stmtFragPtrTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS])
      >- (rpt strip_tac >> irule stmtFragPtrTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS])
      >- (`EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
              (emitted_insts sm sk)` by simp[mk_inst_def, is_terminator_def] >>
          drule_all bodyPtrHashBuiltinsCursorTheory.hash_run_inst_seq_current_bb >> simp[])
      >- fs[exprLoweringPropsTheory.stmt_state_rel_inst_idx, stmt_state_rel_gas_obs] >>
      fs[bodyPtrHashBuiltinsGhostFrameTheory.hash_ghost_inv_inst_idx]) >>
  rpt gen_tac >> strip_tac >>
  suspend "tail"
QED

Resume raw_log_fixed32_body_frag_ptr[tail]:
  `wb_args_post ctx func cenv cx es sa s0 (mid with gas_obs := []) ops vs
     (t' with vs_inst_idx := SUC (LENGTH sm.cs_current_insts))` by
    (qpat_assum `wb_args_post _ _ _ _ _ _ _ _ _ _ t'` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[wb_args_post_def, exprLoweringPropsTheory.stmt_state_rel_inst_idx,
       wb_frame_def, locals_kept_def, lookup_var_def] >> metis_tac[]) >>
  `EVERY (\op. (!x. op = Var x ==> not_fresh_at sk x) /\
       (!l. op <> Label l)) ops` by
    (fs[EVERY_MEM] >> rpt strip_tac >>
     metis_tac[stmtFragPtrTheory.not_fresh_at_mono]) >>
  `sa.cs_next_var <= sk.cs_next_var /\ sa.cs_next_id <= sk.cs_next_id` by
    metis_tac[arithmeticTheory.LESS_EQ_TRANS] >>
  drule_all raw_log_data_post_transport_ptr >> strip_tac >>
  suspend "fixed_frame"
QED

Resume raw_log_fixed32_body_frag_ptr[fixed_frame]:
  `wb_frame cenv (mid with gas_obs := []) sk
     (t' with vs_inst_idx := SUC (LENGTH sm.cs_current_insts)) t''` by
    (drule exprSimWordArgsTheory.expr_post_frame >> simp[]) >>
  `MAP FDOM (mid with gas_obs := []).scopes = MAP FDOM ee.scopes` by
    (drule (SRULE [SF ETA_ss] forced_eval_expr_preserves_scopes_dom) >> simp[]) >>
  `stmt_state_rel ctx func cenv cx (mid with gas_obs := [])
     (t' with vs_inst_idx := SUC (LENGTH sm.cs_current_insts))` by
    fs[exprLoweringPropsTheory.stmt_state_rel_inst_idx, stmt_state_rel_gas_obs] >>
  `lookup_var (STRING #"%" (toString sm.cs_next_var)) t' = SOME w` by
    (qpat_assum `eval_operand buf.buf_operand t' = SOME w` mp_tac >>
     qpat_assum `buf.buf_operand = _` (fn th => pure_rewrite_tac[th]) >>
     pure_rewrite_tac[eval_operand_def] >> disch_then ACCEPT_TAC) >>
  `lookup_var (STRING #"%" (toString sm.cs_next_var))
     (t' with vs_inst_idx := SUC (LENGTH sm.cs_current_insts)) = SOME w` by
    (pure_rewrite_tac[lookup_var_def] >>
     qpat_assum `lookup_var _ t' = SOME w` mp_tac >>
     pure_rewrite_tac[lookup_var_def] >> simp[NoAsms]) >>
  qpat_assum `expr_post _ _ _ _ data _ _ _ _ _ _ _ t''`
    (mp_then Any mp_tac bodySimRawLogTailsTheory.raw_log_fixed_buffer_after_data) >>
  simp[lookup_var_def, local_region_def] >>
  disch_then (qspecl_then [`sa`, `STRING #"%" (toString sm.cs_next_var)`, `w`, `sm.cs_next_id`] mp_tac) >>
  (impl_tac >-
    (simp[GSYM lookup_var_def] >>
     qpat_assum `!name b k. local_region _ _ t' name b k ==> _` mp_tac >>
     simp[local_region_def, lookup_var_def])) >> strip_tac >>
  suspend "coverage"
QED

Resume raw_log_fixed32_body_frag_ptr[coverage]:
  qpat_assum `ptr_covers _ _ _ t' 32` mp_tac >>
  qmatch_goalsub_abbrev_tac `ptr_covers Ga ta pv t' 32` >>
  strip_tac >>
  `ptr_covers Ga ta pv (t' with vs_inst_idx := SUC (LENGTH sm.cs_current_insts)) 32` by
    (qpat_assum `ptr_covers Ga ta pv t' 32` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[ptr_covers_def, lookup_var_def]) >>
  `ptr_covers G' tn' pv t'' 32` by
    (irule ptr_covers_evaluation_frame >>
     qpat_assum `wb_frame _ _ sk _ t''` (irule_at Any) >>
     simp[Abbr `pv`, Abbr `Ga`, Abbr `ta`] >>
     first_assum (irule_at Any) >> simp[]) >>
  `expr_body_pre cenv cx env data (mid with gas_obs := gs)` by fs[] >>
  drule_all (SRULE [SF ETA_ss] expr_body_pre_base_result) >> strip_tac >>
  `?bs. v = BytesV bs` by
    (qpat_x_assum `!v'. INL v = _ ==> _` mp_tac >>
     simp[] >> Cases_on `v` >> simp[vyperTypingTheory.value_has_type_def]) >>
  gvs[] >>
  drule hash_fixed_post_view >> simp[] >> strip_tac >>
  `op_taint tn' data_op = {}` by fs[ptr_val_ok_def] >>
  `stmt_state_rel ctx func cenv cx ee t''` by fs[expr_post_def] >>
  suspend "fixed_suffix"
QED

Resume raw_log_fixed32_body_frag_ptr[fixed_suffix]:
  `fn_has_code sn sb func` by metis_tac[fn_has_code_split] >>
  `LENGTH ops < dimword (:256)` by (simp[dimword_def] >> decide_tac) >>
  `~t''.vs_call_ctx.cc_static` by
    (qpat_assum `stmt_state_rel _ _ _ _ ee t''` mp_tac >>
     rewrite_tac[stmt_state_rel_def, state_rel_def] >> strip_tac >> fs[]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x` by
    (rpt strip_tac >> irule stmtFragPtrTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[] >> decide_tac) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x` by
    (rpt strip_tac >> irule stmtFragPtrTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[] >> decide_tac) >>
  `sb.cs_current_bb = sn.cs_current_bb /\
   sb.cs_current_insts = sn.cs_current_insts ++ emitted_insts sn sb /\
   emitted_insts sn sb =
     [mk_inst sn.cs_next_id MSTORE [Var pv;data_op] [];
      mk_inst sp.cs_next_id LOG (Lit (n2w (LENGTH topics)) :: REVERSE ops ++ [Lit 32w;Var pv]) []]` by
    (qpat_assum `emit_void MSTORE _ _ = _` mp_tac >>
     qpat_assum `emit_inst LOG _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[emit_void_def, emit_inst_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, emit_def] >> rpt strip_tac >> gvs[] >>
     pure_rewrite_tac[emitted_insts_def] >> simp[NoAsms] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >> simp[NoAsms]) >>
  drule_all fn_has_code_code >> strip_tac >>
  `lookup_var pv t'' = SOME w` by fs[eval_operand_def] >>
  `lookup_block t''.vs_current_bb func.fn_blocks = SOME bb /\
   isPREFIX
     [mk_inst sn.cs_next_id MSTORE [Var pv;data_op] [];
      mk_inst sp.cs_next_id LOG (Lit (n2w (LENGTH ops)) :: REVERSE ops ++ [Lit 32w;Var pv]) []]
     (DROP t''.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX (emitted_insts sn sb) _` mp_tac >> simp[]) >>
  `!n b sz i. local_region cenv ee.scopes t'' n b sz /\ b <= i /\ i < b+sz ==>
     ~(w2n w <= i /\ i < w2n w+32)` by
    (qpat_assum `!n b sz. _ ==> regions_disjoint (w2n w) 32 b sz` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[GSYM local_region_def, GSYM lookup_var_def] >>
     rpt strip_tac >> first_x_assum drule >>
     simp[regions_disjoint_def] >> decide_tac) >>
  drule_all raw_log_fixed_tail >>
  disch_then (qspecl_then [`cx_dead cx`, `PG`,
    `ee.logs ++ [encode_raw_event_values cx.txn.target vs bs]`] strip_assume_tac) >>
  suspend "fixed_post"
QED

Resume raw_log_fixed32_body_frag_ptr[fixed_post]:
  qmatch_goalsub_abbrev_tac `expr_post ctx func cenv cx call` >>
  `expr_type call = NoneT` by simp[Abbr `call`, expr_type_def] >>
  `post_value_type cenv call = expr_type call` by simp[Abbr `call`] >>
  `LENGTH sb.cs_current_insts = t''.vs_inst_idx + 2` by simp[] >>
  rename1 `run_inst_seq [_;_] t'' = OK out` >>
  `run_inst_seq (emitted_insts sn sb) t'' = OK out` by
    (qpat_x_assum `run_inst_seq [_;_] t'' = OK out` mp_tac >> simp[]) >>
  `gas_path_ptr (cx_dead cx) 0 ctx func PG G' tn' t'' 0 G' tn''
     (OK (out with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (qpat_assum `gas_path_ptr _ _ _ _ _ _ _ t'' _ _ _ _` mp_tac >>
     qpat_assum `LENGTH sb.cs_current_insts = t''.vs_inst_idx + 2`
       (fn th => pure_rewrite_tac[GSYM th]) >> simp[]) >>
  `ghost_inv d cenv cx (ee with logs := ee.logs ++
      [encode_raw_event_values cx.txn.target vs bs]) G' tn''
      (out with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (qpat_assum `ghost_inv _ _ _ (_ with logs := _) _ _ _` mp_tac >>
     qpat_assum `LENGTH sb.cs_current_insts = t''.vs_inst_idx + 2`
       (fn th => pure_rewrite_tac[GSYM th]) >> simp[]) >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit 32w] [pv]) (fn_insts func) /\
   (mk_inst sm.cs_next_id ALLOCA [Lit 32w] [pv]).inst_opcode = ALLOCA` by
    simp[mk_inst_def] >>
  `!n b sz. local_region cenv ee.scopes t'' n b sz ==>
     regions_disjoint (w2n w) 32 b sz` by
    (qpat_assum `!n b sz. (?entry p w'. _) ==> _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[local_region_def, lookup_var_def]) >>
  qpat_assum `emit_inst LOG _ _ _ = _` mp_tac >>
  qpat_assum `LENGTH ops = LENGTH topics` (fn th => pure_rewrite_tac[GSYM th]) >>
  strip_tac >>
  `TAKE 32 (word_to_bytes_be w') = bs` by
    (qpat_assum `TAKE (LENGTH bs) _ = bs` mp_tac >>
     qpat_assum `LENGTH bs = 32` (fn th => pure_rewrite_tac[th]) >>
     disch_then ACCEPT_TAC) >>
  `expr_post ctx func cenv cx call es sa sb s0
     (ee with logs := ee.logs ++ [encode_raw_event_values cx.txn.target vs bs])
     NoneV (Lit 0w) (out with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule (cj 1 raw_log_fixed_counted_post_ptr) >>
     qpat_assum `run_inst_seq (emitted_insts sn sb) t'' = OK out` (irule_at Any) >>
     qpat_assum `emit_void MSTORE _ sn = _` (irule_at Any) >>
     qpat_assum `eval_operand data_op t'' = SOME w'` (irule_at Any) >>
     qpat_assum `eval_operand (Var pv) t'' = SOME w` (irule_at Any) >>
     qpat_assum `MEM (mk_inst sm.cs_next_id ALLOCA _ _) (fn_insts func)` (irule_at Any) >>
     qpat_assum `eval_operands ops t'' = _` (irule_at Any) >>
     qpat_assum `gas_path_ptr _ _ _ _ _ _ _ t'' _ _ _
       (OK (out with vs_inst_idx := LENGTH sb.cs_current_insts))` (irule_at Any) >>
     qpat_assum `ghost_inv _ _ _ (_ with logs := _) _ _
       (out with vs_inst_idx := LENGTH sb.cs_current_insts)` (irule_at Any) >>
     qpat_assum `post_value_type cenv call = _` (irule_at Any) >>
     simp[mk_inst_def] >> conj_tac >> first_assum ACCEPT_TAC) >>
  `sa.cs_next_var <= sn.cs_next_var /\ sa.cs_next_id <= sn.cs_next_id` by decide_tac >>
  `ghost_kept cenv es sa G0 tn0 s0 G' tn''` by
    (drule_all wordArgsPtrTheory.ghost_kept_wb_trans >> simp[]) >>
  suspend "summary"
QED

Resume raw_log_fixed32_body_frag_ptr[summary]:
  qexists_tac `[]` >> irule raw_log_tail_summary_ptr >>
  simp[] >> first_assum (irule_at Any) >> simp[] >>
  qexistsl_tac [`out with vs_inst_idx := LENGTH sb.cs_current_insts`, `bs`] >>
  simp[dest_BytesV_def, is_word_type_def, ptr_val_ok_def] >>
  `ee with gas_obs := [] = ee` by simp[vyperStateTheory.evaluation_state_component_equality] >>
  `LENGTH vs = LENGTH topics` by fs[wb_args_post_def, LIST_REL_EL_EQN] >>
  simp[GSYM vyperStateTheory.evaluation_state_updates_eq_literal, ptr_mem_ok_def,
    evaluate_type_def, ptr_buf_ok_def, lowered_value_type_def, Abbr `call`,
    expr_type_def] >>
  simp[type_memory_bytes_def, ptrDisciplineTheory.op_taint_def,
       valueEncodingTheory.val_in_memory_def, val_footprint_def,
       valueEncodingTheory.type_memory_size_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sn sb)` by simp[mk_inst_def, is_terminator_def] >>
  `out.vs_current_bb = t''.vs_current_bb` by
    (drule_all bodyPtrHashBuiltinsCursorTheory.hash_run_inst_seq_current_bb >> simp[]) >>
  simp[] >> conj_tac
  >- (qpat_x_assum `expr_post _ _ _ _ _ es sa sb s0 _ NoneV _ _` mp_tac >> simp[]) >>
  qpat_x_assum `ghost_inv _ _ _ (_ with logs := _) _ _
    (out with vs_inst_idx := LENGTH sb.cs_current_insts)` mp_tac >> simp[]
QED

Finalise raw_log_fixed32_body_frag_ptr
