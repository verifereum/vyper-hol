(* RawLog body simulation boundaries. *)
Theory bodySimRawLog
Ancestors
  bodySim exprSimSend exprSimHyps vyperTypeSystem vyperAST list
  exprSimAggregateSource vyperInterpreter vyperValue vyperState vyperContext
  exprSimWordArgs exprLowering compileEnv emitHelper venomExecSemantics
  exprLoweringProps venomState venomMemDefs exprSimDefs exprSimStack loweringPosts exprSimHypsDefs exprSimSource vyperEvent fragExec venomInst
  exprSimHash exprSimBuffer exprSimPrecompiles emitHelperProps ASCIInumbers exprSimRawLog
  bodySimRawLogSource bodySimRawLogBodySource bodySimRawLogTails
Libs
  pairLib


Theorem raw_log_step_frame:
  inst.inst_opcode = LOG /\
  inst.inst_operands = Lit (n2w (LENGTH ops)) ::
    (REVERSE ops ++ [sz; pop]) /\ LENGTH ops <= 4 /\
  eval_operand pop s = SOME off /\ eval_operand sz s = SOME len /\
  eval_operands ops s = SOME (MAP event_value_to_word vals) /\
  TAKE (w2n len) (DROP (w2n off) s.vs_memory ++
    REPLICATE (w2n len) 0w) = bytes /\
  stmt_state_rel ctx func cenv cx es s /\ wb_frame cenv es0 sa s0 s ==>
  ?t. step_inst_base inst s = OK t /\
    stmt_state_rel ctx func cenv cx
      (es with logs := es.logs ++
        [encode_raw_event_values cx.txn.target vals bytes]) t /\
    wb_frame cenv es0 sa s0 t
Proof
  strip_tac >>
  `~s.vs_call_ctx.cc_static` by fs[stmt_state_rel_def, state_rel_def] >>
  drule_all raw_log_step >>
  disch_then SUBST1_TAC >>
  `s.vs_call_ctx.cc_address = cx.txn.target` by
    fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  simp[encode_raw_event_values_def, encode_raw_event_def] >>
  conj_tac >- (irule raw_log_state_rel >> simp[]) >>
  irule raw_log_wb_frame >> simp[]
QED


Theorem raw_log_dynamic_tail_frag:
  emit_op MLOAD [data_op] sm = (len_op, s1) /\
  emit_op ADD [data_op; Lit 32w] s1 = (ptr_op, s2) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) ::
    (REVERSE ops ++ [len_op; ptr_op])) [] s2 = (u, sb) /\
  (!x. data_op = Var x ==> not_fresh_at sm x) /\
  EVERY (\op. !x. op = Var x ==> not_fresh_at sm x) ops /\
  LENGTH ops <= 4 /\
  eval_operand data_op s = SOME (n2w b) /\
  eval_operands ops s = SOME (MAP event_value_to_word vals) /\
  mload b s = n2w (LENGTH bs) /\
  TAKE (LENGTH bs) (DROP (b + 32) s.vs_memory ++
    REPLICATE (LENGTH bs) 0w) = bs /\
  b + 32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sm /\
  wb_frame cenv es0 sa s0 s /\ sa.cs_next_var <= sm.cs_next_var /\
  expr_type e = NoneT ==>
  frag_exec ctx sm sb ($= s)
    (expr_post ctx func cenv cx e es0 sa sb s0
      (es with logs := es.logs ++
        [encode_raw_event_values cx.txn.target vals bs]) NoneV (Lit 0w))
    (expr_exit (INL NoneV))
Proof
  strip_tac >>
  `LENGTH ops < dimword (:256)` by simp[wordsTheory.dimword_def] >>
  irule raw_log_dynamic_tail_core >>
  qpat_assum `emit_inst LOG _ _ _ = _` (irule_at Any) >>
  simp[] >> qexistsl_tac [`s1`, `data_op`, `b`] >> simp[]
QED


Theorem raw_log_fixed_tail_frag:
  emit_void MSTORE [ptr_op; data_op] sm = (u, s1) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) ::
    (REVERSE ops ++ [Lit 32w; ptr_op])) [] s1 = (u', sb) /\
  eval_operand ptr_op s = SOME p /\ eval_operand data_op s = SOME w /\
  eval_operands ops s = SOME (MAP event_value_to_word vals) /\ LENGTH ops <= 4 /\
  LENGTH bs = 32 /\ TAKE 32 (word_to_bytes_be w) = bs /\
  stmt_state_rel ctx func cenv cx es s /\ wb_frame cenv es0 sa s0 s /\
  local_ptrs_reserved cenv sa /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n p,32) /\
  (!aid b sz. aid < sa.cs_next_id /\
     FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
     regions_disjoint (w2n p) 32 b sz) /\
  (!n b sz. local_region cenv es.scopes s n b sz ==>
     regions_disjoint (w2n p) 32 b sz) /\ expr_type e = NoneT ==>
  frag_exec ctx sm sb ($= s)
    (expr_post ctx func cenv cx e es0 sa sb s0
      (es with logs := es.logs ++
        [encode_raw_event_values cx.txn.target vals bs]) NoneV (Lit 0w))
    (expr_exit (INL NoneV))
Proof
  strip_tac >>
  `LENGTH ops < dimword (:256)` by simp[wordsTheory.dimword_def] >>
  Cases_on `u` >> Cases_on `u'` >> fs[] >>
  irule raw_log_fixed_tail_core >> simp[] >>
  qpat_assum `emit_inst LOG _ _ _ = _` (irule_at Any) >>
  simp[] >> metis_tac[]
QED


Theorem raw_log_fixed32_topics_frag[local]:
  (!rr et t0. eval_exprs cx topics es = (rr,et) /\ fn_has_code sa s1 func ==>
    frag_exec ctx sa s1 (\s. s = t0 /\ stmt_state_rel ctx func cenv cx es s)
      (\s. ?vs. rr = INL vs /\ wb_args_post ctx func cenv cx es sa t0 et ops vs s)
      (wb_args_exit rr)) /\
  (!vs et. eval_exprs cx topics es = (INL vs,et) ==> Inv et) /\ Inv es /\
  wb_args_shape cenv expr_type topics /\ wb_args_shape cenv expr_type [data] /\
  LENGTH topics <= n /\ LENGTH topics <= 4 /\
  expr_type data = BaseT (BytesT (Fixed 32)) /\
  e = Call NoneT RawLog
    [Builtin a (MakeArray (SOME (BaseT (BytesT (Fixed 32)))) (Dynamic n)) topics;
     data] dflt /\
  (!vs es1. eval_exprs cx topics es = (INL vs,es1) /\ Inv es1 ==>
    expr_sim ctx func cenv cx (expr_type data) data es1 /\
    (!r es2. (do tv <- eval_expr cx data; read_result cx tv od) es1 = (r,es2) ==>
       expr_res_ok r) /\
    (!v es2. (do tv <- eval_expr cx data; read_result cx tv od) es1 = (INL v,es2) ==>
       ?bs. v = BytesV bs /\ LENGTH bs = 32 /\
            TAKE 32 (word_to_bytes_be (val_to_w256 v)) = bs)) /\
  lower_word_args cenv expr_type topics sa = (ops,s1) /\
  compile_alloc_buffer 32 s1 = (buf,s2) /\
  lower_value compile_expr cenv (expr_type data) data s2 = (data_op,s3) /\
  emit_void MSTORE [buf.buf_operand;data_op] s3 = (u,s4) /\
  emit_inst LOG (Lit (n2w (LENGTH ops)) ::
    (REVERSE ops ++ [Lit 32w;buf.buf_operand])) [] s4 = (u',sb) /\
  (do tv <- eval_expr cx e; read_result cx tv od) es = (res,es') /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa ==>
  frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
    (\s. ?v. res = INL v /\ expr_post ctx func cenv cx e es sa sb s0 es' v (Lit 0w) s)
    (expr_exit res)
Proof
  strip_tac >>
  drule_all lower_word_args_shape_ready >> strip_tac >>
  `cs_extends s2 s3 /\ s2.cs_next_var <= s3.cs_next_var /\
   s2.cs_next_id <= s3.cs_next_id` by
    (qpat_x_assum `wb_args_shape _ _ [data]` mp_tac >>
     simp[wb_args_shape_def] >> strip_tac >>
     first_x_assum (qspecl_then [`s2`, `s3`, `data_op`] mp_tac) >> gvs[]) >>
  `cs_extends s1 s2 /\ s1.cs_next_var <= s2.cs_next_var /\
   s1.cs_next_id <= s2.cs_next_id /\ cs_extends s3 s4 /\ cs_extends s4 sb` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     qpat_x_assum `emit_inst _ _ _ _ = _` mp_tac >>
     simp[contextTheory.compile_alloc_buffer_def, emit_op_def, emit_void_def,
          emit_inst_def, comp_bind_def, comp_return_def, comp_ignore_bind_def,
          fresh_var_def, fresh_id_def, emit_def, cs_extends_def] >>
     rpt strip_tac >> gvs[] >> simp[cs_extends_def, rich_listTheory.IS_PREFIX_APPEND]) >>
  `cs_extends s1 sb /\ cs_extends s2 sb /\ cs_extends s3 sb` by
    metis_tac[cs_extends_trans] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\ fn_has_code s2 s3 func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  `local_ptrs_reserved cenv s1 /\ local_ptrs_reserved cenv s2` by
    metis_tac[local_ptrs_reserved_next_var, arithmeticTheory.LESS_EQ_TRANS] >>
  Cases_on `eval_exprs cx topics es` >>
  rename1 `eval_exprs cx topics es = (tr, es1)` >>
  reverse (Cases_on `tr`)
  >- (qpat_x_assum `e = _` SUBST_ALL_TAC >>
      qpat_x_assum `(do tv <- eval_expr cx _; read_result cx tv od) es = _` mp_tac >>
      simp[raw_log_source_eval, bind_def] >> strip_tac >> gvs[] >>
      qpat_x_assum `!t0. frag_exec _ _ _ _ _ _` (qspec_then `s0` mp_tac) >>
      simp[wb_args_exit_def] >> strip_tac >>
      irule frag_exec_exit_prefix >> goal_assum (drule_at Any) >> simp[]) >>
  rename1 `eval_exprs cx topics es = (INL vals, es1)` >>
  `Inv es1` by metis_tac[] >>
  qpat_x_assum `!vs es1. _` mp_tac >> simp[] >> strip_tac >>
  Cases_on `(do tv <- eval_expr cx data; read_result cx tv od) es1` >>
  rename1 `(do tv <- eval_expr cx data; read_result cx tv od) es1 = (dr, es2)` >>
  `expr_res_ok dr` by metis_tac[] >>
  `MAP FDOM es.scopes = MAP FDOM es1.scopes` by
    metis_tac[vyperEvalExprPreservesScopesDomTheory.eval_exprs_preserves_scopes_dom] >>
  `MAP FDOM es1.scopes = MAP FDOM es2.scopes` by
    metis_tac[forced_eval_expr_preserves_scopes_dom] >>
  reverse (Cases_on `stmt_state_rel ctx func cenv cx es s0`)
  >- (`(\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s) = (\s. F)` by
        (simp[FUN_EQ_THM] >> metis_tac[]) >>
      simp[] >> irule frag_exec_false_pre) >>
  qpat_x_assum `!rr et t0. _` mp_tac >> simp[] >>
  disch_then (qspec_then `s0` mp_tac) >>
  simp[wb_args_exit_def] >>
  disch_then (mp_then Any irule wb_frag_then) >> simp[] >>
  qx_gen_tac `t` >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es1 t` by fs[wb_args_post_def] >>
  `eval_operand (Lit 0w) t = SOME 0w /\
   (!x. Lit 0w = Var x ==> not_fresh_at s1 x) /\ 32 < dimword (:256)` by
    simp[eval_operand_def, wordsTheory.dimword_def] >>
  drule_all exprSimAllocTheory.alloc_buffer_source_frag >>
  disch_then (qspec_then `expr_exit res` strip_assume_tac) >>
  rename1 `frag_exec ctx s1 s2 (\z. z = t) (\z. z = allocated) _` >>
  `wb_args_post ctx func cenv cx es sa s0 es1 ops vals allocated` by
    (qpat_assum `wb_args_post _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [wb_args_post_def]) >>
     simp[wb_args_post_def] >> conj_tac
     >- (qpat_x_assum `!x. not_fresh_at s1 x ==> _` mp_tac >>
         qpat_x_assum `LIST_REL _ ops vals` mp_tac >>
         qpat_x_assum `EVERY _ ops` mp_tac >>
         rpt (pop_assum kall_tac) >>
         qid_spec_tac `vals` >> Induct_on `ops` >> simp[] >>
         gen_tac >> Cases_on `vals` >> simp[] >> rpt strip_tac
         >- (irule exprSimOpsTheory.eval_operand_frame >> simp[] >>
             qexistsl_tac [`s1`, `t`] >> simp[]) >>
         first_x_assum irule >> simp[]) >>
     irule wb_frame_readonly_tail >> qexistsl_tac [`s1`, `t`] >> simp[]) >>
  qpat_x_assum `frag_exec ctx s1 s2 _ _ _`
    (mp_then Any irule frag_exec_then) >> simp[] >>
  `expr_sim ctx func cenv cx (expr_type data) data es1` by simp[] >>
  reverse (Cases_on `dr`)
  >- (`res = INR y /\ es' = es2` by
        (qpat_assum `(do tv <- eval_expr cx data; read_result cx tv od) es1 = _`
           (assume_tac o SRULE [bind_def]) >>
         qpat_x_assum `(do tv <- eval_expr cx e; read_result cx tv od) es = _` mp_tac >>
         simp[raw_log_source_eval, bind_def]) >>
      gvs[] >> drule_all expr_sim_apply >>
      disch_then (qspec_then `allocated` mp_tac) >> simp[] >> strip_tac >>
      irule frag_exec_exit_prefix >> simp[] >>
      goal_assum (drule_at Any) >> simp[] >>
      qpat_x_assum `frag_exec ctx s2 s3 _ _ _`
        (mp_then Any irule frag_exec_weaken) >> simp[]) >>
  rename1 `(do tv <- eval_expr cx data; read_result cx tv od) es1 = (INL dv, es2)` >>
  `?bs. dv = BytesV bs /\ LENGTH bs = 32 /\
        TAKE 32 (word_to_bytes_be (val_to_w256 dv)) = bs` by metis_tac[] >>
  `LENGTH vals = LENGTH topics` by fs[wb_args_post_def, LIST_REL_EL_EQN] >>
  `res = INL NoneV /\ es' = es2 with logs := es2.logs ++
     [encode_raw_event_values cx.txn.target vals bs]` by
    (qpat_assum `(do tv <- eval_expr cx data; read_result cx tv od) es1 = _`
       (assume_tac o SRULE [bind_def]) >>
     qpat_x_assum `(do tv <- eval_expr cx e; read_result cx tv od) es = _` mp_tac >>
     simp[raw_log_source_eval, bind_def, lift_option_type_def, dest_BytesV_def,
          type_check_def, assert_def, push_log_def, ignore_bind_def,
          return_def, read_result_def]) >>
  `expr_exit res = (\r. F)` by simp[expr_exit_def, FUN_EQ_THM] >>
  `(\s. s = allocated) =
   (\s. s = allocated /\ stmt_state_rel ctx func cenv cx es1 s)` by
    (simp[FUN_EQ_THM] >> metis_tac[]) >>
  pop_assum SUBST1_TAC >>
  drule_all expr_sim_apply >> disch_then (qspec_then `allocated` mp_tac) >>
  `expr_exit (INL dv) = (\r. F)` by simp[FUN_EQ_THM] >>
  asm_rewrite_tac[] >> disch_then (mp_then Any irule wb_frag_then) >> simp[] >>
  qx_gen_tac `sD` >> strip_tac >>
  `EVERY (\op. (!x. op = Var x ==> not_fresh_at s2 x) /\
                (!l. op <> Label l)) ops` by
    (qpat_x_assum `EVERY _ ops` mp_tac >>
     simp[EVERY_MEM] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `sa.cs_next_var <= s2.cs_next_var /\ sa.cs_next_id <= s2.cs_next_id` by
    decide_tac >>
  drule_all raw_log_data_post_transport >> strip_tac >>
  `lookup_var p allocated = SOME w` by fs[eval_operand_def] >>
  drule_all raw_log_fixed_buffer_after_data >> strip_tac >>
  `eval_operand data_op sD = SOME (val_to_w256 (BytesV bs))` by
    (qpat_x_assum `expr_post _ _ _ _ data _ _ _ _ _ _ _ _` mp_tac >>
     qpat_x_assum `expr_type data = _` mp_tac >>
     qpat_x_assum `LENGTH bs = 32` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     gvs[expr_post_def, expr_val_rel_def, is_word_type_def, evaluate_type_def,
        valueEncodingTheory.typed_val_to_w256_def, valueEncodingTheory.val_to_w256_def]) >>
  `eval_operands ops sD = SOME (MAP event_value_to_word vals)` by
    (qpat_x_assum `LIST_REL _ ops vals` mp_tac >>
     rpt (pop_assum kall_tac) >> qid_spec_tac `vals` >>
     Induct_on `ops` >> Cases_on `vals` >>
     simp[eval_operands_def, e2eDefsTheory.event_value_to_word_eq_val_to_w256] >>
     rpt strip_tac >> first_x_assum drule >> simp[]) >>
  drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es2 sD` by fs[expr_post_def] >>
  `MAP FDOM es.scopes = MAP FDOM es2.scopes /\ LENGTH ops <= 4 /\
   TAKE 32 (word_to_bytes_be (val_to_w256 (BytesV bs))) = bs` by
    metis_tac[] >>
  `expr_type e = NoneT` by simp[expr_type_def] >>
  `eval_operand buf.buf_operand sD = SOME w` by simp[] >>
  `?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = s1.cs_next_id` by
    (goal_assum (drule_at Any) >> simp[mk_inst_def]) >>
  `FLOOKUP sD.vs_allocas inst.inst_id = SOME (w2n w,32)` by simp[] >>
  drule_all raw_log_fixed_tail_frag >>
  `expr_exit (INL NoneV) = (\r. F)` by simp[FUN_EQ_THM] >>
  `($= sD) = (\s. s = sD)` by simp[FUN_EQ_THM, EQ_SYM_EQ] >>
  asm_rewrite_tac[] >> simp[SF ETA_ss]
QED

Theorem raw_log_body_topics_sim:
  body_inv tops ctx cenv cx /\ body_exprs_ok cx topics /\
  (!e s. MEM e topics /\ expr_sim_inv cenv cx env s ==>
     expr_body_pre cenv cx env e s /\ expr_type e = BaseT (BytesT (Fixed 32))) /\
  expr_sim_inv cenv cx env es /\
  lower_word_args cenv expr_type topics sa = (ops,sb) /\
  eval_exprs cx topics es = (rr,es') /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa ==>
  frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
    (\s. ?vs. rr = INL vs /\ wb_args_post ctx func cenv cx es sa s0 es' ops vs s)
    (wb_args_exit rr)
Proof
  strip_tac >>
  `typed_args_ready ctx func cenv cx expr_type
     (\s. expr_sim_inv cenv cx env s) topics` by
    metis_tac[raw_log_body_topics_ready] >>
  `wb_args_shape cenv expr_type topics` by
    (irule typed_stack_args_shape >> qexistsl_tac [`cx`, `env`, `es`] >>
     simp[] >> rpt strip_tac >> res_tac >> simp[is_word_type_def]) >>
  drule lower_typed_args_sim >> simp[] >>
  disch_then (qspec_then `es` mp_tac) >> simp[] >>
  disch_then drule >> disch_then drule >> simp[] >>
  disch_then (qspec_then `s0` mp_tac) >>
  disch_then (mp_then Any irule frag_exec_weaken) >> simp[] >>
  rpt strip_tac >> gvs[] >>
  drule_all raw_log_body_topics_values >> strip_tac >>
  irule raw_log_topics_post_wb >> simp[] >> qexists_tac `topics` >> simp[]
QED

