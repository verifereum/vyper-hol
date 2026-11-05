(* Piece of bodySimCallCases.body_raw_log_case. *)

Theory bodySimCallRawLog
Ancestors
  bodySimExprCases bodySimRawLog
  list bodySim exprSimHyps vyperAST vyperInterpreter vyperState
  vyperContext vyperTypeCallGraph
  exprSimSend vyperTypeSystem exprSimAggregateSource vyperValue
  exprSimWordArgs exprLowering compileEnv emitHelper venomExecSemantics
  exprLoweringProps venomState venomMemDefs exprSimDefs exprSimStack loweringPosts exprSimHypsDefs exprSimSource vyperEvent
  fragExec venomInst exprSimHash exprSimBuffer exprSimPrecompiles emitHelperProps
  ASCIInumbers exprSimRawLog
Libs
  pairLib

(* HELD for the post-16 bodySim child-closure wave: the elements of a
   MakeArray operand (raw_log's topic list) are body_expr_ok in order.
   s1-ops-widened-expr holds the same fact as body_make_array_children_ok. *)
Theorem raw_log_make_array_children_ok:
  !cx a t n elems.
    body_expr_ok cx (Builtin a (MakeArray t n) elems) /\
    builtin_args_length_ok (MakeArray t n) (LENGTH elems) ==>
    body_exprs_ok cx elems
Proof
  cheat
QED

Theorem raw_log_dynamic_frag:
  body_inv tops ctx cenv cx /\ body_exprs_ok cx args /\
  expr_body_pre cenv cx env (Call ann RawLog args dflt) es /\
  (?a elem bd topics data cap.
    args = [Builtin a (MakeArray elem bd) topics; data] /\
    expr_type data = BaseT (BytesT (Dynamic cap))) /\
  compile_expr cenv ty (Call ann RawLog args dflt) sa = (StackValue ann (Lit 0w),sb) /\
  (do r <- eval_expr cx (Call ann RawLog args dflt); read_result cx r od) es = (res,es') /\
  expr_res_ok res /\ fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa ==>
  frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
    (\s. ?v. res = INL v /\ expr_post ctx func cenv cx (Call ann RawLog args dflt)
       es sa sb s0 es' v (Lit 0w) s) (expr_exit res)
Proof
  strip_tac >>
  `expr_sim_inv cenv cx env es /\ source_supply es` by fs[expr_body_pre_def] >>
  drule raw_log_body_pre_shape >> strip_tac >> gvs[] >>
  drule_all raw_log_literal_typed >> strip_tac >> gvs[] >>
  `body_exprs_ok cx topics` by
    (qpat_assum `body_exprs_ok cx [_;_]`
       (strip_assume_tac o REWRITE_RULE [body_exprs_ok_def]) >>
     drule_all raw_log_make_array_children_ok >> simp[]) >>
  `!arg s. MEM arg topics /\ expr_sim_inv cenv cx env s /\ source_supply s ==>
     expr_body_pre cenv cx env arg s /\ expr_type arg = BaseT (BytesT (Fixed 32))` by
    (rpt gen_tac >> strip_tac >> conj_tac
     >- (qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
         qpat_x_assum `MEM arg topics` mp_tac >>
         qpat_x_assum `expr_sim_inv _ _ _ s` mp_tac >>
         qpat_x_assum `source_supply s` mp_tac >>
         rpt (pop_assum kall_tac) >> rpt strip_tac >>
         metis_tac[expr_body_pre_raw_log_arg, expr_body_pre_builtin_arg, MEM]) >>
     fs[EVERY_MEM, MEM_MAP] >> metis_tac[]) >>
  `wb_args_shape cenv expr_type topics` by
    (irule typed_stack_args_shape >> qexistsl_tac [`cx`, `env`, `es`] >>
     simp[] >> rpt strip_tac >> res_tac >> simp[is_word_type_def]) >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_raw_log_stages] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `lower_word_args cenv expr_type topics sa = (ops,sm)` >>
  rename1 `lower_value compile_expr cenv _ data sm = (data_op,sn)` >>
  rename1 `emit_op MLOAD [data_op] sn = (len_op,sl)` >>
  rename1 `emit_op ADD [data_op; Lit 32w] sl = (ptr_op,sp)` >>
  rename1 `emit_inst LOG _ [] sp = ((),sb)` >>
  `!s. expr_sim_inv cenv cx env s /\ source_supply s ==>
       expr_body_pre cenv cx env data s` by
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
  Cases_on `eval_exprs cx topics es` >>
  rename1 `eval_exprs cx topics es = (tr,es1)` >>
  reverse (Cases_on `tr`)
  >- (qpat_x_assum `(do r <- eval_expr cx call; read_result cx r od) es = _` mp_tac >>
      simp[Abbr `call`, raw_log_eval_cases, bind_def] >> strip_tac >> gvs[] >>
      drule_all raw_log_body_topics_sim >>
      disch_then (qspec_then `s0` mp_tac) >>
      simp[wb_args_exit_def] >> strip_tac >>
      irule frag_exec_exit_prefix >> goal_assum (drule_at Any) >> simp[]) >>
  rename1 `eval_exprs cx topics es = (INL vals,es1)` >>
  `expr_sim_inv cenv cx env es1 /\ source_supply es1` by
    (drule_all raw_log_body_topics_success >> simp[]) >>
  `body_expr_ok cx data` by
    (drule_all raw_log_literal_read_success >>
     simp[bind_def, AllCaseEqs()] >> strip_tac >>
     irule raw_log_body_data_after_topics >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `expr_body_pre cenv cx env data es1` by metis_tac[] >>
  `expr_sim ctx func cenv cx (expr_type data) data es1` by
    (qpat_x_assum `body_expr_ok cx data` mp_tac >>
     simp[Once body_expr_ok_def] >> metis_tac[]) >>
  Cases_on `(do tv <- eval_expr cx data; read_result cx tv od) es1` >>
  rename1 `(do tv <- eval_expr cx data; read_result cx tv od) es1 = (dr,es2)` >>
  drule_all expr_body_pre_base_result >> strip_tac >>
  `MAP FDOM es.scopes = MAP FDOM es1.scopes` by
    metis_tac[vyperEvalExprPreservesScopesDomTheory.eval_exprs_preserves_scopes_dom] >>
  reverse (Cases_on `stmt_state_rel ctx func cenv cx es s0`)
  >- (`(\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s) = (\s. F)` by
        (simp[FUN_EQ_THM] >> metis_tac[]) >>
      simp[] >> irule frag_exec_false_pre) >>
  drule_all raw_log_body_topics_sim >>
  disch_then (qspec_then `s0` mp_tac) >> simp[wb_args_exit_def] >>
  disch_then (mp_then Any irule wb_frag_then) >> simp[] >>
  qx_gen_tac `t` >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es1 t` by fs[wb_args_post_def] >>
  reverse (Cases_on `dr`)
  >- (`res = INR y /\ es' = es2` by
        (qpat_assum `(do tv <- eval_expr cx data; read_result cx tv od) es1 = _`
           (assume_tac o SRULE [bind_def]) >>
         qpat_x_assum `(do tv <- eval_expr cx call; read_result cx tv od) es = _` mp_tac >>
         simp[Abbr `call`, raw_log_eval_cases, bind_def]) >>
      gvs[] >> drule_all expr_sim_apply >>
      disch_then (qspec_then `t` mp_tac) >> simp[] >> strip_tac >>
      irule frag_exec_exit_prefix >> simp[] >>
      goal_assum (drule_at Any) >> simp[] >>
      qpat_x_assum `frag_exec ctx sm sn _ _ _`
        (mp_then Any irule frag_exec_weaken) >> simp[]) >>
  rename1 `(do tv <- eval_expr cx data; read_result cx tv od) es1 = (INL dv,es2)` >>
  `?bs. dv = BytesV bs` by
    (qpat_x_assum `!v. INL dv = _ ==> _` mp_tac >>
     simp[] >> Cases_on `dv` >> simp[vyperTypingTheory.value_has_type_def]) >>
  gvs[] >>
  `LENGTH vals = LENGTH topics` by fs[wb_args_post_def, LIST_REL_EL_EQN] >>
  `res = INL NoneV /\ es' = es2 with logs := es2.logs ++
     [encode_raw_event_values cx.txn.target vals bs]` by
    (qpat_assum `(do tv <- eval_expr cx data; read_result cx tv od) es1 = _`
       (assume_tac o SRULE [bind_def]) >>
     qpat_x_assum `(do tv <- eval_expr cx call; read_result cx tv od) es = _` mp_tac >>
     simp[Abbr `call`, raw_log_eval_cases, bind_def, lift_option_type_def, dest_BytesV_def,
          type_check_def, assert_def, push_log_def, ignore_bind_def,
          return_def, read_result_def]) >>
  `expr_exit res = (\r. F)` by simp[expr_exit_def, FUN_EQ_THM] >>
  `(\s. s = t) = (\s. s = t /\ stmt_state_rel ctx func cenv cx es1 s)` by
    (simp[FUN_EQ_THM] >> metis_tac[]) >>
  pop_assum SUBST1_TAC >>
  drule_all expr_sim_apply >> disch_then (qspec_then `t` mp_tac) >>
  `expr_exit (INL (BytesV bs)) = (\r. F)` by simp[FUN_EQ_THM] >>
  asm_rewrite_tac[] >> disch_then (mp_then Any irule wb_frag_then) >> simp[] >>
  qx_gen_tac `sD` >> strip_tac >>
  drule_all raw_log_data_post_transport >> strip_tac >>
  `evaluate_type (get_tenv cx) (expr_type data) =
     SOME (BaseTV (BytesT (Dynamic cap)))` by
    (`expr_body_pre cenv cx env data es1` by metis_tac[] >>
     qpat_x_assum `expr_body_pre _ _ _ data es1`
       (mp_tac o MATCH_MP expr_body_pre_type_evaluates) >>
     simp[vyperValueTheory.evaluate_type_def, AllCaseEqs()]) >>
  drule_all raw_log_dynamic_data_view >> strip_tac >>
  `eval_operands ops sD = SOME (MAP event_value_to_word vals)` by
    (qpat_x_assum `LIST_REL _ ops vals` mp_tac >>
     rpt (pop_assum kall_tac) >> qid_spec_tac `vals` >>
     Induct_on `ops` >> Cases_on `vals` >>
     simp[eval_operands_def, e2eDefsTheory.event_value_to_word_eq_val_to_w256] >>
     rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es2 sD` by fs[expr_post_def] >>
  `EVERY (\op. !z. op = Var z ==> not_fresh_at sn z) ops` by
    (fs[EVERY_MEM] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `LENGTH ops <= 4 /\ sa.cs_next_var <= sn.cs_next_var` by decide_tac >>
  `expr_type call = NoneT` by simp[Abbr `call`, expr_type_def] >>
  qpat_assum `LENGTH ops = LENGTH topics`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [GSYM th])) >>
  drule_all raw_log_dynamic_tail_frag >>
  `expr_exit (INL NoneV) = (\r. F)` by simp[FUN_EQ_THM] >>
  `($= sD) = (\s. s = sD)` by simp[FUN_EQ_THM, EQ_SYM_EQ] >>
  asm_rewrite_tac[] >> simp[SF ETA_ss]
QED

Theorem raw_log_fixed32_body_frag:
  body_inv tops ctx cenv cx /\ body_exprs_ok cx args /\
  expr_body_pre cenv cx env (Call ann RawLog args dflt) es /\
  (?a elem bd topics data.
    args = [Builtin a (MakeArray elem bd) topics; data] /\
    expr_type data = BaseT (BytesT (Fixed 32))) /\
  compile_expr cenv ty (Call ann RawLog args dflt) sa = (StackValue ann (Lit 0w),sb) /\
  (do r <- eval_expr cx (Call ann RawLog args dflt); read_result cx r od) es = (res,es') /\
  expr_res_ok res /\ fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa ==>
  frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
    (\s. ?v. res = INL v /\ expr_post ctx func cenv cx (Call ann RawLog args dflt)
       es sa sb s0 es' v (Lit 0w) s) (expr_exit res)
Proof
  strip_tac >>
  `expr_sim_inv cenv cx env es /\ source_supply es` by fs[expr_body_pre_def] >>
  drule raw_log_body_pre_shape >> strip_tac >> gvs[] >>
  drule_all raw_log_literal_typed >> strip_tac >> gvs[] >>
  `body_exprs_ok cx topics` by
    (qpat_assum `body_exprs_ok cx [_;_]`
       (strip_assume_tac o REWRITE_RULE [body_exprs_ok_def]) >>
     drule_all raw_log_make_array_children_ok >> simp[]) >>
  `!arg s. MEM arg topics /\ expr_sim_inv cenv cx env s /\ source_supply s ==>
     expr_body_pre cenv cx env arg s /\ expr_type arg = BaseT (BytesT (Fixed 32))` by
    (rpt gen_tac >> strip_tac >> conj_tac
     >- (qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
         qpat_x_assum `MEM arg topics` mp_tac >>
         qpat_x_assum `expr_sim_inv _ _ _ s` mp_tac >>
         qpat_x_assum `source_supply s` mp_tac >>
         rpt (pop_assum kall_tac) >> rpt strip_tac >>
         metis_tac[expr_body_pre_raw_log_arg, expr_body_pre_builtin_arg, MEM]) >>
     fs[EVERY_MEM, MEM_MAP] >> metis_tac[]) >>
  `wb_args_shape cenv expr_type topics` by
    (irule typed_stack_args_shape >> qexistsl_tac [`cx`, `env`, `es`] >>
     simp[] >> rpt strip_tac >> res_tac >> simp[is_word_type_def]) >>
  `!s. expr_sim_inv cenv cx env s /\ source_supply s ==>
       expr_body_pre cenv cx env data s` by
    (qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     metis_tac[expr_body_pre_raw_log_arg, MEM]) >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_raw_log_stages] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  `wb_args_shape cenv expr_type [data]` by
    (irule typed_stack_args_shape >>
     qexistsl_tac [`cx`, `env`, `es`] >> simp[is_word_type_def]) >>
  irule raw_log_fixed32_topics_frag >>
  goal_assum (drule_at Any) >> simp[] >>
  qexists_tac `\s. expr_sim_inv cenv cx env s /\ source_supply s` >> simp[] >>
  reverse conj_tac
  >- (conj_tac
      >- (rpt strip_tac >> drule_all raw_log_body_topics_success >> simp[]) >>
      rpt strip_tac >> drule_all raw_log_body_topics_sim >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `body_expr_ok cx data` by
    (drule_all raw_log_literal_read_success >>
     simp[bind_def, AllCaseEqs()] >> strip_tac >>
     irule raw_log_body_data_after_topics >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `expr_body_pre cenv cx env data es1` by metis_tac[] >>
  conj_tac
  >- (qpat_x_assum `body_expr_ok cx data` mp_tac >>
      simp[Once body_expr_ok_def] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> drule_all expr_body_pre_base_result >> simp[]) >>
  rpt strip_tac >> drule_all expr_body_pre_base_result >> strip_tac >>
  Cases_on `v'` >> gvs[vyperTypingTheory.value_has_type_def] >>
  simp[] >> rename1 `(do tv <- eval_expr cx data; read_result cx tv od) es1 = (INL (BytesV bs),es2)` >>
  mp_tac (Q.INST [`bd` |-> `Fixed 32`] typed_bytes_prefix) >>
  simp[valueEncodingTheory.typed_val_to_w256_def, valueEncodingTheory.val_to_w256_def]
QED

Theorem raw_log_body_expr_ok:
  !cx v20 es v21.
    body_exprs_ok cx es ==> body_expr_ok cx (Call v20 RawLog es v21)
Proof
  rpt gen_tac >> strip_tac >> irule body_expr_ok_intro >>
  rpt gen_tac >> strip_tac >>
  `expr_sim ctx func cenv cx ty (Call v20 RawLog es v21) es'` by
    (simp[expr_sim_def] >> rpt strip_tac >>
     drule_all raw_log_body_lower_value >> strip_tac >> gvs[] >>
     drule raw_log_body_pre_shape >> strip_tac >> gvs[]
     >- (irule raw_log_fixed32_body_frag >> goal_assum (drule_at Any) >>
         simp[] >> metis_tac[]) >>
     irule raw_log_dynamic_frag >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  conj_tac >- simp[] >>
  irule expr_vv_sim_stack >> simp[] >>
  conj_tac >- (drule raw_log_body_compile_stack >> metis_tac[]) >>
  metis_tac[raw_log_body_eval_value]
QED
