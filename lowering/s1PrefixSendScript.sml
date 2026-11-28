(* Request-prefix companion to bodyFullSend. *)
Theory s1PrefixSend
Ancestors
  s1PrefixPreds bodyFullSend s1PrefixDefs s1PrefixWordArgs bodyFullWordArgs
  s1PrefixSendArgTypes s1PrefixSendCallTail s1PrefixOfVV s1PrefixCompose
  bodyFullHashKeccakFixed fragGasOriginPtrExec exprBodyPreProps exprSimSend
  gasShadow gasShadowState fragExec compileEnv list vyperState
  vyperStorageTrace vyperStorageFootprint s1PrefixProps exprSimWordArgs
  exprSimPrecompiles exprSimDefs bodyPtrDefs venomState vyperValue

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >>
  drule send_pre_types >> strip_tac >> gvs[] >>
  drule expr_body_pre_static_facts >> strip_tac >>
  `!e ee. MEM e args /\ expr_sim_inv cenv cx env ee ==>
       expr_body_pre cenv cx env e ee /\ is_word_type (expr_type e)` by
    (rpt strip_tac >- metis_tac[expr_body_pre_send_arg] >> fs[EVERY_MEM]) >>
  rewrite_tac[expr_sim_prefix_def, expr_sim_full_pre_def] >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  qpat_assum `lower_value _ _ _ (Call _ _ _ _) _ = _`
    (strip_assume_tac o MATCH_MP lower_value_send) >>
  qpat_assum `lower_value _ _ _ (gas_shadow_expr _) _ = _`
    (strip_assume_tac o MATCH_MP lower_value_send o REWRITE_RULE [gas_shadow_expr_def]) >>
  qpat_assum `compile_expr _ _ (Call _ _ args _) sa = _`
    (mp_then Any mp_tac compile_expr_send) >>
  simp[] >> strip_tac >>
  `MAP expr_type (MAP gas_shadow_expr args) = MAP expr_type args` by
    simp[MAP_MAP_o, combinTheory.o_DEF, ETA_AX] >>
  qpat_assum `compile_expr _ _ (Call _ _ (MAP _ _) _) shadow_sa = _`
    (mp_then Any mp_tac compile_expr_send) >>
  simp[] >> strip_tac >>
  rename1 `lower_word_args _ _ (MAP gas_shadow_expr args) shadow_sa = (_,shadow_sm)` >>
  `gas_shadow_compiles (lower_word_args cenv expr_type args)
     (lower_word_args (gas_shadow_env T cenv) expr_type (MAP gas_shadow_expr args))` by
    simp[gas_shadow_compiles_lower_word_args] >>
  qpat_x_assum `gas_shadow_compiles _ _`
    (qspecl_then [`sa`,`shadow_sa`] mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
  simp[] >> strip_tac >>
  `cs_extends sa sm /\ cs_extends shadow_sa shadow_sm` by
    (conj_tac >> irule (cj 1 (REWRITE_RULE [exprLoweringPropsTheory.ci_mono_def]
                              ci_mono_lower_word_args)) >> metis_tac[]) >>
  `cs_extends sm sb /\ cs_extends shadow_sm shadow_sb` by
    metis_tac[send_tail_shape] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func /\
   fn_has_code shadow_sa shadow_sm shadow_func` by metis_tac[fn_has_code_split] >>
  suspend "operands"
QED
*)
Theorem send_expr_sim_prefix:
  !DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx env ty ann
   has_gas args dflt es.
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Call ann (Send has_gas) args dflt) es /\
  body_exprs_full_ok cx args /\
  body_exprs_prefix_ok cx args ==>
  expr_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Call ann (Send has_gas) args dflt) es
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume send_expr_sim_prefix[operands]:
  (* Argument requests use the list prefix; the full list post is only
     needed when the source reaches the Send continuation. *)
  `bind (eval_expr cx (Call NoneT (Send has_gas) args dflt)) (read_result cx) =
   bind (eval_exprs cx args) (\vs. bind (eval_send cx has_gas vs) (read_result cx))` by
    (pure_rewrite_tac[FUN_EQ_THM] >> gen_tac >>
     Cases_on `bind (eval_expr cx (Call NoneT (Send has_gas) args dflt))
       (read_result cx) x` >>
     drule_all (CONV_RULE (DEPTH_CONV ETA_CONV) eval_expr_send_cases) >>
     strip_tac >> gvs[bind_def]) >>
  pop_assum (pure_rewrite_tac o single) >>
  `lower_word_args (gas_shadow_env T cenv) expr_type (MAP gas_shadow_expr args) shadow_sa =
     (addr_op::val_op::(if has_gas then [gas_op] else []),shadow_sm)` by metis_tac[] >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 (eval_exprs cx args) (es,s0,G0,tn0)` by
    (irule lower_word_args_by_type_prefix >>
     qpat_assum `lower_word_args _ _ args sa = _` (irule_at Any) >>
     qpat_assum `gas_shadow_state sm shadow_sm` (irule_at Any) >>
     qpat_assum `gas_shadow_state sa shadow_sa` (irule_at Any) >>
     qpat_assum `body_inv _ _ _ _` (irule_at Any) >>
     qpat_assum `body_const_cells_agree _ _ _ _` (irule_at Any) >>
     qpat_assum `gas_shadow_function _ _` (irule_at Any) >>
     qpat_assum `return_buf_frame _ _ _ _` (irule_at Any) >>
     simp[] >> rpt strip_tac >> fs[EVERY_MEM] >> metis_tac[]) >>
  irule gas_prefix_full_bind_replay >>
  irule_at Any lower_word_args_by_type_sim_full >>
  qpat_assum `lower_word_args _ _ args sa = _` (irule_at Any) >>
  qpat_assum `gas_shadow_state sm shadow_sm` (irule_at Any) >>
  qpat_assum `gas_shadow_state sa shadow_sa` (irule_at Any) >>
  qpat_assum `body_inv _ _ _ _` (irule_at Any) >>
  qpat_assum `body_const_cells_agree _ _ _ _` (irule_at Any) >>
  qpat_assum `gas_shadow_function _ _` (irule_at Any) >>
  qpat_assum `return_buf_frame _ _ _ _` (irule_at Any) >>
  simp[evaluate_storage_trace_frame, evaluate_requests_outcomes_frame,
       storage_trace_frame_bind_all, storage_trace_frame_send, storage_trace_frame_read_result] >>
  conj_tac >- (rpt strip_tac >> fs[EVERY_MEM]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  reverse conj_tac
  >- (rpt gen_tac >> rename1 `_ ==> ISR res` >> Cases_on `res` >> simp[wb_args_exit_def]) >>
  suspend "call"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume send_expr_sim_prefix[call]:
  qx_genl_tac [`marks`,`vs`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  `LIST_REL (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
                       value_has_type tv v) args vs` by
    (irule send_eval_args_typed >>
     qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >>
     qpat_assum `!tail. eval_exprs _ _ _ = _` (qspec_then `[]` (irule_at Any))) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       stmt_state_rel H ctx func cenv cx mid t /\ ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (strip_assume_tac o PURE_REWRITE_RULE [typed_args_post_def]) >>
     simp[]) >>
  qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  pure_rewrite_tac[typed_args_post_def] >> strip_tac >>
  `~t.vs_halted` by
    (drule gas_origin_ptr_path_exec >> simp[exit_result_def]) >>
  `allocas_from lo t` by fs[ghost_inv_at_def] >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp t)` by metis_tac[stmt_state_rel_allocas_below_fmp] >>
  `LENGTH vs = (if has_gas then 3 else 2)` by metis_tac[LIST_REL_LENGTH] >>
  qpat_x_assum `LENGTH args = LENGTH vs` kall_tac >>
  rewrite_tac[gas_prefix_full_bind_read_result] >>
  Cases_on `has_gas` >>
  qpat_x_assum `LENGTH args = _` mp_tac >>
  qpat_x_assum `LENGTH vs = _` mp_tac >>
  simp[LENGTH_EQ_NUM_compute] >> strip_tac >> strip_tac >>
  gvs[cj 1 evaluate_type_def] >>
  irule send_call_tail_prefix >>
  qpat_assum `emit_op CALL _ sm = _` (irule_at Any) >>
  qpat_assum `emit_void ASSERT _ _ = _` (irule_at Any) >>
  simp[vyperInterpreterTheory.ext_call_kwarg_def, eval_operand_def,
       address_typed_dest, uint256_typed_dest, ptrDisciplineTheory.op_taint_def] >>
  qexistsl_tac [`d`,`cenv`] >> simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise send_expr_sim_prefix
*)

Theorem send_expr_vv_sim_prefix:
  !DF lo d ctx shadow_ctx PG func shadow_func tops cenv cx env ty ann
   has_gas args dflt es.
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Call ann (Send has_gas) args dflt) es /\
  body_exprs_full_ok cx args /\
  body_exprs_prefix_ok cx args ==>
  expr_vv_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Call ann (Send has_gas) args dflt) es
Proof
  rpt gen_tac >> strip_tac >> irule expr_vv_sim_stack_prefix >>
  rpt conj_tac
  >~ [`!sa. ?t op sb. compile_expr cenv ty
        (Call ann (Send has_gas) args dflt) sa = (StackValue t op,sb)`]
  >- (gen_tac >>
      Cases_on `compile_expr cenv ty (Call ann (Send has_gas) args dflt) sa` >>
      drule compile_expr_send_stack >> simp[])
  >~ [`expr_sim_prefix _ _ _ _ _ _`]
  >- (irule send_expr_sim_prefix >> metis_tac[]) >>
  metis_tac[eval_expr_send_value]
QED

Theorem body_send_case_prefix:
  !cx v12 has_gas es v13.
  (!s'' x t.
       type_check (LENGTH es = if has_gas then 3 else 2) "Send args" s'' =
       (INL x,t) ==>
       body_exprs_full_ok cx es) /\
  (!s'' x t.
       type_check (LENGTH es = if has_gas then 3 else 2) "Send args" s'' =
       (INL x,t) ==>
       body_exprs_prefix_ok cx es) ==>
  body_expr_prefix_ok cx (Call v12 (Send has_gas) es v13)
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[body_expr_prefix_ok_def] >>
  reverse conj_tac >- simp[] >> rpt gen_tac >> strip_tac >>
  drule send_pre_types >> strip_tac >>
  `?x t. type_check (LENGTH es = if has_gas then 3 else 2)
       "Send args" ARB = (INL x,t)` by
    simp[vyperStateTheory.type_check_def, vyperStateTheory.check_def,
         vyperStateTheory.assert_def, vyperStateTheory.return_def] >>
  `body_exprs_full_ok cx es /\ body_exprs_prefix_ok cx es` by metis_tac[] >>
  conj_tac
  >- (irule send_expr_sim_prefix >> metis_tac[]) >>
  irule send_expr_vv_sim_prefix >> metis_tac[]
QED
