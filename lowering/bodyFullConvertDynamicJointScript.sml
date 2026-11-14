Theory bodyFullConvertDynamicJoint
Ancestors
  bodyFullPreds bodySimFull exprLowering bodyFullOfVV bodyFullExprGeneric
  bodyFullConvertChildRead bodyFullPathHistory exprSafeOperand bodyPtrSignedConvertSourceTyping
  valueCopyBytes bodyPtrMakeArrayBytesTransport bodyPtrTypeBuiltinsBytesWordInputs
  bodyFullConvertBytesWordSuffix bodyFullConvertDynamicEmpty
  bodyFullConvertScalarSuffix bodyFullConvertScalarFrame
  bodyFullConvertSignedClamp bodyFullConvertSignedLoader bodyFullConvertSignedOrigin
  exprSimConvertFromBytes exprSimConvert exprSimHyps exprSimSource
  gasShadowCompile gasShadowState exprLoweringProps compileEnv
  vyperContext vyperInterpreter vyperState vyperAST vyperFiniteStoragePreservation

Theorem dynamic_buffer_resources[local]:
  expr_post H ctx func cenv cx e es sa sm s0 mid v x t /\
  ~is_word_type (expr_type e) /\ ptr_buf_ok cenv e x G t /\
  evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
  type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size tv /\
  64 <= type_memory_size tv /\
  (!rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
     eval_operand x t = SOME w ==>
     type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= t.vs_alloca_next) ==>
  alloca_inv t /\ ?z a b sz. x = Var z /\ lookup_var z t = SOME a /\
    FLOOKUP G z = SOME (b,sz) /\ b <= w2n a /\
    w2n a + type_memory_size tv <= b+sz /\ w2n a+64 <= t.vs_alloca_next
Proof
  strip_tac >>
  `alloca_inv t /\ ?a. eval_operand x t = SOME a` by
    gvs[loweringPostsTheory.expr_post_def, stmt_state_rel_def,
        loweringPostsTheory.expr_val_rel_def] >>
  `w2n a+64 <= t.vs_alloca_next` by
    (first_x_assum (qspecl_then [`tv`,`a`] mp_tac) >> simp[] >> decide_tac) >>
  gvs[bodyPtrDefsTheory.ptr_buf_ok_def, venomStateTheory.eval_operand_def] >>
  metis_tac[]
QED

Theorem dynamic_buffer_representation[local]:
  ptr_val_ok cx sty v (Var z) G tn s /\ ~is_word_type sty /\
  is_bytestring_type sty /\ is_bytestring_type lty /\
  evaluate_type (get_tenv cx) sty = SOME tv /\
  evaluate_type (get_tenv cx) lty = SOME ltv /\
  value_has_type ltv v /\ lookup_var z s = SOME a ==>
  !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory ltv v (w2n a) mem
Proof
  strip_tac >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv v (w2n a) mem` by
    (gvs[bodyPtrDefsTheory.ptr_val_ok_def, bodyPtrDefsTheory.ptr_mem_ok_def,
      venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  rpt strip_tac >> irule bytestring_val_in_memory_transfer >> metis_tac[]
QED

Theorem dynamic_word_vv_post[local]:
  expr_post H ctx func cenv cx (TypeBuiltin typ Convert typ [e])
    es sa sb s0 ee v op s /\ storage_well_formed_on cx ee (FST H) ==>
  vv_post H ctx func cenv cx (TypeBuiltin typ Convert typ [e])
    es sa sb s0 ee (Value v) (StackValue typ op) s
Proof
  simp[loweringPostsTheory.expr_post_def, loweringPostsTheory.vv_post_def,
    loweringPostsTheory.vv_holds_def, loweringPostsTheory.vv_at_def,
    expr_type_def, read_result_def, return_def] >>
  strip_tac >> simp[]
QED

Theorem dynamic_endpoint_vv_posts[local]:
  expr_post H ctx func cenv cx e es sa sm s0 ee v1 x t /\
  ghost_inv_at D lo d cenv cx ee G tn t /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  storage_well_formed_on cx ee (FST H) /\
  is_word_type typ /\ evaluate_type (get_tenv cx) typ = SOME tv /\
  value_has_type tv v /\ eval_operand op s = SOME (typed_val_to_w256 tv v) /\
  local_ptrs_reserved cenv sm /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z) /\
  sa.cs_next_var <= sm.cs_next_var /\
  state_frame s = state_frame (t with vs_inst_idx := s.vs_inst_idx) /\
  s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  (!z. not_fresh_at sm z ==> lookup_var z s = lookup_var z t /\
    FLOOKUP Gf z = FLOOKUP G z /\ op_taint tnf (Var z) = op_taint tn (Var z)) /\
  tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
  tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
  op_taint tnf op = {} /\ op_prov Gf op = NONE /\
  alloca_history func s /\ s0.vs_alloca_next <= t.vs_alloca_next ==>
  vv_post H ctx func cenv cx (TypeBuiltin typ Convert typ [e]) es sa sb s0
    ee (Value v) (StackValue typ op) s /\
  vv_store_bound cx typ lt ee (Value v) (StackValue typ op) s /\
  s.vs_current_bb = sb.cs_current_bb /\ s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
  ghost_inv_at D lo d cenv cx ee Gf tnf s /\
  ptr_vv_ok cx typ (Value v) (StackValue typ op) ee Gf tnf s /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gf tnf
Proof
  strip_tac >>
  drule_all scalar_convert_endpoint_frames >> strip_tac >>
  `s = (t with vs_inst_idx := s.vs_inst_idx) with vs_vars := s.vs_vars` by
    metis_tac[stateFrameTheory.state_frame_eq_reconstruct] >>
  `s.vs_allocas = t.vs_allocas /\ s.vs_alloca_next = t.vs_alloca_next` by
    (pop_assum SUBST1_TAC >> simp[]) >>
  simp[exprSimMemDefsTheory.vv_store_bound_stack_word,
    bodyPtrDefsTheory.ptr_vv_ok_def, read_result_def, return_def] >>
  irule dynamic_word_vv_post >> simp[]
QED

Theorem dynamic_source_window[local]:
  is_bytestring_type sty /\ evaluate_type tenv sty = SOME tv /\
  ((?bs. v = BytesV bs /\ n = LENGTH bs) \/
   (?str. v = StringV str /\ n = LENGTH str)) /\
  (!mem. mem_agree_outside dirty s.vs_memory mem ==>
     val_in_memory tv v (w2n a) mem) ==>
  mload (w2n a) s = n2w n /\
  (!i. w2n a <= i /\ i < w2n a + 32 + n ==> i NOTIN dirty)
Proof
  strip_tac >>
  `mload (w2n a) s = n2w n /\
   (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN dirty) /\
   (!i. w2n a + 32 <= i /\ i < w2n a + 32 + n ==> i NOTIN dirty)` by
    metis_tac[robust_bytestring_source_live] >>
  conj_tac >- simp[] >> rpt strip_tac >>
  Cases_on `i < w2n a + 32` >> metis_tac[arithmeticTheory.NOT_LESS]
QED

Theorem dynamic_read_storage_well_formed[local]:
  expr_body_pre cenv cx env e s /\
  storage_well_formed_on cx s (FST H) /\
  valid_horizon cx st0 H mid.storage_trace /\
  bind (eval_expr cx e) (read_result cx) s = (INL v,mid) ==>
  storage_well_formed_on cx mid (FST H)
Proof
  strip_tac >>
  `well_typed_expr env e /\ runtime_consistent env cx s /\
   functions_well_typed cx /\ call_evaluation_safe cx (int_calls_expr e)` by
    gvs[exprSimHypsDefsTheory.expr_body_pre_def,
        exprSimHypsDefsTheory.expr_sim_inv_def,
        vyperTypeExprSoundnessTheory.runtime_consistent_def] >>
  gvs[bind_def, AllCaseEqs()] >>
  drule read_result_state >> strip_tac >> gvs[] >>
  gvs[vyperStorageFootprintTheory.valid_horizon_def] >>
  drule_all (cj 5 (SPEC_ALL eval_storage_well_formed_on_mutual)) >> simp[]
QED

Theorem convert_dynamic_vv_sim_full:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (TypeBuiltin ann Convert dst [e]) es /\
  body_expr_full_ok cx e /\ is_bytestring_type (expr_type e) /\
  ~is_bytestring_type dst ==>
  expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (TypeBuiltin ann Convert dst [e]) es
Proof
  strip_tac >> drule expr_body_pre_convert >> strip_tac >> gvs[] >>
  `well_formed_type env.type_defs ann` by
    metis_tac[dynamic_convert_typing_boundary] >>
  `is_word_type ann /\ (!n. ann <> FlagT n)` by
    (drule_all dynamic_scalar_type >> simp[]) >>
  `?bt. ann = BaseT bt` by (Cases_on `ann` >> gvs[is_word_type_def]) >>
  gvs[] >>
  simp[expr_vv_sim_full_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_expr cenv ty (TypeBuiltin _ _ _ _) sa = _` mp_tac >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def] >>
  simp[Once (CONJUNCT2 (CONJUNCT2 compile_expr_raw_def)),
       compile_type_builtin_dispatch_body_def, exprCallBoundsTheory.expr_child_callback_def] >>
  Cases_on `lower_value compile_expr cenv (expr_type e) e sa` >>
  rename1 `lower_value compile_expr cenv (expr_type e) e sa = (x,sm)` >>
  simp[exprBopLoweringTheory.lower_value_child_call, SF ETA_ss, expr_type_def] >>
  strip_tac >>
  `?shadow_sm. lower_value compile_expr cenv (expr_type e)
      (gas_shadow_expr e) shadow_sa = (x,shadow_sm) /\
      gas_shadow_state sm shadow_sm` by
    (mp_tac (Q.INST [`ty` |-> `expr_type e`, `sh` |-> `T`]
      (MATCH_MP gasShadowCompileHelpersTheory.gas_shadow_compiles_lower_value
        (cj 1 gas_shadow_compile_expr))) >>
     simp[gasShadowStateTheory.gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >>
     simp[] >> metis_tac[pairTheory.PAIR]) >>
  `cs_extends sa sm /\ cs_extends shadow_sa shadow_sm` by
    metis_tac[compile_expr_grows] >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[gasShadowTheory.gas_shadow_expr_def] >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def] >>
  simp[Once (CONJUNCT2 (CONJUNCT2 compile_expr_raw_def)),
       compile_type_builtin_dispatch_body_def, exprCallBoundsTheory.expr_child_callback_def] >>
  simp[exprBopLoweringTheory.lower_value_child_call, SF ETA_ss, expr_type_def] >>
  strip_tac >>
  `cs_extends sm sb /\ cs_extends shadow_sm shadow_sb` by
    (Cases_on `lowered_value_type cenv e = BaseT (BytesT (Dynamic 0)) \/
               lowered_value_type cenv e = BaseT (StringT 0)` >>
     gvs[exprBopLoweringTheory.as_stack_val_pair] >>
     metis_tac[cj 1 externalEntryShapeTheory.compile_type_convert_labels,
       pairTheory.SND, compileEnvTheory.cs_extends_refl]) >>
  `fn_has_code sa sm func /\ fn_has_code shadow_sa shadow_sm shadow_func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `post_value_type cenv e = expr_type e` by simp[] >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by
    (gvs[body_expr_full_ok_def] >> metis_tac[]) >>
  `!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
        ~is_word_type (post_value_type cenv e) ==>
        type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
        type_memory_size rt < 2**64` by
    metis_tac[exprSimHypsTheory.expr_body_pre_copy_ok] >>
  qpat_assum `expr_body_pre _ _ _ e _`
    (mp_tac o MATCH_MP expr_body_pre_type_evaluates) >>
  simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  rename1 `evaluate_type (get_tenv cx) (expr_type e) = SOME rty` >>
  `!gs tv ee v. eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) /\
      read_result cx tv ee = (INL v,ee) ==> value_has_type rty v` by
    (rpt gen_tac >> strip_tac >>
     `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
     drule_all exprSimSourceTheory.expr_body_pre_runtime_typed >>
     strip_tac >> gvs[] >> metis_tac[]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[convert_operand_admissible,
      exprSimStackTheory.eval_expr_force_admissible, eval_expr_type_builtin_value] >>
  mp_tac (Q.INST [`ty` |-> `expr_type e`] (SPEC_ALL expr_sim_full_of_vv_buffer)) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  disch_then (qspecl_then
    [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`x`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
  `eval_expr cx (TypeBuiltin (BaseT bt) Convert (BaseT bt) [e]) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v ee. (sum_CASE (convert_result cx (expr_type e) (BaseT bt) v)
         (\w. INL (Value w)) INR, ee))` by
    (simp[FUN_EQ_THM] >> gen_tac >>
     simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, type_builtin_args_length_ok_def] >>
     simp[Once evaluate_def, bind_def, return_def] >>
     Cases_on `eval_expr cx e x'` >> rename1 `_ = (raw,ee)` >>
     Cases_on `raw` >> simp[] >> rename1 `_ = (INL tv,ee)` >>
     Cases_on `read_result cx tv ee` >> rename1 `_ = (res,fin)` >>
     Cases_on `res` >> simp[] >> rename1 `_ = (INL val,fin)` >>
     simp[Once evaluate_def, bind_def, return_def, lift_sum_def,
       convert_result_def, evaluate_type_builtin_def] >>
     Cases_on `evaluate_convert_from (get_tenv cx) (expr_type e) val (BaseT bt)` >>
     simp[return_def, raise_def]) >>
  pop_assum SUBST1_TAC >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_bind_all >>
  rpt conj_tac
  >- simp[vyperStorageTraceTheory.storage_trace_frame_def]
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
      qexistsl_tac [`mid`,`t`,`v`] >> metis_tac[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_value >> simp[])
  >~ [`storage_trace_frame (bind _ _)`]
  >- simp[vyperStorageTraceTheory.storage_trace_frame_bind,
       vyperStorageTraceTheory.evaluate_storage_trace_frame,
       vyperStorageTraceTheory.storage_trace_frame_read_result] >>
  qexists_tac `\H res ee G tn t. childQ H res ee G tn t /\
    ~t.vs_halted /\ ee.gas_obs = []` >> conj_tac
  >- suspend "continuation" >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_post_source >>
  goal_assum (drule_at Any) >> simp[] >>
  rpt gen_tac >> Cases_on `res` >> simp[Abbr `childR`] >>
  Cases_on `y` >> Cases_on `r` >> simp[exprSimDefsTheory.expr_exit_def] >>
  rename1 `Error err` >> Cases_on `err` >> simp[exprSimDefsTheory.expr_exit_def]
QED

Resume convert_dynamic_vv_sim_full[continuation]:
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >> fs[] >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    gvs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `childQ (storage_trace_horizon mid.storage_trace) res mid G1 tn1 t /\
    ~t.vs_halted /\ mid.gas_obs = []` by metis_tac[] >>
  qpat_x_assum `childQ _ _ _ _ _ _` mp_tac >>
  simp[Abbr `childQ`, NoAsms] >> strip_tac >> gvs[] >>
  `bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,mid)` by
    (qpat_x_assum `!tail. _` (qspec_then `[]` mp_tac) >> simp[] >>
     `mid with gas_obs := [] = mid` by
       (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >> simp[]) >>
  `expr_body_pre cenv cx env e
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       storage_well_formed_on cx mid (FST H)` by
    (gen_tac >> disch_tac >>
     `valid_horizon cx st0 H es.storage_trace` by
       (qpat_assum `bind _ _ _ = (INL v,mid)` mp_tac >>
        qpat_assum `valid_horizon cx st0 H mid.storage_trace` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
        drule_at (Pat `f st = _`) vyperStorageFootprintTheory.valid_horizon_frame >>
        simp[vyperStorageTraceTheory.storage_trace_frame_bind,
          vyperStorageTraceTheory.evaluate_storage_trace_frame,
          vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
     `storage_well_formed_on cx es (FST H)` by
       (qpat_assum `!H. valid_horizon _ _ _ es.storage_trace ==> _`
          (qspec_then `H` mp_tac) >> simp[]) >>
     irule dynamic_read_storage_well_formed >>
     conj_tac >- (qexists_tac `st0` >> simp[]) >>
     qexistsl_tac [`cenv`,`e`,`env`,
       `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,`v`] >>
     simp[] >>
     qpat_assum `storage_well_formed_on cx es (FST H)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[vyperStorageFootprintTheory.storage_well_formed_on_def] >>
     strip_tac >> rpt gen_tac >>
     `get_storage cx (es with gas_obs := gas_explicit marks s0.vs_gas_readings) b =
      get_storage cx es b` by
       (Cases_on `b` >> simp[vyperStorageBackendTheory.get_storage_def]) >>
     simp[]) >>
  drule_at (Pat `bind _ _ _ = _`)
    (SRULE [SF ETA_ss] body_source_read_lowered_layout) >>
  disch_then (qspecl_then [`tops`,`env`,`ctx`,`cenv`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  Cases_on `lowered_value_type cenv e = BaseT (BytesT (Dynamic 0)) \/
    lowered_value_type cenv e = BaseT (StringT 0)`
  >- suspend "zero" >>
  `64 <= type_memory_bytes cenv (lowered_value_type cenv e)` by
    metis_tac[body_source_lowered_nonzero_capacity] >>
  `expr_post (storage_trace_horizon mid.storage_trace) ctx func cenv cx
     e es sa sm s0 mid v x t` by metis_tac[] >>
  `~is_word_type (expr_type e)` by
    metis_tac[eventTopicValuePropsTheory.bytestring_type_not_word] >>
  drule dynamic_buffer_resources >>
  disch_then (qspecl_then [`tv`,`G1`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  qpat_x_assum `x = Var _` SUBST_ALL_TAC >>
  rename1 `lookup_var z t = SOME a` >>
  `?out. compile_type_convert (Var z) (mk_convert_op (expr_type e) (BaseT bt)) sm =
     (out,sb) /\ vv = StackValue (BaseT bt) out` by
    (fs[exprBopLoweringTheory.as_stack_val_pair] >> metis_tac[pairTheory.PAIR]) >>
  `not_fresh_at sm z` by metis_tac[exprOperandVarTheory.compile_lower_value_var] >>
  `fn_has_code sm sb func /\ local_ptrs_reserved cenv sm` by
    (conj_tac
     >- (qspecl_then [`sa`,`sm`,`sb`,`func`] mp_tac
           fragExecTheory.fn_has_code_split >> simp[]) >>
     irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
     simp[] >> metis_tac[compile_expr_grows]) >>
  `!mem. mem_agree_outside tn1.t_mem t.vs_memory mem ==>
     val_in_memory tv v (w2n a) mem` by
    (rpt strip_tac >> irule dynamic_buffer_representation >> metis_tac[]) >>
  `ptr_covers G1 tn1 z t (type_memory_size tv)` by
    (gvs[bodyPtrDefsTheory.ptr_covers_def, bodyPtrDefsTheory.ptr_val_ok_def] >>
     metis_tac[]) >>
  `value_has_type rty v` by
    (qpat_x_assum `!gs tv ee v. _` irule >>
     qpat_assum `bind _ _ _ = (INL v,mid)` mp_tac >>
     simp[vyperStateTheory.bind_def, AllCaseEqs(), NoAsms] >> rpt strip_tac >>
     drule vyperStateTheory.read_result_state >> strip_tac >> gvs[] >>
     qexistsl_tac [`mid`,`gas_explicit marks s0.vs_gas_readings`,`x`] >> simp[]) >>
  Q.SUBGOAL_THEN
    `?n. n <= 32 /\ ((?bs. v = BytesV bs /\ n = LENGTH bs) \/
      (?str. v = StringV str /\ n = LENGTH str))`
    (qx_choose_then `n` (CONJUNCTS_THEN assume_tac))
  >- (drule_all bytes_word_source_length >> strip_tac >> metis_tac[]) >>
  `mload (w2n a) t = n2w n /\
   (!i. w2n a <= i /\ i < w2n a+32+n ==> i NOTIN tn1.t_mem)` by
    (irule dynamic_source_window >>
     qexistsl_tac [`lowered_value_type cenv e`,`get_tenv cx`,`tv`,`v`] >>
     simp[] >> metis_tac[]) >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by
    (qpat_assum `!H. valid_horizon _ _ _ _ ==> _ /\ ghost_inv_at _ _ _ _ _ _ _ _ _` (qspec_then
       `storage_trace_horizon mid.storage_trace` mp_tac) >>
     simp[bodyPtrDefsTheory.ghost_inv_at_def, NoAsms] >>
     disch_then (fn th => mp_tac th) >>
     (impl_tac >- simp[]) >> rpt strip_tac >> simp[]) >>
  `t.vs_alloca_next < dimword(:256)` by
    (irule exprLoweringPropsTheory.alloca_room_next_lt >>
     gvs[loweringPostsTheory.expr_post_def, exprLoweringPropsTheory.stmt_state_rel_def] >>
     metis_tac[]) >>
  `w2n a + 64 <= dimword(:256)` by decide_tac >>
  `well_formed_type (get_tenv cx) (BaseT bt)` by
    (qpat_x_assum `well_formed_type env.type_defs _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `bt` >>
     simp[vyperTypeSystemTheory.well_formed_type_def,
          vyperValueTheory.evaluate_type_def]) >>
  `val_in_memory rty v (w2n a) t.vs_memory` by
    (gvs[bodyPtrDefsTheory.ptr_val_ok_def, bodyPtrDefsTheory.ptr_mem_ok_def,
       venomStateTheory.eval_operand_def] >>
     metis_tac[bodyPtrDefsTheory.mem_agree_outside_def]) >>
  `64 <= type_memory_size tv` by metis_tac[] >>
  Cases_on `(?k. bt = IntT k) \/ bt = DecimalT`
  >- (Q.SUBGOAL_THEN `(?k. BaseT bt = BaseT (IntT k)) \/ BaseT bt = BaseT DecimalT` assume_tac
      >- metis_tac[] >>
      drule_all signed_convert_origin_path >>
      disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`] mp_tac) >>
      strip_tac >> suspend "unsigned") >>
  Q.SUBGOAL_THEN
    `BaseT bt = BaseT BoolT \/ (?k. BaseT bt = BaseT (UintT k)) \/
     BaseT bt = BaseT AddressT \/ (?k. BaseT bt = BaseT (BytesT (Fixed k)))`
    assume_tac
  >- (drule_all bodyPtrTypeBuiltinsBytesWordTypesTheory.bytestring_scalar_type_partition >>
      qpat_x_assum `~((?k. bt = IntT k) \/ bt = DecimalT)` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> simp[] >> metis_tac[]) >>
  Cases_on `v = BytesV [] \/ v = StringV []`
  >- (drule_all bytes_word_empty_convert_origin_path >>
      disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`] mp_tac) >>
      strip_tac >> suspend "unsigned") >>
  `v <> BytesV [] /\ v <> StringV []` by
    (qpat_x_assum `~(v = BytesV [] \/ v = StringV [])` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  drule_all bytes_word_convert_origin_path >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`] mp_tac) >>
  strip_tac >> suspend "unsigned"
QED

Resume convert_dynamic_vv_sim_full[unsigned]:
  markerLib.RESUME_TAC >> (
  Cases_on `convert_result cx (expr_type e) (BaseT bt) v`
  >- (rename1 `convert_result _ _ _ _ = INL vout` >>
      qpat_x_assum `!vout'. INL vout = INL vout' ==> _`
        (qspec_then `vout` mp_tac) >>
      rewrite_tac[] >> strip_tac >>
      irule gasOutcomeFullComposeTheory.gas_outcome_full_pure >>
      conj_tac >- (qexistsl_tac [`Gf`,`mid`,`INL (Value vout)`,`t'`,`tnf`] >>
        simp[] >> gen_tac >> disch_tac >>
        `mid with gas_obs := [] = mid` by
          (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
        pop_assum SUBST1_TAC >>
        `alloca_history func t'` by
          (irule body_full_path_alloca_history >> metis_tac[]) >>
        `!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z` by
          (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
           qexists_tac `sa` >> simp[] >>
           qpat_assum `lower_value _ _ _ _ sa = (_,sm)` mp_tac >>
           POP_ASSUM_LIST (K all_tac) >> metis_tac[compile_expr_grows]) >>
        `!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z` by
          (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
           qexists_tac `sa` >> simp[] >>
           qpat_assum `lower_value _ _ _ _ sa = (_,sm)` mp_tac >>
           POP_ASSUM_LIST (K all_tac) >> metis_tac[compile_expr_grows]) >>
        `sa.cs_next_var <= sm.cs_next_var` by
          (qpat_assum `lower_value _ _ _ _ sa = (_,sm)` mp_tac >>
           POP_ASSUM_LIST (K all_tac) >> metis_tac[compile_expr_grows]) >>
        `storage_well_formed_on cx mid (FST H)` by
          (qpat_assum `!H. _ ==> storage_well_formed_on _ _ _`
             (qspec_then `H` mp_tac) >> simp[]) >>
        qpat_assum `!H. _ ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
          (qspec_then `H` mp_tac) >>
        (impl_tac >- simp[]) >> disch_then strip_assume_tac >>
        drule_all dynamic_endpoint_vv_posts >>
        disch_then (qspecl_then
          [`lowered_value_type cenv (TypeBuiltin (BaseT bt) Convert (BaseT bt) [e])`] mp_tac) >>
        simp[contextTheory.vv_location_def]) >> simp[]) >>
  qpat_x_assum `!exc. INR y = INR exc ==> _` (qspec_then `y` mp_tac) >>
  simp[] >> strip_tac >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_exit >>
  conj_tac >- (qexistsl_tac [`Gf`,`mid`,`Abort err t'`,`INR y`,`tnf`] >>
  simp[fragExecTheory.exit_result_def, exprSimDefsTheory.expr_exit_def]) >> simp[])
QED

Resume convert_dynamic_vv_sim_full[zero]:
  `v = BytesV [] \/ v = StringV []` by
    (qpat_x_assum `lowered_value_type cenv e = _ \/ _` mp_tac >> strip_tac >>
     gvs[vyperValueTheory.evaluate_type_def] >> Cases_on `v` >>
     gvs[vyperTypingTheory.value_has_type_def]) >>
  `value_has_type rty v` by
    (qpat_x_assum `!gs tv ee v. _` irule >>
     qpat_assum `bind _ _ _ = (INL v,mid)` mp_tac >>
     simp[vyperStateTheory.bind_def, AllCaseEqs(), NoAsms] >> rpt strip_tac >>
     drule vyperStateTheory.read_result_state >> strip_tac >> gvs[] >>
     metis_tac[]) >>
  `?vout dtv. convert_result cx (expr_type e) (BaseT bt) v = INL vout /\
     evaluate_type (get_tenv cx) (BaseT bt) = SOME dtv /\
     typed_val_to_w256 dtv vout = 0w` by
    (irule dynamic_empty_scalar_convert >>
     conj_tac >- simp[] >> conj_tac
     >- (qexistsl_tac [`expr_type e`,`rty`,`v`] >> simp[]) >>
     qexists_tac `env.type_defs` >> simp[]) >>
  gvs[] >> (
  irule gasOutcomeFullComposeTheory.gas_outcome_full_pure >>
  conj_tac >- (qexistsl_tac [`G1`,`mid`,`INL (Value vout)`,`t`,`tn1`] >>
    simp[] >> gen_tac >> disch_tac >>
    `mid with gas_obs := [] = mid` by
      (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
    pop_assum SUBST1_TAC >>
    qpat_assum `!H. _ ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
      (qspec_then `H` mp_tac) >>
    (impl_tac >- simp[]) >> disch_then strip_assume_tac >>
    simp[fragGasOriginPtrTheory.gas_origin_ptr_path_rules,
      exprSimMemDefsTheory.vv_store_bound_stack_word, contextTheory.vv_location_def] >>
    conj_tac
    >- (irule dynamic_word_vv_post >> simp[] >>
        irule zero_convert_child_post >> metis_tac[]) >>
    simp[bodyPtrDefsTheory.ptr_vv_ok_def, read_result_def, return_def,
      bodyPtrDefsTheory.ptr_val_ok_def, venomStateTheory.eval_operand_def,
      ptrDisciplineTheory.op_taint_def, ptrDisciplineTheory.op_prov_def,
      loweringPostsTheory.expr_val_rel_def]) >> simp[])
QED

Finalise convert_dynamic_vv_sim_full
