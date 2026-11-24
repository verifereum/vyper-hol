Theory bodyFullConvertDynamicJoint
Ancestors
  bodyFullShadowBodyInv bodyFullConvertDynamicSource bodyFullConvertDynamicSite
  bodyFullConvertDynamicOriginRule bodyFullEmptyLeafData exprSimFullBundleProps
  haltExitProj typeBuiltinPrereqs
  bodyFullPreds bodySimFull exprLowering bodyFullOfVV bodyFullExprGeneric
  bodyFullConvertChildRead bodyFullPathHistory exprSafeOperand bodyPtrSignedConvertSourceTyping
  valueCopyBytes bodyPtrMakeArrayBytesTransport bodyPtrTypeBuiltinsBytesWordInputs
  bodyFullConvertBytesWordSuffix bodyFullConvertDynamicEmpty
  bodyFullConvertScalarSuffix bodyFullConvertScalarFrame bodyFullConvertEndpointPosts
  bodyFullConvertSignedClamp bodyFullConvertSignedLoader bodyFullConvertSignedOrigin
  exprSimConvertFromBytes exprSimConvert exprSimHyps exprSimSource
  gasShadowCompile gasShadowState exprLoweringProps compileEnv
  vyperContext vyperInterpreter vyperState vyperAST vyperFiniteStoragePreservation
  bodyFullHashKeccakFixed[qualified,ignore_grammar] stateFrame[qualified,ignore_grammar]

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


Theorem convert_dynamic_selected_continuation:
  body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env e es /\
  is_bytestring_type (expr_type e) /\ ~is_bytestring_type (BaseT bt) /\
  is_word_type (BaseT bt) /\ well_formed_type env.type_defs (BaseT bt) /\
  valid_conversion (expr_type e) (BaseT bt) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME rty /\
  (!gs tv ee v. eval_expr cx e (es with gas_obs := gs) = (INL tv,ee) /\
      read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  local_ptrs_reserved cenv sa /\ fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> storage_well_formed_on cx es (FST H)) /\
  (if lowered_value_type cenv e = BaseT (BytesT (Dynamic 0)) \/
      lowered_value_type cenv e = BaseT (StringT 0) then
     sm = sb /\ vv = StackValue (BaseT bt) (Lit 0w) /\ P sm sb t (OK t)
   else ?out. vv = StackValue (BaseT bt) out /\
     compile_type_convert x (mk_convert_op (expr_type e) (BaseT bt)) sm = (out,sb)) /\
  convert_dynamic_origin_rule P lo (gas_explicit_sites ctx shadow_ctx) ctx func PG /\
  (!tail. bind (eval_expr cx e) (read_result cx)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
        (child_res, mid with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\ ~t.vs_halted /\ mid.gas_obs = [] /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
     expr_sim_full_post (DF,lo,d,ctx,func) cenv cx e (es,sa,sm,s0,x,G0,tn0)
       H child_res mid G1 tn1 t /\
     (~is_word_type (post_value_type cenv e) ==>
      !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
             eval_operand x t = SOME w ==>
             type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= t.vs_alloca_next)) ==>
  ?v res r Gf tnf. child_res = INL v /\
    (!tail. (sum_CASE (convert_result cx (expr_type e) (BaseT bt) v)
       (\w. INL (Value w)) INR, mid with gas_obs := tail) =
       (res, mid with gas_obs := tail)) /\
    P sm sb t r /\ ((?u. r = OK u) \/ exit_result r) /\
    (!H. valid_horizon cx st0 H mid.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (t,G1,tn1) [] (r,Gf,tnf) /\
      case r of
        OK u => expr_vv_sim_full_post (DF,lo,d,ctx,func) cenv cx
          (TypeBuiltin (BaseT bt) Convert (BaseT bt) [e])
          (es,sa,sb,s0,vv,G0,tn0) H res mid Gf tnf u
      | _ => expr_exit res r /\ halt_exit H cx mid res r /\
           (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    gvs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. _ ==> expr_sim_full_post _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (CONJUNCTS_THEN2
    (qx_choose_then `v` (REPEAT_TCL CONJUNCTS_THEN assume_tac) o
     SIMP_RULE std_ss [expr_sim_full_post_def, expr_sim_full_endpoint_def])
    assume_tac) >>
  qpat_x_assum `child_res = INL _` SUBST_ALL_TAC >>
  qexists_tac `v` >>
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
  `post_value_type cenv e = expr_type e` by simp[] >>
  Cases_on `lowered_value_type cenv e = BaseT (BytesT (Dynamic 0)) \/
    lowered_value_type cenv e = BaseT (StringT 0)`
  >- suspend "zero" >>
  `64 <= type_memory_bytes cenv (lowered_value_type cenv e)` by
    metis_tac[body_source_lowered_nonzero_capacity] >>
  `~is_word_type (expr_type e)` by
    metis_tac[eventTopicValuePropsTheory.bytestring_type_not_word] >>
  drule dynamic_buffer_resources >>
  disch_then (qspecl_then [`tv`,`G1`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  qpat_x_assum `x = Var _` SUBST_ALL_TAC >>
  rename1 `lookup_var z t = SOME a` >>
  qpat_x_assum `if _ then _ else _` mp_tac >> simp[] >> strip_tac >>
  `not_fresh_at sm z` by metis_tac[exprOperandVarTheory.compile_lower_value_var] >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
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
    gvs[bodyPtrDefsTheory.ghost_inv_at_def] >>
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
  qpat_assum `convert_dynamic_origin_rule _ _ _ _ _ _`
    (assume_tac o REWRITE_RULE [convert_dynamic_origin_rule_def]) >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `convert_result cx (expr_type e) (BaseT bt) v`
  >- suspend "normal" >> suspend "abort"
QED

Resume convert_dynamic_selected_continuation[normal]:
  rename1 `convert_result _ _ _ _ = INL vout` >>
  qpat_x_assum `!vout'. INL vout = INL vout' ==> _`
    (qspec_then `vout` mp_tac) >>
  rewrite_tac[] >> strip_tac >>
  qexistsl_tac [`OK t'`,`Gf`,`tnf`] >>
  simp[] >> gen_tac >> disch_tac >>
  `alloca_history func t'` by
    (irule body_full_path_alloca_history >> metis_tac[]) >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (qpat_assum `lower_value _ _ _ _ sa = (_,sm)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[compile_expr_grows]) >>
  `!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sm z` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `storage_well_formed_on cx mid (FST H)` by
    (qpat_assum `!H. _ ==> storage_well_formed_on _ _ _`
       (qspec_then `H` mp_tac) >> simp[]) >>
  qpat_assum `!H. _ ==> expr_sim_full_post _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  simp[expr_sim_full_post_def, expr_sim_full_endpoint_def, NoAsms] >>
  strip_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t'` by
    (`t' = (t with vs_inst_idx := t'.vs_inst_idx) with vs_vars := t'.vs_vars` by
       metis_tac[stateFrameTheory.state_frame_eq_reconstruct] >>
     qpat_x_assum `t' = (t with vs_inst_idx := _) with vs_vars := _` SUBST1_TAC >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp t` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[ptrDisciplineTheory.allocas_below_fmp_def] >> metis_tac[]) >>
  simp[expr_vv_sim_full_post_def, expr_sim_full_endpoint_def, contextTheory.vv_location_def] >>
  drule_all dynamic_endpoint_vv_posts >>
  disch_then (qspecl_then
    [`lowered_value_type cenv (TypeBuiltin (BaseT bt) Convert (BaseT bt) [e])`] mp_tac) >>
  simp[expr_type_def]
QED

Resume convert_dynamic_selected_continuation[abort]:
  rename1 `convert_result _ _ _ _ = INR exc` >>
  qpat_x_assum `!y. INR exc = INR y ==> _` (qspec_then `exc` mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl_tac [`Abort err t'`,`Gf`,`tnf`] >>
  simp[fragExecTheory.exit_result_def, exprSimDefsTheory.expr_exit_def,
       halt_exit_not_halt]
QED

Resume convert_dynamic_selected_continuation[zero]:
  qpat_x_assum `if _ then _ else _` mp_tac >> simp[] >> strip_tac >>
  (Q.SUBGOAL_THEN `v = BytesV [] \/ v = StringV []` assume_tac
   >- (qpat_x_assum `lowered_value_type cenv e = _ \/ _` mp_tac >> strip_tac >>
       gvs[vyperValueTheory.evaluate_type_def] >> Cases_on `v` >>
       gvs[vyperTypingTheory.value_has_type_def])) >>
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
  qpat_x_assum `sm = sb` SUBST_ALL_TAC >>
  qexistsl_tac [`OK t`,`G1`,`tn1`] >>
  simp[fragGasOriginPtrTheory.gas_origin_ptr_path_rules] >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. _ ==> expr_sim_full_post _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  simp[expr_sim_full_post_def, expr_sim_full_endpoint_def, NoAsms] >> strip_tac >>
  simp[expr_vv_sim_full_post_def, expr_sim_full_endpoint_def, expr_type_def,
    exprSimMemDefsTheory.vv_store_bound_stack_word, contextTheory.vv_location_def] >>
  conj_tac
  >- (irule dynamic_word_vv_post >> simp[] >>
      irule zero_convert_child_post >> metis_tac[]) >>
  simp[bodyPtrDefsTheory.ptr_vv_ok_def, read_result_def, return_def,
    bodyPtrDefsTheory.ptr_val_ok_def, venomStateTheory.eval_operand_def,
    ptrDisciplineTheory.op_taint_def, ptrDisciplineTheory.op_prov_def,
    loweringPostsTheory.expr_val_rel_def]
QED

Finalise convert_dynamic_selected_continuation

Theorem convert_dynamic_vv_sim_full:
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (TypeBuiltin ann Convert dst [e]) es /\
  body_expr_full_ok cx e /\ is_bytestring_type (expr_type e) /\
  ~is_bytestring_type dst ==>
  expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (TypeBuiltin ann Convert dst [e]) es
Proof
  strip_tac >> simp[expr_vv_sim_full_via_bundle] >> rpt gen_tac >> strip_tac >>
  drule_all convert_dynamic_child_site >> strip_tac >> gvs[] >>
  rename1 `is_word_type (BaseT bt)` >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by
    (fs[body_expr_full_ok_def] >> metis_tac[]) >>
  qpat_assum `expr_sim_full_hypotheses _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_sim_full_hypotheses_def, expr_sim_full_code_def]) >>
  mp_tac (Q.INST [`ty` |-> `expr_type e`] (SPEC_ALL expr_sim_full_of_vv_post_buffer_exit)) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  disch_then (qspecl_then
    [`st0`,`sa`,`sm`,`sha`,`shadow_sm`,`x`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
  simp[convert_dynamic_source_bind] >>
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
  >- suspend "package" >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_post_source >>
  goal_assum (drule_at Any) >> simp[] >>
  rpt gen_tac >> Cases_on `res` >> simp[Abbr `childR`] >>
  POP_ASSUM_LIST (K all_tac) >>
  metis_tac[stmtSimPropsTheory.expr_exit_INR_type, halt_exit_INR_type]
QED

Resume convert_dynamic_vv_sim_full[package]:
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >> fs[] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       expr_sim_full_post (DF,lo,d,ctx,func) cenv cx e (es,sa,sm,s0,x,G0,tn0)
         H res mid G1 tn1 t /\
       (~is_word_type (post_value_type cenv e) ==>
        !rt w. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME rt /\
               eval_operand x t = SOME w ==>
               type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= t.vs_alloca_next)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. _ ==> childQ _ _ _ _ _ _ /\ _` (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     simp[Abbr `childQ`, NoAsms] >> strip_tac >>
     `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
       (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ t`
         (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [loweringPostsTheory.expr_post_def]) >>
        disch_then (mp_tac o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp) >>
        simp[]) >>
     gvs[expr_sim_full_post_def, expr_sim_full_endpoint_def, AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]) >>
  `~t.vs_halted /\ mid.gas_obs = []` by
    (qpat_assum `!H. _ ==> childQ _ _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     gvs[vyperStorageFootprintTheory.storage_trace_domain_def]) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==> storage_well_formed_on cx es (FST H)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >> simp[]) >>
  `(if lowered_value_type cenv e = BaseT (BytesT (Dynamic 0)) \/
        lowered_value_type cenv e = BaseT (StringT 0) then
      sm = sb /\ vv = StackValue (BaseT bt) (Lit 0w)
    else ?out. vv = StackValue (BaseT bt) out /\
      compile_type_convert x (mk_convert_op (expr_type e) (BaseT bt)) sm = (out,sb))` by
    (IF_CASES_TAC >> fs[] >> metis_tac[]) >>
  drule_all (REWRITE_RULE [convert_dynamic_origin_rule_true] (BETA_RULE
    (Q.INST [`P` |-> `\m b s r. T`] convert_dynamic_selected_continuation))) >>
  `mid with gas_obs := [] = mid` by
    (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  disch_then (qspecl_then [`shadow_ctx`,`PG`] mp_tac) >> strip_tac >>
  disj1_tac >> qexists_tac `v` >> fs[]
  >- (qpat_x_assum `r = OK u` SUBST_ALL_TAC >>
      irule gasOutcomeFullComposeTheory.gas_outcome_full_pure >>
      reverse conj_tac >- simp[] >>
      qexistsl_tac [`Gf`,`mid`,`res'`,`u`,`tnf`] >> fs[]) >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_exit >>
  reverse conj_tac >- simp[] >>
  qexistsl_tac [`Gf`,`mid`,`r`,`res'`,`tnf`] >> simp[] >>
  Cases_on `r` >> fs[fragExecTheory.exit_result_def] >>
  gen_tac >> disch_tac >>
  qpat_assum `!H. _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >> simp[]
QED

Finalise convert_dynamic_vv_sim_full
