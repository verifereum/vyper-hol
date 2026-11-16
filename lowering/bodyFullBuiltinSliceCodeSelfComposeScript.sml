(* Self-code Slice composition over explicit joint runtime interfaces. *)
Theory bodyFullBuiltinSliceCodeSelfCompose
Ancestors
  bodyFullPreds bodySimFull bodyFullOfVV gasOutcomeFullCompose
  exprSimSliceExtcodeTyped bodyFullUnwrapRun exprSimProps exprSimWordArgs exprSimHash
  exprSimSliceExtcodeEntry bodyInvNoDalloca bodyFullBuiltinWordPowCompose
  bodyFullBuiltinBytestringQuery bodyFullBuiltinBytestringBuffer
  bodyFullBuiltinBytestringBounds bodyFullBuiltinBytestringCopy
  bodyFullBuiltinBytestringAbort exprSimSliceSelfCode
  bodyPtrBytestringBuiltinsWindowGhost wordArgsPtr
  exprSimSliceSource exprSimSliceOrdinaryFrame exprSimHypsDefs
  exprLowering vyperInterpreter vyperAST list
  fragExec emitHelperProps bodyPtrBytestringBuiltinsSlice
  bodyPtrBytestringBuiltinsBuffer loweringPosts loweringStateRelDefs
  reasonCodeResourcesPtr bodyPtrAttributeFields

Theorem slice_builtin_self_vv_full_from_tail:
  (!query_op query_ops sa limit sc start cnt sd N out data se copy_op copy_ops sf sb
    func cenv ctx tn s code i k G addr n e args cx st0 es DF lo d explicit PG tops source.
    emit_op query_op query_ops sa = (limit,sc) /\
    compile_assert_slice_bounds start cnt limit sc = ((),sd) /\
    compile_slice_out_buf N sd = ((out,data),se) /\
    emit_void copy_op copy_ops se = ((),sf) /\
    emit_void MSTORE [out;cnt] sf = ((),sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
    MEM query_op [CODESIZE;EXTCODESIZE] /\ LENGTH query_ops <= 1 /\
    (!arg. MEM arg query_ops ==> op_taint tn arg = {}) /\
    step_inst_base
      (mk_inst sa.cs_next_id query_op query_ops
        [STRING #"%" (toString sa.cs_next_var)]) s =
      OK (update_var (STRING #"%" (toString sa.cs_next_var))
        (n2w (LENGTH code)) s) /\
    eval_operand start s = SOME (n2w i) /\ eval_operand cnt s = SOME (n2w k) /\
    op_prov G start = NONE /\ op_taint tn start = {} /\
    op_prov G cnt = NONE /\ op_taint tn cnt = {} /\
    (!x. (start = Var x \/ cnt = Var x) ==> not_fresh_at sa x) /\
    (!l. start <> Label l /\ cnt <> Label l) /\
    ((copy_op = CODECOPY /\ copy_ops = [data;start;cnt]) \/
     (copy_op = EXTCODECOPY /\ copy_ops = [addr;data;start;cnt] /\
      (?aw. eval_operand addr s = SOME aw) /\ op_taint tn addr = {} /\
      (!x. addr = Var x ==> not_fresh_at sa x) /\ (!l. addr <> Label l))) /\
    (!v wd. i+k <= LENGTH code /\
      v.vs_accounts = s.vs_accounts /\ v.vs_call_ctx = s.vs_call_ctx /\
      v.vs_code = s.vs_code /\ eval_operand data v = SOME wd /\
      eval_operand start v = SOME (n2w i) /\ eval_operand cnt v = SOME (n2w k) /\
      (copy_op = EXTCODECOPY ==> eval_operand addr v = eval_operand addr s) ==>
      step_inst_base (mk_inst se.cs_next_id copy_op copy_ops []) v =
        OK (write_memory_with_expansion (w2n wd) (TAKE k (DROP i code)) v)) /\
    i < dimword (:256) /\ 0 < k /\ k < dimword (:256) /\ k <= n /\
    LENGTH code < dimword (:256) /\
    e = Builtin (BaseT (BytesT (Dynamic n))) (Slice n) args /\
    N = type_memory_bytes cenv (BaseT (BytesT (Dynamic n))) /\
    32+n <= N /\ N < dimword (:256) /\ storage_trace_domain cx st0 es.storage_trace /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es s /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
    es.gas_obs = [] /\ alloca_history func s /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!tail. source (es with gas_obs := tail) =
      ((case evaluate_slice (BytesV code) (IntV (&i)) (IntV (&k)) n of
          INL v => INL (Value v) | INR err => INR (Error err)),
       es with gas_obs := tail)) ==>
    gas_outcome_full (DF,lo,explicit,ctx,func,PG) tops cx st0 source (es,s,G,tn)
      (\H res ee HG tm t.
        res = INL (Value (BytesV (TAKE k (DROP i code)))) /\
        vv_post H ctx func cenv cx e es sa sb s ee
          (Value (BytesV (TAKE k (DROP i code))))
          (LocatedValue (BaseT (BytesT (Dynamic n))) (mk_ptr out LocMemory)) t /\
        vv_store_bound cx (BaseT (BytesT (Dynamic n))) (BaseT (BytesT (Dynamic n)))
          ee (Value (BytesV (TAKE k (DROP i code))))
          (LocatedValue (BaseT (BytesT (Dynamic n))) (mk_ptr out LocMemory)) t /\
        t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
        ghost_inv_at (DF H) lo d cenv cx ee HG tm t /\
        ptr_vv_ok cx (BaseT (BytesT (Dynamic n)))
          (Value (BytesV (TAKE k (DROP i code))))
          (LocatedValue (BaseT (BytesT (Dynamic n))) (mk_ptr out LocMemory)) ee HG tm t /\
        ptr_buf_ok cenv e out HG t /\ ghost_kept_at lo cenv es sa G tn s HG tm)
      (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r)) /\
  (!cenv cx env a n ct addr start len es ee e tops ctx DF lo d shadow_ctx PG func shadow_func ty.
    expr_body_pre cenv cx env
      (Builtin a (Slice n) [Builtin ct (Acc Code) [addr];start;len]) es /\
    expr_sim_inv cenv cx env ee /\ (e = start \/ e = len \/ e = addr) /\
    body_expr_full_ok cx e /\ body_inv tops ctx cenv cx ==>
    expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e ee /\
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e ee) ==>
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a n args es code_ty addr.
    (builtin_args_length_ok (Slice n) (LENGTH args) ==>
       case code_slice_source (Slice n) args of
         NONE => body_exprs_full_ok cx args
       | SOME (code_ty,addr) =>
           body_exprs_full_ok cx (TL args) /\
           (!s tail_vs t. eval_exprs cx (TL args) s = (INL tail_vs,t) ==>
              body_exprs_full_ok cx [addr])) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin a (Slice n) args) es /\
    code_slice_source (Slice n) args = SOME (code_ty,addr) /\
    is_self_code (Builtin code_ty (Acc Code) [addr]) ==>
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin a (Slice n) args) es
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "tail_run") (mk_asm "child_run")) >>
  rpt gen_tac >> strip_tac >>
  `~ctx_has_dalloca ctx` by (drule body_inv_no_dalloca >> simp[]) >>
  qpat_assum `code_slice_source _ _ = SOME _`
    (strip_assume_tac o REWRITE_RULE [code_slice_source_SOME]) >>
  gvs[] >> fs[vyperContextTheory.builtin_args_length_ok_def] >>
  rw[expr_vv_sim_full_def] >>
  `body_expr_full_ok cx start` by fs[body_exprs_full_ok_def] >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty start es` by
    (`expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
     asm "child_run" (irule o cj 1) >>
     simp[] >> conj_tac >- (qexists_tac `tops` >> simp[]) >>
     qpat_assum `expr_body_pre _ _ _ (Builtin _ _ _) _` (irule_at Any) >> simp[]) >>
  qpat_assum `is_self_code _`
    (mp_tac o REWRITE_RULE[exprSimSliceSelfCodeTheory.is_self_code_thm]) >>
  disch_then (qx_choose_then `ct` (qx_choose_then `self_ty` strip_assume_tac)) >>
  gvs[] >>
  `well_typed_expr env
      (Builtin a (Slice n) [Builtin code_ty (Acc Code) [Builtin self_ty (Env SelfAddr) []];start;len])` by
    fs[expr_body_pre_def] >>
  `well_typed_expr env (Builtin code_ty (Acc Code) [Builtin self_ty (Env SelfAddr) []])` by
    (qpat_x_assum `well_typed_expr env (Builtin _ (Slice _) _)` mp_tac >>
     simp[vyperTypeSystemTheory.well_typed_expr_def]) >>
  `code_ty = BaseT (BytesT (Dynamic 24576)) /\ self_ty = BaseT AddressT` by
    (qpat_assum `well_typed_expr env (Builtin _ (Acc Code) _)` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[vyperTypeSystemTheory.well_typed_expr_def,
          vyperTypeSystemTheory.well_typed_builtin_app_def,
          vyperTypeSystemTheory.account_item_type_def,vyperTypeSystemTheory.env_item_type_def,
          vyperASTTheory.expr_type_def]) >>
  `a = BaseT (BytesT (Dynamic n)) /\ expr_type start = BaseT (UintT 256) /\
   expr_type len = BaseT (UintT 256) /\
   slice_operands_ok (Slice n) [Builtin code_ty (Acc Code) [Builtin self_ty (Env SelfAddr) []];start;len]` by
    (qpat_assum `well_typed_expr env (Builtin _ (Slice _) _)`
       (mp_tac o MATCH_MP slice_typed_args) >> simp[vyperASTTheory.expr_type_def]) >>
  gvs[] >>
  `!bt xs. names_builtin bt xs ==> bt <> Slice n` by
    (ho_match_mp_tac names_builtin_ind >> simp[names_builtin_def]) >>
  `!xs. ~names_builtin (Slice n) xs` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  qpat_x_assum `!bt xs. _` kall_tac >>
  qpat_x_assum `compile_expr _ _ (Builtin _ _ _) _ = _` mp_tac >>
  simp[compile_expr_builtin_dispatch,compile_builtin_dispatch_component_eq,
       exprBopLoweringTheory.lower_value_child_call,is_self_code_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  Cases_on `compile_slice_code start_op len_op
    (type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))) st2` >>
  gvs[as_ptr_val_def] >>
  rename1 `compile_slice_code start_op len_op _ st2 = (out,sb)` >>
  drule exprSimSliceSelfCodeTheory.slice_code_decompose >> strip_tac >> gvs[] >>
  drule_all exprSimSliceSelfCodeTheory.slice_self_code_pipeline_context >> strip_tac >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[gasShadowTheory.gas_shadow_expr_def,gasShadowTheory.gas_shadow_builtin_def,
       compile_expr_builtin_dispatch,compile_builtin_dispatch_component_eq,
       exprBopLoweringTheory.lower_value_child_call,is_self_code_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  Cases_on `compile_slice_code start_op' len_op'
    (type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))) st2'` >>
  gvs[as_ptr_val_def] >>
  `local_ptrs_reserved cenv shadow_sa` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `sa` >> fs[gasShadowStateTheory.gas_shadow_state_def]) >>
  qpat_assum `compile_slice_code start_op' len_op' _ st2' = _`
    (mp_then Any strip_assume_tac exprSimSliceSelfCodeTheory.slice_code_decompose) >>
  gvs[] >>
  drule_all exprSimSliceSelfCodeTheory.slice_self_code_pipeline_context >> strip_tac >>
  `start_op' = start_op /\ gas_shadow_state st1 st1'` by
    (qpat_x_assum `tail_run :- _` kall_tac >>
     qpat_x_assum `child_run :- _` kall_tac >>
     metis_tac[gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value,
               gasShadowStateTheory.gas_shadow_compiles_def,pairTheory.FST,pairTheory.SND]) >>
  gvs[] >>
  rewrite_tac[exprSimSliceSelfCodeTheory.slice_self_code_actions] >>
  `expr_body_pre cenv cx env start es` by
    (`well_typed_expr env
        (Builtin (BaseT (BytesT (Dynamic n))) (Slice n) [Builtin (BaseT (BytesT (Dynamic 24576))) (Acc Code)
          [Builtin (BaseT AddressT) (Env SelfAddr) []];start;len])` by
       fs[expr_body_pre_def] >>
     drule slice_typed_args >> strip_tac >> gvs[] >>
     `expr_type start <> BaseT (BytesT (Dynamic 24576))` by simp[] >>
     `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
     drule exprSimSourceTheory.expr_body_pre_builtin_typed_arg >>
     disch_then (qspecl_then [`start`,`es`] mp_tac) >> simp[]) >>
  `gas_admissible (bind (eval_expr cx start) (read_result cx)) expr_res_ok es` by
    (drule exprSimSourceTheory.expr_body_pre_gas_admissible >> simp[]) >>
  qpat_x_assum `expr_sim_full _ _ _ _ start _`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then drule >> simp[] >>
  disch_then drule_all >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ child_post _` >>
  irule gas_outcome_full_bind_all >>
  conj_tac >- (rpt gen_tac >> BETA_TAC >>
    rpt (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
         simp[vyperStorageTraceTheory.storage_trace_frame_state_reads,
              vyperStorageTraceTheory.storage_trace_frame_lifts,
              vyperStorageTraceTheory.storage_trace_frame_return,
              exprSimSliceOrdinaryContinueTheory.slice_read_frame] >> rpt gen_tac)) >>
  conj_tac >- (rpt strip_tac >>
    irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
    qexistsl_tac [`mid`,`t`,`v`] >> fs[]) >>
  conj_tac >- (rpt strip_tac >>
    irule gasExemptCertTheory.gas_exempt_cert_error_value >> simp[]) >>
  conj_tac >- simp[exprSimSliceOrdinaryContinueTheory.slice_read_frame] >>
  qexists `\H res ee G tn t. child_post H res ee G tn t /\
    ee.gas_obs = [] /\ ~t.vs_halted` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
      reverse conj_tac
      >- (rpt strip_tac >> Cases_on `res` >>
          fs[exprSimDefsTheory.expr_exit_INL,exprSimDefsTheory.halt_exit_def] >>
          rename1 `expr_exit (INR exc) exit_r` >>
          qspec_then `Value` (qspec_then `INR exc`
            (fn th => simp[SIMP_RULE (srw_ss()) [] th]))
            exprSimDefsTheory.expr_exit_success_map) >>
      simp[]) >>
  rpt gen_tac >> strip_tac >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> child_post _ _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- simp[]) >>
  simp[Abbr `child_post`, NoAsms] >> strip_tac >> gvs[] >>
  `mid with gas_obs := [] = mid` by
    (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  `expr_sim_inv cenv cx env (mid with gas_obs := [])` by
    (qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     strip_tac >>
     `expr_body_pre cenv cx env start
        (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ [])` by simp[] >>
     qspecl_then [`cenv`,`cx`,`env`,`start`,
       `es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ []`,
       `INL v`,`mid with gas_obs := []`] mp_tac
       exprSimSourceTheory.expr_body_pre_eval >> fs[SF ETA_ss]) >>
  `expr_sim_inv cenv cx env mid` by fs[] >>
  `body_expr_full_ok cx len` by
    (qpat_x_assum `body_exprs_full_ok cx [start;len]` mp_tac >>
     simp[body_exprs_full_ok_def] >> strip_tac >>
     first_x_assum irule >>
     qpat_assum `!tail. bind _ _ _ = _`
       (qspec_then `[]` (mp_tac o MATCH_MP vyperStatePreservationTheory.bind_split)) >>
     rpt (pop_assum kall_tac) >> simp[] >> metis_tac[]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty len (mid with gas_obs := [])` by
    (asm "child_run" (irule o cj 1) >> simp[] >>
     conj_tac >- (qexists_tac `tops` >> simp[]) >>
     qpat_assum `expr_body_pre _ _ _ (Builtin _ _ _) _` (irule_at Any) >> simp[]) >>
  `expr_body_pre cenv cx env len mid` by
    (`well_typed_expr env
        (Builtin (BaseT (BytesT (Dynamic n))) (Slice n) [Builtin (BaseT (BytesT (Dynamic 24576))) (Acc Code)
          [Builtin (BaseT AddressT) (Env SelfAddr) []];start;len])` by
       fs[expr_body_pre_def] >>
     drule slice_typed_args >> strip_tac >> gvs[] >>
     `expr_type len <> BaseT (BytesT (Dynamic 24576))` by simp[] >>
     drule exprSimSourceTheory.expr_body_pre_builtin_typed_arg >>
     disch_then (qspecl_then [`len`,`mid`] mp_tac) >> fs[]) >>
  `len_op' = len_op /\ gas_shadow_state st2 st2'` by
    (qpat_x_assum `tail_run :- _` kall_tac >>
     qpat_x_assum `child_run :- _` kall_tac >>
     metis_tac[gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value,
               gasShadowStateTheory.gas_shadow_compiles_def,pairTheory.FST,pairTheory.SND]) >>
  gvs[] >>
  `sa.cs_next_var <= st1.cs_next_var` by fs[exprLoweringPropsTheory.ci_mono_def] >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st1 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st1 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `return_buf_frame d cenv st1 t` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ start _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >>
     irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`,`s0`,`sa`] >> simp[] >>
     qpat_x_assum `tail_run :- _` kall_tac >>
     qpat_x_assum `child_run :- _` kall_tac >>
     metis_tac[cj 6 (iffLR loweringPostsTheory.expr_post_def)]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       stmt_state_rel H ctx func cenv cx mid t /\
       storage_well_formed_on cx mid (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ start _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` (mp_tac o REWRITE_RULE [loweringPostsTheory.expr_post_def])) >>
     simp[]) >>
  `gas_admissible (bind (eval_expr cx len) (read_result cx)) expr_res_ok mid` by
    (drule exprSimSourceTheory.expr_body_pre_gas_admissible >> simp[]) >>
  `!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_no_wrap inst u` by
    (rpt strip_tac >>
     drule_all bodyFullBuiltinWordPowComposeTheory.pow_compose_reachable_no_wrap >>
     simp[]) >>
  qpat_x_assum `expr_sim_full _ _ _ _ len _`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then drule >> simp[] >>
  disch_then drule_all >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ (mid,t,G1,tn1) len_post _` >>
  BETA_TAC >> irule gas_outcome_full_bind_all >>
  conj_tac >- (rpt gen_tac >> BETA_TAC >>
    rpt (irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
         simp[vyperStorageTraceTheory.storage_trace_frame_state_reads,
              vyperStorageTraceTheory.storage_trace_frame_lifts,
              vyperStorageTraceTheory.storage_trace_frame_return,
              exprSimSliceOrdinaryContinueTheory.slice_read_frame] >> rpt gen_tac)) >>
  conj_tac >- (rpt strip_tac >>
    irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
    goal_assum (drule_at Any) >> fs[]) >>
  conj_tac >- (rpt strip_tac >>
    irule gasExemptCertTheory.gas_exempt_cert_error_value >> simp[]) >>
  conj_tac >- simp[exprSimSliceOrdinaryContinueTheory.slice_read_frame] >>
  qexists `\H res ee G tn u. len_post H res ee G tn u /\
    ee.gas_obs = [] /\ ~u.vs_halted` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ (bind (eval_expr cx len) _) _ _ _`
        (irule_at Any) >>
      reverse conj_tac
      >- (rpt strip_tac >> Cases_on `res` >>
          fs[exprSimDefsTheory.expr_exit_INL,exprSimDefsTheory.halt_exit_def] >>
          rename1 `expr_exit (INR exc) exit_r` >>
          qspec_then `Value` (qspec_then `INR exc`
            (fn th => simp[SIMP_RULE (srw_ss()) [] th]))
            exprSimDefsTheory.expr_exit_success_map) >>
      simp[]) >>
  qx_genl_tac [`len_marks`,`len_res`,`len_mid`,`G2`,`tn2`,`u`] >>
  strip_tac >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon len_mid.storage_trace)
      len_mid.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> len_post _ _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon len_mid.storage_trace` mp_tac) >>
  (impl_tac >- simp[]) >>
  simp[Abbr `len_post`, NoAsms] >> strip_tac >>
  rename1 `len_res = INL lv` >> gvs[] >>
  `len_mid with gas_obs := [] = len_mid` by
    (qpat_assum `len_mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  `!H. valid_horizon cx st0 H len_mid.storage_trace ==>
      expr_post H ctx func cenv cx len mid st1 st2 t len_mid lv len_op u` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H len_mid.storage_trace ==>
        expr_post _ _ _ _ _ len _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >> simp[]) >>
  `expr_post (storage_trace_horizon mid.storage_trace) ctx func cenv cx start
      es sa st1 s0 mid v start_op t` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ start _ _ _ _ _ _ _ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >> simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes /\
   ?i. v = IntV (&i) /\ i < dimword (:256) /\
       eval_operand start_op t = SOME (n2w i)` by
    (qpat_assum `!tail. bind (eval_expr cx start) _ _ = _`
       (qspec_then `[]` assume_tac) >> fs[] >>
     qpat_assum `expr_post _ _ _ _ _ start _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac exprSimSliceOrdinaryContinueTheory.slice_uint_read_post) >>
     disch_then (qspecl_then [`gas_explicit marks s0.vs_gas_readings`,`env`] mp_tac) >>
     simp[]) >>
  rename1 `v = IntV (&i)` >> gvs[] >>
  `expr_post (storage_trace_horizon len_mid.storage_trace) ctx func cenv cx len
      mid st1 st2 t len_mid lv len_op u` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> expr_post _ _ _ _ _ len _ _ _ _ _ _ _ _`
       (qspec_then `storage_trace_horizon len_mid.storage_trace` mp_tac) >> simp[]) >>
  `expr_sim_inv cenv cx env len_mid /\
   MAP FDOM mid.scopes = MAP FDOM len_mid.scopes /\
   ?k. lv = IntV (&k) /\ k < dimword (:256) /\
       eval_operand len_op u = SOME (n2w k)` by
    (qpat_assum `!tail. bind (eval_expr cx len) _ _ = _`
       (qspec_then `[]` assume_tac) >> fs[] >>
     qpat_assum `expr_post _ _ _ _ _ len _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac exprSimSliceOrdinaryContinueTheory.slice_uint_read_post) >>
     disch_then (qspecl_then [`gas_explicit len_marks t.vs_gas_readings`,`env`] mp_tac) >>
     simp[]) >>
  rename1 `lv = IntV (&k)` >> gvs[] >>
  `0 < k /\ k <= n` by
    (qpat_x_assum `!tail. bind (eval_expr cx len) _ _ = _`
       (qspec_then `[]` assume_tac) >> fs[] >>
     qpat_x_assum `slice_operands_ok _ _` mp_tac >>
     simp[vyperTypeSystemTheory.slice_operands_ok_def] >>
     Cases_on `len` >> simp[] >>
     rename1 `Literal lt lit` >> Cases_on `lit` >> simp[] >>
     strip_tac >> gvs[] >>
     drule exprSimSliceCapacityReadTheory.slice_literal_read_length >> intLib.ARITH_TAC) >>
  `type_memory_bytes cenv (BaseT (BytesT (Dynamic n))) < dimword (:256)` by
    (fs[expr_body_pre_def,allocLimitsTheory.alloc_limits_expr_def,
       allocLimitsTheory.type_alloc_ok_def,compileEnvTheory.is_word_type_def] >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  `32+n <= type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))` by
    (qspec_then `n` mp_tac valueTypingMemoryPropsTheory.word_size_capacity >>
     simp[compileEnvTheory.type_memory_bytes_def,vfmConstantsTheory.word_size_def]) >>
  `(!x. start_op = Var x ==> not_fresh_at st1 x) /\
   (!l. start_op <> Label l)` by
    (qpat_assum `lower_value _ _ _ start _ = _`
       (mp_then Any mp_tac exprSimSourceTheory.expr_body_pre_lower_value_word_shape) >>
     disch_then (qspecl_then [`es`,`cx`,`env`] mp_tac) >>
     simp[compileEnvTheory.is_word_type_def]) >>
  `(!x. len_op = Var x ==> not_fresh_at st2 x) /\ (!l. len_op <> Label l)` by
    (qpat_assum `lower_value _ _ _ len _ = _`
       (mp_then Any mp_tac exprSimSourceTheory.expr_body_pre_lower_value_word_shape) >>
     disch_then (qspecl_then [`mid`,`cx`,`env`] mp_tac) >>
     simp[compileEnvTheory.is_word_type_def]) >>
  cheat
QED
