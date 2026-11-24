(* Self-code Slice composition over explicit joint runtime interfaces. *)
Theory bodyFullBuiltinSliceCodeSelfCompose
Ancestors
  bodyFullShadowBodyInv
  bodyFullPreds bodySimFull bodyFullOfVV gasOutcomeFullCompose
  exprSimSliceExtcodeTyped bodyFullUnwrapRun exprSimProps exprSimWordArgs exprSimHash
  exprSimSliceExtcodeEntry bodyFullBuiltinWordPowCompose
  bodyFullBuiltinBytestringQuery bodyFullBuiltinBytestringBuffer
  bodyFullBuiltinBytestringBounds bodyFullBuiltinBytestringCopy
  bodyFullBuiltinBytestringAbort exprSimSliceSelfCode
  bodyPtrBytestringBuiltinsWindowGhost wordArgsPtr
  exprSimSliceSource exprSimSliceOrdinaryFrame exprSimHypsDefs
  exprLowering vyperInterpreter vyperAST list
  fragExec emitHelperProps bodyPtrBytestringBuiltinsSlice
  bodyPtrBytestringBuiltinsBuffer loweringPosts loweringStateRelDefs
  reasonCodeResourcesPtr bodyPtrAttributeFields exprLoweringProps stateRelProj
  bodyFullIfExpReach
  bodyFullHashKeccakFixed[qualified,ignore_grammar]

Theorem slice_self_compilation_context[local]:
  lower_value compile_expr cenv ty start sa = (start_op,s1) /\
  lower_value compile_expr cenv ty len s1 = (len_op,s2) /\
  compile_slice_code start_op len_op out_size s2 = (out,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa ==>
  ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 sb /\
  fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\ fn_has_code s2 sb func /\
  local_ptrs_reserved cenv s1 /\ local_ptrs_reserved cenv s2
Proof
  strip_tac >>
  `ci_mono sa s1 /\ ci_mono s1 s2` by
    metis_tac[exprLoweringPropsTheory.compile_expr_grows,ci_mono_def] >>
  `!a b c s. ci_mono s (SND (compile_assert_slice_bounds a b c s))` by
    (rpt gen_tac >> rewrite_tac[builtinBytesTheory.compile_assert_slice_bounds_def] >> BETA_TAC >>
     rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
          (conj_tac >- simp[ci_mono_emit_op,ci_mono_emit_void]) ORELSE gen_tac) >>
     simp[ci_mono_emit_op,ci_mono_emit_void]) >>
  `ci_mono s2 sb` by
    (`ci_mono s2 (SND (compile_slice_code start_op len_op out_size s2))` suffices_by simp[] >>
     rewrite_tac[builtinBytesTheory.compile_slice_code_def] >> BETA_TAC >>
     rpt (ho_match_mp_tac ci_mono_bind ORELSE ho_match_mp_tac ci_mono_ignore_bind ORELSE
          (conj_tac >- simp[ci_mono_emit_op,ci_mono_emit_void,ci_mono_compile_slice_out_buf]) ORELSE
          gen_tac ORELSE strip_tac ORELSE CASE_TAC ORELSE
          (Cases_on `av` >> rewrite_tac[pairTheory.UNCURRY_DEF] >> BETA_TAC)) >>
     simp[ci_mono_emit_op,ci_mono_emit_void,ci_mono_comp_return]) >>
  simp[] >>
  mp_tac (Q.INST [`s3` |-> `s2`, `s4` |-> `sb`]
    (SPEC_ALL exprSimSliceOrdinaryContextTheory.slice_pipeline_code_context)) >>
  simp[ci_mono_def,compileEnvTheory.cs_extends_refl]
QED

Theorem slice_builtin_self_vv_full_from_tail:
  (!query_op query_ops sa limit sc start cnt sd N out data se copy_op copy_ops sf sb
    func cenv ctx tn s code i k G addr n e args cx st0 es DF lo d explicit PG tops source.
    emit_op query_op query_ops sa = (limit,sc) /\
    compile_assert_slice_bounds start cnt limit sc = ((),sd) /\
    compile_slice_out_buf N sd = ((out,data),se) /\
    emit_void copy_op copy_ops se = ((),sf) /\
    emit_void MSTORE [out;cnt] sf = ((),sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
      s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp) /\
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
      (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
         (ctx_has_dalloca ctx ==> !u. r = Halt u ==> allocas_below_fmp u))) /\
  (!cenv cx env a n ct addr start len es ee e tops ctx DF lo d shadow_ctx PG func shadow_func ty.
    expr_body_pre cenv cx env
      (Builtin a (Slice n) [Builtin ct (Acc Code) [addr];start;len]) es /\
    body_const_cells_agree [(NONE,tops)] cx env ee /\
    expr_sim_inv cenv cx env ee /\ (e = start \/ e = len \/ e = addr) /\
    body_expr_full_ok cx e /\ body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx  ==>
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
    shadow_body_inv tops ctx shadow_ctx /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_body_pre cenv cx env (Builtin a (Slice n) args) es /\
    code_slice_source (Slice n) args = SOME (code_ty,addr) /\
    is_self_code (Builtin code_ty (Acc Code) [addr]) ==>
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin a (Slice n) args) es
Proof
  disch_then (CONJUNCTS_THEN2 (mk_asm "tail_run") (mk_asm "child_run")) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `code_slice_source _ _ = SOME _`
    (strip_assume_tac o REWRITE_RULE [code_slice_source_SOME]) >>
  gvs[] >> fs[vyperContextTheory.builtin_args_length_ok_def] >>
  rw[expr_vv_sim_full_def] >>
  `body_expr_full_ok cx start` by fs[body_exprs_full_ok_def] >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty start es` by
    (`expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
     asm "child_run" (irule o cj 1) >>
     simp[] >> qexistsl_tac [`a`, `addr`, `code_ty`, `env`, `es`,
                   `len`, `n`, `start`, `tops`] >> simp[]) >>
  `?self_ty. addr = Builtin self_ty (Env SelfAddr) []` by
    (qpat_x_assum `is_self_code _` mp_tac >> rpt (pop_assum kall_tac) >>
     rewrite_tac[Once (oneline is_self_code_def)] >>
     rpt (CASE_TAC >> fs[]) >> metis_tac[]) >>
  gvs[] >>
  `well_typed_expr env
      (Builtin a (Slice n) [Builtin code_ty (Acc Code) [Builtin self_ty (Env SelfAddr) []];start;len])` by
    fs[expr_body_pre_def] >>
  `well_typed_expr env (Builtin code_ty (Acc Code) [Builtin self_ty (Env SelfAddr) []])` by
    (qpat_x_assum `well_typed_expr env (Builtin _ (Slice _) _)`
       (assume_tac o MATCH_MP (cj 1 (iffLR (cj 9 vyperTypeSystemTheory.well_typed_expr_def)))) >>
     irule exprSimSourceTheory.well_typed_exprs_member >>
     goal_assum (drule_at Any) >> simp[]) >>
  `code_ty = BaseT (BytesT (Dynamic 24576)) /\ self_ty = BaseT AddressT` by
    (qpat_assum `well_typed_expr env (Builtin _ (Acc Code) _)`
       (mp_tac o MATCH_MP (cj 2 (iffLR (cj 9 vyperTypeSystemTheory.well_typed_expr_def)))) >>
     simp[NoAsms,vyperTypeSystemTheory.well_typed_builtin_app_def,
          vyperTypeSystemTheory.account_item_type_def,vyperASTTheory.expr_type_def]) >>
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
  qpat_assum `compile_slice_code start_op len_op _ st2 = _`
    (mp_then Any drule_all slice_self_compilation_context) >> strip_tac >>
  drule exprSimSliceSelfCodeTheory.slice_code_decompose >> strip_tac >> gvs[] >>
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
  `local_ptrs_reserved (gas_shadow_env T cenv) shadow_sa` by
    (irule bodyFullSharedTheory.local_ptrs_reserved_gas_shadow >>
     qexists_tac `sa` >> conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `compile_slice_code start_op' len_op' _ st2' = _`
    (mp_then Any drule_all slice_self_compilation_context) >> strip_tac >>
  `start_op' = start_op /\ gas_shadow_state st1 st1'` by
    (irule bodyFullSharedTheory.gas_shadow_step >>
     qpat_assum `lower_value _ _ _ start sa = _` (irule_at Any) >>
     qpat_assum `lower_value _ _ _ (gas_shadow_expr start) shadow_sa = _`
       (irule_at Any) >>
     simp[] >> irule gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value_env) >>
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
  irule gas_outcome_full_bind_all_path >>
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
  qpat_x_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
                    gas_origin_ptr_path _ _ marks (OK t,G1,tn1)`
    (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then assume_tac)) >>
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
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (`body_const_cells_agree [(NONE,tops)] cx env (mid with gas_obs := [])`
       suffices_by simp[] >>
     irule body_const_cells_agree_expr_read >>
     qpat_assum `!tail. bind (eval_expr cx start) _ _ = _`
       (qspec_then `[]` (irule_at Any)) >> fs[expr_body_pre_def]) >>
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
     qexistsl_tac [`BaseT (BytesT (Dynamic n))`,
       `Builtin (BaseT AddressT) (Env SelfAddr) []`,
       `BaseT (BytesT (Dynamic 24576))`, `env`, `es`,
       `len`, `n`, `start`, `tops`] >> simp[]) >>
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
    (irule bodyFullSharedTheory.gas_shadow_step >>
     qpat_assum `lower_value _ _ _ len st1 = _` (irule_at Any) >>
     qpat_assum `lower_value _ _ _ (gas_shadow_expr len) st1' = _`
       (irule_at Any) >>
     simp[] >> irule gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value_env) >>
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
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (qpat_assum `body_inv tops ctx cenv cx` (fn inv =>
       qpat_assum `MEM func ctx.ctx_functions` (fn member =>
         ACCEPT_TAC (MATCH_MP bodyFullIfExpReachTheory.body_inv_no_phi
           (CONJ inv member))))) >>
  `!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u` by
    (qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) marks (OK t,G1,tn1)` (fn path =>
       qpat_assum `!bb. MEM bb func.fn_blocks ==> phi_prefix_length _ = _` (fn no_phi =>
         qpat_assum `!fn i v. frag_reachable ctx func s0 fn i v ==> _`
           (ACCEPT_TAC o MATCH_MP bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom o
            CONJ path o CONJ no_phi)))) >>
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
     disch_then (qspecl_then [`cx`,`env`,`es`] mp_tac) >>
     simp[compileEnvTheory.is_word_type_def]) >>
  `(!x. len_op = Var x ==> not_fresh_at st2 x) /\ (!l. len_op <> Label l)` by
    (qpat_assum `lower_value _ _ _ len _ = _`
       (mp_then Any mp_tac exprSimSourceTheory.expr_body_pre_lower_value_word_shape) >>
     disch_then (qspecl_then [`cx`,`env`,`mid`] mp_tac) >>
     simp[compileEnvTheory.is_word_type_def]) >>
  `!x. start_op = Var x ==> not_fresh_at st2 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `st1` >> fs[exprLoweringPropsTheory.ci_mono_def]) >>
  `eval_operand start_op u = SOME (n2w i)` by
    (qpat_assum `!H. valid_horizon _ _ H len_mid.storage_trace ==> expr_post _ _ _ _ _ len _ _ _ _ _ _ _ _`
       (qspec_then `storage_trace_horizon len_mid.storage_trace` mp_tac) >>
     (impl_tac >- simp[]) >>
     disch_then (mp_then Any (qspecl_then [`start_op`,`n2w i`] mp_tac) slice_post_operands) >>
     simp[]) >>
  `op_taint tn1 start_op = {} /\ op_prov G1 start_op = NONE /\
   op_taint tn2 len_op = {} /\ op_prov G2 len_op = NONE` by
    (qpat_assum `ptr_val_ok _ _ _ start_op G1 tn1 t` mp_tac >>
     qpat_assum `ptr_val_ok _ _ _ len_op G2 tn2 u` mp_tac >>
     qpat_assum `expr_type start = _` mp_tac >>
     qpat_assum `expr_type len = _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     fs[bodyPtrDefsTheory.ptr_val_ok_def,post_value_type_word,
        compileEnvTheory.is_word_type_def]) >>
  qpat_assum `ghost_kept_at lo cenv mid st1 G1 tn1 t G2 tn2`
    (assume_tac o CONJUNCT1 o REWRITE_RULE[bodyPtrDefsTheory.ghost_kept_at_def]) >>
  `op_taint tn2 start_op = {} /\ op_prov G2 start_op = NONE` by
    (qpat_assum `!x. not_fresh_at st1 x ==> _` mp_tac >>
     qpat_assum `!x. start_op = Var x ==> not_fresh_at st1 x` mp_tac >>
     qpat_assum `op_taint tn1 start_op = {}` mp_tac >>
     qpat_assum `op_prov G1 start_op = NONE` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> Cases_on `start_op` >>
     gvs[ptrDisciplineTheory.op_prov_def,ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H len_mid.storage_trace ==>
     stmt_state_rel H ctx func cenv cx len_mid u /\
     storage_well_formed_on cx len_mid (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx len_mid G2 tn2 u` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H len_mid.storage_trace ==>
        ghost_inv_at _ _ _ _ _ _ G2 tn2 u`
       (qspec_then `H` mp_tac) >>
     qpat_assum `!H. valid_horizon _ _ H len_mid.storage_trace ==>
        expr_post _ _ _ _ _ len _ _ _ _ _ _ _ _`
       (qspec_then `H` (mp_tac o REWRITE_RULE[loweringPostsTheory.expr_post_def])) >> simp[]) >>
  `u.vs_code = cx.txn.code` by
    (qpat_assum `!H. valid_horizon _ _ H len_mid.storage_trace ==>
        stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon len_mid.storage_trace` mp_tac) >>
     (impl_tac >- simp[]) >>
     disch_then (ACCEPT_TAC o
       MATCH_MP (cj 3 (iffLR loweringStateRelDefsTheory.accounts_rel_def)) o
       MATCH_MP (cj 6 (iffLR loweringStateRelDefsTheory.state_rel_def)) o
       MATCH_MP stmt_state_rel_state_rel o CONJUNCT1)) >>
  `LENGTH cx.txn.code < dimword (:256)` by
    (fs[exprSimHypsDefsTheory.expr_sim_inv_def,
        vyperTypeInvariantsTheory.context_well_typed_def,wordsTheory.dimword_def]) >>
  `step_inst_base (mk_inst st2.cs_next_id CODESIZE []
      [STRING #"%" (toString st2.cs_next_var)]) u =
    OK (update_var (STRING #"%" (toString st2.cs_next_var))
      (n2w (LENGTH cx.txn.code)) u)` by
    simp[venomExecSemanticsTheory.step_inst_base_opcode_eqs,
         venomInstTheory.mk_inst_def,venomExecSemanticsTheory.exec_read0_def] >>
  `!v wd. i+k <= LENGTH cx.txn.code /\
    v.vs_accounts = u.vs_accounts /\ v.vs_call_ctx = u.vs_call_ctx /\
    v.vs_code = u.vs_code /\
    eval_operand dst v = SOME wd /\ eval_operand start_op v = SOME (n2w i) /\
    eval_operand len_op v = SOME (n2w k) /\
    (CODECOPY = EXTCODECOPY ==> eval_operand start_op v = eval_operand start_op u) ==>
    step_inst_base (mk_inst se.cs_next_id CODECOPY [dst;start_op;len_op] []) v =
      OK (write_memory_with_expansion (w2n wd)
        (TAKE k (DROP i cx.txn.code)) v)` by
    (rpt strip_tac >>
     `TAKE k (DROP i cx.txn.code ++ REPLICATE k 0w) = TAKE k (DROP i cx.txn.code)` by
       (irule rich_listTheory.TAKE_APPEND1 >> simp[]) >>
     simp[venomExecSemanticsTheory.step_inst_base_opcode_eqs,
       venomInstTheory.mk_inst_def,venomExecSemanticsTheory.exec_write2_def,
       wordsTheory.w2n_n2w]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
      not_fresh_at st2 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> fs[exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
      not_fresh_at st2 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> fs[exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u /\
    u.vs_alloca_next + pending_alloca_size func u <= w2n u.vs_initial_fmp` by
    (qpat_assum `!H. valid_horizon _ _ H len_mid.storage_trace ==>
       stmt_state_rel H ctx func cenv cx len_mid u /\ _`
       (qspec_then `storage_trace_horizon len_mid.storage_trace` mp_tac) >>
     (impl_tac >- simp[]) >>
     disch_then (fn th =>
       mp_tac (MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp
         (CONJUNCT1 th)) >>
       mp_tac (MATCH_MP stmt_state_rel_fmp_room (CONJUNCT1 th))) >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[exprLoweringPropsTheory.fmp_room_def] >> decide_tac) >>
  rpt (qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` kall_tac) >>
  irule gas_outcome_full_post_source >>
  asm "tail_run" (irule_at Any) >>
  qpat_assum `emit_op CODESIZE [] st2 = _` (irule_at Any) >>
  qpat_assum `compile_assert_slice_bounds start_op len_op src_len sc = _` (irule_at Any) >>
  qpat_assum `compile_slice_out_buf _ sd = ((out,dst),se)` (irule_at Any) >>
  qpat_assum `emit_void CODECOPY _ se = _` (irule_at Any) >>
  qpat_assum `emit_void MSTORE _ sf = _` (irule_at Any) >>
  qpat_assum `eval_operand start_op u = SOME (n2w i)` (irule_at Any) >>
  qpat_assum `eval_operand len_op u = SOME (n2w k)` (irule_at Any) >>
  qpat_assum `local_ptrs_reserved cenv st2` (irule_at Any) >>
  qrefinel [`n`,`_`,`d`,`cx.txn.code`] >>
  simp[MEM,NoAsms] >>
  qexists_tac `[Builtin (BaseT (BytesT (Dynamic 24576))) (Acc Code)
     [Builtin (BaseT AddressT) (Env SelfAddr) []];start;len]` >>
  simp[] >>
  conj_tac
  >- (qpat_assum `!x. start_op = Var x ==> not_fresh_at st2 x` mp_tac >>
      qpat_assum `!x. len_op = Var x ==> not_fresh_at st2 x` mp_tac >>
      rpt (pop_assum kall_tac) >> metis_tac[]) >>
  conj_tac
  >- (simp[vyperStateTheory.get_accounts_def,vyperStateTheory.bind_def,
        vyperStateTheory.lift_sum_def,vyperStateTheory.return_def,
        vyperStateTheory.raise_def,exprSimSliceSourceTheory.slice_bytes_nat] >>
      Cases_on `i+k <= LENGTH cx.txn.code` >>
      simp[vyperStateTheory.return_def,vyperStateTheory.raise_def]) >>
  qx_genl_tac [`H`,`ee`,`G'`,`tn'`,`target`] >> strip_tac >>
  `ee with gas_obs := [] = ee` by
    (qpat_assum `ee.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  `ee = len_mid` by
    (qpat_assum `!tail. bind get_accounts _ _ = _` (qspec_then `[]` mp_tac) >>
     qpat_assum `ee with gas_obs := [] = ee` mp_tac >>
     qpat_assum `len_mid with gas_obs := [] = len_mid` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `evaluate_slice (BytesV cx.txn.code) (IntV (&i)) (IntV (&k)) n` >>
     simp[vyperStateTheory.get_accounts_def,vyperStateTheory.bind_def,
          vyperStateTheory.lift_sum_def,vyperStateTheory.return_def,
          vyperStateTheory.raise_def] >> rpt strip_tac >>
     qpat_x_assum `len_mid with gas_obs := _ = ee`
       (mp_tac o Q.AP_TERM `\st:evaluation_state. st with gas_obs := []`) >> simp[]) >>
  qpat_assum `ee = len_mid` SUBST_ALL_TAC >>
  `!H. valid_horizon cx st0 H len_mid.storage_trace ==>
       valid_horizon cx st0 H mid.storage_trace` by
    (rpt strip_tac >>
     qpat_assum `!tail. bind (eval_expr cx len) _ _ = _`
       (qspec_then `[]`
         (mp_then (Pos (el 2)) mp_tac vyperStorageFootprintTheory.valid_horizon_frame)) >>
     simp[exprSimSliceOrdinaryContinueTheory.slice_read_frame]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       valid_horizon cx st0 H es.storage_trace` by
    (rpt strip_tac >>
     qpat_assum `!tail. bind (eval_expr cx start) _ _ = _`
       (qspec_then `[]`
         (mp_then (Pos (el 2)) mp_tac vyperStorageFootprintTheory.valid_horizon_frame)) >>
     simp[exprSimSliceOrdinaryContinueTheory.slice_read_frame]) >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (qpat_assum `!H. valid_horizon _ _ H len_mid.storage_trace ==>
       valid_horizon _ _ H mid.storage_trace` irule >> simp[]) >>
  `valid_horizon cx st0 H es.storage_trace` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
       valid_horizon _ _ H es.storage_trace` irule >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
      expr_post H _ _ _ _ start _ _ _ _ _ _ _ _`
    (qspec_then `H` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H len_mid.storage_trace ==>
      expr_post H _ _ _ _ len _ _ _ _ _ _ _ _`
    (qspec_then `H` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
    (qspec_then `H` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
  `sa.cs_next_var <= st1.cs_next_var /\ st1.cs_next_var <= st2.cs_next_var /\
   sa.cs_next_id <= st1.cs_next_id /\ st1.cs_next_id <= st2.cs_next_id` by
    (qpat_assum `ci_mono sa st1` mp_tac >>
     qpat_assum `ci_mono st1 st2` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[exprLoweringPropsTheory.ci_mono_def]) >>
  conj_tac
  >- (irule exprSimSliceOrdinaryContinueTheory.slice_two_operand_post_rebase >>
      qpat_assum `expr_post H _ _ _ _ len _ _ _ _ _ _ _ _` (irule_at Any) >>
      qpat_assum `expr_post H _ _ _ _ start _ _ _ _ _ _ _ _` (irule_at Any) >>
      simp[loweringPostsTheory.expr_has_effect_thm]) >>
  `wb_frame cenv es mid sa s0 t` by
    (qpat_assum `expr_post H _ _ _ _ start _ _ _ _ _ _ _ _`
       (mp_then Any ACCEPT_TAC exprSimWordArgsTheory.expr_post_frame)) >>
  `wb_frame cenv mid len_mid st1 t u` by
    (qpat_assum `expr_post H _ _ _ _ len _ _ _ _ _ _ _ _`
       (mp_then Any ACCEPT_TAC exprSimWordArgsTheory.expr_post_frame)) >>
  `wb_frame cenv es len_mid sa s0 u` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx es s0`
       (mp_then Any irule exprSimWordArgsTheory.wb_frame_trans) >>
     qpat_assum `wb_frame cenv mid len_mid st1 t u` (irule_at Any) >> simp[]) >>
  `sa.cs_next_var <= st2.cs_next_var /\ sa.cs_next_id <= st2.cs_next_id` by decide_tac >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx es s0`
       (mp_then Any irule wordArgsPtrTheory.ghost_kept_at_wb_trans) >>
     qpat_assum `ghost_kept_at lo cenv mid st1 G1 tn1 t G2 tn2` (irule_at Any) >>
     qexists_tac `mid` >> simp[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn'` by
    (qpat_assum `stmt_state_rel H ctx func cenv cx es s0`
       (mp_then Any irule wordArgsPtrTheory.ghost_kept_at_wb_trans) >>
     qpat_assum `ghost_kept_at lo cenv len_mid st2 G2 tn2 u G' tn'` (irule_at Any) >>
     qexists_tac `len_mid` >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp target` by
    (qpat_assum `vv_post H ctx func cenv cx _ _ _ _ _ _ _ _ target`
       (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp o
        CONJUNCT1 o REWRITE_RULE [loweringPostsTheory.vv_post_def])) >>
  fs[vyperASTTheory.expr_type_def,exprLoweringTheory.lowered_value_type_def,
     contextTheory.mk_ptr_def,contextTheory.vv_location_def,
     compileEnvTheory.is_bytestring_type_def]
QED
