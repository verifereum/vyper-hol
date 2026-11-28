(* Request-prefix companion to bodyFullBuiltinSliceCodeExternalCompose. *)
Theory s1PrefixBuiltinSliceCodeExternalCompose
Ancestors
  s1PrefixPreds s1PrefixDefs s1PrefixCompose s1PrefixFrame s1PrefixProps exprBodyPreProps
  exprSimSliceExtcodeContext exprSimSliceExtcodeTyped
  exprSimSliceOrdinaryContinue exprSimSliceSource exprSimSource
  bodyFullPreds bodyFullExprsListFacts bodyFullExprsSingleton
  exprSimWordArgs gasOutcomeFullCompose
  exprLowering exprLoweringProps exprSimHypsDefs list gasShadow gasShadowCompileStmtHelpers
  bodyFullShared bodyFullIfExpReach bodyMemoryDefs
  vyperStorageTrace vyperStorageFootprint vyperInterpreter vyperState
Libs monadsyntax

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  (* The copy/bounds suffix adds no requests, so its full simulation is not needed. *)
  disch_then (CONJUNCTS_THEN2 kall_tac
    (CONJUNCTS_THEN2 (mk_asm "child_full") (mk_asm "child_prefix"))) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `code_slice_source _ _ = SOME _`
    (strip_assume_tac o REWRITE_RULE [code_slice_source_SOME]) >>
  gvs[] >> fs[vyperContextTheory.builtin_args_length_ok_def] >>
  drule expr_body_pre_static_facts >> strip_tac >>
  `body_expr_full_ok cx start` by fs[Once body_exprs_full_ok_cons] >>
  `body_expr_prefix_ok cx start` by fs[body_exprs_prefix_ok_def] >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty start es` by
    (asm "child_full" (irule o cj 1) >> simp[] >>
     qexistsl_tac [`a`,`addr`,`code_ty`,`env`,`es`,`len`,`n`,`start`,`tops`] >> simp[]) >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty start es` by
    (asm "child_prefix" (irule o cj 1) >> simp[] >>
     qexistsl_tac [`a`,`addr`,`code_ty`,`env`,`es`,`len`,`n`,`start`,`tops`] >> simp[]) >>
  `expr_type start = BaseT (UintT 256) /\ expr_type len = BaseT (UintT 256)` by
    (drule slice_typed_args >> simp[]) >>
  `expr_body_pre cenv cx env start es` by
    (`expr_type start <> BaseT (BytesT (Dynamic 24576))` by simp[] >>
     qpat_assum `expr_body_pre _ _ _ (Builtin _ _ _) _`
       (mp_then Any mp_tac expr_body_pre_builtin_typed_arg) >>
     disch_then (qspecl_then [`start`,`es`] mp_tac) >> simp[]) >>
  rw[expr_vv_sim_prefix_def,expr_vv_sim_full_pre_def] >>
  suspend "pipeline"
QED
*)
Theorem slice_builtin_external_vv_prefix_from_tail:
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
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e ee) /\
  (!cenv cx env a n ct addr start len es ee e tops ctx DF lo d shadow_ctx PG func shadow_func ty.
    expr_body_pre cenv cx env
      (Builtin a (Slice n) [Builtin ct (Acc Code) [addr];start;len]) es /\
    body_const_cells_agree [(NONE,tops)] cx env ee /\
    expr_sim_inv cenv cx env ee /\ (e = start \/ e = len \/ e = addr) /\
    body_expr_prefix_ok cx e /\ body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx  ==>
    expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e ee /\
    expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e ee) ==>
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a n args es code_ty addr.
    (builtin_args_length_ok (Slice n) (LENGTH args) ==>
       case code_slice_source (Slice n) args of
         NONE => body_exprs_full_ok cx args
       | SOME (code_ty,addr) =>
           body_exprs_full_ok cx (TL args) /\
           (!s tail_vs t. eval_exprs cx (TL args) s = (INL tail_vs,t) ==>
              body_exprs_full_ok cx [addr])) /\
    (builtin_args_length_ok (Slice n) (LENGTH args) ==>
       case code_slice_source (Slice n) args of
         NONE => body_exprs_prefix_ok cx args
       | SOME (code_ty,addr) =>
           body_exprs_prefix_ok cx (TL args) /\
           (!s tail_vs t. eval_exprs cx (TL args) s = (INL tail_vs,t) ==>
              body_exprs_prefix_ok cx [addr])) /\
    body_inv tops ctx cenv cx /\
    shadow_body_inv tops ctx shadow_ctx /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_body_pre cenv cx env (Builtin a (Slice n) args) es /\
    code_slice_source (Slice n) args = SOME (code_ty,addr) /\
    ~is_self_code (Builtin code_ty (Acc Code) [addr]) ==>
    expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin a (Slice n) args) es
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume slice_builtin_external_vv_prefix_from_tail[pipeline]:
  `!xs. ~names_builtin (Slice n) xs` by
    (`!bt xs. names_builtin bt xs ==> bt <> Slice n` by
       (ho_match_mp_tac names_builtin_ind >> simp[names_builtin_def]) >>
     metis_tac[]) >>
  qpat_x_assum `compile_expr _ _ (Builtin _ _ _) _ = _` mp_tac >>
  simp[compile_expr_builtin_dispatch,compile_builtin_dispatch_component_eq,
    exprBopLoweringTheory.lower_value_child_call,is_extcode_def,extcode_addr_expr_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  drule_all slice_extcode_pipeline_context >> strip_tac >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[gas_shadow_expr_def,gas_shadow_builtin_def,
    compile_expr_builtin_dispatch,compile_builtin_dispatch_component_eq,
    exprBopLoweringTheory.lower_value_child_call,is_extcode_def,extcode_addr_expr_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  `~is_self_code (Builtin code_ty (Acc Code) [gas_shadow_expr addr])` by
    (qspec_then `Builtin code_ty (Acc Code) [addr]` mp_tac
       (GEN_ALL gasShadowCompilePureTheory.gas_shadow_is_self_code) >>
     pure_rewrite_tac[gas_shadow_expr_def,gas_shadow_builtin_def,MAP] >> simp[]) >>
  gvs[] >>
  `local_ptrs_reserved (gas_shadow_env T cenv) shadow_sa` by
    (`local_ptrs_reserved cenv shadow_sa` by
       (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
        fs[gasShadowStateTheory.gas_shadow_state_def]) >>
     qpat_assum `local_ptrs_reserved cenv shadow_sa` mp_tac >>
     pure_rewrite_tac[loweringStateRelDefsTheory.local_ptrs_reserved_def,
       gasShadowCompileBaseTheory.gas_shadow_env_fields] >>
     disch_then ACCEPT_TAC) >>
  qpat_assum `as_ptr_val _ _ (compile_slice_extcode _ _ _ _ _) = (_,shadow_sb)`
    (mp_then Any mp_tac slice_extcode_pipeline_context) >>
  disch_then drule_all >> strip_tac >>
  rename [`lower_value _ _ _ start sa = (start_op,sm)`,
          `lower_value _ _ _ len sm = (len_op,sn)`,
          `lower_value _ _ _ addr sn = (addr_op,sp)`,
          `lower_value _ _ _ (gas_shadow_expr start) shadow_sa = (sh_start_op,sh_sm)`,
          `lower_value _ _ _ (gas_shadow_expr len) sh_sm = (sh_len_op,sh_sn)`,
          `lower_value _ _ _ (gas_shadow_expr addr) sh_sn = (sh_addr_op,sh_sp)`] >>
  `sh_start_op = start_op /\ gas_shadow_state sm sh_sm` by
    (irule gas_shadow_step >>
     qpat_assum `lower_value _ _ _ start sa = _` (irule_at Any) >>
     qpat_assum `lower_value _ _ _ (gas_shadow_expr start) shadow_sa = _` (irule_at Any) >>
     simp[gas_shadow_stmt_lower_value_env]) >>
  gvs[] >> suspend "start"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume slice_builtin_external_vv_prefix_from_tail[start]:
  `gas_admissible (bind (eval_expr cx start) (read_result cx)) expr_res_ok es` by
    (drule expr_body_pre_gas_admissible >> simp[]) >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 (bind (eval_expr cx start) (read_result cx)) (es,s0,G0,tn0)` by
    (qpat_x_assum `expr_sim_prefix _ _ _ _ start _`
       (irule o REWRITE_RULE[expr_sim_prefix_def]) >>
     qexistsl_tac [`sh_start_op`,`sa`,`sm`,`shadow_sa`,`sh_sm`] >>
     simp[expr_sim_full_pre_def] >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `expr_sim_full _ _ _ _ start _` (mp_tac o REWRITE_RULE[bodySimFullTheory.expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`sh_sm`,`sh_start_op`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ startQ startR` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (bind (eval_expr cx start) (read_result cx)) (es,s0,G0,tn0)
     (\H r ee G tn t. startQ H r ee G tn t /\
       ?marks. gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          (s0,G0,tn0) marks (OK t,G,tn)) startR` by
    (irule gas_outcome_full_post_path >>
     qpat_assum `gas_outcome_full _ _ _ _ _ _ startQ startR` (irule_at Any) >>
     rpt strip_tac >> simp[] >> goal_assum (drule_at Any)) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ startQ startR` kall_tac >>
  rev_drule slice_extcode_actions >> disch_then (fn th => rewrite_tac[th]) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ startR`
    (mp_then Any irule gas_prefix_full_bind) >>
  simp[slice_read_frame,requests_outcomes_frame_bind_all,
       evaluate_requests_outcomes_frame,requests_outcomes_frame_read_result] >>
  rpt conj_tac
  >- suspend "length"
  >- (simp[Abbr `startR`] >> rpt gen_tac >> Cases_on `res` >>
      simp[sumTheory.ISR,exprSimDefsTheory.expr_exit_INL]) >>
  rpt gen_tac >> BETA_TAC >>
  rpt (irule storage_trace_frame_bind_all >>
       simp[storage_trace_frame_state_reads,storage_trace_frame_lifts,
            storage_trace_frame_return,slice_read_frame] >> rpt gen_tac)
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume slice_builtin_external_vv_prefix_from_tail[length]:
  qpat_x_assum `Abbrev (startR = _)` kall_tac >>
  qx_genl_tac [`marks`,`sv`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then mp_tac)) >>
  simp[Abbr `startQ`, NoAsms] >> strip_tac >> gvs[] >>
  `~t.vs_halted` by
    (drule fragGasOriginPtrExecTheory.gas_origin_ptr_path_exec >> simp[fragExecTheory.exit_result_def]) >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (qpat_assum `body_inv tops ctx cenv cx` mp_tac >>
     qpat_assum `MEM func ctx.ctx_functions` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[body_inv_no_phi]) >>
  `!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u` by
    (rpt strip_tac >> drule_all gas_origin_ptr_path_dalloca_fmp_headroom >> simp[]) >>
  `sa.cs_next_var <= sm.cs_next_var` by fs[ci_mono_def] >>
  `return_buf_frame d cenv sm t` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`s0`,`sa`] >>
     simp[] >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then strip_assume_tac)) >>
     qpat_assum `expr_post _ _ _ _ _ start _ _ _ _ _ _ _ _`
       (ACCEPT_TAC o cj 6 o REWRITE_RULE[loweringPostsTheory.expr_post_def])) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       stmt_state_rel H ctx func cenv cx mid t /\ storage_well_formed_on cx mid (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     fs[loweringPostsTheory.expr_post_def]) >>
  suspend "length_source"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume slice_builtin_external_vv_prefix_from_tail[length_source]:
  qpat_assum `!tail. bind (eval_expr cx start) _ _ = _`
    (qspec_then `mid.gas_obs` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  `expr_sim_inv cenv cx env mid` by
    (irule (cj 1 exprSimSourceTheory.expr_body_pre_eval) >>
     simp[SF ETA_ss] >> goal_assum (drule_at Any) >> simp[]) >>
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (irule bodyFullPredsTheory.body_const_cells_agree_expr_read >>
     qpat_assum `bind (eval_expr cx start) _ _ = _` (irule_at Any) >>
     simp[] >> drule expr_body_pre_static_facts >> simp[]) >>
  `?s raw ee w ee'. eval_expr cx start s = (INL raw,ee) /\
                    read_result cx raw ee = (INL w,ee')` by
    (qpat_assum `bind (eval_expr cx start) _ _ = _`
       (mp_tac o MATCH_MP vyperStatePreservationTheory.bind_split) >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[] >> metis_tac[]) >>
  `body_expr_full_ok cx len` by
    (qpat_assum `body_exprs_full_ok cx [start;len]` mp_tac >>
     simp[NoAsms,Once body_exprs_full_ok_cons,body_exprs_full_ok_singleton] >>
     strip_tac >> first_x_assum irule >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[]) >>
  `body_expr_prefix_ok cx len` by
    (qpat_assum `body_exprs_prefix_ok cx [start;len]` mp_tac >>
     simp[NoAsms,body_exprs_prefix_ok_def] >>
     strip_tac >> first_x_assum irule >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty len mid` by
    (asm "child_full" (irule o cj 1) >> simp[] >>
     qexistsl_tac [`a`,`addr`,`code_ty`,`env`,`es`,`len`,`n`,`start`,`tops`] >> simp[]) >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty len mid` by
    (asm "child_prefix" (irule o cj 1) >> simp[] >>
     qexistsl_tac [`a`,`addr`,`code_ty`,`env`,`es`,`len`,`n`,`start`,`tops`] >> simp[]) >>
  `expr_body_pre cenv cx env len mid` by
    (`expr_type len <> BaseT (BytesT (Dynamic 24576))` by simp[] >>
     qpat_assum `expr_body_pre _ _ _ (Builtin _ _ _) _`
       (mp_then Any mp_tac expr_body_pre_builtin_typed_arg) >>
     disch_then (qspecl_then [`len`,`mid`] mp_tac) >> simp[]) >>
  `sh_len_op = len_op /\ gas_shadow_state sn sh_sn` by
    (irule gas_shadow_step >>
     qpat_assum `lower_value _ _ _ len sm = _` (irule_at Any) >>
     qpat_assum `lower_value _ _ _ (gas_shadow_expr len) sh_sm = _` (irule_at Any) >>
     simp[gas_shadow_stmt_lower_value_env]) >>
  gvs[] >> suspend "length_bind"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume slice_builtin_external_vv_prefix_from_tail[length_bind]:
  `gas_admissible (bind (eval_expr cx len) (read_result cx)) expr_res_ok mid` by
    (drule expr_body_pre_gas_admissible >> simp[]) >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 (bind (eval_expr cx len) (read_result cx)) (mid,t,G1,tn1)` by
    (qpat_x_assum `expr_sim_prefix _ _ _ _ len _`
       (irule o REWRITE_RULE[expr_sim_prefix_def]) >>
     qexistsl_tac [`len_op`,`sm`,`sn`,`sh_sm`,`sh_sn`] >>
     simp[expr_sim_full_pre_def] >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `expr_sim_full _ _ _ _ len _` (mp_tac o REWRITE_RULE[bodySimFullTheory.expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`sm`,`sn`,`sh_sm`,`sh_sn`,`len_op`,`t`,`G1`,`tn1`] mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ lenQ lenR` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (bind (eval_expr cx len) (read_result cx)) (mid,t,G1,tn1)
     (\H r ee G tn u. lenQ H r ee G tn u /\
       ?marks. gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          (t,G1,tn1) marks (OK u,G,tn)) lenR` by
    (irule gas_outcome_full_post_path >>
     qpat_assum `gas_outcome_full _ _ _ _ _ _ lenQ lenR` (irule_at Any) >>
     rpt strip_tac >> simp[] >> goal_assum (drule_at Any)) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ lenQ lenR` kall_tac >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ lenR`
    (mp_then Any irule gas_prefix_full_bind) >>
  simp[slice_read_frame,requests_outcomes_frame_bind_all,
       evaluate_requests_outcomes_frame,requests_outcomes_frame_read_result] >>
  rpt conj_tac
  >- suspend "address"
  >- (simp[Abbr `lenR`] >> rpt gen_tac >> Cases_on `res` >>
      simp[sumTheory.ISR,exprSimDefsTheory.expr_exit_INL]) >>
  rpt gen_tac >> BETA_TAC >>
  rpt (irule storage_trace_frame_bind_all >>
       simp[storage_trace_frame_state_reads,storage_trace_frame_lifts,
            storage_trace_frame_return,slice_read_frame] >> rpt gen_tac)
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume slice_builtin_external_vv_prefix_from_tail[address]:
  qx_genl_tac [`len_marks`,`lv`,`mid2`,`G2`,`tn2`,`u`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid2.storage_trace) mid2.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid2.storage_trace` (drule_then mp_tac)) >>
  simp[Abbr `lenQ`, NoAsms] >> strip_tac >> gvs[] >>
  `~u.vs_halted` by
    (drule fragGasOriginPtrExecTheory.gas_origin_ptr_path_exec >> simp[fragExecTheory.exit_result_def]) >>
  `!fn inst z. frag_reachable ctx func u fn inst z ==> dalloca_fmp_headroom inst z` by
    (rpt strip_tac >> drule_all gas_origin_ptr_path_dalloca_fmp_headroom >> simp[]) >>
  `sm.cs_next_var <= sn.cs_next_var` by fs[ci_mono_def] >>
  `return_buf_frame d cenv sn u` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`,`t`,`sm`] >>
     simp[] >>
     qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==> _`
       (qspec_then `storage_trace_horizon mid2.storage_trace` (drule_then strip_assume_tac)) >>
     qpat_assum `expr_post _ _ _ _ _ len _ _ _ _ _ _ _ _`
       (ACCEPT_TAC o cj 6 o REWRITE_RULE[loweringPostsTheory.expr_post_def])) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sm` >> simp[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sn x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sm` >> simp[]) >>
  `!H. valid_horizon cx st0 H mid2.storage_trace ==>
       stmt_state_rel H ctx func cenv cx mid2 u /\ storage_well_formed_on cx mid2 (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx mid2 G2 tn2 u` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==> _`
       (qspec_then `H` (drule_then strip_assume_tac)) >>
     fs[loweringPostsTheory.expr_post_def]) >>
  suspend "address_source"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume slice_builtin_external_vv_prefix_from_tail[address_source]:
  qpat_x_assum `Abbrev (lenR = _)` kall_tac >>
  qpat_assum `!tail. bind (eval_expr cx len) _ _ = _`
    (qspec_then `mid2.gas_obs` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  `expr_sim_inv cenv cx env mid2` by
    (irule (cj 1 exprSimSourceTheory.expr_body_pre_eval) >>
     simp[SF ETA_ss] >> goal_assum (drule_at Any) >> simp[]) >>
  `body_const_cells_agree [(NONE,tops)] cx env mid2` by
    (irule bodyFullPredsTheory.body_const_cells_agree_expr_read >>
     qpat_assum `bind (eval_expr cx len) _ _ = _` (irule_at Any) >>
     simp[] >> drule expr_body_pre_static_facts >> simp[]) >>
  `?st. eval_exprs cx [start;len] st = (INL [sv;lv],mid2)` by
    (qexists_tac `es with gas_obs := gas_explicit marks s0.vs_gas_readings ++
                       (gas_explicit len_marks t.vs_gas_readings ++ mid2.gas_obs)` >>
     rewrite_tac[exprSimWordArgsTheory.eval_exprs_cons_action] >>
     `eval_exprs cx [] = return []` by
       simp[FUN_EQ_THM,exprSimWordArgsTheory.eval_exprs_nil,return_def] >>
     qpat_assum `!tail. bind (eval_expr cx start) _ _ = _`
       (qspec_then `gas_explicit len_marks t.vs_gas_readings ++ mid2.gas_obs` assume_tac) >>
     gvs[bind_def,return_def]) >>
  `body_expr_full_ok cx addr` by
    (qpat_assum `!st vs z. eval_exprs cx [start;len] st = _ ==> body_exprs_full_ok cx [addr]`
       (drule_then mp_tac) >> simp[body_exprs_full_ok_singleton]) >>
  `body_expr_prefix_ok cx addr` by
    (qpat_assum `!st vs z. eval_exprs cx [start;len] st = _ ==> body_exprs_prefix_ok cx [addr]`
       (drule_then mp_tac) >> simp[body_exprs_prefix_ok_def]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty addr mid2` by
    (asm "child_full" (irule o cj 1) >> simp[] >>
     qexistsl_tac [`a`,`addr`,`code_ty`,`env`,`es`,`len`,`n`,`start`,`tops`] >> simp[]) >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty addr mid2` by
    (asm "child_prefix" (irule o cj 1) >> simp[] >>
     qexistsl_tac [`a`,`addr`,`code_ty`,`env`,`es`,`len`,`n`,`start`,`tops`] >> simp[]) >>
  `expr_body_pre cenv cx env addr mid2` by
    (irule slice_code_address_body_pre >>
     qpat_assum `expr_body_pre _ _ _ (Builtin _ (Slice _) _) es` (irule_at Any) >> simp[]) >>
  `sh_addr_op = addr_op /\ gas_shadow_state sp sh_sp` by
    (irule gas_shadow_step >>
     qpat_assum `lower_value _ _ _ addr sn = _` (irule_at Any) >>
     qpat_assum `lower_value _ _ _ (gas_shadow_expr addr) sh_sn = _` (irule_at Any) >>
     simp[gas_shadow_stmt_lower_value_env]) >>
  gvs[] >> suspend "address_bind"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume slice_builtin_external_vv_prefix_from_tail[address_bind]:
  `gas_admissible (bind (eval_expr cx addr) (read_result cx)) expr_res_ok mid2` by
    (drule expr_body_pre_gas_admissible >> simp[]) >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 (bind (eval_expr cx addr) (read_result cx)) (mid2,u,G2,tn2)` by
    (qpat_x_assum `expr_sim_prefix _ _ _ _ addr _`
       (irule o REWRITE_RULE[expr_sim_prefix_def]) >>
     qexistsl_tac [`addr_op`,`sn`,`sp`,`sh_sn`,`sh_sp`] >>
     simp[expr_sim_full_pre_def] >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `expr_sim_full _ _ _ _ addr _` (mp_tac o REWRITE_RULE[bodySimFullTheory.expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`sn`,`sp`,`sh_sn`,`sh_sp`,`addr_op`,`u`,`G2`,`tn2`] mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (bind (eval_expr cx addr) (read_result cx)) (mid2,u,G2,tn2)
     (\H r ee G tn z. ~z.vs_halted) (\H res ee gt r. ISR res)` by
    (irule gasOutcomeFullComposeTheory.gas_outcome_full_post_source >>
     qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
     simp[] >> rpt gen_tac >> Cases_on `res` >>
     simp[sumTheory.ISR,exprSimDefsTheory.expr_exit_INL]) >>
  (* The accounts reads and the two pure builtin operations add no requests. *)
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ (\H res ee gt r. ISR res)`
    (mp_then Any irule gas_prefix_full_bind_no_outcome) >>
  simp[slice_read_frame,requests_outcomes_frame_bind_all,
       evaluate_requests_outcomes_frame,requests_outcomes_frame_read_result] >>
  conj_tac
  >- (POP_ASSUM_LIST (K ALL_TAC) >> rpt gen_tac >> BETA_TAC >>
      simp[bind_def,get_accounts_def,return_def,lift_sum_def] >>
      rpt (CASE_TAC >> simp[return_def,raise_def]) >> strip_tac >> gvs[]) >>
  rpt gen_tac >> BETA_TAC >>
  rpt (irule storage_trace_frame_bind_all >>
       simp[storage_trace_frame_state_reads,storage_trace_frame_lifts,
            storage_trace_frame_return] >> rpt gen_tac)
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise slice_builtin_external_vv_prefix_from_tail
*)
