(* Request-prefix companion to bodyFullBuiltinSliceCodeSelfCompose. *)
Theory s1PrefixBuiltinSliceCodeSelfCompose
Ancestors
  s1PrefixPreds bodyFullBuiltinSliceCodeSelfCompose s1PrefixDefs
  exprBodyPreProps externalEntryShape exprSimLiteralWord
  exprSimSource bodyFullShared gasShadowCompileStmtHelpers exprSimSliceSource
  vyperInterpreter vyperState exprLowering exprSimHypsDefs exprLoweringProps
  exprSimSliceSelfCode gasShadow fragExec compileEnv
Libs monadsyntax

Theorem slice_builtin_self_vv_prefix_from_tail:
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
    is_self_code (Builtin code_ty (Acc Code) [addr]) ==>
    expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin a (Slice n) args) es
Proof
  disch_then (CONJUNCTS_THEN2 kall_tac
    (CONJUNCTS_THEN2 kall_tac (mk_asm "child_prefix"))) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `code_slice_source _ _ = SOME _`
    (strip_assume_tac o REWRITE_RULE [code_slice_source_SOME]) >>
  gvs[] >> fs[vyperContextTheory.builtin_args_length_ok_def] >>
  `body_expr_prefix_ok cx start` by fs[body_exprs_prefix_ok_def] >>
  drule expr_body_pre_static_facts >> strip_tac >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty start es` by
    (asm "child_prefix" (irule o cj 1) >> simp[] >>
     qexistsl_tac [`a`,`addr`,`code_ty`,`env`,`es`,`len`,`n`,`start`,`tops`] >> simp[]) >>
  `?self_ty. addr = Builtin self_ty (Env SelfAddr) []` by
    (qpat_x_assum `is_self_code _` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     rewrite_tac[Once (oneline is_self_code_def)] >>
     rpt (CASE_TAC >> fs[]) >> metis_tac[]) >>
  gvs[] >>
  `well_typed_expr env (Builtin code_ty (Acc Code) [Builtin self_ty (Env SelfAddr) []])` by
    (qpat_assum `well_typed_expr env (Builtin _ (Slice _) _)`
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
  `?lt j. len = Literal lt (IntL j)` by
    (qpat_x_assum `slice_operands_ok _ _` mp_tac >>
     simp[vyperTypeSystemTheory.slice_operands_ok_def] >>
     Cases_on `len` >> simp[] >>
     rename1 `Literal lt lit` >> Cases_on `lit` >> simp[]) >>
  gvs[] >>
  `expr_body_pre cenv cx env start es` by
    (`expr_type start <> BaseT (BytesT (Dynamic 24576))` by simp[] >>
     qpat_assum `expr_body_pre _ _ _ (Builtin _ _ _) _`
       (mp_then Any mp_tac exprSimSourceTheory.expr_body_pre_builtin_typed_arg) >>
     disch_then (qspecl_then [`start`,`es`] mp_tac) >> simp[]) >>
  suspend "start_compilation"
QED

Resume slice_builtin_self_vv_prefix_from_tail[start_compilation]:
  rw[expr_vv_sim_prefix_def,expr_vv_sim_full_pre_def] >>
  `!xs. ~names_builtin (Slice n) xs` by
    (`!bt xs. names_builtin bt xs ==> bt <> Slice n` by
       (ho_match_mp_tac names_builtin_ind >> simp[names_builtin_def]) >>
     metis_tac[]) >>
  qpat_x_assum `compile_expr _ _ (Builtin _ _ _) _ = _` mp_tac >>
  simp[compile_expr_builtin_dispatch,compile_builtin_dispatch_component_eq,
       exprBopLoweringTheory.lower_value_child_call,is_self_code_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[gas_shadow_expr_def,gas_shadow_builtin_def,
       compile_expr_builtin_dispatch,compile_builtin_dispatch_component_eq,
       exprBopLoweringTheory.lower_value_child_call,is_self_code_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  rename [`lower_value _ _ _ start sa = (start_op,sm)`,
          `lower_value _ _ _ (Literal lt (IntL j)) sm = (len_op,sn)`,
          `lower_value _ _ _ (gas_shadow_expr start) shadow_sa = (sh_start_op,sh_sm)`,
          `lower_value _ _ _ (Literal lt (IntL j)) sh_sm = (sh_len_op,sh_sn)`] >>
  qabbrev_tac `sz = type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))` >>
  `cs_extends sn sb` by
    (qspecl_then [`start_op`,`len_op`,`sz`,`sn`,`\x. T`] mp_tac compile_slice_code_labels >>
     Cases_on `compile_slice_code start_op len_op sz sn` >> gvs[as_ptr_val_def]) >>
  `cs_extends sh_sn shadow_sb` by
    (qspecl_then [`sh_start_op`,`sh_len_op`,`sz`,`sh_sn`,`\x. T`] mp_tac compile_slice_code_labels >>
     Cases_on `compile_slice_code sh_start_op sh_len_op sz sh_sn` >> gvs[as_ptr_val_def]) >>
  `fn_has_code sa sm func /\ fn_has_code shadow_sa sh_sm shadow_func` by
    (imp_res_tac (cj 2 compile_expr_grows) >>
     metis_tac[fn_has_code_split,cs_extends_trans]) >>
  `sh_start_op = start_op /\ gas_shadow_state sm sh_sm` by
    (irule gas_shadow_step >>
     qpat_assum `lower_value _ _ _ start sa = _` (irule_at Any) >>
     qpat_assum `lower_value _ _ _ (gas_shadow_expr start) shadow_sa = _` (irule_at Any) >>
     simp[gas_shadow_stmt_lower_value_env]) >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 (bind (eval_expr cx start) (read_result cx)) (es,s0,G0,tn0)` by
    (qpat_x_assum `expr_sim_prefix _ _ _ _ start _`
       (irule o REWRITE_RULE[expr_sim_prefix_def]) >>
     qexistsl_tac [`start_op`,`sa`,`sm`,`shadow_sa`,`sh_sm`] >>
     simp[expr_sim_full_pre_def] >> conj_tac
     >- metis_tac[expr_body_pre_gas_admissible] >>
     first_assum ACCEPT_TAC) >>
  suspend "source_trace"
QED

Resume slice_builtin_self_vv_prefix_from_tail[source_trace]:
  (* Only the start expression can append requests: length is an integer
     literal and the self-code evaluator reads code without an external call. *)
  qpat_x_assum `gas_prefix_full _ _ _ (bind (eval_expr cx start) _) _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  rewrite_tac[slice_self_code_actions,gas_prefix_full_def] >>
  disch_then (qx_choose_then `marks` (CONJUNCTS_THEN ASSUME_TAC)) >>
  qexists_tac `marks` >> conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `st = es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail` >>
  Cases_on `bind (eval_expr cx start) (read_result cx) st` >>
  rename1 `bind (eval_expr cx start) (read_result cx) st = (ans,mid)` >>
  `ee.storage_trace = mid.storage_trace` by
    (qpat_x_assum `_ st = (res,ee)` mp_tac >>
     simp[Once bind_def] >> Cases_on `ans` >> simp[] >>
     rename1 `_ st = (INL sv,mid)` >>
     `bind (eval_expr cx (Literal lt (IntL j))) (read_result cx) mid =
       (INL (evaluate_literal (IntL j)),mid)` by
       (qspecl_then [`cx`,`lt`,`IntL j`,`mid`,`mid.gas_obs`] mp_tac literal_read_all_tails >> simp[]) >>
     Cases_on `evaluate_slice (BytesV cx.txn.code) sv (evaluate_literal (IntL j)) n` >>
     simp[bind_def,get_accounts_def,lift_sum_def,return_def,raise_def]) >>
  qpat_assum `!tail res ee obs_pre rq outcome sfx H. _` irule >> simp[] >>
  qexistsl_tac [`mid`,`ans`,`sfx`,`tail`] >> gs[Abbr `st`]
QED

Finalise slice_builtin_self_vv_prefix_from_tail
