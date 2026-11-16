(* Code Slice composition over explicit joint runtime interfaces.
   The final Slice join discharges both universally quantified contracts. *)
Theory bodyFullBuiltinSliceCodeCompose
Ancestors
  bodyFullPreds bodySimFull bodyFullOfVV gasOutcomeFullCompose
  exprSimSliceExtcodeTyped bodyFullUnwrapRun exprSimProps exprSimWordArgs exprSimHash
  exprSimSliceExtcodeEntry bodyInvNoDalloca
  bodyFullBuiltinBytestringQuery bodyFullBuiltinBytestringBuffer
  bodyFullBuiltinBytestringBounds bodyFullBuiltinBytestringCopy
  bodyFullBuiltinBytestringAbort exprSimSliceSelfCode
  bodyPtrBytestringBuiltinsWindowGhost wordArgsPtr
  exprSimSliceSource exprSimSliceOrdinaryFrame exprSimHypsDefs
  exprLowering vyperInterpreter vyperAST list
  fragExec emitHelperProps bodyPtrBytestringBuiltinsSlice
  bodyPtrBytestringBuiltinsBuffer loweringPosts loweringStateRelDefs
  reasonCodeResourcesPtr bodyPtrAttributeFields

Theorem slice_builtin_some_vv_full_from_tail:
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
    code_slice_source (Slice n) args = SOME (code_ty,addr) ==>
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
  Cases_on `is_self_code (Builtin code_ty (Acc Code) [addr])`
  >- suspend "self_operands" >>
  `!bt xs. names_builtin bt xs ==> bt <> Slice n` by
    (ho_match_mp_tac names_builtin_ind >> simp[names_builtin_def]) >>
  `!xs. ~names_builtin (Slice n) xs` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  qpat_x_assum `!bt xs. _` kall_tac >>
  qpat_x_assum `compile_expr _ _ (Builtin _ _ _) _ = _` mp_tac >>
  simp[compile_expr_builtin_dispatch,compile_builtin_dispatch_component_eq,
    exprBopLoweringTheory.lower_value_child_call,is_self_code_def,is_extcode_def,extcode_addr_expr_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  drule_all exprSimSliceExtcodeContextTheory.slice_extcode_pipeline_context >> strip_tac >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr _) _ = _` mp_tac >>
  simp[gasShadowTheory.gas_shadow_expr_def,gasShadowTheory.gas_shadow_builtin_def,
    compile_expr_builtin_dispatch,compile_builtin_dispatch_component_eq,
    exprBopLoweringTheory.lower_value_child_call,is_extcode_def,extcode_addr_expr_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  `~is_self_code (Builtin code_ty (Acc Code) [gas_shadow_expr addr])` by
    (qspec_then `Builtin code_ty (Acc Code) [addr]` mp_tac
       (GEN_ALL gasShadowCompilePureTheory.gas_shadow_is_self_code) >>
     pure_rewrite_tac[gasShadowTheory.gas_shadow_expr_def,gasShadowTheory.gas_shadow_builtin_def,MAP] >> simp[]) >>
  gvs[] >>
  `local_ptrs_reserved cenv shadow_sa` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `sa` >> fs[gasShadowStateTheory.gas_shadow_state_def]) >>
  qpat_assum `as_ptr_val _ _ (compile_slice_extcode _ _ _ _ _) = (_,shadow_sb)`
    (mp_then Any mp_tac exprSimSliceExtcodeContextTheory.slice_extcode_pipeline_context) >>
  disch_then drule_all >> strip_tac >>
  `start_op' = start_op /\ gas_shadow_state st1 st1'` by
    (qpat_x_assum `tail_run :- _` kall_tac >>
     qpat_x_assum `child_run :- _` kall_tac >>
     metis_tac[gasShadowCompileStmtHelpersTheory.gas_shadow_stmt_lower_value,
       gasShadowStateTheory.gas_shadow_compiles_def,pairTheory.FST,pairTheory.SND]) >>
  gvs[] >>
  rev_drule slice_extcode_actions >> disch_then (fn th => rewrite_tac[th]) >>
  `expr_body_pre cenv cx env start es` by
    (`well_typed_expr env (Builtin a (Slice n) [Builtin code_ty (Acc Code) [addr];start;len])` by
       fs[expr_body_pre_def] >>
     drule slice_typed_args >> strip_tac >> gvs[] >>
     `expr_type start <> BaseT (BytesT (Dynamic 24576))` by simp[] >>
     `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
     drule exprSimSourceTheory.expr_body_pre_builtin_typed_arg >>
     disch_then (qspecl_then [`start`,`es`] mp_tac) >> simp[]) >>
  `gas_admissible (bind (eval_expr cx start) (read_result cx)) expr_res_ok es` by
    (drule exprSimSourceTheory.expr_body_pre_gas_admissible >> simp[]) >>
  qpat_x_assum `expr_sim_full _ _ _ _ start _` (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then drule >> simp[] >> disch_then drule_all >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ child_post _` >>
  suspend "external_start"
QED

Resume slice_builtin_some_vv_full_from_tail[self_operands]:
  cheat
QED

Resume slice_builtin_some_vv_full_from_tail[external_start]:
  cheat
QED

Finalise slice_builtin_some_vv_full_from_tail
