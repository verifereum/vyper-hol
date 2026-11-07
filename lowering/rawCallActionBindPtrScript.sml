(* Bind the evaluated operands to the source raw-call continuation.
   Keep gas observations in the action: implicit machine GAS is not a source keyword. *)
Theory rawCallActionBindPtr
Ancestors
  rawCallPrefixReadyPtr gasSummaryComposePtr gasExemptCert stmtSimForRounds
  vyperInterpreter vyperState vyperValue exprReasonOperand

Theorem raw_call_eval_action:
  eval_expr cx (Call ann (RawCallTarget flags) args dflt) =
  bind (eval_exprs cx args) (\vs.
    do
      type_check (LENGTH vs = 2 + LENGTH flags.rcf_kws) "raw_call args";
      target <- lift_option_type (dest_AddressV (EL 0 vs)) "raw_call target";
      data <- lift_option_type (dest_BytesV (EL 1 vs)) "raw_call data";
      amount <- lift_option_type (raw_call_value flags.rcf_kws (DROP 2 vs)) "raw_call value";
      eval_raw_call cx flags target data amount
        (forwarded_gas default_evm_gas_limit
          (ext_call_kwarg EKGas flags.rcf_kws (DROP 2 vs)))
    od)
Proof
  simp[Once evaluate_def]
QED

Theorem raw_call_source_continuation:
  dest_AddressV av = SOME target /\ LENGTH kvs = LENGTH flags.rcf_kws /\
  raw_call_value flags.rcf_kws kvs = SOME amount ==>
  (do
      type_check (LENGTH (av::BytesV bs::kvs) = 2 + LENGTH flags.rcf_kws) "raw_call args";
      target' <- lift_option_type (dest_AddressV (EL 0 (av::BytesV bs::kvs))) "raw_call target";
      data <- lift_option_type (dest_BytesV (EL 1 (av::BytesV bs::kvs))) "raw_call data";
      value <- lift_option_type (raw_call_value flags.rcf_kws (DROP 2 (av::BytesV bs::kvs))) "raw_call value";
      eval_raw_call cx flags target' data value
        (forwarded_gas default_evm_gas_limit
          (ext_call_kwarg EKGas flags.rcf_kws (DROP 2 (av::BytesV bs::kvs))))
   od) = eval_raw_call cx flags target bs amount
     (forwarded_gas default_evm_gas_limit (ext_call_kwarg EKGas flags.rcf_kws kvs))
Proof
  strip_tac >> simp[type_check_def, assert_def, ignore_bind_def,
    lift_option_type_def, check_def, dest_BytesV_def] >>
  simp[FUN_EQ_THM, vyperStateTheory.bind_def, vyperStateTheory.assert_def,
    vyperStateTheory.return_def]
QED

Theorem raw_call_marked_continuation_admissible:
  gas_admissible (eval_expr cx (Call ann (RawCallTarget flags) args dflt)) expr_vv_res_ok es /\
  gas_marked_exec F (ctx,func) (eval_exprs cx args) (es,s) marks
    (INL (av::BytesV bs::kvs)) mid (OK t) /\
  dest_AddressV av = SOME target /\ LENGTH kvs = LENGTH flags.rcf_kws /\
  raw_call_value flags.rcf_kws kvs = SOME amount ==>
  gas_admissible (eval_raw_call cx flags target bs amount
    (forwarded_gas default_evm_gas_limit (ext_call_kwarg EKGas flags.rcf_kws kvs)))
    expr_vv_res_ok (mid with gas_obs := [])
Proof
  rewrite_tac[raw_call_eval_action, gasSummaryTheory.gas_marked_exec_def] >>
  strip_tac >> drule_all gas_admissible_bind_tail >>
  BETA_TAC >> drule_all raw_call_source_continuation >>
  disch_then (qspecl_then [`cx`, `bs`] SUBST1_TAC) >> simp[]
QED

Theorem raw_call_scalar_action_outcome:
  body_inv tops ctx cenv cx /\ body_exprs_ptr_ok cx (a::d::kws) /\
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) dflt) es /\
  gas_admissible (eval_expr cx (Call ann (RawCallTarget flags) (a::d::kws) dflt)) expr_vv_res_ok es /\
  lower_value compile_expr cenv (BaseT AddressT) a sa = (addr,s1) /\
  lower_value compile_expr cenv (expr_type d) d s1 = (data,s2) /\
  emit_op MLOAD [data] s2 = (len_op,sl) /\
  emit_op ADD [data; Lit 32w] sl = (data_op,sm) /\
  compile_ext_call_kwargs compile_expr cenv NoneT flags.rcf_kws kws sm = ((vo,go,ig),s5) /\
  (case go of SOME g => (g,s5) | NONE => emit_op GAS [] s5) = (gas_op,s6) /\
  compile_raw_call_outbuf 0 s6 = ((ov,op),s7) /\
  compile_raw_call_finish addr data_op len_op gas_op
    (case vo of SOME v => v | NONE => Lit 0w)
    (if flags.rcf_is_static then StaticCall else RegularCall) 0 F ov op s7 = (result,sb) /\
  fn_has_code sa s6 func /\ fn_has_code s6 s7 func /\ fn_has_code s7 sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  stmt_state_rel ctx func cenv cx es s0 /\ ghost_inv dep cenv cx es G0 tn0 s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  flags.rcf_max_outsize = 0 /\ ~flags.rcf_revert_on_failure ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_expr cx (Call ann (RawCallTarget flags) (a::d::kws) dflt)) (es,s0,G0,tn0)
    (\res ee H un t. ?v em tm J jn u K kn.
      MAP FDOM es.scopes = MAP FDOM em.scopes /\
      res = INL (Value v) /\ ptr_val_ok cx (BaseT BoolT) v result H un t /\
      expr_val_rel cx (BaseT BoolT) v result t /\
      expr_val_at cenv cx (BaseT BoolT) sa sb ee v result t /\
      stmt_state_rel ctx func cenv cx ee t /\ ghost_inv dep cenv cx ee H un t /\
      ghost_kept cenv es sa G0 tn0 s0 J jn /\ wb_frame cenv es sa s0 tm /\
      ghost_kept cenv em s6 J jn tm K kn /\ wb_frame cenv em s6 tm u /\
      ghost_kept cenv em s6 K kn u H un /\ wb_frame cenv em s6 u t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted)
    (\res ee gt r. expr_exit res r)
Proof
  strip_tac >> drule rawCallShapePtrTheory.raw_call_pre_flags >>
  simp[] >> strip_tac >>
  `gas_admissible (eval_exprs cx (a::d::kws))
    (\rr. case rr of INL vs => T | INR exc => expr_res_ok (INR exc)) es` by
    (drule rawCallPrefixPtrTheory.raw_call_operands_admissible >> simp[]) >>
  drule_all rawCallPrefixPtrTheory.raw_call_prefix_sim_ptr >>
  disch_then (qspec_then `PG` assume_tac) >>
  rewrite_tac[raw_call_eval_action] >>
  irule gas_outcome_ptr_bind >> rpt conj_tac
  >- suspend "certificate_head"
  >- suspend "certificate_tail" >>
  irule operandOutcomePtrTheory.gas_outcome_ptr_marked_conseq >>
  goal_assum (drule_at Any) >> conj_tac
  >- suspend "normal" >>
  rpt strip_tac >> Cases_on `res` >>
  gvs[exprSimWordArgsTheory.wb_args_exit_def,
    oneline exprSimDefsTheory.expr_exit_def, AllCaseEqs()]
QED

Resume raw_call_scalar_action_outcome[certificate_head]:
  rpt strip_tac >> gvs[ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_bind_values >> goal_assum (drule_at Any) >> simp[]
QED

Resume raw_call_scalar_action_outcome[certificate_tail]:
  rpt strip_tac >> gvs[ignore_bind_def, bind_assoc] >>
  irule gas_exempt_cert_error_values >> simp[ignore_bind_def]
QED

Resume raw_call_scalar_action_outcome[normal]:
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _` kall_tac >>
  drule_all raw_call_prefix_address >> strip_tac >>
  `eval_exprs cx (a::d::kws)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
      (INL (av::BytesV bs::kvs),mid with gas_obs := [])` by
    (fs[gasSummaryTheory.gas_marked_exec_def] >>
     qpat_x_assum `!tail. eval_exprs _ _ _ = _`
       (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_body_pre cenv cx env
      (Call (raw_call_return_type flags) (RawCallTarget flags) (a::d::kws) NONE)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  drule_at (Pat `eval_exprs _ _ _ = _`) raw_call_prefix_amount >>
  disch_then drule_all >> strip_tac >>
  drule_all raw_call_marked_continuation_admissible >> disch_tac >>
  drule_all raw_call_source_continuation >>
  disch_then (qspecl_then [`cx`, `bs`]
    (fn th => rewrite_tac[SIMP_RULE
      (srw_ss() ++ listSimps.LIST_ss ++ numSimps.ARITH_ss) [] th])) >>
  suspend "ready"
QED

Resume raw_call_scalar_action_outcome[ready]:
  drule rawCallShapePtrTheory.raw_call_pre_operands >> simp[] >> strip_tac >>
  drule_all raw_call_prefix_data_type >> disch_tac >>
  `expr_val_at cenv cx (BaseT (BytesT (Dynamic n))) s1 s6
      (mid with gas_obs := []) (BytesV bs) (Var x) t` by metis_tac[] >>
  `stmt_state_rel ctx func cenv cx (mid with gas_obs := []) t` by simp[] >>
  drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`) raw_call_prefix_data_word_bounds >>
  disch_then drule_all >> strip_tac >>
  `ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 sl /\ ci_mono sl sm` by
    metis_tac[exprLoweringPropsTheory.ci_mono_lower_value_cfn,
      exprLoweringPropsTheory.compile_expr_ci_mono, pairTheory.SND,
      exprLoweringPropsTheory.ci_mono_emit_op] >>
  drule rawCallShapePtrTheory.raw_call_kwargs_types >> strip_tac >>
  `LENGTH kws = LENGTH flags.rcf_kws` by decide_tac >>
  drule_all rawCallShapePtrTheory.raw_call_kwargs_word_args >> strip_tac >>
  `!e ee. MEM e kws /\ expr_sim_inv cenv cx env ee ==>
      expr_body_pre cenv cx env e ee /\ is_word_type (expr_type e)` by
    (rpt strip_tac
     >- (irule rawCallShapePtrTheory.expr_body_pre_raw_call_arg >>
         first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
     fs[listTheory.EVERY_MEM, compileEnvTheory.is_word_type_def]) >>
  `wb_args_shape cenv (K (BaseT (UintT 256))) kws` by
    (irule exprSimPrecompilesTheory.typed_stack_args_shape >> metis_tac[]) >>
  drule_all exprSimWordArgsTheory.lower_word_args_shape_ready >> strip_tac >>
  `ci_mono s5 s6` by
    (Cases_on `ext_call_kwarg EKGas flags.rcf_kws xs` >> gvs[] >>
     metis_tac[exprLoweringPropsTheory.ci_mono_emit_op, pairTheory.SND,
       exprLoweringPropsTheory.ci_mono_refl]) >>
  `sa.cs_next_var <= s6.cs_next_var` by
    (fs[exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
  `local_ptrs_reserved cenv s6` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `(!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at s6 z) /\
   (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at s6 z)` by
    metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >>
  suspend "checks"
QED

Resume raw_call_scalar_action_outcome[checks]:
  `expr_sim_inv cenv cx env es` by fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
  `expr_body_pre cenv cx env a es` by
    (irule rawCallShapePtrTheory.expr_body_pre_raw_call_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >>
     simp[exprSimHypsDefsTheory.expr_body_pre_def]) >>
  `is_word_type (expr_type a)` by simp[compileEnvTheory.is_word_type_def] >>
  `!l. addr <> Label l` by
    (drule_all exprSimSourceTheory.expr_body_pre_lower_value_word_shape >>
     simp[compileEnvTheory.is_word_type_def]) >>
  `(!l. len_op <> Label l) /\ (!l. data_op <> Label l)` by
    (map_every (fn pat => qpat_x_assum pat mp_tac)
       [`emit_op ADD _ _ = _`, `emit_op MLOAD _ _ = _`] >>
     simp[emitHelperTheory.emit_op_def, compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_ignore_bind_def, compileEnvTheory.fresh_var_def,
       compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def,
       compileEnvTheory.comp_return_def] >> rpt strip_tac >> gvs[]) >>
  `EVERY (\op. (!z. op = Var z ==> not_fresh_at s6 z) /\
      (!l. op <> Label l) /\ op_taint tn op = {}) xs` by
    (fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  `(!z. (case ext_call_kwarg EKValue flags.rcf_kws xs of
      NONE => Lit 0w | SOME op => op) = Var z ==> not_fresh_at s6 z) /\
   (!l. (case ext_call_kwarg EKValue flags.rcf_kws xs of
      NONE => Lit 0w | SOME op => op) <> Label l) /\
   op_taint tn (case ext_call_kwarg EKValue flags.rcf_kws xs of
      NONE => Lit 0w | SOME op => op) = {}` by
    (irule raw_call_selected_operand_checks >> goal_assum (drule_at Any)) >>
  `EVERY (\op. (!z. op = Var z ==> not_fresh_at s5 z) /\ (!l. op <> Label l)) xs'` by simp[] >>
  drule raw_call_optional_gas_operand_checks >>
  disch_then (qspecl_then [`xs'`, `flags.rcf_kws`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >> suspend "finish"
QED

Resume raw_call_scalar_action_outcome[finish]:
  `?gw. eval_operand gas_op t = SOME gw` by metis_tac[] >>
  `EVERY (\arg. (!z. arg = Var z ==> not_fresh_at s6 z) /\
      (!l. arg <> Label l) /\ op_taint tn arg = {})
      (if flags.rcf_is_static then [gas_op;addr;data_op;len_op]
       else [gas_op;addr;
         (case ext_call_kwarg EKValue flags.rcf_kws xs of NONE => Lit 0w | SOME v => v);
         data_op;len_op])` by
    (Cases_on `flags.rcf_is_static` >> simp[] >> metis_tac[]) >>
  drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)
    rawCallAllocatedFinishPtrTheory.raw_call_allocated_scalar_outcome >>
  disch_then (drule_at (Pat `compile_raw_call_outbuf _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `gas_admissible _ _ _`)) >>
  disch_then (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `op_prov _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand (Var _) _ = _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
  disch_then (qspecl_then [`n2w amount`, `env`, `PG`] mp_tac) >>
  impl_tac
  >- (simp[wordsTheory.w2n_n2w] >> decide_tac) >>
  strip_tac >> irule gas_outcome_ptr_conseq >> goal_assum (drule_at Any) >>
  simp[] >> rpt strip_tac >>
  qexistsl_tac [`v`, `mid with gas_obs := []`, `t`, `G`, `tn`, `u`, `J`, `jn`] >> simp[] >>
  irule exprSimPropsTheory.expr_val_at_start_mono >>
  goal_assum (drule_at Any) >>
  fs[exprLoweringPropsTheory.ci_mono_def, compileEnvTheory.cs_extends_def]
QED

Finalise raw_call_scalar_action_outcome

(* Capacity-independent adapter: consumers need no source observation witnesses. *)
Theorem raw_call_prepared_prefix_sim_ptr:
  body_inv tops ctx cenv cx /\ body_exprs_ptr_ok cx (a::d::kws) /\
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) dflt) es /\
  gas_admissible (eval_expr cx (Call ann (RawCallTarget flags) (a::d::kws) dflt)) expr_vv_res_ok es /\
  gas_admissible (eval_exprs cx (a::d::kws))
    (\rr. case rr of INL vs => T | INR exc => expr_res_ok (INR exc)) es /\
  raw_call_kws_ok flags kws /\
  lower_value compile_expr cenv (BaseT AddressT) a sa = (addr,s1) /\
  lower_value compile_expr cenv (expr_type d) d s1 = (data,s2) /\
  emit_op MLOAD [data] s2 = (len_op,sl) /\
  emit_op ADD [data; Lit 32w] sl = (data_op,sm) /\
  compile_ext_call_kwargs compile_expr cenv NoneT flags.rcf_kws kws sm = ((vo,go,ig),s5) /\
  (case go of SOME g => (g,s5) | NONE => emit_op GAS [] s5) = (gas_op,s6) /\
  fn_has_code sa s6 func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  stmt_state_rel ctx func cenv cx es s0 /\
  ghost_inv dep cenv cx es G0 tn0 s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_exprs cx (a::d::kws)) (es,s0,G0,tn0)
    (\rr ee G tn t. ?av bs kvs xs ea ed ta tb th b x base sz t5 gasw aw amount lim.
      rr = INL (av::BytesV bs::kvs) /\ value_has_type (BaseTV AddressT) av /\
      expr_post ctx func cenv cx a es sa s1 s0 ea av addr ta /\
      expr_post ctx func cenv cx d ea s1 s2 ta ed (BytesV bs) data tb /\
      typed_args_post ctx func cenv cx ed sm th ee kws xs kvs t /\
      vo = ext_call_kwarg EKValue flags.rcf_kws xs /\
      go = ext_call_kwarg EKGas flags.rcf_kws xs /\ ig = NONE /\
      EVERY (\op. op_taint tn op = {}) xs /\
      EVERY (\op. !l. op <> Label l) xs /\
      EVERY (\op. !v. op = Var v ==> not_fresh_at s6 v) xs /\
      stmt_state_rel ctx func cenv cx ee t /\ expr_sim_inv cenv cx env ee /\
      wb_frame cenv es sa s0 t /\ ghost_inv dep cenv cx ee G tn t /\
      ghost_kept cenv es sa G0 tn0 s0 G tn /\
      MAP FDOM es.scopes = MAP FDOM ee.scopes /\
      sa.cs_next_id <= s6.cs_next_id /\
      t.vs_current_bb = s6.cs_current_bb /\
      t.vs_inst_idx = LENGTH s6.cs_current_insts /\ ~t.vs_halted /\
      expr_val_rel cx (BaseT AddressT) av addr t /\ op_taint tn addr = {} /\
      eval_operand len_op t = SOME (n2w (LENGTH bs)) /\
      eval_operand data_op t = SOME (n2w (b+32)) /\
      op_taint tn len_op = {} /\ op_taint tn data_op = {} /\
      data = Var x /\ eval_operand data t = SOME (n2w b) /\
      FLOOKUP G x = SOME (base,sz) /\ op_prov G data_op = SOME (base,sz) /\ base <= b /\
      b + 32 + LENGTH bs <= base + sz /\ b < dimword (:256) /\
      (!i. b+32 <= i /\ i < b+32+LENGTH bs ==> i NOTIN tn.t_mem) /\
      mem_bytes_at (b+32) (LENGTH bs) t.vs_memory = bs /\
      (!v. addr = Var v \/ data = Var v \/ len_op = Var v \/ data_op = Var v ==>
        not_fresh_at s6 v) /\
      (!g. go = SOME g ==> eval_operand g t5 = SOME gasw) /\
      eval_operand gas_op t = SOME (case go of SOME g => gasw
        | NONE => case t5.vs_gas_readings of [] => 0w | r::rs => r) /\
      op_taint tn gas_op = {} /\
      t.vs_gas_readings = (case go of SOME g => t5.vs_gas_readings
        | NONE => TL t5.vs_gas_readings) /\
      expr_val_at cenv cx (expr_type d) s1 s6 ee (BytesV bs) data t /\
      dest_AddressV av = SOME (w2w aw) /\ eval_operand addr t = SOME aw /\
      raw_call_value flags.rcf_kws kvs = SOME amount /\ LENGTH kvs = LENGTH flags.rcf_kws /\
      amount < dimword(:256) /\ (flags.rcf_is_static ==> amount = 0) /\
      eval_operand (case vo of NONE => Lit 0w | SOME v => v) t = SOME (n2w amount) /\
      gas_admissible (eval_raw_call cx flags (w2w aw) bs amount
        (forwarded_gas default_evm_gas_limit (ext_call_kwarg EKGas flags.rcf_kws kvs))) expr_vv_res_ok ee /\
      expr_type d = BaseT (BytesT (Dynamic lim)) /\
      evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic lim))) = SOME (BaseTV (BytesT (Dynamic lim))) /\
      b+32 < dimword(:256) /\ LENGTH bs < dimword(:256) /\
      local_ptrs_reserved cenv s6 /\
      (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at s6 z) /\
      (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at s6 z) /\
      EVERY (\arg. (!z. arg = Var z ==> not_fresh_at s6 z) /\
        (!l. arg <> Label l) /\ op_taint tn arg = {})
        (if flags.rcf_is_static then [gas_op;addr;data_op;len_op]
         else [gas_op;addr;(case vo of NONE => Lit 0w | SOME v => v);data_op;len_op]))
    (\rr ee gt r. wb_args_exit rr r)
Proof
  strip_tac >> drule_all rawCallPrefixPtrTheory.raw_call_prefix_sim_ptr >>
  disch_then (qspec_then `PG` assume_tac) >>
  irule operandOutcomePtrTheory.gas_outcome_ptr_marked_conseq >>
  goal_assum (drule_at Any) >> simp[] >> suspend "normal"
QED

Resume raw_call_prepared_prefix_sim_ptr[normal]:
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _` kall_tac >>
  drule_all raw_call_prefix_address >> strip_tac >>
  `eval_exprs cx (a::d::kws)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
      (INL (av::BytesV bs::kvs),mid with gas_obs := [])` by
    (fs[gasSummaryTheory.gas_marked_exec_def] >>
     qpat_x_assum `!tail. eval_exprs _ _ _ = _`
       (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_body_pre cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) dflt)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  drule_at (Pat `eval_exprs _ _ _ = _`) raw_call_prefix_amount >>
  disch_then drule_all >> strip_tac >>
  drule_all raw_call_marked_continuation_admissible >> disch_tac >>
  suspend "ready"
QED

Resume raw_call_prepared_prefix_sim_ptr[ready]:
  drule rawCallShapePtrTheory.raw_call_pre_operands >> simp[] >> strip_tac >>
  drule_all raw_call_prefix_data_type >> disch_tac >>
  `expr_val_at cenv cx (BaseT (BytesT (Dynamic n))) s1 s6
      (mid with gas_obs := []) (BytesV bs) (Var x) t` by metis_tac[] >>
  `stmt_state_rel ctx func cenv cx (mid with gas_obs := []) t` by simp[] >>
  drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`) raw_call_prefix_data_word_bounds >>
  disch_then drule_all >> strip_tac >>
  `ci_mono sa s1 /\ ci_mono s1 s2 /\ ci_mono s2 sl /\ ci_mono sl sm` by
    metis_tac[exprLoweringPropsTheory.ci_mono_lower_value_cfn,
      exprLoweringPropsTheory.compile_expr_ci_mono, pairTheory.SND,
      exprLoweringPropsTheory.ci_mono_emit_op] >>
  drule rawCallShapePtrTheory.raw_call_kwargs_types >> strip_tac >>
  `LENGTH kws = LENGTH flags.rcf_kws` by
    fs[vyperTypeSystemTheory.raw_call_kws_ok_def, listTheory.LENGTH_MAP] >>
  drule_all rawCallShapePtrTheory.raw_call_kwargs_word_args >> strip_tac >>
  `!e ee. MEM e kws /\ expr_sim_inv cenv cx env ee ==>
      expr_body_pre cenv cx env e ee /\ is_word_type (expr_type e)` by
    (rpt strip_tac
     >- (irule rawCallShapePtrTheory.expr_body_pre_raw_call_arg >>
         first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
     fs[listTheory.EVERY_MEM, compileEnvTheory.is_word_type_def]) >>
  `wb_args_shape cenv (K (BaseT (UintT 256))) kws` by
    (irule exprSimPrecompilesTheory.typed_stack_args_shape >> metis_tac[]) >>
  drule_all exprSimWordArgsTheory.lower_word_args_shape_ready >> strip_tac >>
  `ci_mono s5 s6` by
    (Cases_on `ext_call_kwarg EKGas flags.rcf_kws xs` >> gvs[] >>
     metis_tac[exprLoweringPropsTheory.ci_mono_emit_op, pairTheory.SND,
       exprLoweringPropsTheory.ci_mono_refl]) >>
  `sa.cs_next_var <= s6.cs_next_var` by
    (fs[exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
  `local_ptrs_reserved cenv s6` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `(!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at s6 z) /\
   (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at s6 z)` by
    metis_tac[stmtFragPtrTheory.not_fresh_at_mono] >> suspend "checks"
QED

Resume raw_call_prepared_prefix_sim_ptr[checks]:
  `expr_sim_inv cenv cx env es` by fs[exprSimHypsDefsTheory.expr_body_pre_def] >>
  `expr_body_pre cenv cx env a es` by
    (irule rawCallShapePtrTheory.expr_body_pre_raw_call_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >>
     simp[exprSimHypsDefsTheory.expr_body_pre_def]) >>
  `is_word_type (expr_type a)` by simp[compileEnvTheory.is_word_type_def] >>
  `!l. addr <> Label l` by
    (drule_all exprSimSourceTheory.expr_body_pre_lower_value_word_shape >>
     simp[compileEnvTheory.is_word_type_def]) >>
  `(!l. len_op <> Label l) /\ (!l. data_op <> Label l)` by
    (map_every (fn pat => qpat_x_assum pat mp_tac)
       [`emit_op ADD _ _ = _`, `emit_op MLOAD _ _ = _`] >>
     simp[emitHelperTheory.emit_op_def, compileEnvTheory.comp_bind_def,
       compileEnvTheory.comp_ignore_bind_def, compileEnvTheory.fresh_var_def,
       compileEnvTheory.fresh_id_def, compileEnvTheory.emit_def,
       compileEnvTheory.comp_return_def] >> rpt strip_tac >> gvs[]) >>
  `EVERY (\op. (!z. op = Var z ==> not_fresh_at s6 z) /\
      (!l. op <> Label l) /\ op_taint tn op = {}) xs` by
    (fs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  `(!z. (case ext_call_kwarg EKValue flags.rcf_kws xs of
      NONE => Lit 0w | SOME op => op) = Var z ==> not_fresh_at s6 z) /\
   (!l. (case ext_call_kwarg EKValue flags.rcf_kws xs of
      NONE => Lit 0w | SOME op => op) <> Label l) /\
   op_taint tn (case ext_call_kwarg EKValue flags.rcf_kws xs of
      NONE => Lit 0w | SOME op => op) = {}` by
    (irule raw_call_selected_operand_checks >> goal_assum (drule_at Any)) >>
  drule raw_call_optional_gas_operand_checks >>
  disch_then (qspecl_then [`xs'`, `flags.rcf_kws`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >> suspend "post"
QED

Resume raw_call_prepared_prefix_sim_ptr[post]:
  qexistsl_tac [`xs`, `ea`, `ed`, `ta`, `tb`, `th`, `b`, `t5`, `gasw`, `n`] >>
  `sa.cs_next_id <= s6.cs_next_id` by
    (fs[exprLoweringPropsTheory.ci_mono_def, compileEnvTheory.cs_extends_def] >> decide_tac) >>
  gvs[] >> Cases_on `flags.rcf_is_static` >> gvs[] >> metis_tac[]
QED

Finalise raw_call_prepared_prefix_sim_ptr

Theorem raw_call_zero_reverting_action_outcome:
  body_inv tops ctx cenv cx /\ body_exprs_ptr_ok cx (a::d::kws) /\
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) dflt) es /\
  gas_admissible (eval_expr cx (Call ann (RawCallTarget flags) (a::d::kws) dflt)) expr_vv_res_ok es /\
  lower_value compile_expr cenv (BaseT AddressT) a sa = (addr,s1) /\
  lower_value compile_expr cenv (expr_type d) d s1 = (data,s2) /\
  emit_op MLOAD [data] s2 = (len_op,sl) /\ emit_op ADD [data; Lit 32w] sl = (data_op,sm) /\
  compile_ext_call_kwargs compile_expr cenv NoneT flags.rcf_kws kws sm = ((vo,go,ig),s5) /\
  (case go of SOME g => (g,s5) | NONE => emit_op GAS [] s5) = (gas_op,s6) /\
  compile_raw_call_outbuf 0 s6 = ((ov,op),s7) /\
  compile_raw_call_finish addr data_op len_op gas_op (case vo of SOME v => v | NONE => Lit 0w)
    (if flags.rcf_is_static then StaticCall else RegularCall) 0 T ov op s7 = (result,sb) /\
  fn_has_code sa s6 func /\ fn_has_code s6 s7 func /\ fn_has_code s7 sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  stmt_state_rel ctx func cenv cx es s0 /\ ghost_inv dep cenv cx es G0 tn0 s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  flags.rcf_max_outsize = 0 /\ flags.rcf_revert_on_failure ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_expr cx (Call ann (RawCallTarget flags) (a::d::kws) dflt)) (es,s0,G0,tn0)
    (\res ee H un t. ?v em tm J jn u K kn.
      MAP FDOM es.scopes = MAP FDOM em.scopes /\
      res = INL (Value v) /\ ptr_val_ok cx NoneT v result H un t /\
      expr_val_rel cx NoneT v result t /\
      expr_val_at cenv cx NoneT sa sb ee v result t /\
      ptr_buf_ok cenv (Call ann (RawCallTarget flags) (a::d::kws) dflt) result H t /\
      stmt_state_rel ctx func cenv cx ee t /\ ghost_inv dep cenv cx ee H un t /\
      ghost_kept cenv es sa G0 tn0 s0 J jn /\ wb_frame cenv es sa s0 tm /\
      ghost_kept cenv em s6 J jn tm K kn /\ wb_frame cenv em s6 tm u /\
      ghost_kept cenv em s6 K kn u H un /\ wb_frame cenv em s6 u t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted)
    (\res ee gt r. expr_exit res r)
Proof
  strip_tac >> drule rawCallShapePtrTheory.raw_call_pre_flags >> simp[] >> strip_tac >>
  `gas_admissible (eval_exprs cx (a::d::kws))
    (\rr. case rr of INL vs => T | INR exc => expr_res_ok (INR exc)) es` by
    (drule rawCallPrefixPtrTheory.raw_call_operands_admissible >> simp[]) >>
  drule_all raw_call_prepared_prefix_sim_ptr >> disch_then (qspec_then `PG` assume_tac) >>
  rewrite_tac[raw_call_eval_action] >> irule gas_outcome_ptr_bind >> rpt conj_tac
  >- (rpt strip_tac >> gvs[ignore_bind_def, bind_assoc] >>
      irule gas_exempt_cert_bind_values >> goal_assum (drule_at Any) >> simp[])
  >- (rpt strip_tac >> gvs[ignore_bind_def, bind_assoc] >>
      irule gas_exempt_cert_error_values >> simp[ignore_bind_def]) >>
  irule gas_outcome_ptr_conseq >> goal_assum (drule_at Any) >> conj_tac
  >- suspend "normal" >>
  rpt strip_tac >> Cases_on `res` >>
  gvs[exprSimWordArgsTheory.wb_args_exit_def,
    oneline exprSimDefsTheory.expr_exit_def, AllCaseEqs()]
QED

Resume raw_call_zero_reverting_action_outcome[normal]:
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _` kall_tac >>
  drule_all raw_call_source_continuation >>
  disch_then (qspecl_then [`cx`, `bs`] assume_tac) >> gvs[] >>
  `type_memory_bytes cenv (lowered_value_type cenv
      (Call (raw_call_return_type flags) (RawCallTarget flags) (a::d::kws) NONE)) = 0` by
    simp[vyperTypeSystemTheory.raw_call_return_type_def,
      exprLoweringTheory.lowered_value_type_def, vyperASTTheory.expr_type_def,
      compileEnvTheory.type_memory_bytes_def] >>
  `?gw. eval_operand gas_op t = SOME gw` by metis_tac[] >>
  drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)
    rawCallAllocatedFinishPtrTheory.raw_call_allocated_zero_reverting_outcome >>
  disch_then (drule_at (Pat `compile_raw_call_outbuf _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `gas_admissible _ _ _`)) >>
  disch_then (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `op_prov _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand (Var _) _ = _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `type_memory_bytes _ _ = _`)) >>
  disch_then (qspecl_then [`n2w amount`, `env`, `PG`] mp_tac) >>
  impl_tac >- (simp[wordsTheory.w2n_n2w] >> decide_tac) >>
  strip_tac >> irule gas_outcome_ptr_conseq >> goal_assum (drule_at Any) >>
  simp[] >> rpt strip_tac >>
  qexistsl_tac [`v`, `ee`, `t`, `G`, `tn`, `u`, `J`, `jn`] >> simp[] >>
  irule exprSimPropsTheory.expr_val_at_start_mono >>
  goal_assum (drule_at Any) >>
  fs[exprLoweringPropsTheory.ci_mono_def, compileEnvTheory.cs_extends_def]
QED

Finalise raw_call_zero_reverting_action_outcome

Theorem raw_call_bytes_action_outcome:
  body_inv tops ctx cenv cx /\ body_exprs_ptr_ok cx (a::d::kws) /\
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) dflt) es /\
  gas_admissible (eval_expr cx (Call ann (RawCallTarget flags) (a::d::kws) dflt)) expr_vv_res_ok es /\
  lower_value compile_expr cenv (BaseT AddressT) a sa = (addr,s1) /\
  lower_value compile_expr cenv (expr_type d) d s1 = (data,s2) /\
  emit_op MLOAD [data] s2 = (len_op,sl) /\ emit_op ADD [data; Lit 32w] sl = (data_op,sm) /\
  compile_ext_call_kwargs compile_expr cenv NoneT flags.rcf_kws kws sm = ((vo,go,ig),s5) /\
  (case go of SOME g => (g,s5) | NONE => emit_op GAS [] s5) = (gas_op,s6) /\
  compile_raw_call_outbuf flags.rcf_max_outsize s6 = ((ov,op),s7) /\
  compile_raw_call_finish addr data_op len_op gas_op (case vo of SOME v => v | NONE => Lit 0w)
    (if flags.rcf_is_static then StaticCall else RegularCall)
    flags.rcf_max_outsize T ov op s7 = (result,sb) /\
  fn_has_code sa s6 func /\ fn_has_code s6 s7 func /\ fn_has_code s7 sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  stmt_state_rel ctx func cenv cx es s0 /\ ghost_inv dep cenv cx es G0 tn0 s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  0 < flags.rcf_max_outsize /\ flags.rcf_revert_on_failure ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_expr cx (Call ann (RawCallTarget flags) (a::d::kws) dflt)) (es,s0,G0,tn0)
    (\res ee H un t. ?v em tm J jn u K kn.
      MAP FDOM es.scopes = MAP FDOM em.scopes /\
      res = INL (Value v) /\ ptr_val_ok cx (BaseT (BytesT (Dynamic flags.rcf_max_outsize))) v result H un t /\
      expr_val_rel cx (BaseT (BytesT (Dynamic flags.rcf_max_outsize))) v result t /\
      expr_val_at cenv cx (BaseT (BytesT (Dynamic flags.rcf_max_outsize))) sa sb ee v result t /\
      ptr_buf_ok cenv (Call ann (RawCallTarget flags) (a::d::kws) dflt) result H t /\
      stmt_state_rel ctx func cenv cx ee t /\ ghost_inv dep cenv cx ee H un t /\
      ghost_kept cenv es sa G0 tn0 s0 J jn /\ wb_frame cenv es sa s0 tm /\
      ghost_kept cenv em s6 J jn tm K kn /\ wb_frame cenv em s6 tm u /\
      ghost_kept cenv em s6 K kn u H un /\ wb_frame cenv em s6 u t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted)
    (\res ee gt r. expr_exit res r)
Proof
  strip_tac >> drule rawCallShapePtrTheory.raw_call_pre_flags >> simp[] >> strip_tac >>
  `gas_admissible (eval_exprs cx (a::d::kws))
    (\rr. case rr of INL vs => T | INR exc => expr_res_ok (INR exc)) es` by
    (drule rawCallPrefixPtrTheory.raw_call_operands_admissible >> simp[]) >>
  drule_all raw_call_prepared_prefix_sim_ptr >> disch_then (qspec_then `PG` assume_tac) >>
  rewrite_tac[raw_call_eval_action] >> irule gas_outcome_ptr_bind >> rpt conj_tac
  >- (rpt strip_tac >> gvs[ignore_bind_def, bind_assoc] >>
      irule gas_exempt_cert_bind_values >> goal_assum (drule_at Any) >> simp[])
  >- (rpt strip_tac >> gvs[ignore_bind_def, bind_assoc] >>
      irule gas_exempt_cert_error_values >> simp[ignore_bind_def]) >>
  irule gas_outcome_ptr_conseq >> goal_assum (drule_at Any) >> conj_tac
  >- suspend "normal" >>
  rpt strip_tac >> Cases_on `res` >>
  gvs[exprSimWordArgsTheory.wb_args_exit_def,
    oneline exprSimDefsTheory.expr_exit_def, AllCaseEqs()]
QED

Resume raw_call_bytes_action_outcome[normal]:
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _` kall_tac >>
  drule_all raw_call_source_continuation >>
  disch_then (qspecl_then [`cx`, `bs`] assume_tac) >> gvs[] >>
  drule_all raw_call_prefix_result_capacity >> strip_tac >>
  `?gw. eval_operand gas_op t = SOME gw` by metis_tac[] >>
  drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)
    rawCallAllocatedFinishPtrTheory.raw_call_allocated_positive_reverting_outcome >>
  disch_then (drule_at (Pat `compile_raw_call_outbuf _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `gas_admissible _ _ _`)) >>
  disch_then (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `op_prov _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand (Var _) _ = _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
  disch_then (qspecl_then [`n2w amount`, `env`,
    `Call (raw_call_return_type flags) (RawCallTarget flags) (a::d::kws) NONE`, `PG`] mp_tac) >>
  impl_tac >- (simp[wordsTheory.w2n_n2w] >> decide_tac) >>
  strip_tac >> irule gas_outcome_ptr_conseq >> goal_assum (drule_at Any) >>
  simp[] >> rpt strip_tac >>
  qexistsl_tac [`v`, `ee`, `t`, `G`, `tn`, `u`, `J`, `jn`] >> simp[] >>
  irule exprSimPropsTheory.expr_val_at_start_mono >>
  goal_assum (drule_at Any) >>
  fs[exprLoweringPropsTheory.ci_mono_def, compileEnvTheory.cs_extends_def]
QED

Finalise raw_call_bytes_action_outcome

Theorem raw_call_tuple_action_outcome:
  body_inv tops ctx cenv cx /\ body_exprs_ptr_ok cx (a::d::kws) /\
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) dflt) es /\
  gas_admissible (eval_expr cx (Call ann (RawCallTarget flags) (a::d::kws) dflt)) expr_vv_res_ok es /\
  lower_value compile_expr cenv (BaseT AddressT) a sa = (addr,s1) /\
  lower_value compile_expr cenv (expr_type d) d s1 = (data,s2) /\
  emit_op MLOAD [data] s2 = (len_op,sl) /\ emit_op ADD [data; Lit 32w] sl = (data_op,sm) /\
  compile_ext_call_kwargs compile_expr cenv NoneT flags.rcf_kws kws sm = ((vo,go,ig),s5) /\
  (case go of SOME g => (g,s5) | NONE => emit_op GAS [] s5) = (gas_op,s6) /\
  compile_raw_call_outbuf flags.rcf_max_outsize s6 = ((ov,op),s7) /\
  compile_raw_call_finish addr data_op len_op gas_op (case vo of SOME v => v | NONE => Lit 0w)
    (if flags.rcf_is_static then StaticCall else RegularCall)
    flags.rcf_max_outsize F ov op s7 = (result,sb) /\
  fn_has_code sa s6 func /\ fn_has_code s6 s7 func /\ fn_has_code s7 sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  stmt_state_rel ctx func cenv cx es s0 /\ ghost_inv dep cenv cx es G0 tn0 s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  0 < flags.rcf_max_outsize /\ ~flags.rcf_revert_on_failure ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (eval_expr cx (Call ann (RawCallTarget flags) (a::d::kws) dflt)) (es,s0,G0,tn0)
    (\res ee H un t. ?v em tm J jn u K kn.
      MAP FDOM es.scopes = MAP FDOM em.scopes /\
      res = INL (Value v) /\
      ptr_val_ok cx (TupleT [BaseT BoolT;BaseT (BytesT (Dynamic flags.rcf_max_outsize))]) v result H un t /\
      expr_val_rel cx (TupleT [BaseT BoolT;BaseT (BytesT (Dynamic flags.rcf_max_outsize))]) v result t /\
      expr_val_at cenv cx (TupleT [BaseT BoolT;BaseT (BytesT (Dynamic flags.rcf_max_outsize))]) sa sb ee v result t /\
      ptr_buf_ok cenv (Call ann (RawCallTarget flags) (a::d::kws) dflt) result H t /\
      stmt_state_rel ctx func cenv cx ee t /\ ghost_inv dep cenv cx ee H un t /\
      ghost_kept cenv es sa G0 tn0 s0 J jn /\ wb_frame cenv es sa s0 tm /\
      ghost_kept cenv em s6 J jn tm K kn /\ wb_frame cenv em s6 tm u /\
      ghost_kept cenv em s6 K kn u H un /\ wb_frame cenv em s6 u t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted)
    (\res ee gt r. expr_exit res r)
Proof
  strip_tac >> drule rawCallShapePtrTheory.raw_call_pre_flags >> simp[] >> strip_tac >>
  `gas_admissible (eval_exprs cx (a::d::kws))
    (\rr. case rr of INL vs => T | INR exc => expr_res_ok (INR exc)) es` by
    (drule rawCallPrefixPtrTheory.raw_call_operands_admissible >> simp[]) >>
  drule_all raw_call_prepared_prefix_sim_ptr >> disch_then (qspec_then `PG` assume_tac) >>
  rewrite_tac[raw_call_eval_action] >> irule gas_outcome_ptr_bind >> rpt conj_tac
  >- (rpt strip_tac >> gvs[ignore_bind_def, bind_assoc] >>
      irule gas_exempt_cert_bind_values >> goal_assum (drule_at Any) >> simp[])
  >- (rpt strip_tac >> gvs[ignore_bind_def, bind_assoc] >>
      irule gas_exempt_cert_error_values >> simp[ignore_bind_def]) >>
  irule gas_outcome_ptr_conseq >> goal_assum (drule_at Any) >> conj_tac
  >- suspend "normal" >>
  rpt strip_tac >> Cases_on `res` >>
  gvs[exprSimWordArgsTheory.wb_args_exit_def,
    oneline exprSimDefsTheory.expr_exit_def, AllCaseEqs()]
QED

Resume raw_call_tuple_action_outcome[normal]:
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _` kall_tac >>
  drule_all raw_call_source_continuation >>
  disch_then (qspecl_then [`cx`, `bs`] assume_tac) >> gvs[] >>
  drule_all raw_call_prefix_result_capacity >> strip_tac >>
  `?gw. eval_operand gas_op t = SOME gw` by metis_tac[] >>
  drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)
    (Q.INST [`be` |-> `Call (BaseT (BytesT (Dynamic flags.rcf_max_outsize)))
      (RawCallTarget flags) [] NONE`]
      rawCallAllocatedFinishPtrTheory.raw_call_allocated_positive_nonreverting_outcome) >>
  disch_then (drule_at (Pat `compile_raw_call_outbuf _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `gas_admissible _ _ _`)) >>
  disch_then (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `op_prov _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand (Var _) _ = _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
  disch_then (qspecl_then [`n2w amount`, `env`,
    `Call (raw_call_return_type flags) (RawCallTarget flags) (a::d::kws) NONE`, `PG`] mp_tac) >>
  impl_tac
  >- (simp[wordsTheory.w2n_n2w, rawCallResultLayoutPtrTheory.raw_call_bytes_type_capacity] >> decide_tac) >>
  strip_tac >> irule gas_outcome_ptr_conseq >> goal_assum (drule_at Any) >>
  simp[] >> rpt strip_tac >>
  qexistsl_tac [`v`, `ee`, `t`, `G`, `tn`, `u`, `J`, `jn`] >> simp[] >>
  irule exprSimPropsTheory.expr_val_at_start_mono >>
  goal_assum (drule_at Any) >>
  fs[exprLoweringPropsTheory.ci_mono_def, compileEnvTheory.cs_extends_def]
QED

Finalise raw_call_tuple_action_outcome
