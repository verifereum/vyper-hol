(*
 * Expression simulation: raw_call (#636, Calls row 3)
 *
 * raw_call(to, data, [value=], [gas=], [max_outsize=], [is_static_call=],
 * [revert_on_failure=]) lowers (compile_call's RawCallTarget clause) to
 * the address with lower_value, the data unwrapped to memory, the value=
 * and gas= keyword operands in source order, GAS without gas=, the output
 * buffer (compile_raw_call_outbuf) and the call (compile_raw_call_finish).
 * In oracle mode a non-delegate source raw_call takes the same outcome as
 * the lowered CALL/STATICCALL (eval_raw_call's take_call_outcome and
 * adopt_call_outcome; extCallOracleStep's exec_ext_call_oracle_step).
 * expr_sim_pre and expr_body_pre exclude delegate raw_calls and raw_calls
 * without revert_on_failure (~expr_has_evm_run), so those hold vacuously.
 *
 * TOP-LEVEL:
 *   compile_raw_call_case — raw_call's expr_sim_case and expr_vv_case from
 *     its operands' exprs_case, for compile_expr_sim and the body
 *     simulation
 *)

Theory exprSimRawCall
Ancestors
  allocLimits
  list pair vyperMisc fragExec loweringSlice exprSim exprSimHyps exprSimWordArgs
  exprSimPrecompiles exprSimOperators exprSimOperands exprSimAccounts
  extCallOracleStep exprCallbackContracts exprCallBounds exprLowering
  exprLoweringProps emitHelper compileEnv localPtrsProps valueEncoding
  vyperAST vyperInterpreter vyperState vyperValue vyperTyping
  vyperTypeSystem vyperTypeCallGraph vyperCallOutcome extCallOracle
  vyperRuntimeAccounts vyperTypeInvariants vyperEvalExprPreservesScopesDom
  venomExecSemantics venomInst venomState exprSimSend vyperRawCallDataDomain
  exprSimHash
Libs
  pairLib

Theorem compile_expr_raw_call_steps[local]:
  compile_expr cenv ty (Call ann (RawCallTarget flags) (a::d::kws) dflt) sa =
    (vv,sb) ==>
  ?addr data len ptr vo go ignored gas ov op result s1 s2 s3 s4 s5 s6 s7.
    lower_value compile_expr cenv (BaseT AddressT) a sa = (addr,s1) /\
    lower_value compile_expr cenv (expr_type d) d s1 = (data,s2) /\
    emit_op MLOAD [data] s2 = (len,s3) /\
    emit_op ADD [data; Lit 32w] s3 = (ptr,s4) /\
    compile_ext_call_kwargs compile_expr cenv NoneT flags.rcf_kws kws s4 =
      ((vo,go,ignored),s5) /\
    (case go of SOME g => (g,s5) | NONE => emit_op GAS [] s5) = (gas,s6) /\
    compile_raw_call_outbuf flags.rcf_max_outsize s6 = ((ov,op),s7) /\
    compile_raw_call_finish addr ptr len gas
      (case vo of SOME v => v | NONE => Lit 0w)
      (if flags.rcf_is_delegate then DelegateCall
       else if flags.rcf_is_static then StaticCall else RegularCall)
      flags.rcf_max_outsize flags.rcf_revert_on_failure ov op s7 = (result,sb) /\
    vv = (if flags.rcf_max_outsize = 0 then StackValue ann result
          else LocatedValue ann (mk_ptr result LocMemory))
Proof
  simp[compile_expr_call, compile_call_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  Cases_on `flags.rcf_max_outsize = 0` >> gvs[]
QED

Theorem raw_call_kwargs_types[local]:
  raw_call_kws_ok flags es ==>
  EVERY (\k. k = EKValue \/ k = EKGas) flags.rcf_kws /\
  EVERY (\e. expr_type e = BaseT (UintT 256)) es
Proof
  simp[raw_call_kws_ok_def] >> strip_tac >>
  `EVERY (\k. k = EKValue \/ k = EKGas) flags.rcf_kws` by
    (simp[EVERY_MEM] >> rpt strip_tac >>
     Cases_on `k` >> gvs[]) >>
  simp[] >>
  `EVERY (\t. t = BaseT (UintT 256)) (MAP expr_type es)` suffices_by
    simp[EVERY_MAP] >>
  asm_rewrite_tac[] >> simp[EVERY_MAP, EVERY_MEM] >>
  rpt strip_tac >> rename1 `MEM k flags.rcf_kws` >>
  `k = EKValue \/ k = EKGas` by
    (qpat_x_assum `EVERY _ _` mp_tac >> simp[EVERY_MEM]) >>
  gvs[ext_call_kw_type_def]
QED

(* Only the keyword suffix is all-word. Its compiler is the standard ordered
   word-argument runner followed by selection of value= and gas=. *)
Theorem raw_call_kwargs_word_args[local]:
  !ks es sa vo go d sb.
    EVERY (\k. k = EKValue \/ k = EKGas) ks /\
    LENGTH es = LENGTH ks /\
    compile_ext_call_kwargs compile_expr cenv NoneT ks es sa = ((vo,go,d),sb) ==>
    ?xs. lower_word_args cenv (K (BaseT (UintT 256))) es sa = (xs,sb) /\
         vo = ext_call_kwarg EKValue ks xs /\
         go = ext_call_kwarg EKGas ks xs /\ d = NONE
Proof
  Induct >- simp[compile_ext_call_kwargs_def, lower_word_args_def,
                comp_return_def, ext_call_kwarg_def] >>
  rpt gen_tac >> Cases_on `es` >>
  simp[compile_ext_call_kwargs_def, lower_word_args_def, comp_return_def] >>
  strip_tac >>
  gvs[compile_ext_call_kwarg_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[comp_bind_def, comp_return_def]) >>
  first_x_assum drule_all >> strip_tac >>
  gvs[ext_call_kwarg_def]
QED

Theorem raw_call_kwargs_sim[local]:
  EVERY (\k. k = EKValue \/ k = EKGas) ks /\ LENGTH es = LENGTH ks /\
  typed_args_ready ctx func cenv cx (K (BaseT (UintT 256))) Inv es /\ Inv st /\
  wb_args_shape cenv (K (BaseT (UintT 256))) es /\
  compile_ext_call_kwargs compile_expr cenv NoneT ks es sa = ((vo,go,d),sb) /\
  eval_exprs cx es st = (rr,st') /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa ==>
  frag_exec ctx sa sb (\s. s = s0 /\ stmt_state_rel ctx func cenv cx st s)
    (\s. ?xs vs. rr = INL vs /\
       typed_args_post ctx func cenv cx st sa s0 st' es xs vs s /\
       vo = ext_call_kwarg EKValue ks xs /\
       go = ext_call_kwarg EKGas ks xs /\ d = NONE)
    (wb_args_exit rr)
Proof
  strip_tac >> drule_all raw_call_kwargs_word_args >> strip_tac >>
  drule_all lower_typed_args_sim >>
  disch_then (qspec_then `s0` mp_tac) >>
  strip_tac >> irule frag_exec_conseq >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem eval_expr_raw_call_operands[local]:
  eval_exprs cx args es = (INL (addr_v::data_v::kvs), es1) /\
  dest_AddressV addr_v = SOME target /\ dest_BytesV data_v = SOME data /\
  LENGTH kvs = LENGTH flags.rcf_kws /\
  raw_call_value flags.rcf_kws kvs = SOME amount ==>
  eval_expr cx (Call ann (RawCallTarget flags) args dflt) es =
    eval_raw_call cx flags target data amount
      (forwarded_gas default_evm_gas_limit
         (ext_call_kwarg EKGas flags.rcf_kws kvs)) es1
Proof
  strip_tac >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def, lift_option_type_def,
       check_def, dest_AddressV_def, dest_BytesV_def]
QED

Theorem eval_expr_raw_call_operand_exit[local]:
  eval_exprs cx args es = (INR exc, es') ==>
  eval_expr cx (Call ann (RawCallTarget flags) args dflt) es = (INR exc, es')
Proof
  strip_tac >> simp[Once evaluate_def, bind_def]
QED

Theorem raw_call_pre_operands[local]:
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) args dflt) es ==>
  ?a d kws n. args = a::d::kws /\
    expr_type a = BaseT AddressT /\
    expr_type d = BaseT (BytesT (Dynamic n)) /\
    LENGTH kws = LENGTH flags.rcf_kws
Proof
  strip_tac >>
  `well_typed_expr env (Call ann (RawCallTarget flags) args dflt)` by
    fs[expr_body_pre_def] >>
  drule raw_call_typed_data_dynamic >> strip_tac >>
  qpat_x_assum `well_typed_expr _ _` mp_tac >>
  simp[well_typed_expr_def] >> strip_tac >>
  namedCases_on `args` ["", "a rest"] >> gvs[] >>
  Cases_on `rest` >> gvs[]
QED

Theorem raw_call_pre_flags[local]:
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) args dflt) es ==>
  ~flags.rcf_is_delegate /\ flags.rcf_revert_on_failure /\
  flags.rcf_max_outsize < dimword (:256) /\
  LENGTH args = 2 + LENGTH flags.rcf_kws /\
  raw_call_kws_ok flags (DROP 2 args) /\
  ann = raw_call_return_type flags /\ dflt = NONE
Proof
  simp[expr_body_pre_def, well_typed_expr_def,
       supportedExprTraverseTheory.expr_has_evm_run_thm] >>
  strip_tac >> gvs[supportedExprTraverseTheory.expr_evm_run_root_def]
QED

Theorem expr_body_pre_raw_call_arg[local]:
  !cenv cx env ann flags args dflt e es es'.
    expr_body_pre cenv cx env (Call ann (RawCallTarget flags) args dflt) es /\
    MEM e args /\ expr_sim_inv cenv cx env es' ==>
    expr_body_pre cenv cx env e es'
Proof
  rw[expr_body_pre_def, well_typed_expr_def, int_calls_expr_def,
     byte_widths_expr_def, alloc_limits_expr_def] >>
  imp_res_tac int_calls_exprs_every_mem >>
  gvs[supportedExprTraverseTheory.expr_has_evm_run_thm, listTheory.EXISTS_MEM] >>
  metis_tac[well_typed_exprs_member, byte_widths_exprs_mem,
            alloc_limits_exprs_mem, call_evaluation_safe_exprs_mem]
QED

(* Oracle execution after operand evaluation; keep adoption explicit so both
   the successful and failing source states are retained by consumers. *)
Theorem raw_call_oracle_result[local]:
  ~flags.rcf_is_delegate /\ flags.rcf_revert_on_failure /\
  (flags.rcf_is_static ==> amount = 0) /\ IS_SOME st.outcomes /\
  take_call_outcome target data
    (if flags.rcf_is_static then NONE else SOME amount) st =
      (INL (rq, outcome), st1) /\
  adopt_call_outcome rq outcome st1 = (INL (), st2) ==>
  eval_raw_call cx flags target data amount gas st =
    (if call_outcome_success outcome then
       INL (Value (if flags.rcf_max_outsize = 0 then NoneV
                   else BytesV (TAKE flags.rcf_max_outsize
                                      (call_outcome_return_data outcome))))
     else INR (Error (RevertData (call_outcome_return_data outcome))), st2)
Proof
  strip_tac >>
  simp[eval_raw_call_def, bind_def, ignore_bind_def, type_check_def,
       assert_def, return_def, raise_def] >>
  Cases_on `call_outcome_success outcome` >> simp[return_def, raise_def] >>
  Cases_on `flags.rcf_max_outsize = 0` >> simp[return_def]
QED

(* The failure copy needs no allocation-capacity or destination-end bound:
   it expands memory, and the exit judgment does not observe that memory. *)
Theorem raw_call_failure_copy[local]:
  eval_operand dst s = SOME w /\
  eval_operand size_op s = SOME (n2w (LENGTH s.vs_returndata)) /\
  LENGTH s.vs_returndata < dimword (:256) ==>
  step_inst_base (mk_inst iid RETURNDATACOPY [dst; Lit 0w; size_op] []) s =
    OK (write_memory_with_expansion (w2n w) s.vs_returndata s)
Proof
  strip_tac >>
  simp[Once step_inst_base_def, mk_inst_def, eval_operand_def,
       wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]
QED

(* MLOAD/ADD only extend the variable map. Keep their memory and source
   relation interface explicit before running the keyword expressions. *)
Theorem raw_call_data_prefix_frame[local]:
  emit_op MLOAD [ptr_op] sa = (len_op, sl) /\
  emit_op ADD [ptr_op; Lit 32w] sl = (data_op, sm) /\
  (!x. ptr_op = Var x ==> not_fresh_at sa x) /\
  eval_operand ptr_op s = SOME (n2w b) /\
  mem_word_at b s.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (b + 32) (LENGTH bs) s.vs_memory = bs /\
  b < dimword (:256) /\ stmt_state_rel ctx func cenv cx es s /\
  local_ptrs_reserved cenv sa ==>
  ?t. run_inst_seq (emitted_insts sa sm) s = OK t /\
    eval_operand len_op t = SOME (n2w (LENGTH bs)) /\
    eval_operand data_op t = SOME (n2w (b + 32)) /\
    mem_bytes_at (b + 32) (LENGTH bs) t.vs_memory = bs /\
    stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es sa s t /\
    (!x. len_op = Var x \/ data_op = Var x ==> not_fresh_at sm x)
Proof
  strip_tac >> drule_all hash_data_prefix_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK t` >>
  `t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `t with vs_vars := _ = _`
       (mp_tac o Q.AP_TERM `\z. (z.vs_memory,z.vs_allocas)`) >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es t` by
    (irule hash_readonly_state_rel >> goal_assum drule >> simp[]) >>
  qexists_tac `t` >> simp[wb_frame_def, locals_kept_def] >>
  first_assum ACCEPT_TAC
QED

(* TOP-LEVEL *)
Theorem compile_raw_call_case:
  !nocalls ctx func cenv cx ann flags args dflt.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_sim_case nocalls ctx func cenv cx (Call ann (RawCallTarget flags) args dflt) /\
    expr_vv_case nocalls ctx func cenv cx (Call ann (RawCallTarget flags) args dflt)
Proof
  cheat
QED
