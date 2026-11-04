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
  allocLimits freshWrites builtinSimple builtinProps
  list pair vyperMisc fragExec loweringSlice exprSim exprSimHyps exprSimWordArgs
  exprSimPrecompiles exprSimOperators exprSimOperands exprSimAccounts
  extCallOracleStep exprCallbackContracts exprCallBounds exprLowering
  exprLoweringProps emitHelper emitHelperProps compileEnv localPtrsProps valueEncoding
  vyperAST vyperInterpreter vyperState vyperValue vyperTyping
  vyperTypeSystem vyperTypeCallGraph vyperCallOutcome extCallOracle
  vyperRuntimeAccounts vyperTypeInvariants vyperEvalExprPreservesScopesDom
  venomExecSemantics venomInst venomState exprSimSend vyperRawCallDataDomain
  exprSimHash exprSimAlloc exprSimBuffer builtinSystem exprWordOperand exprSafeOperand exprOperandVar
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
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
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

Theorem raw_call_outbuf_capacity[local]:
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) args dflt) es /\
  0 < flags.rcf_max_outsize ==>
  ((flags.rcf_max_outsize + 31) DIV 32) * 32 + 32 < dimword (:256)
Proof
  strip_tac >> drule raw_call_pre_flags >> strip_tac >>
  `type_alloc_ok cenv ann` by
    fs[expr_body_pre_def, alloc_limits_expr_def] >>
  gvs[raw_call_return_type_def, type_alloc_ok_def, is_word_type_def,
      type_memory_bytes_def] >>
  `2 ** 64 < dimword (:256)` by simp[wordsTheory.dimword_def] >>
  fs[] >> decide_tac
QED

Theorem raw_call_outbuf_zero_run[local]:
  compile_raw_call_outbuf 0 sa = ((ov,op),sb) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ fn_has_code sa sb func ==>
  ?t w. run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel ctx func cenv cx es t /\ ov = op /\
    eval_operand ov t = SOME w /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,0) /\
    w2n w < dimword (:256) /\ t.vs_memory = s.vs_memory /\
    wb_frame cenv es sa s t /\
    (!x. ov = Var x ==> not_fresh_at sb x)
Proof
  simp[compile_raw_call_outbuf_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  drule_all buffer_alloc_code >> strip_tac >>
  `0 < dimword (:256)` by simp[] >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  qexistsl_tac [`t`, `w`] >> simp[wb_frame_def, locals_kept_def] >>
  metis_tac[]
QED

Theorem raw_call_outbuf_steps[local]:
  0 < cap /\ compile_raw_call_outbuf cap sa = ((ov,op),sb) ==>
  ?buf sm.
    compile_alloc_buffer (((cap + 31) DIV 32) * 32 + 32) sa = (buf,sm) /\
    ov = buf.buf_operand /\ emit_op ADD [ov; Lit 32w] sm = (op,sb)
Proof
  strip_tac >> qpat_x_assum `compile_raw_call_outbuf _ _ = _` mp_tac >>
  simp[compile_raw_call_outbuf_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[comp_bind_def, comp_return_def]) >>
  strip_tac >> gvs[] >> goal_assum (drule_at Any) >> simp[]
QED

Theorem raw_call_outbuf_add_frame[local]:
  emit_op ADD [ov; Lit 32w] sa = (op,sb) /\
  eval_operand ov s = SOME w /\
  (!x. ov = Var x ==> not_fresh_at sa x) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand ov t = SOME w /\ eval_operand op t = SOME (w + 32w) /\
    stmt_state_rel ctx func cenv cx es t /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    wb_frame cenv es sa s t /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!x. ov = Var x \/ op = Var x ==> not_fresh_at sb x)
Proof
  strip_tac >>
  `run_inst_seq (emitted_insts sa sb) s =
     OK (update_var (STRING #"%" (toString sa.cs_next_var)) (w + 32w) s)` by
    (irule buffer_emit_add_run >> simp[] >> metis_tac[]) >>
  drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
  qmatch_asmsub_abbrev_tac `run_inst_seq _ s = OK t` >>
  `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s` by
    (simp[Abbr `t`, emitHelperPropsTheory.lookup_var_update_var] >>
     rpt strip_tac >> gvs[not_fresh_at_def]) >>
  `(t with vs_vars := s.vs_vars) = s` by simp[Abbr `t`, update_var_def] >>
  `stmt_state_rel ctx func cenv cx es t` by
    (irule hash_readonly_state_rel >> goal_assum drule >> simp[]) >>
  qexists_tac `t` >>
  simp[Abbr `t`, update_var_def, wb_frame_def, locals_kept_def,
       eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  conj_tac
  >- (Cases_on `ov` >> gvs[eval_operand_def, lookup_var_def,
                          emitHelperPropsTheory.lookup_var_update_var, not_fresh_at_def] >>
      first_x_assum (qspec_then `sa.cs_next_var` assume_tac) >>
      gvs[finite_mapTheory.FLOOKUP_UPDATE]) >>
  rpt strip_tac >> gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj]
QED

Theorem raw_call_outbuf_positive_run[local]:
  0 < cap /\ compile_raw_call_outbuf cap sa = ((ov,op),sb) /\
  ((cap + 31) DIV 32) * 32 + 32 < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ fn_has_code sa sb func ==>
  ?t w. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand ov t = SOME w /\ eval_operand op t = SOME (w + 32w) /\
    w2n (w + 32w) = w2n w + 32 /\
    FLOOKUP t.vs_allocas sa.cs_next_id =
      SOME (w2n w, ((cap + 31) DIV 32) * 32 + 32) /\
    w2n w + (((cap + 31) DIV 32) * 32 + 32) < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es t /\ t.vs_memory = s.vs_memory /\
    wb_frame cenv es sa s t /\
    (!name b len. local_region cenv es.scopes t name b len ==>
      regions_disjoint (w2n w) (((cap + 31) DIV 32) * 32 + 32) b len) /\
    (cenv.ce_is_ctor ==> !name tv v off.
      FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
      regions_disjoint off (type_memory_size tv) (w2n w)
        (((cap + 31) DIV 32) * 32 + 32)) /\
    (!x. ov = Var x \/ op = Var x ==> not_fresh_at sb x)
Proof
  strip_tac >> drule_all raw_call_outbuf_steps >> strip_tac >> gvs[] >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    (fs[ci_mono_def] >> metis_tac[ci_mono_compile_alloc_buffer,
       ci_mono_emit_op, pairTheory.SND, ci_mono_def]) >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK allocated` >>
  `sm.cs_next_var = sa.cs_next_var + 1 /\
   sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[contextTheory.compile_alloc_buffer_def, emit_op_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def, fresh_id_def, fresh_var_def,
          emit_def, emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND] >>
     strip_tac >> gvs[rich_listTheory.DROP_LENGTH_APPEND]) >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `!x. buf.buf_operand = Var x ==> not_fresh_at sm x` by
    (asm_rewrite_tac[] >> simp[]) >>
  drule_all raw_call_outbuf_add_frame >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sm sb) allocated = OK final` >>
  `sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb` by
    (drule emitHelperPropsTheory.emitted_insts_emit_op >> simp[]) >>
  `run_inst_seq (emitted_insts sa sb) s =
   run_inst_seq (emitted_insts sm sb) allocated` by
    (irule (cj 1 run_inst_seq_chain) >> simp[]) >>
  `w2n (w + 32w) = w2n w + 32` by
    (irule buffer_offset_no_wrap >> goal_assum drule >> simp[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x final = lookup_var x s` by
    (rpt strip_tac >>
     `not_fresh_at sm x` by
       (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
     qpat_x_assum `!x. not_fresh_at sm x ==> _` drule >> simp[]) >>
  `!name b len. local_region cenv es.scopes final name b len ==>
     regions_disjoint (w2n w) (32 * ((cap + 31) DIV 32) + 32) b len` by
    (rpt strip_tac >> simp[] >>
     qpat_x_assum `!name b len. local_region _ _ allocated _ _ _ ==> _` irule >>
     qexists_tac `name` >> irule exprSimOpsTheory.local_region_frame >>
     conj_tac >- (qexists_tac `func` >> fs[stmt_state_rel_def, state_rel_def]) >>
     qexistsl_tac [`sm`, `es.scopes`, `final`] >> simp[]) >>
  qexistsl_tac [`final`, `w`] >> simp[] >> conj_tac
  >- (simp[wb_frame_def, locals_kept_def] >> rpt strip_tac >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- suspend "immutable" >>
  qpat_x_assum `!x. buf.buf_operand = Var x \/ op = Var x ==> _` mp_tac >>
  asm_rewrite_tac[] >> simp[]
QED

Resume raw_call_outbuf_positive_run[immutable]:
  rpt strip_tac >>
  qpat_assum `stmt_state_rel ctx func cenv cx es final` mp_tac >>
  pure_rewrite_tac[stmt_state_rel_def, immutable_alloca_sep_def] >> strip_tac >>
  qpat_x_assum `cenv.ce_is_ctor ==> _` drule >>
  disch_then drule_all >> strip_tac >>
  qpat_x_assum `!inst b sz. MEM inst _ /\ _ ==> _`
    (qspec_then `mk_inst sa.cs_next_id ALLOCA
      [Lit (n2w (((cap + 31) DIV 32) * 32 + 32))]
      [STRING #"%" (toString sa.cs_next_var)]` mp_tac) >>
  fs[mk_inst_def]
QED

Finalise raw_call_outbuf_positive_run

Theorem raw_call_frame_footprint[local]:
  expr_val_at cenv cx ty sa sb es v op s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  ~is_word_type ty /\ ~dynarray_type ty /\
  eval_operand op s = SOME w /\ sb.cs_next_id <= sk.cs_next_id /\
  wb_frame cenv es sk s t ==>
  mem_bytes_at (w2n w) (val_footprint tv v) t.vs_memory =
  mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory
Proof
  strip_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def] >> strip_tac >> gvs[]
  >- (fs[wb_frame_def] >>
      `aid < sk.cs_next_id` by decide_tac >>
      qpat_x_assum `!aid off sz. _ ==> mem_bytes_at _ _ _ = _` drule_all >>
      disch_then (mp_tac o cj 1 o MATCH_MP valueEncodingProofsTheory.mem_bytes_at_agree_window) >>
      disch_then (qspecl_then [`w2n w`, `val_footprint tv v`] mp_tac) >>
      simp[])
  >- (fs[wb_frame_def, locals_kept_def] >>
      qpat_x_assum `!n b sz off len. _ ==> _` irule >>
      qexistsl_tac [`b`, `n`, `sz`] >> simp[] >> decide_tac)
  >> simp[mem_bytes_at_def]
QED

Theorem raw_call_frame_bytes[local]:
  expr_val_at cenv cx (BaseT (BytesT (Dynamic cap))) sa sb es (BytesV bs) op s /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic cap))) =
    SOME (BaseTV (BytesT (Dynamic cap))) /\
  eval_operand op s = SOME (n2w b) /\ b < dimword (:256) /\
  sb.cs_next_id <= sk.cs_next_id /\ wb_frame cenv es sk s t /\
  mem_bytes_at (b+32) (LENGTH bs) s.vs_memory = bs ==>
  mem_bytes_at (b+32) (LENGTH bs) t.vs_memory = bs
Proof
  strip_tac >>
  `~is_word_type (BaseT (BytesT (Dynamic cap))) /\
   ~dynarray_type (BaseT (BytesT (Dynamic cap)))` by
    simp[is_word_type_def, dynarray_type_def] >>
  drule_all raw_call_frame_footprint >>
  simp[val_footprint_def, wordsTheory.w2n_n2w] >> strip_tac >>
  drule (cj 1 valueEncodingProofsTheory.mem_bytes_at_agree_window) >>
  disch_then (qspecl_then [`b+32`, `LENGTH bs`] mp_tac) >> simp[]
QED

Theorem raw_call_addr_data_post[local]:
  expr_post ctx func cenv cx d es1 s1 s2 ta es2 (BytesV bs) data td /\
  expr_type d = BaseT (BytesT (Dynamic cap)) /\
  evaluate_type (get_tenv cx) (expr_type d) = SOME (BaseTV (BytesT (Dynamic cap))) /\
  expr_val_rel cx (BaseT AddressT) av addr td /\
  (!x. addr = Var x \/ data = Var x ==> not_fresh_at s2 x) /\
  (!l. addr <> Label l) /\ local_ptrs_reserved cenv s2 /\
  emit_op MLOAD [data] s2 = (len,s3) /\
  emit_op ADD [data; Lit 32w] s3 = (ptr_op,s4) ==>
  ?t b. run_inst_seq (emitted_insts s2 s4) td = OK t /\
    expr_val_rel cx (BaseT AddressT) av addr t /\
    eval_operand data td = SOME (n2w b) /\
    eval_operand len t = SOME (n2w (LENGTH bs)) /\
    eval_operand ptr_op t = SOME (n2w (b+32)) /\
    mem_bytes_at (b+32) (LENGTH bs) t.vs_memory = bs /\
    b+32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
    t.vs_memory = td.vs_memory /\ t.vs_allocas = td.vs_allocas /\
    stmt_state_rel ctx func cenv cx es2 t /\ wb_frame cenv es2 s2 td t /\
    (!x. addr = Var x \/ len = Var x \/ ptr_op = Var x ==> not_fresh_at s4 x)
Proof
  strip_tac >>
  drule_all hash_dynamic_post_view >> strip_tac >>
  `b < dimword (:256)` by decide_tac >>
  `stmt_state_rel ctx func cenv cx es2 td` by fs[expr_post_def] >>
  `!x. data = Var x ==> not_fresh_at s2 x` by simp[] >>
  drule_all raw_call_data_prefix_frame >> strip_tac >>
  `s2.cs_next_var <= s4.cs_next_var` by
    (metis_tac[ci_mono_emit_op, ci_mono_def, pairTheory.SND,
       arithmeticTheory.LESS_EQ_TRANS]) >>
  `!x. addr = Var x ==> not_fresh_at s4 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `s2` >> fs[ci_mono_def]) >>
  `expr_val_rel cx (BaseT AddressT) av addr t` by
    (qpat_x_assum `expr_val_rel cx (BaseT AddressT) av addr td` mp_tac >>
     simp[expr_val_rel_def, is_word_type_def] >> strip_tac >>
     qexists_tac `w` >> simp[] >>
     irule exprSimOpsTheory.eval_operand_frame >> simp[] >>
     qexistsl_tac [`s2`, `td`] >> fs[wb_frame_def]) >>
  qexistsl_tac [`t`, `b`] >> simp[] >> metis_tac[]
QED

Theorem raw_call_addr_data_values[local]:
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) dflt) es /\
  (do r <- eval_expr cx a; read_result cx r od) es = (INL av,es1) /\
  (do r <- eval_expr cx d; read_result cx r od) es1 = (rr,es2) ==>
  expr_sim_inv cenv cx env es1 /\ expr_sim_inv cenv cx env es2 /\
  expr_res_ok rr /\ value_has_type (BaseTV AddressT) av /\
  ?cap. expr_type d = BaseT (BytesT (Dynamic cap)) /\
    (!v. rr = INL v ==> ?bs. v = BytesV bs)
Proof
  strip_tac >> drule raw_call_pre_operands >> strip_tac >> gvs[] >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  `expr_body_pre cenv cx env a es` by
    (irule expr_body_pre_raw_call_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
  drule_all expr_body_pre_base_result >> strip_tac >>
  `expr_body_pre cenv cx env d es1` by
    (irule expr_body_pre_raw_call_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
  drule_at (Pat `expr_body_pre _ _ _ d _`) expr_body_pre_base_result >>
  simp[] >> strip_tac >> rpt strip_tac >>
  first_x_assum drule >> Cases_on `v` >> simp[value_has_type_def]
QED

Theorem raw_call_addr_data_sim[local]:
  exprs_case nocalls ctx func cenv cx (a::d::kws) /\
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) dflt) es /\
  (nocalls ==> int_calls_expr (Call ann (RawCallTarget flags) (a::d::kws) dflt) = []) /\
  lower_value compile_expr cenv (BaseT AddressT) a sa = (addr,s1) /\
  lower_value compile_expr cenv (expr_type d) d s1 = (data,s2) /\
  emit_op MLOAD [data] s2 = (len,s3) /\
  emit_op ADD [data; Lit 32w] s3 = (ptr_op,s4) /\
  eval_exprs cx [a;d] es = (rr,es2) /\ fn_has_code sa s4 func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa ==>
  frag_exec ctx sa s4 (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
    (\t. ?av bs es1 ta td b.
      rr = INL [av;BytesV bs] /\
      (?u. run_inst_seq (emitted_insts s2 s4) td = OK u /\
           t = u with vs_inst_idx := t.vs_inst_idx) /\
      expr_post ctx func cenv cx a es sa s1 s0 es1 av addr ta /\
      expr_post ctx func cenv cx d es1 s1 s2 ta es2 (BytesV bs) data td /\
      expr_val_rel cx (BaseT AddressT) av addr t /\
      eval_operand data td = SOME (n2w b) /\
      eval_operand len t = SOME (n2w (LENGTH bs)) /\
      eval_operand ptr_op t = SOME (n2w (b+32)) /\
      mem_bytes_at (b+32) (LENGTH bs) t.vs_memory = bs /\
      b+32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
      t.vs_memory = td.vs_memory /\ t.vs_allocas = td.vs_allocas /\
      stmt_state_rel ctx func cenv cx es2 t /\ wb_frame cenv es sa s0 t /\
      (!x. addr = Var x \/ len = Var x \/ ptr_op = Var x ==> not_fresh_at s4 x))
    (wb_args_exit rr)
Proof
  strip_tac >> drule raw_call_pre_operands >> strip_tac >> gvs[] >>
  `ci_mono sa s1 /\ ci_mono s1 s2` by
    (metis_tac[ci_mono_lower_value_cfn, compile_expr_ci_mono, pairTheory.SND]) >>
  `ci_mono s2 s3 /\ ci_mono s3 s4` by
    metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `cs_extends sa s1 /\ cs_extends s1 s2 /\ cs_extends s2 s3 /\ cs_extends s3 s4` by
    fs[ci_mono_def] >>
  `cs_extends s2 s4 /\ cs_extends s1 s4` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s4 func /\
   fn_has_code s1 s2 func /\ fn_has_code s2 s4 func` by
    metis_tac[fn_has_code_split] >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  `expr_body_pre cenv cx env a es` by
    (irule expr_body_pre_raw_call_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
  `nocalls ==> int_calls_expr a = []` by
    (fs[int_calls_expr_def] >> metis_tac[int_calls_exprs_mem, MEM]) >>
  `expr_sim ctx func cenv cx (BaseT AddressT) a es` by
    (fs[exprs_case_def, expr_sim_case_def] >> metis_tac[]) >>
  drule eval_exprs_cons_cases >> strip_tac
  >- suspend "address_exit"
  >> drule_all expr_body_pre_base_result >> strip_tac >>
  `exprs_case nocalls ctx func cenv cx (d::kws)` by
    (drule eval_expr_read_INL >> strip_tac >> fs[exprs_case_def] >> metis_tac[]) >>
  `expr_body_pre cenv cx env d es1` by
    (irule expr_body_pre_raw_call_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
  `nocalls ==> int_calls_expr d = []` by
    (fs[int_calls_expr_def] >> metis_tac[int_calls_exprs_mem, MEM]) >>
  `expr_sim ctx func cenv cx (expr_type d) d es1` by
    (fs[exprs_case_def, expr_sim_case_def] >> metis_tac[]) >>
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> fs[ci_mono_def]) >>
  qpat_x_assum `eval_exprs _ [d] _ = _` mp_tac >>
  disch_then (strip_assume_tac o MATCH_MP eval_exprs_cons_cases) >>
  gvs[eval_exprs_nil]
  >- suspend "data_exit"
  >> suspend "success"
QED

Resume raw_call_addr_data_sim[address_exit]:
  gvs[] >> drule_all expr_body_pre_base_result >> strip_tac >>
  irule expr_sim_suffix >> goal_assum (drule_at Any) >> simp[] >>
  first_assum (irule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
  first_assum (irule_at (Pat `bind _ _ _ = _`)) >>
  simp[wb_args_exit_def, expr_exit_def]
QED

Resume raw_call_addr_data_sim[data_exit]:
  drule_all raw_call_addr_data_values >> strip_tac >>
  irule expr_sim_suffix >>
  qpat_assum `expr_sim _ _ _ _ _ a es` (irule_at Any) >>
  first_assum (irule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
  first_assum (irule_at (Pat `bind _ _ _ = _`)) >> simp[] >>
  rpt strip_tac >>
  irule frag_exec_conseq >>
  irule_at Any expr_sim_suffix >>
  qpat_assum `expr_sim _ _ _ _ _ d es1` (irule_at Any) >>
  first_assum (irule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
  first_assum (irule_at (Pat `bind _ _ _ = _`)) >>
  simp[expr_post_def, wb_args_exit_def, expr_exit_def] >>
  qexistsl_tac [`expr_exit (INR exc : value + exception)`, `\s. F`] >>
  fs[expr_post_def]
QED

Resume raw_call_addr_data_sim[success]:
  reverse (Cases_on `stmt_state_rel ctx func cenv cx es s0`)
  >- (irule frag_exec_pointwise >> simp[]) >>
  drule_all raw_call_addr_data_values >> strip_tac >> gvs[] >>
  irule expr_sim_suffix >>
  qpat_assum `expr_sim _ _ _ _ _ a es` (irule_at Any) >>
  first_assum (irule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
  first_assum (irule_at (Pat `bind _ _ _ = _`)) >> simp[] >>
  rpt strip_tac >>
  irule frag_exec_pre_exit >> irule_at Any expr_sim_suffix >>
  qpat_assum `expr_sim _ _ _ _ _ d es1` (irule_at Any) >>
  first_assum (irule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
  first_assum (irule_at (Pat `bind _ _ _ = _`)) >> simp[] >>
  qexists_tac `\r. F` >>
  simp[wb_args_exit_def] >>
  reverse conj_tac >- fs[expr_post_def] >>
  rpt strip_tac >>
  `safe_operand s1 addr` by
    (irule lower_value_word_safe_operand >>
     first_assum (irule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
     qexists_tac `env` >>
     drule_at (Pat `expr_body_pre _ _ _ a _`) expr_body_pre_var_types_well_formed >>
     fs[expr_body_pre_def, is_word_type_def]) >>
  `(!x. addr = Var x ==> not_fresh_at s1 x) /\ (!l. addr <> Label l)` by
    fs[safe_operand_def] >>
  drule_all expr_post_operand_word >> strip_tac >>
  `expr_val_rel cx (BaseT AddressT) v addr t'` by
    (fs[expr_post_def, expr_val_rel_def] >>
     gvs[is_word_type_def, vyperValueTheory.evaluate_type_def]) >>
  `evaluate_type (get_tenv cx) (expr_type d) = SOME (BaseTV (BytesT (Dynamic cap)))` by
    (drule_at (Pat `expr_body_pre _ _ _ d _`) expr_body_pre_type_evaluates >>
     simp[vyperValueTheory.evaluate_type_def]) >>
  `!x. addr = Var x \/ data = Var x ==> not_fresh_at s2 x` by
    (rpt strip_tac
     >- (irule freshWritesTheory.not_fresh_at_mono >>
         qexists_tac `s1` >> fs[ci_mono_def]) >>
     metis_tac[compile_lower_value_var]) >>
  `local_ptrs_reserved cenv s2` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `s1` >> fs[ci_mono_def]) >>
  drule_all raw_call_addr_data_post >> strip_tac >>
  suspend "run_packaging"
QED

Resume raw_call_addr_data_sim[run_packaging]:
  `MAP FDOM es.scopes = MAP FDOM es1.scopes /\
   MAP FDOM es1.scopes = MAP FDOM es1'.scopes` by
    metis_tac[forced_eval_expr_preserves_scopes_dom] >>
  `wb_frame cenv es sa s0 t'` by
    (irule wb_frame_trans >>
     simp[] >> reverse conj_tac
     >- (goal_assum (drule_at Any)) >>
     qexistsl_tac [`es1`, `s1`, `t`] >>
     fs[expr_post_def, wb_frame_def, ci_mono_def] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `wb_frame cenv es sa s0 t''` by
    (irule wb_frame_trans >>
     simp[] >> reverse conj_tac
     >- (goal_assum (drule_at Any)) >>
     qexistsl_tac [`es1'`, `s2`, `t'`] >>
     fs[ci_mono_def] >> decide_tac) >>
  irule frag_exec_run_inst_seq >>
  conj_tac
  >- (simp[] >>
      qexistsl_tac [`es1`, `t`, `t'`, `b`] >>
      simp[stmt_state_rel_inst_idx, wb_frame_def, lookup_var_def] >>
      fs[wb_frame_def, lookup_var_def, expr_val_rel_def] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
  qpat_x_assum `emit_op MLOAD _ _ = _` mp_tac >>
  simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_id_def, fresh_var_def, emit_def] >>
  rpt strip_tac >> gvs[emitted_insts_def,
    rich_listTheory.DROP_LENGTH_APPEND, is_terminator_def,
    mk_inst_def, rich_listTheory.IS_PREFIX_APPEND] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[rich_listTheory.DROP_LENGTH_APPEND, is_terminator_def]
QED

Finalise raw_call_addr_data_sim

Theorem raw_call_data_prefix_placement[local]:
  emit_op MLOAD [data] sd = (len,sl) /\
  emit_op ADD [data; Lit 32w] sl = (ptr_op,sm) /\
  (!x. data = Var x ==> not_fresh_at sd x) /\
  eval_operand data u = SOME (n2w b) /\
  mem_word_at b u.vs_memory = n2w (LENGTH bs) /\ b < dimword (:256) /\
  local_ptrs_reserved cenv sd /\
  expr_val_at cenv cx (BaseT (BytesT (Dynamic cap))) sa sd es (BytesV bs) data u /\
  run_inst_seq (emitted_insts sd sm) u = OK s ==>
  expr_val_at cenv cx (BaseT (BytesT (Dynamic cap))) sa sd es (BytesV bs) data s /\
  eval_operand data s = SOME (n2w b)
Proof
  strip_tac >> drule_all hash_data_prefix_run >> strip_tac >> gvs[] >>
  `s.vs_labels = u.vs_labels /\ s.vs_allocas = u.vs_allocas` by
    (qpat_x_assum `s with vs_vars := _ = _`
      (mp_tac o Q.AP_TERM `\z. (z.vs_labels,z.vs_allocas)`) >> simp[]) >>
  `eval_operand data s = SOME (n2w b)` by
    (Cases_on `data` >> gvs[eval_operand_def] >> metis_tac[]) >>
  `!n base sz. local_region cenv es.scopes s n base sz <=>
              local_region cenv es.scopes u n base sz` by
    (simp[local_region_def] >> rpt gen_tac >>
     `!p sz. FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var p) sz) ==>
       lookup_var p s = lookup_var p u` by
       (rpt strip_tac >> first_x_assum irule >>
        fs[local_ptrs_reserved_def] >> metis_tac[]) >>
     metis_tac[]) >>
  conj_tac
  >- (fs[expr_val_at_def] >> rpt strip_tac >>
      first_x_assum drule >> simp[]) >>
  simp[]
QED

Theorem raw_call_kwargs_payload[local]:
  expr_val_at cenv cx (BaseT (BytesT (Dynamic cap))) sa sd es (BytesV bs) data s /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic cap))) =
    SOME (BaseTV (BytesT (Dynamic cap))) /\
  eval_operand data s = SOME (n2w b) /\ b < dimword (:256) /\
  mem_bytes_at (b+32) (LENGTH bs) s.vs_memory = bs /\
  sd.cs_next_id <= sk.cs_next_id /\
  typed_args_post ctx func cenv cx es sk s es' kws xs vs t ==>
  mem_bytes_at (b+32) (LENGTH bs) t.vs_memory = bs
Proof
  strip_tac >>
  `wb_frame cenv es sk s t` by fs[typed_args_post_def] >>
  drule_all raw_call_frame_bytes >> simp[]
QED

Theorem raw_call_optional_gas_run[local]:
  (case go of SOME g => (g,sa) | NONE => emit_op GAS [] sa) = (gas,sb) /\
  (!g. go = SOME g ==> ?w. eval_operand g s = SOME w) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa ==>
  ?t gw. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand gas t = SOME gw /\ stmt_state_rel ctx func cenv cx es t /\
    wb_frame cenv es sa s t /\ t.vs_memory = s.vs_memory /\
    t.vs_allocas = s.vs_allocas
Proof
  Cases_on `go`
  >- (simp[] >> strip_tac >>
      drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
      qabbrev_tac `t = update_var (STRING #"%" (toString sa.cs_next_var))
        (n2w s.vs_call_ctx.cc_gas) s` >>
      `run_inst_seq (emitted_insts sa sb) s = OK t` by
        simp[Abbr `t`, run_inst_seq_def, step_inst_def, step_inst_base_def,
             mk_inst_def, exec_read0_def] >>
      `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s` by
        (simp[Abbr `t`, emitHelperPropsTheory.lookup_var_update_var] >>
         rpt strip_tac >> gvs[not_fresh_at_def]) >>
      `(t with vs_vars := s.vs_vars) = s` by simp[Abbr `t`, update_var_def] >>
      `stmt_state_rel ctx func cenv cx es t` by
        (irule hash_readonly_state_rel >> goal_assum drule >> simp[]) >>
      qexists_tac `t` >> simp[Abbr `t`, update_var_def, eval_operand_def,
        lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE, wb_frame_def,
        locals_kept_def] >>
      rpt strip_tac >> gvs[not_fresh_at_def, lookup_var_def]) >>
  simp[] >> strip_tac >> gvs[] >>
  qexists_tac `s` >> simp[emitted_insts_def, run_inst_seq_def, wb_frame_refl]
QED

Theorem raw_call_kwargs_ready[local]:
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) dflt) es /\
  (nocalls ==> int_calls_expr (Call ann (RawCallTarget flags) (a::d::kws) dflt) = []) /\
  exprs_case nocalls ctx func cenv cx kws ==>
  typed_args_ready ctx func cenv cx (K (BaseT (UintT 256)))
    (expr_sim_inv cenv cx env) kws
Proof
  strip_tac >> drule raw_call_pre_flags >> strip_tac >>
  drule raw_call_kwargs_types >> simp[] >> strip_tac >>
  irule typed_args_ready_of_case >> qexists_tac `nocalls` >> simp[] >>
  rpt gen_tac >> strip_tac >> rpt conj_tac
  >- (`MEM e (a::d::kws)` by simp[] >>
      drule_all expr_body_pre_raw_call_arg >> simp[]) 
  >- (rw[] >> gvs[int_calls_expr_def] >> metis_tac[int_calls_exprs_mem]) >>
  fs[EVERY_MEM, is_word_type_def]
QED

Theorem raw_call_eval_exprs_append[local]:
  !xs ys cx st.
    eval_exprs cx (xs ++ ys) st =
    (case eval_exprs cx xs st of
       (INR ex,st1) => (INR ex,st1)
     | (INL vs,st1) =>
       case eval_exprs cx ys st1 of
         (INR ex,st2) => (INR ex,st2)
       | (INL ws,st2) => (INL (vs ++ ws),st2))
Proof
  Induct_on `xs`
  >- (simp[Once evaluate_def, return_def] >>
      rpt gen_tac >> Cases_on `eval_exprs cx ys st` >>
      rename1 `eval_exprs cx ys st = (res,t)` >> Cases_on `res` >> simp[])
  >> rpt gen_tac >> simp[Once evaluate_def, bind_def, return_def] >>
  simp[Once evaluate_def, bind_def, return_def] >>
  Cases_on `eval_expr cx h st` >>
  rename1 `eval_expr cx h st = (res,t)` >> Cases_on `res` >> simp[] >>
  rename1 `read_result cx tv t` >>
  Cases_on `read_result cx tv t` >>
  rename1 `read_result cx tv t = (res,u)` >> Cases_on `res` >> simp[] >>
  Cases_on `eval_exprs cx xs u` >>
  rename1 `eval_exprs cx xs u = (res,vst)` >> Cases_on `res` >> simp[] >>
  Cases_on `eval_exprs cx ys vst` >>
  rename1 `eval_exprs cx ys vst = (res,wst)` >> Cases_on `res` >> simp[]
QED

Theorem raw_call_prefix_sim[local]:
  exprs_case nocalls ctx func cenv cx (a::d::kws) /\
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) dflt) es /\
  (nocalls ==> int_calls_expr (Call ann (RawCallTarget flags) (a::d::kws) dflt) = []) /\
  lower_value compile_expr cenv (BaseT AddressT) a sa = (addr,s1) /\
  lower_value compile_expr cenv (expr_type d) d s1 = (data,s2) /\
  emit_op MLOAD [data] s2 = (len,s3) /\
  emit_op ADD [data; Lit 32w] s3 = (ptr_op,s4) /\
  compile_ext_call_kwargs compile_expr cenv NoneT flags.rcf_kws kws s4 =
    ((vo,go,ignored),s5) /\
  (case go of SOME g => (g,s5) | NONE => emit_op GAS [] s5) = (gas,s6) /\
  eval_exprs cx (a::d::kws) es = (rr,es') /\ fn_has_code sa s6 func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa ==>
  frag_exec ctx sa s6 (\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s)
    (\t. ?av bs kvs xs b gw es2 tm tk.
      rr = INL (av::BytesV bs::kvs) /\
      eval_exprs cx [a;d] es = (INL [av;BytesV bs],es2) /\
      eval_exprs cx kws es2 = (INL kvs,es') /\
      expr_val_rel cx (BaseT AddressT) av addr t /\
      typed_args_post ctx func cenv cx es2 s4 tm es' kws xs kvs tk /\
      vo = ext_call_kwarg EKValue flags.rcf_kws xs /\
      go = ext_call_kwarg EKGas flags.rcf_kws xs /\ ignored = NONE /\
      (!x w. MEM x xs /\ eval_operand x tk = SOME w ==> eval_operand x t = SOME w) /\
      eval_operand len t = SOME (n2w (LENGTH bs)) /\
      eval_operand ptr_op t = SOME (n2w (b+32)) /\ eval_operand gas t = SOME gw /\
      mem_bytes_at (b+32) (LENGTH bs) t.vs_memory = bs /\
      b+32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
      stmt_state_rel ctx func cenv cx es' t /\ wb_frame cenv es sa s0 t /\
      (!x. addr = Var x \/ len = Var x \/ ptr_op = Var x \/ gas = Var x \/
           MEM (Var x) xs ==> not_fresh_at s6 x))
    (wb_args_exit rr)
Proof
  strip_tac >> drule raw_call_pre_flags >> strip_tac >>
  drule raw_call_kwargs_types >> simp[] >> strip_tac >>
  `LENGTH kws = LENGTH flags.rcf_kws` by fs[] >>
  drule_all raw_call_kwargs_word_args >> strip_tac >>
  qspecl_then [`kws`, `cenv`, `K (BaseT (UintT 256))`] mp_tac lower_word_args_shape >>
  (impl_tac
   >- (rpt strip_tac >>
       `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
       `MEM e (a::d::kws)` by simp[] >>
       `expr_body_pre cenv cx env e es` by
         (drule_all expr_body_pre_raw_call_arg >> simp[]) >>
       `is_word_type (expr_type e)` by fs[EVERY_MEM, is_word_type_def] >>
       drule_all expr_body_pre_lower_value_word_shape >> simp[])) >>
  disch_then drule >> strip_tac >>
  `ci_mono sa s1 /\ ci_mono s1 s2` by
    metis_tac[ci_mono_lower_value_cfn, compile_expr_ci_mono, pairTheory.SND] >>
  `ci_mono s2 s3 /\ ci_mono s3 s4` by
    metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `cs_extends sa s4` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `ci_mono s5 s6` by
    (Cases_on `go` >> gvs[]
     >- metis_tac[ci_mono_emit_op, pairTheory.SND] >> simp[ci_mono_refl]) >>
  `cs_extends s4 s6` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sa s4 func /\ fn_has_code s4 s6 func` by
    metis_tac[fn_has_code_split] >>
  suspend "compose"
QED

Resume raw_call_prefix_sim[compose]:
  reverse (Cases_on `stmt_state_rel ctx func cenv cx es s0`)
  >- (irule frag_exec_pointwise >> simp[]) >>
  Cases_on `eval_exprs cx [a;d] es` >>
  rename1 `eval_exprs cx [a;d] es = (rd,es2)` >>
  `eval_exprs cx ([a;d] ++ kws) es = (rr,es')` by simp[] >>
  qpat_x_assum `eval_exprs cx ([a;d] ++ kws) es = _` mp_tac >>
  pure_rewrite_tac[raw_call_eval_exprs_append] >> asm_rewrite_tac[] >>
  disch_tac >>
  drule_all raw_call_addr_data_sim >>
  disch_then (qspec_then `s0` mp_tac) >>
  disch_then (mp_tac o MATCH_MP frag_exec_pre_exit_c) >>
  disch_then (qspecl_then [`\s. s = s0 /\ stmt_state_rel ctx func cenv cx es s`,
                         `wb_args_exit rr`] mp_tac) >>
  (impl_tac >- (simp[] >> Cases_on `rd` >> gvs[wb_args_exit_def])) >>
  disch_then (mp_tac o MATCH_MP frag_exec_then) >>
  disch_then irule >> simp[] >> rpt strip_tac >>
  `exprs_case nocalls ctx func cenv cx kws /\ expr_sim_inv cenv cx env es2` by
    (qpat_assum `eval_exprs cx [a;d] es = _`
       (strip_assume_tac o MATCH_MP eval_exprs_cons_cases) >>
     gvs[] >>
     qpat_assum `eval_exprs cx [d] _ = _`
       (strip_assume_tac o MATCH_MP eval_exprs_cons_cases) >>
     gvs[eval_exprs_nil] >>
     drule_all raw_call_addr_data_values >> strip_tac >>
     drule eval_expr_read_INL >> strip_tac >>
     fs[exprs_case_def] >> metis_tac[eval_expr_read_INL]) >>
  drule_all raw_call_kwargs_ready >> strip_tac >>
  `wb_args_shape cenv (K (BaseT (UintT 256))) kws` by
    (irule typed_stack_args_shape >> qexistsl_tac [`cx`, `env`, `es2`] >>
     simp[] >> rpt gen_tac >> strip_tac >> conj_tac
     >- (irule expr_body_pre_raw_call_arg >>
         first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
     fs[EVERY_MEM, is_word_type_def]) >>
  `local_ptrs_reserved cenv s4` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
     fs[ci_mono_def] >> decide_tac) >>
  `fn_has_code s4 s5 func` by
    metis_tac[fn_has_code_split, ci_mono_def] >>
  suspend "keywords"
QED

Resume raw_call_prefix_sim[keywords]:
  `?cap. expr_type d = BaseT (BytesT (Dynamic cap))` by
    (drule raw_call_pre_operands >> simp[] >> metis_tac[]) >>
  `expr_body_pre cenv cx env d es2` by
    (irule expr_body_pre_raw_call_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
  `evaluate_type (get_tenv cx) (expr_type d) = SOME (BaseTV (BytesT (Dynamic cap)))` by
    (drule_at (Pat `expr_body_pre _ _ _ d _`) expr_body_pre_type_evaluates >>
     simp[vyperValueTheory.evaluate_type_def]) >>
  drule_all hash_dynamic_post_view >> strip_tac >>
  `b < dimword (:256) /\ b' < dimword (:256)` by decide_tac >>
  `b = b'` by
    (`(n2w b : bytes32) = n2w b'` by metis_tac[optionTheory.SOME_11] >>
     fs[wordsTheory.n2w_11] >> metis_tac[arithmeticTheory.LESS_MOD]) >>
  qpat_x_assum `b = b'` (fn th => fs[GSYM th]) >>
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> fs[ci_mono_def]) >>
  `!x. data = Var x ==> not_fresh_at s2 x` by
    metis_tac[compile_lower_value_var] >>
  `local_ptrs_reserved cenv s2` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
     fs[ci_mono_def] >> decide_tac) >>
  `expr_val_at cenv cx (BaseT (BytesT (Dynamic cap))) s1 s2 es2 (BytesV bs) data td` by
    fs[expr_post_def] >>
  drule_all raw_call_data_prefix_placement >> strip_tac >>
  `expr_val_at cenv cx (BaseT (BytesT (Dynamic cap))) s1 s2 es2 (BytesV bs) data t /\
   eval_operand data t = SOME (n2w b)` by
    (qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ u` mp_tac >>
     qpat_x_assum `eval_operand data u = _` mp_tac >>
     qpat_x_assum `t = u with vs_inst_idx := _` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     once_asm_rewrite_tac[] >>
     Cases_on `data` >>
     simp[expr_val_at_def, eval_operand_def, lookup_var_def, local_region_def]) >>
  suspend "kwargs_run"
QED

Resume raw_call_prefix_sim[kwargs_run]:
  qpat_x_assum `run_inst_seq _ _ = OK u` kall_tac >>
  qpat_x_assum `t = u with vs_inst_idx := _` kall_tac >>
  qpat_x_assum `expr_post _ _ _ _ a _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `expr_post _ _ _ _ d _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ td` kall_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ u` kall_tac >>
  `cs_extends s5 s6` by fs[ci_mono_def] >>
  Cases_on `eval_exprs cx kws es2` >>
  rename1 `eval_exprs cx kws es2 = (kr,es3)` >>
  drule_all lower_typed_args_sim >>
  disch_then (qspec_then `t` mp_tac) >>
  disch_then (mp_tac o MATCH_MP frag_exec_pre_exit_c) >>
  disch_then (qspecl_then [`\s. s = t`, `wb_args_exit rr`] mp_tac) >>
  (impl_tac >- (simp[] >> Cases_on `kr` >> gvs[wb_args_exit_def])) >>
  disch_then (mp_tac o MATCH_MP frag_exec_then) >>
  disch_then irule >> simp[] >> rpt strip_tac >>
  suspend "gas_run"
QED

Resume raw_call_prefix_sim[gas_run]:
  gvs[] >>
  `stmt_state_rel ctx func cenv cx es' t' /\ wb_frame cenv es2 s4 t t'` by
    fs[typed_args_post_def] >>
  `local_ptrs_reserved cenv s5` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `s4` >> simp[]) >>
  `!ks (ops : operand list) g.
     ext_call_kwarg EKGas ks ops = SOME g ==> MEM g ops` by
    (rpt (pop_assum kall_tac) >>
     Induct_on `ks` >> Cases_on `ops` >>
     simp[ext_call_kwarg_def] >> rpt strip_tac >>
     rename1 `(if key = EKGas then SOME op else _) = SOME g` >>
     Cases_on `key = EKGas` >> gvs[] >> metis_tac[]) >>
  `!g. ext_call_kwarg EKGas flags.rcf_kws xs = SOME g ==>
       ?w. eval_operand g t' = SOME w` by
    (rpt strip_tac >>
     `MEM g xs` by metis_tac[] >>
     qpat_x_assum `typed_args_post _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[typed_args_post_def] >> strip_tac >>
     drule_all LIST_REL_MEM_IMP >> simp[] >> metis_tac[]) >>
  drule_all raw_call_optional_gas_run >> strip_tac >>
  suspend "gas_pack"
QED

Resume raw_call_prefix_sim[gas_pack]:
  `mem_bytes_at (b+32) (LENGTH bs) t.vs_memory = bs` by simp[] >>
  `b < dimword (:256)` by decide_tac >>
  `s2.cs_next_id <= s4.cs_next_id` by (fs[ci_mono_def] >> decide_tac) >>
  `mem_bytes_at (b+32) (LENGTH bs) t'.vs_memory = bs` by
    (drule_all raw_call_kwargs_payload >> simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM es2.scopes /\
   MAP FDOM es2.scopes = MAP FDOM es'.scopes` by
    metis_tac[eval_exprs_preserves_scopes_dom] >>
  suspend "frames"
QED

Resume raw_call_prefix_sim[frames]:
  `wb_frame cenv es sa s0 t'` by
    (irule wb_frame_trans >> simp[] >> reverse conj_tac
     >- (goal_assum (drule_at Any)) >>
     qexistsl_tac [`es2`, `s4`, `t`] >> fs[ci_mono_def] >> decide_tac) >>
  `wb_frame cenv es sa s0 t''` by
    (irule wb_frame_trans >> simp[] >> reverse conj_tac
     >- (goal_assum (drule_at Any)) >>
     qexistsl_tac [`es'`, `s5`, `t'`] >> fs[ci_mono_def] >> decide_tac) >>
  suspend "operand_keep"
QED

Resume raw_call_prefix_sim[operand_keep]:
  `!x. not_fresh_at s4 x ==> not_fresh_at s5 x` by
    (fs[not_fresh_at_def] >> decide_tac) >>
  `!op w. (!x. op = Var x ==> not_fresh_at s4 x) /\
           (!l. op <> Label l) /\ eval_operand op t = SOME w ==> eval_operand op t'' = SOME w` by
    (qpat_x_assum `wb_frame cenv es2 s4 t t'` mp_tac >>
     qpat_x_assum `wb_frame cenv es' s5 t' t''` mp_tac >>
     qpat_x_assum `!x. not_fresh_at s4 x ==> _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     Cases_on `op` >> gvs[eval_operand_def] >>
     fs[wb_frame_def] >> metis_tac[]) >>
  `!op w. MEM op xs /\ eval_operand op t' = SOME w ==>
          eval_operand op t'' = SOME w` by
    (qpat_x_assum `EVERY _ xs` mp_tac >>
     qpat_x_assum `wb_frame cenv es' s5 t' t''` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> strip_tac >>
     Cases_on `op` >> gvs[eval_operand_def] >> metis_tac[wb_frame_vars]) >>
  suspend "run_final"
QED

Resume raw_call_prefix_sim[run_final]:
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  `expr_body_pre cenv cx env a es` by
    (irule expr_body_pre_raw_call_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
  `expr_type a = BaseT AddressT` by
    (drule raw_call_pre_operands >> simp[]) >>
  `is_word_type (expr_type a)` by simp[is_word_type_def] >>
  `!l. addr <> Label l` by
    (qpat_x_assum `lower_value _ _ _ _ sa = (addr,s1)` mp_tac >>
     qpat_x_assum `expr_body_pre _ _ _ a es` mp_tac >>
     qpat_x_assum `is_word_type (expr_type a)` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[expr_body_pre_lower_value_word_shape]) >>
  `safe_operand s3 len /\ safe_operand s4 ptr_op` by
    metis_tac[emit_op_safe_operand] >>
  `eval_operand len t'' = SOME (n2w (LENGTH bs)) /\
   eval_operand ptr_op t'' = SOME (n2w (b+32))` by
    (fs[safe_operand_def] >> metis_tac[]) >>
  suspend "address_final"
QED

Resume raw_call_prefix_sim[address_final]:
  `expr_val_rel cx (BaseT AddressT) av addr t''` by
    (qpat_x_assum `expr_val_rel _ _ _ addr t` mp_tac >>
     qpat_x_assum `!op w. (_ /\ _ /\ _) ==> _` mp_tac >>
     qpat_x_assum `!x. addr = Var x \/ _ ==> _` mp_tac >>
     qpat_x_assum `!l. addr <> Label l` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[expr_val_rel_def, is_word_type_def] >> metis_tac[]) >>
  suspend "fresh_final"
QED

Resume raw_call_prefix_sim[fresh_final]:
  `!x. gas = Var x ==> not_fresh_at s6 x` by
    (Cases_on `ext_call_kwarg EKGas flags.rcf_kws xs` >> gvs[]
     >- metis_tac[emit_op_safe_operand, safe_operand_def] >>
     rename1 `ext_call_kwarg EKGas flags.rcf_kws xs = SOME g` >>
     `MEM g xs` by metis_tac[] >>
     fs[EVERY_MEM, not_fresh_at_def, ci_mono_def] >> metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  `!x. addr = Var x \/ len = Var x \/ ptr_op = Var x \/ gas = Var x \/
       MEM (Var x) xs ==> not_fresh_at s6 x` by
    (qpat_x_assum `!x. addr = Var x \/ len = Var x \/ ptr_op = Var x ==> _` mp_tac >>
     qpat_x_assum `!x. gas = Var x ==> _` mp_tac >>
     qpat_x_assum `EVERY _ xs` mp_tac >>
     qpat_x_assum `ci_mono s5 s6` mp_tac >>
     qpat_x_assum `s4.cs_next_var <= s5.cs_next_var` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[EVERY_MEM, not_fresh_at_def, ci_mono_def] >> rpt strip_tac >>
     metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS, arithmeticTheory.LESS_EQ_TRANS]) >>
  suspend "normalize_final"
QED

Resume raw_call_prefix_sim[normalize_final]:
  irule frag_exec_run_inst_seq >> conj_tac
  >- (simp[] >> qexistsl_tac [`xs`, `b`, `t`, `t'`] >>
      simp[stmt_state_rel_inst_idx, wb_frame_def, lookup_var_def,
           eval_operand_def, expr_val_rel_def] >>
      fs[expr_val_rel_def, is_word_type_def, wb_frame_def, lookup_var_def] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "gas_code"
QED

Resume raw_call_prefix_sim[gas_code]:
  Cases_on `ext_call_kwarg EKGas flags.rcf_kws xs` >> gvs[]
  >- (qpat_x_assum `emit_op GAS [] _ = _` mp_tac >>
      simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
           fresh_id_def, fresh_var_def, emit_def] >>
      rpt strip_tac >> gvs[emitted_insts_def,
        rich_listTheory.DROP_LENGTH_APPEND, is_terminator_def,
        mk_inst_def, rich_listTheory.IS_PREFIX_APPEND]) >>
  simp[emitted_insts_def]
QED

Finalise raw_call_prefix_sim

(* Oracle tail, independent of the expression producing calldata. *)
Theorem raw_call_oracle_step:
  stmt_state_rel ctx func cenv cx es s /\ inst.inst_outputs = [out] /\
  w2w aw = target /\
  w2n vw = (case value_opt of NONE => 0 | SOME n => n) /\
  stat = IS_NONE value_opt /\
  take_call_outcome target (read_memory (w2n ao) (w2n az) s) value_opt es =
    (INL (rq,outcome),es1) /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
     b + sz <= w2n ro \/ w2n ro + w2n rz <= b) /\
  (cenv.ce_is_ctor ==> !name tv v off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
    off + type_memory_size tv <= w2n ro \/ w2n ro + w2n rz <= off) ==>
  ?t. exec_ext_call inst s (gas:bytes32) aw vw ao az (ro:bytes32) (rz:bytes32) stat =
        OK (update_var out (if outcome.co_success then 1w else 0w) t) /\
    t = s with <| vs_outcomes := t.vs_outcomes; vs_requests := t.vs_requests;
      vs_accounts := t.vs_accounts; vs_transient := t.vs_transient;
      vs_logs := t.vs_logs; vs_pending_deletions := t.vs_pending_deletions;
      vs_returndata := t.vs_returndata; vs_memory := t.vs_memory |> /\
    t.vs_memory = (write_memory_with_expansion (w2n ro)
      (TAKE (w2n rz) outcome.co_returnData) s).vs_memory /\
    t.vs_returndata = outcome.co_returnData /\
    mem_bytes_at (w2n ro) (LENGTH (TAKE (w2n rz) outcome.co_returnData)) t.vs_memory =
      TAKE (w2n rz) outcome.co_returnData /\
    state_rel func cenv cx (SND (adopt_call_outcome rq outcome es1)) t
Proof
  strip_tac >>
  `state_rel func cenv cx es s` by fs[stmt_state_rel_def] >>
  drule_all exec_ext_call_oracle_step >>
  disch_then (strip_assume_tac o Q.ISPECL [`gas:bytes32`, `ro:bytes32`, `rz:bytes32`]) >>
  suspend "output_frame"
QED

Resume raw_call_oracle_step[output_frame]:
  qabbrev_tac `payload = TAKE (w2n rz) outcome.co_returnData` >>
  qabbrev_tac `dst = w2n ro` >>
  `LENGTH payload <= w2n rz` by simp[Abbr `payload`, LENGTH_TAKE_EQ, arithmeticTheory.MIN_DEF] >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es
     (write_memory_with_expansion dst payload s)` by
    (irule immutables_rel_mem_agree >> qexists_tac `s` >>
     conj_tac >- simp[immutableMemoryFrameTheory.immutable_write_memory_capacity] >>
     conj_tac >- simp[write_memory_with_expansion_def, LET_THM] >>
     reverse conj_tac >- fs[state_rel_def] >>
     rpt strip_tac >> irule hash_write_memory_disjoint >>
     first_x_assum drule_all >> decide_tac) >>
  `stmt_state_rel ctx func cenv cx es (write_memory_with_expansion dst payload s)` by
    (irule write_memory_stmt_state_rel >> simp[] >>
     rpt strip_tac >> first_x_assum drule >> simp[Abbr `dst`] >> decide_tac) >>
  suspend "oracle_fields"
QED

Resume raw_call_oracle_step[oracle_fields]:
  `s' = (write_memory_with_expansion dst payload s) with
    <| vs_outcomes := s'.vs_outcomes; vs_requests := s'.vs_requests;
       vs_accounts := s'.vs_accounts; vs_transient := s'.vs_transient;
       vs_logs := s'.vs_logs; vs_pending_deletions := s'.vs_pending_deletions;
       vs_returndata := s'.vs_returndata |>` by
    (qpat_x_assum `_ = _ with <| vs_outcomes := _; vs_requests := _;
       vs_accounts := _; vs_transient := _; vs_logs := _;
       vs_pending_deletions := _; vs_returndata := _; vs_memory := _ |>` mp_tac >>
     qpat_x_assum `s'.vs_memory = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[venom_state_component_equality, write_memory_with_expansion_def, LET_THM]) >>
  `local_ptrs_rel func cenv es.scopes s' /\
   immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es s'` by
    (qpat_x_assum `stmt_state_rel _ _ _ _ _ (write_memory_with_expansion _ _ _)` mp_tac >>
     qpat_x_assum `_ = _ with <| vs_outcomes := _; vs_requests := _;
       vs_accounts := _; vs_transient := _; vs_logs := _;
       vs_pending_deletions := _; vs_returndata := _ |>` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >> once_asm_rewrite_tac[] >>
     simp[local_ptrs_rel_oracle_fields, stmt_state_rel_def, state_rel_def,
          immutables_rel_def] >> strip_tac >> simp[]) >>
  qexists_tac `s'` >> simp[hash_write_memory_read_self] >>
  metis_tac[]
QED

Finalise raw_call_oracle_step

(* Turn the parametric external-call equation into emitted code execution. *)
Theorem raw_call_emit_run:
  emit_op (if static_call then STATICCALL else CALL)
    (if static_call then [gas_op; to_op; ao_op; az_op; ro_op; rz_op]
     else [gas_op; to_op; val_op; ao_op; az_op; ro_op; rz_op]) sm = (ok_op,sb) /\
  eval_operand gas_op s = SOME gas /\ eval_operand to_op s = SOME aw /\
  eval_operand ao_op s = SOME ao /\ eval_operand az_op s = SOME az /\
  eval_operand ro_op s = SOME ro /\ eval_operand rz_op s = SOME rz /\
  (~static_call ==> eval_operand val_op s = SOME vw) /\
  exec_ext_call
    (mk_inst sm.cs_next_id (if static_call then STATICCALL else CALL)
      (if static_call then [gas_op; to_op; ao_op; az_op; ro_op; rz_op]
       else [gas_op; to_op; val_op; ao_op; az_op; ro_op; rz_op])
      [STRING #"%" (toString sm.cs_next_var)])
    s gas aw (if static_call then 0w else vw) ao az ro rz
    (static_call \/ s.vs_call_ctx.cc_static) = OK t ==>
  run_inst_seq (emitted_insts sm sb) s = OK t
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  Cases_on `static_call` >>
  gvs[run_inst_seq_def, Once step_inst_base_def, mk_inst_def]
QED

(* A fresh result variable is disjoint from source locals even after adoption. *)
Theorem raw_call_result_frame:
  emit_op opc ops sm = (ok_op,sb) /\ local_ptrs_reserved cenv sm /\
  state_rel func cenv cx es t ==>
  ?u. u = update_var (STRING #"%" (toString sm.cs_next_var)) w t /\
    eval_operand ok_op u = SOME w /\ state_rel func cenv cx es u /\
    u.vs_memory = t.vs_memory /\ u.vs_returndata = t.vs_returndata
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  qexists_tac `update_var (STRING #"%" (toString sm.cs_next_var)) w t` >>
  simp[eval_operand_def, lookup_var_update_var] >>
  irule state_rel_update_var >> simp[] >>
  irule fresh_not_local_ptr >> qexists_tac `sm` >>
  simp[not_fresh_at_def]
QED

(* The two new blocks are essential: the failure arm is not a linear prefix
   of the successful arm.  Leave the final length-store program packaged. *)
Theorem raw_call_finish_steps[local]:
  compile_raw_call_finish to_op dp dl gas_op val_op call_ty cap T ov op sa =
    (result,sb) ==>
  ?success s1 fl s2 kl s3 s4 u4 s5 rds s6 buf s7 s8 s9 u9 s10.
    (case call_ty of
       DelegateCall => emit_op DELEGATECALL [gas_op;to_op;dp;dl;op;Lit (n2w cap)]
     | StaticCall => emit_op STATICCALL [gas_op;to_op;dp;dl;op;Lit (n2w cap)]
     | RegularCall => emit_op CALL [gas_op;to_op;val_op;dp;dl;op;Lit (n2w cap)]) sa =
        (success,s1) /\
    fresh_label "call_failed" s1 = (fl,s2) /\
    fresh_label "call_ok" s2 = (kl,s3) /\
    emit_inst JNZ [success;Label kl;Label fl] [] s3 = ((),s4) /\
    new_block fl s4 = (u4,s5) /\
    emit_op RETURNDATASIZE [] s5 = (rds,s6) /\
    compile_alloc_buffer 0 s6 = (buf,s7) /\
    emit_void RETURNDATACOPY [buf.buf_operand;Lit 0w;rds] s7 = ((),s8) /\
    emit_inst REVERT [buf.buf_operand;rds] [] s8 = ((),s9) /\
    new_block kl s9 = (u9,s10) /\
    (if 0 < cap then
       do len <- emit_op RETURNDATASIZE [];
          cmp <- emit_op LT [len;Lit (n2w cap)];
          capped <- compile_select cmp len (Lit (n2w cap));
          emit_void MSTORE [ov;capped]; return ov od
     else return (Lit 0w)) s10 = (result,sb)
Proof
  simp[compile_raw_call_finish_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  fs[arithmeticTheory.GREATER_DEF]
QED

(* Forward the full returndata, irrespective of the success buffer capacity. *)
Theorem raw_call_failure_run[local]:
  eval_operand dst s = SOME w /\
  eval_operand size_op s = SOME (n2w (LENGTH s.vs_returndata)) /\
  LENGTH s.vs_returndata < dimword (:256) ==>
  ?t. run_inst_seq
    [mk_inst iid RETURNDATACOPY [dst;Lit 0w;size_op] [];
     mk_inst jid REVERT [dst;size_op] []] s = Abort Revert_abort t /\
    t.vs_returndata = s.vs_returndata
Proof
  strip_tac >>
  `step_inst_base (mk_inst iid RETURNDATACOPY [dst;Lit 0w;size_op] []) s =
     OK (write_memory_with_expansion (w2n w) s.vs_returndata s)` by
    (irule raw_call_failure_copy >> simp[]) >>
  simp[Once run_inst_seq_def] >>
  `eval_operand dst (write_memory_with_expansion (w2n w) s.vs_returndata s) = SOME w /\
   eval_operand size_op (write_memory_with_expansion (w2n w) s.vs_returndata s) =
      SOME (n2w (LENGTH s.vs_returndata))` by
    (Cases_on `dst` >> Cases_on `size_op` >>
     gvs[eval_operand_def, lookup_var_def, write_memory_with_expansion_def, LET_THM]) >>
  simp[run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
       wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD,
       GSYM mem_bytes_at_def, hash_write_memory_read_self,
       revert_state_def, set_returndata_def]
QED

(* Erasing variables exposes every field framed by the pure success prefix. *)
Theorem raw_call_length_prefix_frame[local]:
  (do len <- emit_op RETURNDATASIZE [];
      cmp <- emit_op LT [len;Lit (n2w cap)];
      compile_select cmp len (Lit (n2w cap)) od) sa = (capped,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  t with vs_vars := FEMPTY = s with vs_vars := FEMPTY
Proof
  strip_tac >>
  irule run_inst_seq_preserves_field >>
  qexists_tac `emitted_insts sa sb` >> simp[] >>
  `EVERY (\i. i.inst_opcode = RETURNDATASIZE \/ fresh_write_op i.inst_opcode)
    (emitted_insts sa sb)` by
    (qpat_x_assum `run_inst_seq _ _ = _` kall_tac >>
     qpat_x_assum `comp_bind _ _ _ = _` mp_tac >>
     simp[compile_select_def, comp_bind_def, emit_op_def, fresh_var_def,
          fresh_id_def, comp_ignore_bind_def, comp_return_def, emit_def] >>
     strip_tac >> gvs[] >>
     simp[emitted_insts_def] >>
     pure_rewrite_tac [GSYM APPEND_ASSOC] >>
     pure_rewrite_tac [rich_listTheory.DROP_LENGTH_APPEND] >>
     simp[mk_inst_def, fresh_write_op_def]) >>
  rpt strip_tac >> fs[EVERY_MEM] >>
  first_x_assum drule >> strip_tac
  >- (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
      asm_simp_tac bool_ss [step_inst_base_opcode_eqs] >>
      simp[exec_read0_def, bind_outputs_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[update_var_def]) >>
  drule_all step_fresh_write_op >> strip_tac >>
  qpat_x_assum `_ = _ with vs_vars := _` SUBST1_TAC >> simp[]
QED

Theorem raw_call_size_run[local]:
  emit_op RETURNDATASIZE [] sa = (v,sb) /\ fresh_vars_wrt sa s ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand v t = SOME (n2w (LENGTH s.vs_returndata)) /\
    same_blocks sa sb /\ fresh_vars_wrt sb t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w)
Proof
  strip_tac >>
  mp_tac (Q.ISPECL [`RETURNDATASIZE`,
    `\s:venom_state. n2w (LENGTH s.vs_returndata):bytes32`]
    emit_op_read0_correct) >>
  disch_then drule >> disch_then (qspec_then `s` mp_tac) >> simp[] >>
  impl_tac
  >- simp[Once step_inst_base_def, mk_inst_def, exec_read0_def, bind_outputs_def] >>
  metis_tac[]
QED

Theorem raw_call_length_prefix_run[local]:
  (do len <- emit_op RETURNDATASIZE [];
      cmp <- emit_op LT [len;Lit (n2w cap)];
      compile_select cmp len (Lit (n2w cap)) od) sa = (capped,sb) /\
  fresh_vars_wrt sa s /\ cap < dimword (:256) /\
  LENGTH s.vs_returndata < dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand capped t = SOME (n2w (MIN (LENGTH s.vs_returndata) cap)) /\
    fresh_vars_wrt sb t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t with vs_vars := FEMPTY = s with vs_vars := FEMPTY
Proof
  strip_tac >>
  qpat_x_assum `comp_bind _ _ _ = _` mp_tac >>
  simp[comp_bind_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >> strip_tac >> gvs[] >>
  rename1 `emit_op RETURNDATASIZE [] sa = (len,sc1)` >>
  rename1 `emit_op LT [len;Lit (n2w cap)] sc1 = (cmp,sc2)` >>
  drule_all raw_call_size_run >> strip_tac >>
  drule emit_op_LT_correct_mem >>
  disch_then drule >>
  simp[eval_operand_def] >>
  strip_tac >>
  drule compile_select_correct >>
  disch_then drule >>
  simp[eval_operand_def] >>
  disch_then (qspecl_then [`n2w (LENGTH s.vs_returndata):bytes32`,
    `LENGTH s.vs_returndata < cap`] mp_tac) >>
  impl_tac >- (simp[] >> first_x_assum irule >> simp[]) >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  `run_inst_seq (emitted_insts sa sb) s = OK u` by
    (irule run_emitted_compose3 >>
     qexistsl_tac [`t`,`ss'`,`sc1`,`sc2`] >> simp[] >>
     imp_res_tac emit_op_extends >>
     imp_res_tac compile_select_extends >> gvs[]) >>
  qexists_tac `u` >> simp[] >> conj_tac
  >- (Cases_on `LENGTH s.vs_returndata < cap` >> simp[arithmeticTheory.MIN_DEF]) >>
  irule raw_call_length_prefix_frame >>
  goal_assum (drule_at Any) >>
  qexistsl_tac [`cap`,`capped`] >> simp[comp_bind_def]
QED

Theorem raw_call_success_run[local]:
  (do len <- emit_op RETURNDATASIZE [];
      cmp <- emit_op LT [len;Lit (n2w cap)];
      capped <- compile_select cmp len (Lit (n2w cap));
      emit_void MSTORE [ov;capped]; return ov od) sa = (result,sb) /\
  fresh_vars_wrt sa s /\ eval_operand ov s = SOME addr /\
  cap < dimword (:256) /\ LENGTH s.vs_returndata < dimword (:256) ==>
  ?t u. run_inst_seq (emitted_insts sa sb) s = OK t /\
    result = ov /\ eval_operand result t = SOME addr /\
    fresh_vars_wrt sb t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t = mstore (w2n addr) (n2w (MIN (LENGTH s.vs_returndata) cap)) u /\
    u with vs_vars := FEMPTY = s with vs_vars := FEMPTY
Proof
  strip_tac >>
  qpat_x_assum `comp_bind _ _ _ = _` mp_tac >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `emit_op RETURNDATASIZE [] sa = (len,sc1)` >>
  rename1 `emit_op LT [len;Lit (n2w cap)] sc1 = (cmp,sc2)` >>
  rename1 `compile_select cmp len (Lit (n2w cap)) sc2 = (capped,sc3)` >>
  ` (do len <- emit_op RETURNDATASIZE [];
        cmp <- emit_op LT [len;Lit (n2w cap)];
        compile_select cmp len (Lit (n2w cap)) od) sa = (capped,sc3)` by
    simp[comp_bind_def] >>
  drule_all raw_call_length_prefix_run >> strip_tac >>
  `eval_operand ov t = SOME addr` by (first_x_assum irule >> simp[]) >>
  drule emit_void_MSTORE_correct >>
  disch_then (qspecl_then [`addr`,
    `n2w (MIN (LENGTH s.vs_returndata) cap):bytes32`,`t`] mp_tac) >>
  simp[] >> strip_tac >>
  qexists_tac `t` >> simp[] >>
  irule run_emitted_compose2 >> qexistsl_tac [`t`,`sc3`] >> simp[] >>
  imp_res_tac emit_op_extends >> imp_res_tac compile_select_extends >>
  imp_res_tac emit_void_extends >>
  `sc2.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sc2` by
    (irule emit_extends_trans >> qexists_tac `sc1` >> simp[]) >>
  conj_tac
  >- (irule emit_extends_trans >> qexists_tac `sc2` >> simp[]) >>
  simp[]
QED

Theorem raw_call_zero_success_run[local]:
  comp_return (Lit 0w) sa = (result,sb) ==>
  result = Lit 0w /\ sb = sa /\
  run_inst_seq (emitted_insts sa sb) s = OK s /\
  eval_operand result s = SOME 0w
Proof
  simp[comp_return_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def, run_inst_seq_def, eval_operand_def]
QED

(* Enter either finish block from the JNZ, without linearising the CFG. *)
Theorem raw_call_jnz_frag[local]:
  emit_inst JNZ [ok;Label kl;Label fl] [] sa = ((),sj) /\
  new_block fl sj = (old,sf) /\ cs_extends sf sb /\
  cs_extends sa bs /\ cs_extends bs sb /\
  bs.cs_current_bb = (if success then kl else fl) /\
  bs.cs_current_insts = [] /\ eval_operand ok t = SOME (bool_to_word success) /\
  frag_exec ctx bs sb (\s. s = jump_to bs.cs_current_bb t) Q R ==>
  frag_exec ctx sa sb (\s. s = t) Q R
Proof
  strip_tac >> pure_rewrite_tac[frag_exec_def] >> BETA_TAC >> rpt strip_tac >>
  qpat_x_assum `s = t` SUBST_ALL_TAC >>
  `?bb. lookup_block sa.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb (LENGTH sa.cs_current_insts) =
      SOME (mk_inst sa.cs_next_id JNZ [ok;Label kl;Label fl] [])` by
    (irule fn_has_code_emit_new_block >>
     goal_assum (drule_at (Pat `fn_has_code`)) >>
     goal_assum (drule_at (Pat `emit_inst`)) >>
     goal_assum (drule_at (Pat `new_block`)) >> simp[cs_extends_refl]) >>
  `step_inst_base (mk_inst sa.cs_next_id JNZ [ok;Label kl;Label fl] []) t =
     OK (jump_to bs.cs_current_bb t)` by
    (simp[mk_inst_def] >> drule venomExecProofsTheory.step_jnz_behavior >>
     disch_then (fn th => simp[th]) >>
     Cases_on `success` >> simp[bool_to_word_def]) >>
  irule frag_exec_enter >> conj_tac >- simp[] >>
  qexistsl_tac [`\s. s = jump_to bs.cs_current_bb t`,
    `bb`,`mk_inst sa.cs_next_id JNZ [ok;Label kl;Label fl] []`,`bs`] >>
  simp[mk_inst_def, is_terminator_def] >>
  irule fn_has_code_mid >> conj_tac >- simp[] >>
  goal_assum (drule_at (Pat `fn_has_code`)) >> simp[cs_extends_refl]
QED

Theorem raw_call_success_code[local]:
  (do len <- emit_op RETURNDATASIZE [];
      cmp <- emit_op LT [len;Lit (n2w cap)];
      capped <- compile_select cmp len (Lit (n2w cap));
      emit_void MSTORE [ov;capped]; return ov od) sa = (result,sb) ==>
  same_blocks sa sb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)
Proof
  simp[compile_select_def, comp_bind_def, emit_op_def, fresh_var_def,
       fresh_id_def, comp_ignore_bind_def, comp_return_def, emit_def,
       emit_void_def] >> strip_tac >> gvs[] >>
  simp[same_blocks_def, emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  pure_rewrite_tac [rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[mk_inst_def, is_terminator_def]
QED

Theorem raw_call_success_frag[local]:
  (do len <- emit_op RETURNDATASIZE [];
      cmp <- emit_op LT [len;Lit (n2w cap)];
      capped <- compile_select cmp len (Lit (n2w cap));
      emit_void MSTORE [ov;capped]; return ov od) sa = (result,sb) /\
  fresh_vars_wrt sa s /\ eval_operand ov s = SOME addr /\
  cap < dimword (:256) /\ LENGTH s.vs_returndata < dimword (:256) ==>
  frag_exec ctx sa sb (\t. t = s)
    (\t. ?u. result = ov /\ eval_operand result t = SOME addr /\
       fresh_vars_wrt sb t /\
       (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
       t = (mstore (w2n addr) (n2w (MIN (LENGTH s.vs_returndata) cap)) u)
         with vs_inst_idx := LENGTH sb.cs_current_insts /\
       u with vs_vars := FEMPTY = s with vs_vars := FEMPTY) R
Proof
  strip_tac >> drule raw_call_success_code >> strip_tac >>
  irule frag_exec_run_inst_seq >>
  fs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND] >>
  rpt strip_tac >> gvs[] >>
  drule_all raw_call_success_run >> strip_tac >> disj1_tac >>
  goal_assum (drule_at Any) >> qexists_tac `u` >>
  gvs[eval_operand_def, lookup_var_def, fresh_vars_wrt_def]
QED

Theorem raw_call_revert_frag[local]:
  emit_inst REVERT [dst;size_op] [] sa = ((),sb) /\
  eval_operand dst s = SOME addr /\ eval_operand size_op s = SOME szw /\
  R (Abort Revert_abort
    (revert_state (set_returndata (mem_bytes_at (w2n addr) (w2n szw) s.vs_memory) s))) ==>
  frag_exec ctx sa sb (\t. t = s) Q R
Proof
  strip_tac >>
  `sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id REVERT [dst;size_op] []]` by
    (qpat_x_assum `emit_inst _ _ _ _ = _` mp_tac >>
     simp[emit_inst_def, comp_bind_def, fresh_id_def, emit_def] >>
     rpt strip_tac >> gvs[]) >>
  irule frag_exec_step_abort >> simp[] >>
  qexists_tac `0` >>
  simp[step_inst_non_invoke, mk_inst_def, Once step_inst_base_def,
       GSYM mem_bytes_at_def]
QED

(* RETURNDATASIZE only binds a fresh, non-local variable. *)
Theorem raw_call_size_state[local]:
  emit_op RETURNDATASIZE [] sa = (v,sb) /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  stmt_state_rel ctx func cenv cx es t /\
  t.vs_returndata = s.vs_returndata
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  gvs[run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
      exec_read0_def, bind_outputs_def] >>
  irule stmt_state_rel_update_var >> simp[] >>
  irule local_ptrs_reserved_fresh >> qexists_tac `sa` >> simp[]
QED

Theorem raw_call_failure_prefix[local]:
  emit_op RETURNDATASIZE [] sa = (rds,sb) /\
  compile_alloc_buffer 0 sb = (buf,sc) /\
  fresh_vars_wrt sa s /\ stmt_state_rel ctx func cenv cx es s /\
  local_ptrs_reserved cenv sa /\ fn_inst_ids_distinct func /\
  MEM (mk_inst sb.cs_next_id ALLOCA [Lit 0w]
    [STRING #"%" (toString sb.cs_next_var)]) (fn_insts func) ==>
  ?t u addr. run_inst_seq (emitted_insts sa sb) s = OK t /\
    run_inst_seq (emitted_insts sb sc) t = OK u /\
    eval_operand buf.buf_operand u = SOME addr /\
    eval_operand rds u = SOME (n2w (LENGTH s.vs_returndata)) /\
    u.vs_returndata = s.vs_returndata
Proof
  strip_tac >> drule_all raw_call_size_run >> strip_tac >>
  drule_all raw_call_size_state >> strip_tac >>
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[] >>
     drule emitted_insts_emit_op >> simp[]) >>
  drule literal_alloc_buffer_run >>
  disch_then (drule_at (Pat `stmt_state_rel`)) >> simp[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sb sc) t = OK u` >>
  `not_fresh_at sb (STRING #"%" (toString sa.cs_next_var))` by
    (drule emitted_insts_emit_op >> strip_tac >>
     simp[not_fresh_at_def, ASCIInumbersTheory.toString_11]) >>
  `eval_operand rds u = SOME (n2w (LENGTH s.vs_returndata))` by
    (drule emitted_insts_emit_op >> strip_tac >>
     gvs[eval_operand_def]) >>
  `u.vs_returndata = t.vs_returndata` by
    (drule loweringHaltTheory.compile_alloc_buffer_insts >> strip_tac >>
     qpat_x_assum `run_inst_seq (emitted_insts sb sc) t = OK u` mp_tac >>
     simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND,
          run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
          exec_alloca_def] >>
     Cases_on `FLOOKUP t.vs_allocas sb.cs_next_id` >>
     simp[AllCaseEqs()] >> rpt strip_tac >> gvs[update_var_def]) >>
  qexistsl_tac [`u`,`w`] >> simp[]
QED

Theorem raw_call_failure_prefix_frag[local]:
  emit_op RETURNDATASIZE [] sa = (rds,sb) /\
  compile_alloc_buffer 0 sb = (buf,sc) /\ fn_has_code sa sc func /\
  fresh_vars_wrt sa s /\ stmt_state_rel ctx func cenv cx es s /\
  local_ptrs_reserved cenv sa /\ fn_inst_ids_distinct func ==>
  frag_exec ctx sa sc (\t. t = s)
    (\u. ?addr. eval_operand buf.buf_operand u = SOME addr /\
       eval_operand rds u = SOME (n2w (LENGTH s.vs_returndata)) /\
       u.vs_returndata = s.vs_returndata) R
Proof
  strip_tac >>
  `cs_appends (emit_op RETURNDATASIZE [])` by simp[cs_appends_emit_helpers] >>
  `cs_extends sa sb /\ cs_extends sb sc` by
    (fs[cs_appends_def] >> metis_tac[loweringHaltTheory.compile_alloc_buffer_extends]) >>
  drule emit_op_extends >> strip_tac >>
  drule loweringHaltTheory.compile_alloc_buffer_insts >> strip_tac >>
  `emitted_insts sb sc =
    [mk_inst sb.cs_next_id ALLOCA [Lit 0w] [STRING #"%" (toString sb.cs_next_var)]]` by
    (pure_rewrite_tac[emitted_insts_def] >>
     qpat_assum `sc.cs_current_insts = _` (fn th => pure_rewrite_tac[th]) >>
     pure_rewrite_tac[rich_listTheory.DROP_LENGTH_APPEND] >> REFL_TAC) >>
  `fn_has_code sb sc func` by
    (irule fn_has_code_mid >> conj_tac >- simp[] >>
     goal_assum (drule_at (Pat `fn_has_code`)) >> simp[cs_extends_refl]) >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all raw_call_failure_prefix >> strip_tac >>
  `run_inst_seq (emitted_insts sa sc) s = OK u` by
    (irule run_emitted_compose2 >> qexistsl_tac [`t`,`sb`] >> simp[] >>
     imp_res_tac emit_op_extends >>
     imp_res_tac loweringHaltTheory.compile_alloc_buffer_extends >>
     simp[]) >>
  irule frag_exec_run_inst_seq >>
  conj_tac
  >- (rpt strip_tac >> gvs[] >> disj1_tac >>
      qexists_tac `u` >> simp[] >> qexists_tac `addr` >>
      gvs[eval_operand_def, lookup_var_def]) >>
  qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
  qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
  simp[contextTheory.compile_alloc_buffer_def, emit_op_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, fresh_var_def, fresh_id_def,
       emit_def] >> rpt strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[mk_inst_def, is_terminator_def, rich_listTheory.IS_PREFIX_APPEND]
QED

Theorem raw_call_failure_tail_frag[local]:
  emit_void RETURNDATACOPY [dst;Lit 0w;sz] sa = ((),sb) /\
  emit_inst REVERT [dst;sz] [] sb = ((),sc) /\
  eval_operand dst s = SOME addr /\
  eval_operand sz s = SOME (n2w (LENGTH s.vs_returndata)) /\
  LENGTH s.vs_returndata < dimword (:256) /\
  (!t. t.vs_returndata = s.vs_returndata ==> R (Abort Revert_abort t)) ==>
  frag_exec ctx sa sc (\t. t = s) Q R
Proof
  strip_tac >>
  qmatch_asmsub_abbrev_tac `eval_operand sz s = SOME sizew` >>
  qabbrev_tac `u = (write_memory_with_expansion (w2n addr) s.vs_returndata s)
    with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  `step_inst_base (mk_inst sa.cs_next_id RETURNDATACOPY [dst;Lit 0w;sz] []) s =
     OK (write_memory_with_expansion (w2n addr) s.vs_returndata s)` by
    (irule raw_call_failure_copy >> simp[Abbr `sizew`]) >>
  `frag_exec ctx sa sb (\t. t = s) (\t. t = u) R` by
    (irule frag_exec_run_inst_seq >>
     drule emit_void_extends >> strip_tac >>
     drule emitted_insts_emit_void >> strip_tac >>
     simp[same_blocks_def] >>
     conj_tac
     >- (rpt strip_tac >> gvs[] >> disj1_tac >>
         simp[run_inst_seq_def, Abbr `u`]) >>
     fs[mk_inst_def, is_terminator_def, rich_listTheory.IS_PREFIX_APPEND,
        same_blocks_def]) >>
  `frag_exec ctx sb sc (\t. t = u) Q R` by
    (irule raw_call_revert_frag >> goal_assum (drule_at (Pat `emit_inst`)) >>
     qexistsl_tac [`addr`,`sizew`] >>
     `eval_operand dst u = SOME addr /\ eval_operand sz u = SOME sizew` by
       (Cases_on `dst` >> Cases_on `sz` >>
        gvs[Abbr `u`, eval_operand_def, lookup_var_def,
            write_memory_with_expansion_def, LET_THM]) >>
     simp[] >> first_x_assum irule >>
     simp[Abbr `u`, revert_state_def, set_returndata_def,
          hash_write_memory_read_self, Abbr `sizew`,
          wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]) >>
  irule frag_exec_seq >> qexistsl_tac [`\t. t = u`,`sb`] >> simp[] >>
  metis_tac[cs_appends_emit_helpers, cs_appends_def, loweringHaltTheory.emit_inst_metadata]
QED

Theorem raw_call_failure_frag[local]:
  emit_op RETURNDATASIZE [] sa = (rds,sb) /\
  compile_alloc_buffer 0 sb = (buf,sc) /\
  emit_void RETURNDATACOPY [buf.buf_operand;Lit 0w;rds] sc = ((),sd) /\
  emit_inst REVERT [buf.buf_operand;rds] [] sd = ((),se) /\
  fn_has_code sa sc func /\ fresh_vars_wrt sa s /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  fn_inst_ids_distinct func /\ LENGTH s.vs_returndata < dimword (:256) /\
  (!t. t.vs_returndata = s.vs_returndata ==> R (Abort Revert_abort t)) ==>
  frag_exec ctx sa se (\t. t = s) Q R
Proof
  strip_tac >>
  drule_all raw_call_failure_prefix_frag >>
  disch_then (qspec_then `R` assume_tac) >>
  irule frag_exec_seq_pointwise >>
  goal_assum (drule_at (Pat `frag_exec`)) >>
  conj_tac
  >- (rpt strip_tac >> gvs[] >> irule raw_call_failure_tail_frag >>
      simp[] >> goal_assum (drule_at (Pat `emit_void`)) >>
      qexists_tac `addr` >> simp[]) >>
  `cs_appends (emit_op RETURNDATASIZE []) /\
   cs_appends (emit_void RETURNDATACOPY [buf.buf_operand;Lit 0w;rds])` by
    simp[cs_appends_emit_helpers] >>
  fs[cs_appends_def] >>
  metis_tac[loweringHaltTheory.compile_alloc_buffer_extends,
            loweringHaltTheory.emit_inst_metadata, cs_extends_trans]
QED

(* The success length store is separated from every older allocation and local. *)
Theorem raw_call_success_frame[local]:
  wb_frame cenv es st0 s0 s /\
  (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
  t = mstore (w2n addr) len u /\
  u with vs_vars := FEMPTY = s with vs_vars := FEMPTY /\
  (!aid b sz. aid < st0.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
    regions_disjoint (w2n addr) 32 b sz) /\
  (!name b sz. local_region cenv es.scopes s0 name b sz ==>
    regions_disjoint (w2n addr) 32 b sz) ==>
  wb_frame cenv es st0 s0 t
Proof
  strip_tac >>
  `u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `_ with vs_vars := _ = _` mp_tac >>
     simp[venom_state_component_equality]) >>
  `!b sz. regions_disjoint (w2n addr) 32 b sz ==>
    mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory` by
    (rpt strip_tac >>
     qpat_assum `t = _` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `u.vs_memory = s.vs_memory` (fn th => pure_rewrite_tac[GSYM th]) >>
     irule mstore_region_frame >> qexistsl_tac [`w2n addr`,`32`] >> simp[]) >>
  fs[wb_frame_def] >> conj_tac
  >- (rpt strip_tac >>
      `lookup_var x s = SOME w` by metis_tac[] >>
      qpat_x_assum `!op w. _ ==> _` (qspecl_then [`Var x`,`w`] mp_tac) >>
      simp[eval_operand_def]) >>
  conj_tac
  >- (rpt strip_tac >>
      `FLOOKUP s.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
      metis_tac[]) >>
  irule locals_kept_regions_tail >> qexists_tac `s` >> simp[] >>
  metis_tac[]
QED
(* Forget temporary variables and control positions only in finish posts. *)
Definition raw_call_finish_view_def[local]:
  raw_call_finish_view (s:venom_state) =
    s with <|vs_vars := FEMPTY; vs_prev_bb := NONE;
             vs_current_bb := ""; vs_inst_idx := 0|>
End

Theorem raw_call_finish_view_control[local]:
  raw_call_finish_view (jump_to l s) = raw_call_finish_view s /\
  raw_call_finish_view (s with vs_inst_idx := k) = raw_call_finish_view s
Proof
  simp[raw_call_finish_view_def, jump_to_def]
QED

Theorem raw_call_finish_view_fields[local]:
  (raw_call_finish_view s).vs_memory = s.vs_memory /\
  (raw_call_finish_view s).vs_allocas = s.vs_allocas /\
  (raw_call_finish_view s).vs_alloca_next = s.vs_alloca_next
Proof
  simp[raw_call_finish_view_def]
QED

(* Reconstruct allocation invariants after oracle consumption.  Unlike control
   positions, local pointer variables must be retained by this boundary. *)
Theorem raw_call_oracle_stmt_frame[local]:
  take_call_outcome target calldata value_opt es = (INL (rq,outcome),es1) /\
  es' = SND (adopt_call_outcome rq outcome es1) /\
  stmt_state_rel ctx func cenv cx es s /\ state_rel func cenv cx es' t /\
  t.vs_vars = s.vs_vars /\ t.vs_allocas = s.vs_allocas /\
  t.vs_alloca_next = s.vs_alloca_next ==>
  stmt_state_rel ctx func cenv cx es' t
Proof
  strip_tac >>
  `es'.scopes = es.scopes /\ es'.immutables = es.immutables` by
    (drule take_call_outcome_frame >>
     simp[Once evaluation_state_component_equality] >> strip_tac >>
     qpat_x_assum `es' = _` mp_tac >>
     simp[adopt_call_outcome_equation] >>
     Cases_on `outcome.co_success /\ ~rq.cr_static` >> simp[] >>
     rpt strip_tac >> gvs[]) >>
  irule stmt_state_rel_allocas_frame >>
  reverse conj_tac >- (simp[] >> qexistsl_tac [`es`,`s`] >> simp[]) >>
  irule immutable_alloca_sep_fields >>
  qexistsl_tac [`s`,`es`] >> simp[] >>
  reverse conj_tac >- fs[stmt_state_rel_def] >>
  simp[local_region_def, lookup_var_def] >> metis_tac[]
QED

Theorem raw_call_control_operands[local]:
  eval_operand a (jump_to l s) = eval_operand a s /\
  fresh_vars_wrt st (jump_to l s) = fresh_vars_wrt st s /\
  fresh_vars_wrt st (s with vs_inst_idx := k) = fresh_vars_wrt st s
Proof
  Cases_on `a` >> simp[eval_operand_def, lookup_var_def,
    jump_to_def, fresh_vars_wrt_def]
QED

Theorem raw_call_control_frame[local]:
  wb_frame cenv es st s0 (jump_to l s) = wb_frame cenv es st s0 s /\
  wb_frame cenv es st s0 (s with vs_inst_idx := k) = wb_frame cenv es st s0 s
Proof
  simp[wb_frame_def, locals_kept_def, local_region_def, lookup_var_def,
       jump_to_def]
QED

Theorem raw_call_finish_frag[local]:
  compile_raw_call_finish to_op dp dl gas_op val_op
    (if stat then StaticCall else RegularCall) cap T ov op sa = (result,sb) /\
  emit_op (if stat then STATICCALL else CALL)
    (if stat then [gas_op;to_op;dp;dl;op;Lit (n2w cap)]
     else [gas_op;to_op;val_op;dp;dl;op;Lit (n2w cap)]) sa = (ok,sc) /\
  run_inst_seq (emitted_insts sa sc) s = OK t /\
  eval_operand ok t = SOME (bool_to_word success) /\ fresh_vars_wrt sc t /\
  stmt_state_rel ctx func cenv cx es' t /\ local_ptrs_reserved cenv sa /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  cap < dimword (:256) /\ LENGTH t.vs_returndata < dimword (:256) /\
  (0 < cap ==> eval_operand ov t = SOME addr) ==>
  frag_exec ctx sa sb (\u. u = s)
    (\u. success /\ fresh_vars_wrt sb u /\
      (!a w. eval_operand a t = SOME w ==> eval_operand a u = SOME w) /\
      (if 0 < cap then result = ov /\ eval_operand result u = SOME addr /\
         raw_call_finish_view u = raw_call_finish_view
           (mstore (w2n addr) (n2w (MIN (LENGTH t.vs_returndata) cap)) t)
       else result = Lit 0w /\ eval_operand result u = SOME 0w /\
         raw_call_finish_view u = raw_call_finish_view t))
    (\r. ?u. ~success /\ r = Abort Revert_abort u /\
      u.vs_returndata = t.vs_returndata)
Proof
  strip_tac >> drule raw_call_finish_steps >> strip_tac >>
  rename1 `fresh_label "call_failed" call_end = (fl,s2)` >>
  `call_end = sc /\ success' = ok` by (Cases_on `stat` >> gvs[]) >> gvs[] >>
  qpat_x_assum `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `(case _ of RegularCall => _ | DelegateCall => _ | StaticCall => _) _ = _` kall_tac >>
  qmatch_goalsub_abbrev_tac `frag_exec ctx sa sb P Q R` >>
  `cs_extends sa s3 /\ cs_extends s3 s5 /\ cs_extends s5 s7 /\
   cs_extends s7 s9 /\ cs_extends s9 s10 /\ cs_extends s10 sb` by
    suspend "extensions" >>
  `cs_extends s3 sb` by
    (irule cs_extends_trans >> qexists_tac `s5` >> simp[] >>
     irule cs_extends_trans >> qexists_tac `s7` >> simp[] >>
     irule cs_extends_trans >> qexists_tac `s9` >> simp[] >>
     irule cs_extends_trans >> qexists_tac `s10` >> simp[]) >>
  irule frag_exec_seq >>
  qexistsl_tac [`\u. u = t with vs_inst_idx := LENGTH s3.cs_current_insts`,`s3`] >>
  simp[] >> conj_tac >- suspend "entry" >> suspend "branches"
QED

Resume raw_call_finish_frag[extensions]:
  `cs_extends s10 sb` by
    (Cases_on `0 < cap` >> gvs[comp_return_def]
     >- (drule raw_call_success_code >> strip_tac >>
         irule cs_extends_same_block >>
         gvs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND]) >>
     simp[cs_extends_refl]) >>
  imp_res_tac cs_extends_fresh_label >>
  imp_res_tac cs_extends_new_block >> imp_res_tac cs_extends_emit_inst >>
  imp_res_tac loweringHaltTheory.compile_alloc_buffer_extends >>
  `cs_appends (emit_op (if stat then STATICCALL else CALL)
     (if stat then [gas_op;to_op;dp;dl;op;Lit (n2w cap)]
      else [gas_op;to_op;val_op;dp;dl;op;Lit (n2w cap)])) /\
   cs_appends (emit_op RETURNDATASIZE []) /\
   cs_appends (emit_void RETURNDATACOPY [buf.buf_operand;Lit 0w;rds])` by
    simp[cs_appends_emit_helpers] >>
  fs[cs_appends_def] >>
  conj_tac
  >- (irule cs_extends_trans >> qexists_tac `call_end` >> simp[] >>
      irule cs_extends_trans >> qexists_tac `s2` >> simp[]) >>
  conj_tac
  >- (irule cs_extends_trans >> qexists_tac `s4` >> simp[]) >>
  conj_tac
  >- (irule cs_extends_trans >> qexists_tac `s6` >> simp[]) >>
  irule cs_extends_trans >> qexists_tac `s8` >> simp[]
QED

Resume raw_call_finish_frag[entry]:
  imp_res_tac fresh_label_props >>
  qpat_assum `emit_op (if _ then _ else _) _ sa = _`
    (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
  qpat_assum `emit_op (if _ then _ else _) _ sa = _`
    (mp_then Any strip_assume_tac emit_op_extends) >>
  `emitted_insts sa s3 = emitted_insts sa call_end` by
    (pure_rewrite_tac[emitted_insts_def] >>
     qpat_assum `s3.cs_current_insts = _` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `s2.cs_current_insts = _` (fn th => pure_rewrite_tac[th]) >>
     REFL_TAC) >>
  irule frag_exec_run_inst_seq >>
  fs[same_blocks_def] >>
  simp[Abbr `P`, rich_listTheory.IS_PREFIX_APPEND, mk_inst_def] >>
  reverse conj_tac >- (Cases_on `stat` >> simp[is_terminator_def]) >>
  rpt strip_tac >> gvs[] >> disj1_tac >> qexists_tac `t` >> fs[mk_inst_def]
QED

Resume raw_call_finish_frag[branches]:
  irule raw_call_jnz_frag >>
  goal_assum (drule_at (Pat `emit_inst`)) >>
  goal_assum (drule_at (Pat `new_block`)) >>
  qexistsl_tac [`if success then s10 else s5`,`success`] >>
  `cs_extends s5 sb /\ cs_extends s3 s10` by
    (conj_tac
     >- (irule cs_extends_trans >> qexists_tac `s7` >> simp[] >>
         irule cs_extends_trans >> qexists_tac `s9` >> simp[] >>
         irule cs_extends_trans >> qexists_tac `s10` >> simp[]) >>
     irule cs_extends_trans >> qexists_tac `s5` >> simp[] >>
     irule cs_extends_trans >> qexists_tac `s7` >> simp[] >>
     irule cs_extends_trans >> qexists_tac `s9` >> simp[]) >>
  `fresh_vars_wrt s5 t /\ fresh_vars_wrt s10 t /\
   local_ptrs_reserved cenv s5` by suspend "freshness" >>
  imp_res_tac new_block_props >>
  Cases_on `success` >> simp[instIdxIndepTheory.eval_op_inst_idx]
  >- suspend "success" >> suspend "failure"
QED

Resume raw_call_finish_frag[freshness]:
  imp_res_tac fresh_label_props >>
  imp_res_tac new_block_props >>
  qspecl_then [`JNZ`,`[ok;Label kl;Label fl]`,`[]`,`s3`] mp_tac ci_mono_emit_inst >>
  qspecl_then [`RETURNDATASIZE`,`[]`,`s5`] mp_tac ci_mono_emit_op >>
  qspecl_then [`0`,`s6`] mp_tac ci_mono_compile_alloc_buffer >>
  qspecl_then [`RETURNDATACOPY`,`[buf.buf_operand;Lit 0w;rds]`,`s7`]
    mp_tac ci_mono_emit_void >>
  qspecl_then [`REVERT`,`[buf.buf_operand;rds]`,`[]`,`s8`] mp_tac ci_mono_emit_inst >>
  qspecl_then [`if stat then STATICCALL else CALL`,
    `if stat then [gas_op;to_op;dp;dl;op;Lit (n2w cap)]
     else [gas_op;to_op;val_op;dp;dl;op;Lit (n2w cap)]`,`sa`]
    mp_tac ci_mono_emit_op >>
  simp[ci_mono_def] >> rpt (disch_then strip_assume_tac) >>
  `call_end.cs_next_var <= s5.cs_next_var /\
   call_end.cs_next_var <= s10.cs_next_var /\
   sa.cs_next_var <= s5.cs_next_var` by decide_tac >>
  conj_tac >- (irule fresh_vars_wrt_mono >> qexists_tac `call_end` >> simp[]) >>
  conj_tac >- (irule fresh_vars_wrt_mono >> qexists_tac `call_end` >> simp[]) >>
  irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]
QED

Resume raw_call_finish_frag[success]:
  Cases_on `0 < cap` >> fs[]
  >- suspend "positive" >> suspend "zero"
QED

Resume raw_call_finish_frag[positive]:
  qmatch_goalsub_abbrev_tac `frag_exec ctx s10 sb (\u. u = entry) Q R` >>
  `fresh_vars_wrt s10 entry /\ eval_operand ov entry = SOME addr /\
   LENGTH entry.vs_returndata < dimword (:256)` by
    simp[Abbr `entry`, raw_call_control_operands, jump_to_def,
         instIdxIndepTheory.eval_op_inst_idx] >>
  drule_all raw_call_success_frag >>
  disch_then (qspecl_then [`ctx`,`R`] mp_tac) >>
  disch_then (mp_then Any irule frag_exec_weaken) >>
  simp[] >> rpt strip_tac >>
  `!a w. eval_operand a t = SOME w ==> eval_operand a s'' = SOME w` by
    (rpt strip_tac >> first_x_assum irule >>
     simp[Abbr `entry`, raw_call_control_operands,
          instIdxIndepTheory.eval_op_inst_idx]) >>
  simp[Abbr `Q`] >>
  qpat_x_assum `u with vs_vars := FEMPTY = _` mp_tac >>
  simp[raw_call_finish_view_def, mstore_def, Abbr `entry`, jump_to_def] >>
  simp[venom_state_component_equality]
QED

Resume raw_call_finish_frag[zero]:
  fs[comp_return_def] >> gvs[] >>
  irule frag_exec_refl >>
  simp[Abbr `Q`, raw_call_control_operands,
       instIdxIndepTheory.eval_op_inst_idx,
       raw_call_finish_view_control, eval_operand_def]
QED

Resume raw_call_finish_frag[failure]:
  `cs_extends sa s5 /\ cs_extends s7 sb /\ cs_extends s5 s9 /\
   cs_extends s9 sb` by
    (conj_tac >- (irule cs_extends_trans >> qexists_tac `s3` >> simp[]) >>
     conj_tac >- (irule cs_extends_trans >> qexists_tac `s9` >> simp[] >>
                  irule cs_extends_trans >> qexists_tac `s10` >> simp[]) >>
     conj_tac >- (irule cs_extends_trans >> qexists_tac `s7` >> simp[]) >>
     irule cs_extends_trans >> qexists_tac `s10` >> simp[]) >>
  `fn_has_code s5 s7 func` by
    (irule fn_has_code_mid >> simp[] >> qexistsl_tac [`sb`,`sa`] >> simp[]) >>
  qmatch_goalsub_abbrev_tac `frag_exec ctx s5 sb (\u. u = entry) Q R` >>
  `fresh_vars_wrt s5 entry /\ stmt_state_rel ctx func cenv cx es' entry /\
   LENGTH entry.vs_returndata < dimword (:256)` by
    simp[Abbr `entry`, raw_call_control_operands,
         stmt_state_rel_jump_to, stmt_state_rel_inst_idx, jump_to_def] >>
  irule frag_exec_exit_prefix >> qexists_tac `s9` >> simp[] >>
  irule raw_call_failure_frag >>
  simp[Abbr `R`, Abbr `entry`, jump_to_def] >>
  qexistsl_tac [`cenv`,`cx`,`es'`,`func`] >>
  simp[stmt_state_rel_jump_to, stmt_state_rel_inst_idx] >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ (jump_to _ _)` mp_tac >>
  simp[jump_to_def]
QED

Finalise raw_call_finish_frag

Theorem raw_call_finish_frame[local]:
  wb_frame cenv es st0 s0 t /\
  (!a w. eval_operand a t = SOME w ==> eval_operand a u = SOME w) /\
  (if 0 < cap then
     raw_call_finish_view u = raw_call_finish_view (mstore (w2n addr) len t)
   else raw_call_finish_view u = raw_call_finish_view t) /\
  (0 < cap ==>
    (!aid b sz. aid < st0.cs_next_id /\
      FLOOKUP t.vs_allocas aid = SOME (b,sz) ==>
      regions_disjoint (w2n addr) 32 b sz) /\
    (!name b sz. local_region cenv es.scopes s0 name b sz ==>
      regions_disjoint (w2n addr) 32 b sz)) ==>
  wb_frame cenv es st0 s0 u
Proof
  strip_tac >>
  `u.vs_allocas = t.vs_allocas /\
   (!b sz. (0 < cap ==> regions_disjoint (w2n addr) 32 b sz) ==>
     mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz t.vs_memory)` by
    (Cases_on `0 < cap` >> fs[] >>
     qpat_x_assum `raw_call_finish_view _ = _` mp_tac >>
     simp[raw_call_finish_view_def, venom_state_component_equality] >>
     strip_tac >> simp[] >> rpt strip_tac >>
     irule mstore_region_frame >> qexistsl_tac [`w2n addr`,`32`] >> simp[]) >>
  fs[wb_frame_def] >> conj_tac
  >- (rpt strip_tac >>
      `lookup_var x t = SOME w` by metis_tac[] >>
      qpat_x_assum `!a w. _ ==> _` (qspecl_then [`Var x`,`w`] mp_tac) >>
      simp[eval_operand_def]) >>
  conj_tac
  >- (rpt strip_tac >>
      `FLOOKUP t.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
      metis_tac[]) >>
  irule locals_kept_regions_tail >> qexists_tac `t` >> simp[] >>
  metis_tac[]
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
