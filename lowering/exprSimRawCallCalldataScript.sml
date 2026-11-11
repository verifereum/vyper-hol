(*
 * Expression simulation: raw_call of msg.data (#636, Calls row 3)
 *
 * raw_call(to, msg.data, [value=], [gas=], [max_outsize=],
 * [is_static_call=], [revert_on_failure=]) lowers (compile_call's
 * RawCallCalldataTarget clause) to the address with lower_value, the
 * value= and gas= keyword operands in source order, GAS without gas=, the
 * output buffer (compile_raw_call_outbuf), a copy of all calldata into a
 * fresh DALLOCA region at vs_fmp (compile_msg_data_to_memory), the call
 * (compile_raw_call_finish), and SETFMP [data_ptr], which gives vs_fmp
 * back.  stmt_state_rel's fmp_room puts the DALLOCA region above every
 * ALLOCA allocation.
 * In oracle mode a non-delegate source raw_call takes the same outcome as
 * the lowered CALL/STATICCALL (eval_raw_call's take_call_outcome and
 * adopt_call_outcome; extCallOracleStep's exec_ext_call_oracle_step).
 * expr_sim_pre and expr_body_pre exclude delegate raw_calls
 * (~expr_has_evm_run); both revert_on_failure modes are in scope.
 *
 * TOP-LEVEL:
 *   compile_raw_call_calldata_case — its expr_sim_case and expr_vv_case
 *     from its operands' exprs_case, for compile_expr_sim and the body
 *     simulation
 *)

Theory exprSimRawCallCalldata
Ancestors
  exprSimHashBoundary
  exprSimSource exprSimHypsDefs exprSimDefs exprSimStack exprSimProps
  gasSummary gasSummaryCompose gasOutcome gasExemptCert
  fragGasMode fragGasPath fragGasSeq fragGasSeqAbort rawCallFragPath gasContext
  exprSimECArith recursiveLengthPrefix allocLimits loweringPosts vyperTypeExtCallSoundness vyperTypeEvalSoundness
  list pair vyperMisc fragExec loweringSlice exprSimHyps exprSimWordArgs
  exprSimPrecompiles exprSimOperators exprSimOperands exprSimAccounts
  extCallOracleStep exprCallbackContracts exprCallBounds exprLowering
  exprLoweringProps emitHelper compileEnv loweringStateRelDefs localPtrsProps valueEncoding valueEncodingDefs valueEncodingProps
  vyperAST vyperInterpreter vyperState vyperValue vyperTyping
  vyperTypeSystem vyperTypeCallGraph vyperCallOutcome extCallOracle
  vyperRuntimeAccounts vyperTypeInvariants vyperEvalExprPreservesScopesDom
  venomExecSemantics venomInst venomState exprSimSend builtinSystem context
  venomMemProps exprSimHash venomExecProps emitHelperProps
  supportedExprTraverse exprSimAlloc exprSimBuffer builtinProps varsExt exprSafeOperand valueCopy
Libs
  pairLib

(* Every precompile that answers returns at most two 32-byte words. *)
Theorem precompile_result_length:
  precompile_result target input = SOME (SOME bs) ==> LENGTH bs <= 64
Proof
  simp[precompile_result_def] >>
  Cases_on `target = 1w`
  >- (simp[] >> Cases_on `ecrecover
        (word_of_bytes T 0w (take_pad_0 32 input))
        (num_of_be_bytes (take_pad_0 32 (DROP 32 input)))
        (num_of_be_bytes (take_pad_0 32 (DROP 64 input)))
        (num_of_be_bytes (take_pad_0 32 (DROP 96 input)))` >>
      simp[listTheory.PAD_LEFT, byteTheory.LENGTH_word_to_bytes,
           fcpLib.INDEX_CONV ``dimindex(:160)``] >> strip_tac >>
      gvs[fcpLib.INDEX_CONV ``dimindex(:160)``]) >>
  Cases_on `target = 2w`
  >- (simp[byteTheory.LENGTH_word_to_bytes] >> strip_tac >> gvs[]) >>
  Cases_on `target = 6w`
  >- (simp[] >>
      Cases_on `vfmExecution$ecadd
        (num_of_be_bytes (take_pad_0 32 input),
         num_of_be_bytes (take_pad_0 32 (DROP 32 input)))
        (num_of_be_bytes (take_pad_0 32 (DROP 64 input)),
         num_of_be_bytes (take_pad_0 32 (DROP 96 input)))` >> simp[] >>
      rename1 `_ = SOME xy` >> PairCases_on `xy` >>
      drule ecadd_success_bounds >> strip_tac >>
      simp[padded_num_to_be_bytes_word32, byteTheory.LENGTH_word_to_bytes,
           fcpLib.INDEX_CONV ``dimindex(:256)``] >>
      strip_tac >> gvs[byteTheory.LENGTH_word_to_bytes]) >>
  Cases_on `target = 7w` >> simp[] >>
  Cases_on `vfmExecution$ecmul
    (num_of_be_bytes (take_pad_0 32 input),
     num_of_be_bytes (take_pad_0 32 (DROP 32 input)))
    (num_of_be_bytes (take_pad_0 32 (DROP 64 input)))` >> simp[] >>
  rename1 `_ = SOME xy` >> PairCases_on `xy` >>
  drule ecmul_success_bounds >> strip_tac >>
  simp[padded_num_to_be_bytes_word32, byteTheory.LENGTH_word_to_bytes,
       fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  strip_tac >> gvs[byteTheory.LENGTH_word_to_bytes]
QED

(* PORT NOTES (facts met on earlier ports to the counted judgments):
   - `do r <- eval_expr cx e; read_result cx r od` is `bind ... (\r. read_result
     cx r)`, not syntactically `bind ... (read_result cx)` as in expr_sim_def
     and gas_admissible; lemmas stated in do-form need
     `CONV_RULE (DEPTH_CONV ETA_CONV)` before `drule`.
   - gas_marked_exec_bind_normal composes an operand and a continuation; apply
     it forward (drule_all) after splitting the continuation's gas_summary_at:
     the middle state and value are not in its conclusion.
   - gas_marked_exec_bind_normal and the gas_exempt_cert bind rules hand the
     continuation `mid with gas_obs := []`; expr_sim_inv_gas_obs [simp] makes
     that free for expr_sim_inv.
   - A straight-line run becomes a counted path by tuple_run_inst_seq_gas_path,
     exprSimHash.hash_run_path / hash_abort_path, run_inst_seq_abort_zero_path;
     their conclusions are `!ctx. ...`.
   - step_GAS on [] readings: gvs[update_var_def, venom_state_component_equality].
   - Expression-precondition lemmas now also need supported_expr_exists_def and
     expr_abi_decode_target_root_def.
   - An operand exemption certificate lifts over the whole call by
     gas_exempt_cert_error_values (see send_exempt_cert in the reference copy
     of exprSimSend). *)

(* Why it holds (a reading, not a plan): expr_sim's stmt_state_rel carries
   fmp_room, so [vs_fmp, vs_fmp + len) is above vs_alloca_next and misses
   every ALLOCA region, live local and constructor immutable.  DALLOCA puts
   the old vs_fmp in data_ptr and SETFMP [data_ptr] gives it back, so
   fmp_room holds at the end; the bump itself may wrap, but nothing reads
   vs_fmp before the SETFMP.  The source sends cx.txn.calldata, which
   call_ctx_rel equates with cc_calldata, and context_well_typed bounds its
   length below 2 ** 256, so CALLDATASIZE/CALLDATACOPY give exactly those
   bytes at w2n data_ptr. *)

(* The temporary allocation is deliberately described without fmp_room:
   its bumped pointer can wrap, while the copy uses natural offsets. *)
Theorem calldata_memory_insts[local]:
  !sa ptr len sb. compile_msg_data_to_memory sa = ((ptr,len),sb) ==>
  ptr = Var ("%" ++ toString (sa.cs_next_var + 1)) /\
  len = Var ("%" ++ toString sa.cs_next_var) /\
  emitted_insts sa sb =
    [mk_inst sa.cs_next_id CALLDATASIZE [] ["%" ++ toString sa.cs_next_var];
     mk_inst (sa.cs_next_id + 1) DALLOCA
       [Var ("%" ++ toString sa.cs_next_var)]
       ["%" ++ toString (sa.cs_next_var + 1)];
     mk_inst (sa.cs_next_id + 2) CALLDATACOPY
       [Var ("%" ++ toString (sa.cs_next_var + 1)); Lit 0w;
        Var ("%" ++ toString sa.cs_next_var)] []]
Proof
  simp[compile_msg_data_to_memory_def, compile_alloc_dynamic_def,
       emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, fresh_id_def, fresh_var_def, emit_def] >>
  strip_tac >> gvs[emitted_insts_def, rich_listTheory.DROP_APPEND1]
QED

Theorem calldata_memory_run[local]:
  !sa ptr len sb s.
  compile_msg_data_to_memory sa = ((ptr,len),sb) /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand ptr t = SOME s.vs_fmp /\
    eval_operand len t = SOME (n2w (LENGTH s.vs_call_ctx.cc_calldata)) /\
    t.vs_memory = (write_memory_with_expansion (w2n s.vs_fmp)
      s.vs_call_ctx.cc_calldata s).vs_memory /\
    t.vs_fmp = s.vs_fmp + n2w (venomLayout$ceil32 (LENGTH s.vs_call_ctx.cc_calldata)) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t = s with <| vs_vars := t.vs_vars; vs_memory := t.vs_memory;
                  vs_fmp := t.vs_fmp |>
Proof
  rpt gen_tac >> strip_tac >> drule calldata_memory_insts >> strip_tac >>
  gvs[] >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_read0_def, eval_operand_def, bind_outputs_def,
       lookup_var_update_var] >>
  simp[update_var_def, lookup_var_def, not_fresh_at_def,
       wordsTheory.w2n_n2w, TAKE_APPEND1] >>
  simp[finite_mapTheory.FLOOKUP_UPDATE, wordsTheory.w2n_n2w,
       TAKE_APPEND1, write_memory_with_expansion_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem calldata_memory_readback[local]:
  !sa ptr len sb s.
  compile_msg_data_to_memory sa = ((ptr,len),sb) /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand ptr t = SOME s.vs_fmp /\
    eval_operand len t = SOME (n2w (LENGTH s.vs_call_ctx.cc_calldata)) /\
    read_memory (w2n s.vs_fmp) (LENGTH s.vs_call_ctx.cc_calldata) t =
      s.vs_call_ctx.cc_calldata /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_call_ctx = s.vs_call_ctx /\
    (!off n. off + n <= w2n s.vs_fmp ==>
      mem_bytes_at off n t.vs_memory = mem_bytes_at off n s.vs_memory)
Proof
  rpt strip_tac >> drule_all calldata_memory_run >> strip_tac >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
   t.vs_call_ctx = s.vs_call_ctx` by
    (qpat_x_assum `t = s with <| vs_vars := _; vs_memory := _; vs_fmp := _ |>`
       SUBST1_TAC >> simp[]) >>
  qexists_tac `t` >> simp[] >>
  conj_tac
  >- simp[read_memory_def, GSYM mem_bytes_at_def, hash_write_memory_read_self] >>
  rpt strip_tac >> irule hash_write_memory_disjoint >> simp[]
QED

Theorem calldata_memory_frontier[local]:
  !ctx func s.
  fmp_room ctx func s /\
  EXISTS (\inst. inst.inst_opcode = DALLOCA) (fn_insts func) ==>
  s.vs_alloca_next <= w2n s.vs_fmp
Proof
  simp[fmp_room_def] >> rpt strip_tac >>
  qpat_x_assum `_ ==> _` mp_tac >> simp[] >> decide_tac
QED

Theorem calldata_memory_locals[local]:
  !sa ptr len sb s func cenv scopes.
  compile_msg_data_to_memory sa = ((ptr,len),sb) /\
  LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_rel func cenv scopes s /\
  s.vs_alloca_next <= w2n s.vs_fmp ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    local_ptrs_rel func cenv scopes t /\
    eval_operand ptr t = SOME s.vs_fmp /\
    eval_operand len t = SOME (n2w (LENGTH s.vs_call_ctx.cc_calldata)) /\
    read_memory (w2n s.vs_fmp) (LENGTH s.vs_call_ctx.cc_calldata) t =
      s.vs_call_ctx.cc_calldata
Proof
  rpt strip_tac >> drule_all calldata_memory_readback >> strip_tac >>
  qexists_tac `t` >> simp[] >>
  irule local_ptrs_rel_mem_agree >> qexists_tac `s` >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> sym_tac >> first_x_assum irule >>
      qpat_x_assum `local_ptrs_rel _ _ _ _` mp_tac >>
      gvs[local_region_def, local_ptrs_rel_def] >>
      metis_tac[arithmeticTheory.LESS_EQ_TRANS, optionTheory.SOME_11]) >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `!x. not_fresh_at sa x ==> _` (qspec_then `p` mp_tac) >>
  gvs[local_ptrs_reserved_def] >> metis_tac[]
QED

Theorem calldata_memory_restore_fmp[local]:
  !ctx func s t op id.
  fmp_room ctx func s /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  eval_operand op t = SOME s.vs_fmp ==>
  step_inst_base (mk_inst id SETFMP [op] []) t =
    OK (t with vs_fmp := s.vs_fmp) /\
  fmp_room ctx func (t with vs_fmp := s.vs_fmp)
Proof
  rpt strip_tac
  >- simp[step_inst_base_opcode_eqs, mk_inst_def] >>
  irule fmp_room_fields >> qexists_tac `s` >> simp[]
QED

(* ===== Legal source shape ===== *)
Theorem calldata_call_pre[local]:
  !cenv cx env ann flags args dflt es.
  expr_body_pre cenv cx env
    (Call ann (RawCallCalldataTarget flags) args dflt) es ==>
  ?addr kws. args = addr::kws /\ dflt = NONE /\
    ann = raw_call_return_type flags /\
    expr_type addr = BaseT AddressT /\
    well_typed_exprs env args /\ raw_call_kws_ok flags kws /\
    LENGTH kws = LENGTH flags.rcf_kws /\
    flags.rcf_max_outsize < dimword (:256) /\
    ~flags.rcf_is_delegate
Proof
  rpt gen_tac >>
  simp[expr_body_pre_def, well_typed_expr_def,
       expr_has_evm_run_def, supported_expr_exists_def, expr_evm_run_root_def] >>
  strip_tac >> Cases_on `args` >> gvs[]
QED

Theorem calldata_call_compile[local]:
  !cenv ty ann flags addr kws dflt sa vv sb.
  compile_expr cenv ty
    (Call ann (RawCallCalldataTarget flags) (addr::kws) dflt) sa = (vv,sb) ==>
  ?addr_op s1 value_opt gas_opt default_opt s2 gas_op s3
    out_val out_ptr s4 data_ptr data_len s5 result_op s6.
    lower_value compile_expr cenv (BaseT AddressT) addr sa = (addr_op,s1) /\
    compile_ext_call_kwargs compile_expr cenv NoneT flags.rcf_kws kws s1 =
      ((value_opt,gas_opt,default_opt),s2) /\
    (case gas_opt of SOME g => (g,s2) | NONE => emit_op GAS [] s2) = (gas_op,s3) /\
    compile_raw_call_outbuf flags.rcf_max_outsize s3 = ((out_val,out_ptr),s4) /\
    compile_msg_data_to_memory s4 = ((data_ptr,data_len),s5) /\
    compile_raw_call_finish addr_op data_ptr data_len gas_op
      (case value_opt of SOME v => v | NONE => Lit 0w)
      (if flags.rcf_is_delegate then DelegateCall
       else if flags.rcf_is_static then StaticCall else RegularCall)
      flags.rcf_max_outsize flags.rcf_revert_on_failure out_val out_ptr s5 =
      (result_op,s6) /\
    emit_void SETFMP [data_ptr] s6 = ((),sb) /\
    vv = (if flags.rcf_max_outsize = 0 then StackValue ann result_op
          else LocatedValue ann (mk_ptr result_op LocMemory))
Proof
  rpt gen_tac >> simp[compile_expr_call, compile_call_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  Cases_on `flags.rcf_max_outsize = 0` >> gvs[]
QED

Theorem calldata_call_eval[local]:
  !cx ann flags args dflt es es1 to_v target vals amount.
  eval_exprs cx args es = (INL (to_v::vals),es1) /\
  dest_AddressV to_v = SOME target /\
  LENGTH vals = LENGTH flags.rcf_kws /\
  raw_call_value flags.rcf_kws vals = SOME amount ==>
  eval_expr cx (Call ann (RawCallCalldataTarget flags) args dflt) es =
    eval_raw_call cx flags target cx.txn.calldata amount
      (forwarded_gas default_evm_gas_limit
        (ext_call_kwarg EKGas flags.rcf_kws vals)) es1
Proof
  rpt strip_tac >> simp[Once evaluate_def] >>
  simp[bind_def, ignore_bind_def, type_check_def, assert_def,
       lift_option_type_def, vyperStateTheory.return_def]
QED

Theorem calldata_call_operand_exit[local]:
  !cx ann flags args dflt es es' exc.
  eval_exprs cx args es = (INR exc,es') ==>
  eval_expr cx (Call ann (RawCallCalldataTarget flags) args dflt) es =
    (INR exc,es')
Proof
  rpt strip_tac >> simp[Once evaluate_def] >> simp[bind_def]
QED

Theorem calldata_call_action[local]:
  eval_expr cx (Call ann (RawCallCalldataTarget flags) args dflt) =
  do
    vs <- eval_exprs cx args;
    type_check (LENGTH vs = LENGTH flags.rcf_kws + 1) "raw_call calldata args";
    target_addr <- lift_option_type (dest_AddressV (HD vs)) "raw_call target";
    amount <- lift_option_type (raw_call_value flags.rcf_kws (DROP 1 vs))
                "raw_call value";
    eval_raw_call cx flags target_addr cx.txn.calldata amount
      (forwarded_gas default_evm_gas_limit
        (ext_call_kwarg EKGas flags.rcf_kws (DROP 1 vs)))
  od
Proof
  simp[FUN_EQ_THM, Once evaluate_def]
QED

Theorem raw_call_typed_outcome:
  !target data vo es.
  IS_SOME es.outcomes /\ outcomes_accounts_typed es.outcomes /\
  accounts_runtime_well_typed es.accounts ==>
  ?rq outcome es1. take_call_outcome target data vo es =
    (INL (rq,outcome),es1)
Proof
  rpt strip_tac >>
  `FST (take_call_outcome target data vo es) <>
    INR (Error (RuntimeError "call outcome accounts"))` by
    metis_tac[take_call_outcome_typed] >>
  Cases_on `es.outcomes` >> gvs[] >>
  qpat_x_assum `FST _ <> _` mp_tac >>
  simp[take_call_outcome_def, take_request_outcome_def] >> pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[]
QED

Theorem calldata_frame_value_state_rel[local]:
  state_rel func cenv cx es s ==>
  frame_call_value cx vo es = (INL vo, es)
Proof
  simp[state_rel_def, frame_call_value_def, vyperStateTheory.return_def]
QED

Theorem raw_call_oracle_result:
  !cx flags target data amount gas es es1 es2 rq outcome.
  ~cx.txn.is_static /\ ~flags.rcf_is_delegate /\
  (flags.rcf_is_static ==> amount = 0) /\ IS_SOME es.outcomes /\
  take_call_outcome target data
    (if flags.rcf_is_static then NONE else SOME amount) es =
      (INL (rq,outcome),es1) /\
  adopt_call_outcome rq outcome es1 = (INL (),es2) ==>
  eval_raw_call cx flags target data amount gas es =
    (if flags.rcf_revert_on_failure /\ ~call_outcome_success outcome then
       (INR (Error (RevertData (call_outcome_return_data outcome))), es2)
     else
       (INL (Value
         (if flags.rcf_revert_on_failure then
            if flags.rcf_max_outsize = 0 then NoneV
            else BytesV (TAKE flags.rcf_max_outsize
                         (call_outcome_return_data outcome))
          else if flags.rcf_max_outsize = 0 then
            BoolV (call_outcome_success outcome)
          else ArrayV (TupleV [BoolV (call_outcome_success outcome);
            BytesV (TAKE flags.rcf_max_outsize
                    (call_outcome_return_data outcome))]))), es2))
Proof
  rpt strip_tac >>
  simp[eval_raw_call_def, frame_call_value_def, bind_def, ignore_bind_def,
       type_check_def, assert_def, vyperStateTheory.return_def, raise_def] >>
  Cases_on `flags.rcf_revert_on_failure` >>
  Cases_on `call_outcome_success outcome` >>
  simp[vyperStateTheory.return_def, raise_def, COND_RATOR] >>
  Cases_on `flags.rcf_max_outsize = 0` >>
  simp[bind_def, vyperStateTheory.return_def, raise_def]
QED

(* Keyword evaluation is ordinary uint256 operand evaluation in source order;
   only the final projection into value and gas slots is special. *)
Theorem raw_call_kwargs_lower[local]:
  !ks es cenv sa.
  LENGTH ks = LENGTH es /\ ~MEM EKDefault ks /\
  EVERY (\e. expr_type e = BaseT (UintT 256)) es ==>
  compile_ext_call_kwargs compile_expr cenv NoneT ks es sa =
    let (ops,sb) = lower_word_args cenv expr_type es sa in
    ((ext_call_kwarg EKValue ks ops, ext_call_kwarg EKGas ks ops, NONE),sb)
Proof
  Induct >> Cases_on `es` >> simp[compile_ext_call_kwargs_def,
    lower_word_args_def, comp_return_def, ext_call_kwarg_def] >>
  rpt gen_tac >> strip_tac >>
  rename1 `k <> EKDefault` >>
  Cases_on `k` >> gvs[compile_ext_call_kwarg_def, comp_bind_def,
    comp_return_def, ext_call_kwarg_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  simp[comp_bind_def, comp_return_def, ext_call_kwarg_def]
QED

Theorem raw_call_kw_types[local]:
  !ks es.
    ~MEM EKDefault ks /\
    MAP expr_type es = MAP (ext_call_kw_type NoneT) ks ==>
    EVERY (\e. expr_type e = BaseT (UintT 256)) es
Proof
  Induct >> Cases_on `es` >> simp[] >> rpt strip_tac >>
  rename1 `k <> EKDefault` >> Cases_on `k` >>
  gvs[ext_call_kw_type_def]
QED

Theorem calldata_call_arg_pre[local]:
  !cenv cx env ann flags args dflt e es es'.
    expr_body_pre cenv cx env
      (Call ann (RawCallCalldataTarget flags) args dflt) es /\
    MEM e args /\ expr_sim_inv cenv cx env es' ==>
    expr_body_pre cenv cx env e es'
Proof
  rw[expr_body_pre_def, well_typed_expr_def, int_calls_expr_def,
     byte_widths_expr_def, alloc_limits_expr_def,
     supported_expr_exists_def, supported_exprs_exists_every, EXISTS_MEM] >>
  imp_res_tac int_calls_exprs_every_mem >>
  gvs[supportedExprTraverseTheory.expr_has_evm_run_thm, listTheory.EXISTS_MEM] >>
  metis_tac[exprSimSourceTheory.well_typed_exprs_member,
            exprSimSourceTheory.byte_widths_exprs_mem,
            exprSimSourceTheory.alloc_limits_exprs_mem,
            exprSimSourceTheory.call_evaluation_safe_exprs_mem]
QED

Theorem calldata_call_args_ready[local]:
  !nocalls ctx func cenv cx env ann flags args dflt es.
    expr_body_pre cenv cx env
      (Call ann (RawCallCalldataTarget flags) args dflt) es /\
    (nocalls ==> int_calls_expr
      (Call ann (RawCallCalldataTarget flags) args dflt) = []) /\
    exprs_case nocalls ctx func cenv cx args ==>
    typed_args_ready ctx func cenv cx expr_type
      (expr_sim_inv cenv cx env) args /\ wb_args_shape cenv expr_type args
Proof
  rpt gen_tac >> strip_tac >>
  drule calldata_call_pre >> strip_tac >> gvs[] >>
  `EVERY (\e. expr_type e = BaseT (UintT 256)) kws` by
    (irule raw_call_kw_types >>
     qexists_tac `flags.rcf_kws` >> gvs[raw_call_kws_ok_def]) >>
  `!e s. MEM e (addr::kws) /\ expr_sim_inv cenv cx env s ==>
     expr_body_pre cenv cx env e s /\
     (nocalls ==> int_calls_expr e = []) /\ is_word_type (expr_type e)` by
    (rpt strip_tac
     >- metis_tac[calldata_call_arg_pre]
     >- (irule int_calls_exprs_mem >> qexists_tac `addr::kws` >>
         gvs[int_calls_expr_def]) >>
     gvs[EVERY_MEM, is_word_type_def] >> metis_tac[]) >>
  conj_tac
  >- (irule typed_args_ready_of_case >> goal_assum (drule_at Any) >> simp[]) >>
  irule typed_stack_args_shape >>
  qexistsl_tac [`cx`, `env`, `es`] >> gvs[expr_body_pre_def] >> metis_tac[]
QED

Theorem calldata_call_prefix_lower[local]:
  !cenv addr kws flags sa addr_op s1 vo go defo sb.
    expr_type addr = BaseT AddressT /\ raw_call_kws_ok flags kws /\
    LENGTH kws = LENGTH flags.rcf_kws /\
    lower_value compile_expr cenv (BaseT AddressT) addr sa = (addr_op,s1) /\
    compile_ext_call_kwargs compile_expr cenv NoneT flags.rcf_kws kws s1 =
      ((vo,go,defo),sb) ==>
    ?ops. lower_word_args cenv expr_type (addr::kws) sa = (addr_op::ops,sb) /\
      vo = ext_call_kwarg EKValue flags.rcf_kws ops /\
      go = ext_call_kwarg EKGas flags.rcf_kws ops /\ defo = NONE
Proof
  rpt strip_tac >>
  `EVERY (\e. expr_type e = BaseT (UintT 256)) kws` by
    (irule raw_call_kw_types >> qexists_tac `flags.rcf_kws` >>
     gvs[raw_call_kws_ok_def]) >>
  drule_at Any raw_call_kwargs_lower >>
  disch_then (qspecl_then [`flags.rcf_kws`, `cenv`, `s1`] mp_tac) >>
  impl_tac >- gvs[raw_call_kws_ok_def] >>
  Cases_on `lower_word_args cenv expr_type kws s1` >> simp[] >>
  strip_tac >> gvs[] >> simp[lower_word_args_cons] >> metis_tac[]
QED

Theorem calldata_default_gas[local]:
  !ctx func cenv cx es sa op sb s.
    emit_op GAS [] sa = (op,sb) /\ local_ptrs_reserved cenv sa /\
    stmt_state_rel ctx func cenv cx es s ==>
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand op t = SOME (HD (s.vs_gas_readings ++ [0w])) /\
      stmt_state_rel ctx func cenv cx es t /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      t = s with <| vs_vars := t.vs_vars;
                    vs_gas_readings := DROP 1 s.vs_gas_readings |>
Proof
  rpt gen_tac >> strip_tac >>
  drule emitted_insts_emit_op_local >> strip_tac >> gvs[] >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_gas_def] >>
  `not_local_ptr cenv es.scopes (STRING #"%" (toString sa.cs_next_var))` by
    (irule local_ptrs_reserved_fresh >> goal_assum (drule_at Any) >> simp[]) >>
  `!w rs. stmt_state_rel ctx func cenv cx es
            (update_var (STRING #"%" (toString sa.cs_next_var)) w
               (s with vs_gas_readings := rs))` by
    (rpt gen_tac >> irule stmt_state_rel_update_var >>
     simp[hash_gas_readings_state_rel]) >>
  `!w. stmt_state_rel ctx func cenv cx es
         (update_var (STRING #"%" (toString sa.cs_next_var)) w s)` by
    (gen_tac >> irule stmt_state_rel_update_var >> simp[]) >>
  Cases_on `s.vs_gas_readings` >>
  fs[update_var_def, eval_operand_def, lookup_var_def, not_fresh_at_def,
     finite_mapTheory.FLOOKUP_UPDATE] >>
  rw[] >> gvs[venom_state_component_equality]
QED

Theorem calldata_outbuf_size[local]:
  !cenv cx env ann flags args dflt es.
    expr_body_pre cenv cx env
      (Call ann (RawCallCalldataTarget flags) args dflt) es /\
    0 < flags.rcf_max_outsize ==>
    ((flags.rcf_max_outsize + 31) DIV 32) * 32 + 32 < 2 ** 64
Proof
  rpt strip_tac >> drule calldata_call_pre >> strip_tac >>
  Cases_on `flags.rcf_revert_on_failure` >>
  gvs[expr_body_pre_def, alloc_limits_expr_def, type_alloc_ok_def,
      raw_call_return_type_def, is_word_type_def, type_memory_bytes_def]
QED

Theorem calldata_outbuf_compile[local]:
  !n sa valop ptrop sb.
    compile_raw_call_outbuf n sa = ((valop,ptrop),sb) ==>
    ?buf sm. compile_alloc_buffer
      (if n = 0 then 0 else ((n + 31) DIV 32) * 32 + 32) sa = (buf,sm) /\
      valop = buf.buf_operand /\
      (if n = 0 then ptrop = valop /\ sb = sm
       else emit_op ADD [valop; Lit 32w] sm = (ptrop,sb))
Proof
  rpt gen_tac >> Cases_on `n = 0` >>
  simp[compile_raw_call_outbuf_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem calldata_outbuf_positive_run[local]:
  !n sa valop ptrop sb ctx func cenv cx es s.
    0 < n /\ ((n + 31) DIV 32) * 32 + 32 < dimword (:256) /\
    compile_raw_call_outbuf n sa = ((valop,ptrop),sb) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    MEM (mk_inst sa.cs_next_id ALLOCA
      [Lit (n2w (((n + 31) DIV 32) * 32 + 32))]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) ==>
    ?t w. run_inst_seq (emitted_insts sa sb) s = OK t /\
      stmt_state_rel ctx func cenv cx es t /\
      eval_operand valop t = SOME w /\ eval_operand ptrop t = SOME (w + 32w) /\
      FLOOKUP t.vs_allocas sa.cs_next_id =
        SOME (w2n w, ((n + 31) DIV 32) * 32 + 32) /\
      w2n w + (((n + 31) DIV 32) * 32 + 32) < dimword (:256) /\
      t.vs_memory = s.vs_memory /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
         FLOOKUP t.vs_allocas aid = SOME entry)
Proof
  rpt gen_tac >> strip_tac >> drule calldata_outbuf_compile >> strip_tac >>
  gvs[] >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK allocated` >>
  `sm.cs_next_var = sa.cs_next_var + 1 /\
   sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> strip_tac >> gvs[] >>
     drule emitted_insts_emit_op_local >> simp[] >> metis_tac[]) >>
  `run_inst_seq (emitted_insts sm sb) allocated =
    OK (update_var (STRING #"%" (toString sm.cs_next_var)) (w + 32w) allocated)` by
    (irule buffer_emit_add_run >> simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  suspend "finish"
QED

Resume calldata_outbuf_positive_run[finish]:
  drule emitted_insts_emit_op_local >> strip_tac >>
  `run_inst_seq (emitted_insts sa sb) s =
   run_inst_seq (emitted_insts sm sb) allocated` by
    (irule (cj 1 run_inst_seq_chain) >> simp[]) >>
  qexistsl_tac [`update_var (STRING #"%" (toString sm.cs_next_var))
      (w + 32w) allocated`, `w`] >>
  simp[] >> conj_tac
  >- (irule stmt_state_rel_update_var >> simp[] >>
      irule local_ptrs_reserved_fresh >> qexists_tac `sa` >> simp[]) >>
  simp[update_var_def, eval_operand_def, lookup_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >> conj_tac
  >- (gvs[not_fresh_at_def, eval_operand_def, lookup_var_def]) >>
  rpt strip_tac >>
  `x <> STRING #"%" (toString sm.cs_next_var)` by
    (gvs[not_fresh_at_def] >> strip_tac >> gvs[]) >>
  gvs[lookup_var_def]
QED
Finalise calldata_outbuf_positive_run

Theorem calldata_outbuf_zero_run[local]:
  !sa valop ptrop sb ctx func cenv cx es s.
    compile_raw_call_outbuf 0 sa = ((valop,ptrop),sb) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit 0w]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) ==>
    ?t w. run_inst_seq (emitted_insts sa sb) s = OK t /\
      stmt_state_rel ctx func cenv cx es t /\
      eval_operand valop t = SOME w /\ eval_operand ptrop t = SOME w /\
      FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,0) /\
      w2n w < dimword (:256) /\ t.vs_memory = s.vs_memory /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
         FLOOKUP t.vs_allocas aid = SOME entry)
Proof
  rpt strip_tac >> drule calldata_outbuf_compile >> strip_tac >> gvs[] >>
  `0 < dimword (:256)` by simp[wordsTheory.dimword_def] >>
  drule_all literal_alloc_buffer_run >> simp[] >>
  strip_tac >> goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]
QED

(* TOP-LEVEL *)
(* An oracle's bounded return write stays within its own fresh ALLOCA. *)
Theorem raw_call_outbuf_write_frame:
  !ctx func cenv cx es s inst q b sz dst data.
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
    b <= dst /\ dst + LENGTH data <= b + sz ==>
    stmt_state_rel ctx func cenv cx es (write_memory_with_expansion dst data s)
Proof
  rpt gen_tac >> strip_tac >> irule write_memory_stmt_state_rel >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> drule_all alloca_clear_of_locals >> decide_tac) >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es s` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  `(write_memory_with_expansion dst data s).vs_data_section = s.vs_data_section /\
   LENGTH s.vs_memory <= LENGTH (write_memory_with_expansion dst data s).vs_memory` by
    (simp[write_memory_with_expansion_def] >>
     Cases_on `dst + LENGTH data > LENGTH s.vs_memory` >>
     simp[LENGTH_TAKE, LENGTH_DROP, arithmeticTheory.MIN_DEF] >> decide_tac) >>
  irule immutables_rel_mem_agree >> qexists_tac `s` >> simp[] >>
  rpt strip_tac >>
  `regions_disjoint off (type_memory_size tv) b sz` by
    (qpat_x_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
     simp[stmt_state_rel_def, immutable_alloca_sep_def] >> metis_tac[]) >>
  irule hash_write_memory_disjoint >>
  gvs[regions_disjoint_def] >> decide_tac
QED

Theorem calldata_outbuf_below_fmp[local]:
  !ctx func cenv cx es s aid b sz.
    stmt_state_rel ctx func cenv cx es s /\
    EXISTS (\inst. inst.inst_opcode = DALLOCA) (fn_insts func) /\
    FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
    b + sz <= w2n s.vs_fmp
Proof
  rpt strip_tac >>
  `fmp_room ctx func s /\ alloca_inv s` by gvs[stmt_state_rel_def] >>
  drule_all calldata_memory_frontier >> strip_tac >>
  gvs[venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.alloca_next_valid_def] >>
  first_x_assum drule >> decide_tac
QED

Theorem raw_call_outbuf_write_contents:
  !(w:bytes32) n data s.
    w2n w + (((n + 31) DIV 32) * 32 + 32) < dimword (:256) ==>
    w2n (w + 32w) = w2n w + 32 /\
    mem_bytes_at (w2n w) 32
      (write_memory_with_expansion (w2n (w + 32w)) (TAKE n data) s).vs_memory =
      mem_bytes_at (w2n w) 32 s.vs_memory /\
    mem_bytes_at (w2n (w + 32w)) (LENGTH (TAKE n data))
      (write_memory_with_expansion (w2n (w + 32w)) (TAKE n data) s).vs_memory =
      TAKE n data /\
    w2n (w + 32w) + LENGTH (TAKE n data) <=
      w2n w + (((n + 31) DIV 32) * 32 + 32)
Proof
  rpt gen_tac >> strip_tac >>
  `w2n (w + 32w) = w2n w + 32` by
    (irule buffer_offset_no_wrap >>
     qexists_tac `((n + 31) DIV 32) * 32 + 32` >> simp[]) >>
  simp[hash_write_memory_read_self] >> conj_tac
  >- (irule hash_write_memory_disjoint >> simp[]) >>
  qspec_then `n` mp_tac le_word_size_mul >>
  simp[vfmConstantsTheory.word_size_def, LENGTH_TAKE_EQ,
       arithmeticTheory.MIN_DEF] >> rpt strip_tac >> gvs[] >> decide_tac
QED

(* Both CALL variants share the oracle and the same bounded memory frame. *)
Theorem raw_call_oracle_step:
  !func cenv cx es s inst gop aop vop iop zop rop cop
   gas aw vw ip iz rp cap stat out rq outcome es1.
    state_rel func cenv cx es s /\ inst.inst_outputs = [out] /\
    inst.inst_opcode = (if stat then STATICCALL else CALL) /\
    inst.inst_operands =
      (if stat then [gop;aop;iop;zop;rop;cop]
       else [gop;aop;vop;iop;zop;rop;cop]) /\
    eval_operand gop s = SOME gas /\ eval_operand aop s = SOME aw /\
    eval_operand vop s = SOME vw /\ eval_operand iop s = SOME ip /\
    eval_operand zop s = SOME iz /\ eval_operand rop s = SOME rp /\
    eval_operand cop s = SOME cap /\
    take_call_outcome (w2w aw) (read_memory (w2n ip) (w2n iz) s)
      (if stat then NONE else SOME (w2n vw)) es = (INL (rq,outcome),es1) /\
    local_ptrs_rel func cenv es.scopes
      (write_memory_with_expansion (w2n rp) (TAKE (w2n cap) outcome.co_returnData) s) /\
    immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es
      (write_memory_with_expansion (w2n rp) (TAKE (w2n cap) outcome.co_returnData) s) ==>
    ?t. step_inst_base inst s =
          OK (update_var out (if outcome.co_success then 1w else 0w) t) /\
        state_rel func cenv cx (SND (adopt_call_outcome rq outcome es1)) t /\
        t.vs_returndata = outcome.co_returnData /\
        t.vs_memory = (write_memory_with_expansion (w2n rp)
                        (TAKE (w2n cap) outcome.co_returnData) s).vs_memory /\
        t.vs_fmp = s.vs_fmp /\ t.vs_allocas = s.vs_allocas /\
        t.vs_vars = s.vs_vars /\ t.vs_inst_idx = s.vs_inst_idx /\
        t.vs_data_section = s.vs_data_section
Proof
  rpt gen_tac >> strip_tac >>
  `~s.vs_call_ctx.cc_static` by gvs[state_rel_def] >>
  `?t. exec_ext_call inst s gas aw (if stat then 0w else vw) ip iz rp cap stat =
      OK (update_var out (if outcome.co_success then 1w else 0w) t) /\
    t = s with <| vs_outcomes := t.vs_outcomes; vs_requests := t.vs_requests;
      vs_accounts := t.vs_accounts; vs_transient := t.vs_transient;
      vs_logs := t.vs_logs; vs_pending_deletions := t.vs_pending_deletions;
      vs_returndata := t.vs_returndata; vs_memory := t.vs_memory |> /\
    t.vs_memory = (write_memory_with_expansion (w2n rp)
      (TAKE (w2n cap) outcome.co_returnData) s).vs_memory /\
    t.vs_returndata = outcome.co_returnData /\
    (local_ptrs_rel func cenv es.scopes t /\
     immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es t ==>
     state_rel func cenv cx (SND (adopt_call_outcome rq outcome es1)) t)` by
    (irule exec_ext_call_oracle_step >> simp[] >>
     qexists_tac `if stat then NONE else SOME (w2n vw)` >>
     Cases_on `stat` >> gvs[]) >>
  `write_memory_with_expansion (w2n rp)
      (TAKE (w2n cap) outcome.co_returnData) s = s with vs_memory := t.vs_memory` by
    (qpat_x_assum `t.vs_memory = _` (fn th => REWRITE_TAC [th]) >>
     simp[write_memory_with_expansion_def]) >>
  `local_ptrs_rel func cenv es.scopes t /\
   immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es t` by
    (qpat_x_assum `local_ptrs_rel _ _ _ (write_memory_with_expansion _ _ _)` mp_tac >>
     qpat_x_assum `immutables_rel _ _ _ _ _ (write_memory_with_expansion _ _ _)` mp_tac >>
     qpat_x_assum `write_memory_with_expansion _ _ _ = _`
       (fn th => ONCE_REWRITE_TAC [th]) >>
     qpat_x_assum `t = _` mp_tac >> rpt (pop_assum kall_tac) >>
     disch_then (fn th => ONCE_REWRITE_TAC [th]) >>
     simp[local_ptrs_rel_def, local_region_def, local_backed_def,
          lookup_var_def, immutables_rel_def] >> metis_tac[]) >>
  qexists_tac `t` >> conj_tac
  >- (qpat_x_assum `t = _` kall_tac >>
      qpat_x_assum `write_memory_with_expansion _ _ _ = _` kall_tac >>
      Cases_on `stat` >> fs[] >> simp[step_inst_base_def]) >>
  conj_tac >- (first_x_assum irule >> simp[NoAsms] >>
               conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `t = _` mp_tac >> rpt (pop_assum kall_tac) >>
  disch_then (fn th => ONCE_REWRITE_TAC [th]) >> simp[]
QED

(* Expose the two blocks once; consumers need not unfold the call compiler. *)
Theorem raw_call_finish_nonrevert_compile[local]:
  compile_raw_call_finish to_op dp dl gas_op value_op call_ty n F
    out_val out_ptr sa = (result,sb) ==>
  ?success s1.
    (case call_ty of
      DelegateCall => emit_op DELEGATECALL
        [gas_op;to_op;dp;dl;out_ptr;Lit (n2w n)] sa
    | StaticCall => emit_op STATICCALL
        [gas_op;to_op;dp;dl;out_ptr;Lit (n2w n)] sa
    | RegularCall => emit_op CALL
        [gas_op;to_op;value_op;dp;dl;out_ptr;Lit (n2w n)] sa) = (success,s1) /\
    (if n > 0 then
       do z <- emit_op RETURNDATASIZE [];
          cmp <- emit_op LT [z;Lit (n2w n)];
          cap <- compile_select cmp z (Lit (n2w n));
          emit_void MSTORE [out_val;cap];
          buf <- compile_alloc_buffer (64 + ((n + 31) DIV 32) * 32);
          emit_void MSTORE [buf.buf_operand;success];
          dst <- emit_op ADD [buf.buf_operand;Lit 32w];
          emit_void MCOPY [dst;out_val;Lit (n2w (32 + ((n + 31) DIV 32) * 32))];
          return buf.buf_operand od
     else return success) s1 = (result,sb) /\ ci_mono s1 sb
Proof
  simp[compile_raw_call_finish_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  Cases_on `call_ty` >> gvs[] >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  qpat_x_assum `(if _ then _ else _) _ = _` mp_tac >>
  Cases_on `n > 0` >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  gvs[builtinSimpleTheory.compile_select_def, compile_alloc_buffer_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  simp[ci_mono_def, cs_extends_def, same_blocks_def,
    rich_listTheory.IS_PREFIX_APPEND]
QED

Theorem raw_call_finish_nonrevert_outbuf_compile[local]:
  compile_raw_call_finish to_op dp dl gas_op value_op call_ty n F
    out_val out_ptr sa = (result,sb) /\ n > 0 ==>
  ?success s1 z s2 cmp s3 cap s4 s5 buf s6 s7 dst s8.
    (case call_ty of
      DelegateCall => emit_op DELEGATECALL
        [gas_op;to_op;dp;dl;out_ptr;Lit (n2w n)] sa
    | StaticCall => emit_op STATICCALL
        [gas_op;to_op;dp;dl;out_ptr;Lit (n2w n)] sa
    | RegularCall => emit_op CALL
        [gas_op;to_op;value_op;dp;dl;out_ptr;Lit (n2w n)] sa) = (success,s1) /\
    emit_op RETURNDATASIZE [] s1 = (z,s2) /\
    emit_op LT [z;Lit (n2w n)] s2 = (cmp,s3) /\
    compile_select cmp z (Lit (n2w n)) s3 = (cap,s4) /\
    emit_void MSTORE [out_val;cap] s4 = ((),s5) /\
    compile_alloc_buffer (64 + ((n + 31) DIV 32) * 32) s5 = (buf,s6) /\
    emit_void MSTORE [buf.buf_operand;success] s6 = ((),s7) /\
    emit_op ADD [buf.buf_operand;Lit 32w] s7 = (dst,s8) /\
    emit_void MCOPY [dst;out_val;Lit (n2w (32 + ((n + 31) DIV 32) * 32))]
      s8 = ((),sb) /\ result = buf.buf_operand
Proof
  strip_tac >> drule raw_call_finish_nonrevert_compile >> strip_tac >>
  gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED

Theorem raw_call_finish_nonrevert_empty[local]:
  compile_raw_call_finish to_op dp dl gas_op value_op call_ty 0 F
    out_val out_ptr sa =
    (case call_ty of
      DelegateCall => emit_op DELEGATECALL
        [gas_op;to_op;dp;dl;out_ptr;Lit 0w] sa
    | StaticCall => emit_op STATICCALL
        [gas_op;to_op;dp;dl;out_ptr;Lit 0w] sa
    | RegularCall => emit_op CALL
        [gas_op;to_op;value_op;dp;dl;out_ptr;Lit 0w] sa)
Proof
  simp[compile_raw_call_finish_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> Cases_on `call_ty` >> gvs[]
QED

Theorem raw_call_finish_revert_compile:
  !to_op dp dl gas_op value_op call_ty n out_val out_ptr sa result sb.
    compile_raw_call_finish to_op dp dl gas_op value_op call_ty n T
      out_val out_ptr sa = (result,sb) ==>
    ?success s1 fail s2 ok s3 s4 x4 s5 rds s6 rbuf s7 s8 s9 x9 s10.
      (case call_ty of
        DelegateCall => emit_op DELEGATECALL
          [gas_op;to_op;dp;dl;out_ptr;Lit (n2w n)] sa
      | StaticCall => emit_op STATICCALL
          [gas_op;to_op;dp;dl;out_ptr;Lit (n2w n)] sa
      | RegularCall => emit_op CALL
          [gas_op;to_op;value_op;dp;dl;out_ptr;Lit (n2w n)] sa) = (success,s1) /\
      fresh_label "call_failed" s1 = (fail,s2) /\
      fresh_label "call_ok" s2 = (ok,s3) /\
      emit_inst JNZ [success;Label ok;Label fail] [] s3 = ((),s4) /\
      new_block fail s4 = (x4,s5) /\
      emit_op RETURNDATASIZE [] s5 = (rds,s6) /\
      compile_alloc_buffer 0 s6 = (rbuf,s7) /\
      emit_void RETURNDATACOPY [rbuf.buf_operand;Lit 0w;rds] s7 = ((),s8) /\
      emit_inst REVERT [rbuf.buf_operand;rds] [] s8 = ((),s9) /\
      new_block ok s9 = (x9,s10) /\
      (if n > 0 then
         do rds2 <- emit_op RETURNDATASIZE [];
            cmp <- emit_op LT [rds2;Lit (n2w n)];
            capped <- compile_select cmp rds2 (Lit (n2w n));
            emit_void MSTORE [out_val;capped]; return out_val od
       else return (Lit 0w)) s10 = (result,sb)
Proof
  rpt gen_tac >>
  simp[compile_raw_call_finish_def, comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rename1 `fresh_label "call_failed" a1 = (fl,a2)` >>
  rename1 `fresh_label "call_ok" a2 = (ol,a3)` >>
  rename1 `emit_inst JNZ [succ;Label ol;Label fl] [] a3 = ((),a4)` >>
  rename1 `new_block fl a4 = (u4,a5)` >>
  rename1 `emit_op RETURNDATASIZE [] a5 = (rsize,a6)` >>
  rename1 `compile_alloc_buffer 0 a6 = (rb1,a7)` >>
  rename1 `emit_void RETURNDATACOPY _ a7 = ((),a8)` >>
  rename1 `emit_inst REVERT _ [] a8 = ((),a9)` >>
  rename1 `new_block ol a9 = (u9,a10)` >>
  qexistsl_tac [`succ`,`a1`,`fl`,`a2`,`ol`,`a3`,`a4`,`u4`,`a5`,
               `rsize`,`a6`,`rb1`,`a7`,`a8`,`a9`,`u9`,`a10`] >>
  Cases_on `call_ty` >> gvs[]
QED

(* The failure path copies the complete returndata, not the capped output. *)
Theorem raw_call_revert_copy:
  !s pop zop ptr data cid rid.
    s.vs_returndata = data /\ LENGTH data < dimword (:256) /\
    eval_operand pop s = SOME ptr /\
    eval_operand zop s = SOME (n2w (LENGTH data)) ==>
    step_inst_base (mk_inst cid RETURNDATACOPY [pop; Lit 0w; zop] []) s =
      OK (write_memory_with_expansion (w2n ptr) data s) /\
    step_inst_base (mk_inst rid REVERT [pop; zop] [])
      (write_memory_with_expansion (w2n ptr) data s) =
      Abort Revert_abort
        (revert_state (set_returndata data
          (write_memory_with_expansion (w2n ptr) data s)))
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- simp[step_inst_base_def, mk_inst_def, eval_operand_def, wordsTheory.w2n_n2w] >>
  rename1 `eval_operand pop s = SOME pw` >>
  `eval_operand pop (write_memory_with_expansion (w2n pw) data s) = SOME pw /\
   eval_operand zop (write_memory_with_expansion (w2n pw) data s) =
     SOME (n2w (LENGTH data))` by
    (simp[write_memory_with_expansion_def, eval_operand_def, lookup_var_def] >>
     Cases_on `pop` >> Cases_on `zop` >>
     gvs[eval_operand_def, lookup_var_def]) >>
  simp[step_inst_base_def, mk_inst_def, wordsTheory.w2n_n2w] >>
  `TAKE (LENGTH data)
    (DROP (w2n pw) (write_memory_with_expansion (w2n pw) data s).vs_memory ++
     REPLICATE (LENGTH data) 0w) = data` suffices_by simp[] >>
  rewrite_tac[GSYM mem_bytes_at_def] >> irule hash_write_memory_read_self
QED

Theorem raw_call_revert_run:
  !s z p sid aid cid rid.
    z <> p /\ LENGTH s.vs_returndata < dimword (:256) ==>
    ?t. run_inst_seq
      [mk_inst sid RETURNDATASIZE [] [z];
       mk_inst aid ALLOCA [Lit 0w] [p];
       mk_inst cid RETURNDATACOPY [Var p;Lit 0w;Var z] [];
       mk_inst rid REVERT [Var p;Var z] []] s = Abort Revert_abort t /\
      t.vs_returndata = s.vs_returndata
Proof
  rpt gen_tac >> strip_tac >>
  `?a pw. run_inst_seq
      [mk_inst sid RETURNDATASIZE [] [z];mk_inst aid ALLOCA [Lit 0w] [p]] s = OK a /\
    eval_operand (Var p) a = SOME pw /\
    eval_operand (Var z) a = SOME (n2w (LENGTH s.vs_returndata)) /\
    a.vs_returndata = s.vs_returndata` by
    (simp[Once run_inst_seq_def, step_inst_base_def, mk_inst_def, exec_read0_def] >>
     simp[Once run_inst_seq_def, step_inst_base_def, mk_inst_def,
          eval_operand_def] >>
     simp[exec_alloca_def, update_var_def] >>
     Cases_on `FLOOKUP s.vs_allocas aid` >>
     gvs[AllCaseEqs(), run_inst_seq_def, eval_operand_def, lookup_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >>
     TRY (rename1 `FLOOKUP _ _ = SOME pairv` >> PairCases_on `pairv`) >>
     simp[finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]) >>
  drule run_inst_seq_append >>
  disch_then (qspec_then
    `[mk_inst cid RETURNDATACOPY [Var p;Lit 0w;Var z] [];
      mk_inst rid REVERT [Var p;Var z] []]` assume_tac) >>
  qspecl_then [`a`,`Var p`,`Var z`,`pw`,`s.vs_returndata`]
    mp_tac raw_call_revert_copy >> simp[] >>
  disch_then (qspecl_then [`cid`,`rid`] strip_assume_tac) >>
  qexists_tac `revert_state (set_returndata s.vs_returndata
    (write_memory_with_expansion (w2n pw) s.vs_returndata a))` >>
  conj_tac >- (gvs[run_inst_seq_def]) >>
  simp[revert_state_def, set_returndata_def]
QED

Theorem raw_call_revert_frag:
  !ctx sa sz sp sc sb zop rb P R.
    emit_op RETURNDATASIZE [] sa = (zop,sz) /\
    compile_alloc_buffer 0 sz = (rb,sp) /\
    emit_void RETURNDATACOPY [rb.buf_operand;Lit 0w;zop] sp = ((),sc) /\
    emit_inst REVERT [rb.buf_operand;zop] [] sc = ((),sb) /\
    (!s. P s ==> LENGTH s.vs_returndata < dimword (:256) /\
       !t. t.vs_returndata = s.vs_returndata ==> R (Abort Revert_abort t)) ==>
    frag_path ctx sa sb P (\s. F) R
Proof
  rpt gen_tac >>
  simp[compile_alloc_buffer_def, emit_op_def, emit_void_def, emit_inst_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >>
  strip_tac >> gvs[] >>
  irule frag_path_abort_suffix >> simp[] >>
  reverse conj_tac
  >- simp[rich_listTheory.IS_PREFIX_APPEND, GSYM APPEND_ASSOC] >>
  qexistsl_tac
    [`mk_inst (sa.cs_next_id + 3) REVERT
        [Var (STRING #"%" (toString (sa.cs_next_var + 1)));
         Var (STRING #"%" (toString sa.cs_next_var))] []`,
     `[mk_inst sa.cs_next_id RETURNDATASIZE []
         [STRING #"%" (toString sa.cs_next_var)];
       mk_inst (sa.cs_next_id + 1) ALLOCA [Lit 0w]
         [STRING #"%" (toString (sa.cs_next_var + 1))];
       mk_inst (sa.cs_next_id + 2) RETURNDATACOPY
         [Var (STRING #"%" (toString (sa.cs_next_var + 1)));Lit 0w;
          Var (STRING #"%" (toString sa.cs_next_var))] []]`] >>
  simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND,
       mk_inst_def, is_terminator_def] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  qspecl_then [`s`,`STRING #"%" (toString sa.cs_next_var)`,
    `STRING #"%" (toString (sa.cs_next_var + 1))`,
    `sa.cs_next_id`,`sa.cs_next_id + 1`,`sa.cs_next_id + 2`,`sa.cs_next_id + 3`]
    mp_tac raw_call_revert_run >>
  simp[ASCIInumbersTheory.toString_11] >> strip_tac >>
  qexistsl_tac [`Revert_abort`,`t`] >> fs[mk_inst_def]
QED

(* A common branch-entry boundary for both call outcomes. *)
Theorem raw_call_jnz_frag[local]:
  !ctx sa sx sf sk sb cond ok fl x s Q R.
    emit_inst JNZ [cond;Label ok;Label fl] [] sa = ((),sx) /\
    new_block fl sx = (x,sf) /\
    cs_extends sf sk /\ cs_extends sk sb /\
    sk.cs_current_insts = [] /\
    step_inst_base (mk_inst sa.cs_next_id JNZ [cond;Label ok;Label fl] []) s =
      OK (jump_to sk.cs_current_bb s) /\
    frag_path ctx sk sb (\u. u = jump_to sk.cs_current_bb s) Q R ==>
    frag_path ctx sa sb (\u. u = s) Q R
Proof
  rpt gen_tac >> strip_tac >>
  `cs_extends sa sx /\ cs_extends sx sf` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def, cs_extends_new_block] >>
  imp_res_tac emit_inst_extends >>
  PURE_REWRITE_TAC[frag_path_def] >> BETA_TAC >> rpt strip_tac >> gvs[] >>
  `fn_has_code sx sf fn` by
    (irule fn_has_code_mid >> simp[] >> qexistsl_tac [`sb`,`sa`] >>
     simp[] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sk sb fn` by
    (irule fn_has_code_mid >> simp[] >> qexistsl_tac [`sb`,`sa`] >>
     simp[cs_extends_refl] >>
     irule cs_extends_trans >> qexists_tac `sx` >> simp[] >>
     irule cs_extends_trans >> qexists_tac `sf` >> simp[]) >>
  qabbrev_tac `j = mk_inst sa.cs_next_id JNZ [cond;Label ok;Label fl] []` >>
  qabbrev_tac `bb = <|bb_label := sx.cs_current_bb;
                       bb_instructions := sx.cs_current_insts|>` >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by
    (simp[Abbr `bb`] >> metis_tac[fn_has_code_new_block]) >>
  `get_instruction bb s.vs_inst_idx = SOME j` by
    simp[Abbr `bb`, Abbr `j`, get_instruction_def, rich_listTheory.EL_LENGTH_APPEND] >>
  `is_terminator j.inst_opcode /\ j.inst_opcode <> INVOKE /\
   step_inst_base j s = OK (jump_to sk.cs_current_bb s)` by
    simp[Abbr `j`, mk_inst_def, is_terminator_def] >>
  drule_at (Pat `frag_path _ _ _ _ _ _`) frag_path_enter >>
  disch_then (qspecl_then [`fn`,`s`,`bb`,`j`] mp_tac) >> simp[]
QED

Theorem raw_call_failed_jnz_frag:
  !ctx sa sx sf se sb cond ok fl x s R.
    emit_inst JNZ [cond;Label ok;Label fl] [] sa = ((),sx) /\
    new_block fl sx = (x,sf) /\
    cs_extends sf se /\ cs_extends se sb /\
    eval_operand cond s = SOME 0w /\
    frag_path ctx sf se (\u. u = jump_to fl s) (\u. F) R ==>
    frag_path ctx sa sb (\u. u = s) (\u. F) R
Proof
  rpt strip_tac >>
  `sf.cs_current_bb = fl /\ sf.cs_current_insts = []` by
    gvs[new_block_def, comp_bind_def, comp_get_def, comp_set_def, comp_return_def] >>
  `frag_path ctx sf sb (\u. u = jump_to fl s) (\u. F) R` by
    (irule frag_path_exit_prefix >> goal_assum (drule_at Any) >> simp[]) >>
  irule raw_call_jnz_frag >>
  qexistsl_tac [`cond`, `fl`, `ok`, `sf`, `sf`, `sx`, `x`] >>
  simp[cs_extends_refl, step_inst_base_def, mk_inst_def] >>
  metis_tac[cs_extends_trans]
QED

Theorem raw_call_success_jnz_frag[local]:
  !ctx sa sx sf se sk sb cond ok fl x y s Q R.
    emit_inst JNZ [cond;Label ok;Label fl] [] sa = ((),sx) /\
    new_block fl sx = (x,sf) /\ cs_extends sf se /\
    new_block ok se = (y,sk) /\ cs_extends sk sb /\
    eval_operand cond s = SOME 1w /\
    frag_path ctx sk sb (\u. u = jump_to ok s) Q R ==>
    frag_path ctx sa sb (\u. u = s) Q R
Proof
  rpt strip_tac >>
  `sk.cs_current_bb = ok /\ sk.cs_current_insts = []` by
    gvs[new_block_def, comp_bind_def, comp_get_def, comp_set_def, comp_return_def] >>
  `cs_extends se sk` by metis_tac[cs_extends_new_block] >>
  irule raw_call_jnz_frag >>
  qexistsl_tac [`cond`, `fl`, `ok`, `sf`, `sk`, `sx`, `x`] >>
  simp[step_inst_base_def, mk_inst_def] >>
  irule cs_extends_trans >> qexists_tac `se` >> simp[]
QED

Theorem raw_call_size_run[local]:
  !sa op sb s.
    emit_op RETURNDATASIZE [] sa = (op,sb) /\ fresh_vars_wrt sa s ==>
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand op t = SOME (n2w (LENGTH s.vs_returndata)) /\
      fresh_vars_wrt sb t /\
      (!p w. eval_operand p s = SOME w ==> eval_operand p t = SOME w)
Proof
  rpt strip_tac >>
  qspecl_then [`RETURNDATASIZE`, `\u. n2w (LENGTH u.vs_returndata)`,
               `sa`, `op`, `sb`, `s`] mp_tac emit_op_read0_correct >>
  simp[] >> impl_tac
  >- simp[step_inst_base_def, mk_inst_def, exec_read0_def] >>
  metis_tac[]
QED

Theorem raw_call_cap_value_run[local]:
  !sa z s1 cmp s2 cap sb s n.
    emit_op RETURNDATASIZE [] sa = (z,s1) /\
    emit_op LT [z;Lit (n2w n)] s1 = (cmp,s2) /\
    compile_select cmp z (Lit (n2w n)) s2 = (cap,sb) /\
    fresh_vars_wrt sa s /\ n < dimword (:256) /\
    LENGTH s.vs_returndata < dimword (:256) ==>
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand cap t = SOME (n2w (MIN n (LENGTH s.vs_returndata))) /\
      fresh_vars_wrt sb t /\
      (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w)
Proof
  rpt strip_tac >> drule_all raw_call_size_run >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  `eval_operand (Lit (n2w n)) u = SOME (n2w n)` by simp[eval_operand_def] >>
  drule_all emit_op_LT_correct >>
  disch_then (qx_choose_then `v` strip_assume_tac) >>
  `eval_operand z v = SOME (n2w (LENGTH s.vs_returndata))` by metis_tac[] >>
  `?t. run_inst_seq (emitted_insts s2 sb) v = OK t /\
    eval_operand cap t = SOME
      (if w2n (n2w (LENGTH s.vs_returndata):bytes32) < w2n (n2w n:bytes32)
       then n2w (LENGTH s.vs_returndata) else n2w n) /\
    fresh_vars_wrt sb t /\
    (!op w. eval_operand op v = SOME w ==> eval_operand op t = SOME w)` by
    (irule compile_select_correct >> simp[] >>
     qexistsl_tac [`cmp`, `Lit (n2w n)`, `z`] >>
     simp[eval_operand_def]) >>
  qexists_tac `t` >> conj_tac
  >- (irule run_emitted_compose3 >>
      qexistsl_tac [`u`, `v`, `s1`, `s2`] >> simp[] >>
      imp_res_tac emit_op_extends >> imp_res_tac compile_select_extends >> simp[]) >>
  conj_tac
  >- (gvs[wordsTheory.w2n_n2w] >>
      simp[arithmeticTheory.MIN_DEF] >> rpt IF_CASES_TAC >> gvs[]) >>
  simp[] >> metis_tac[]
QED

Theorem raw_call_cap_step_frame[local]:
  !inst s t out.
    MEM inst.inst_opcode [RETURNDATASIZE;LT;XOR;MUL] /\
    inst.inst_outputs = [out] /\ step_inst_base inst s = OK t ==>
    (?vars. t = s with vs_vars := vars) /\
    (!x. x <> out ==> FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x)
Proof
  rpt gen_tac >> simp[MEM] >> strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  asm_rewrite_tac[] >>
  pure_rewrite_tac[opcode_case_def] >>
  simp[exec_read0_def, exec_pure2_def, bind_outputs_def,
       AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[] >>
  simp[venom_state_component_equality, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem raw_call_cap_seq_frame[local]:
  !insts s t.
    EVERY (\i. MEM i.inst_opcode [RETURNDATASIZE;LT;XOR;MUL] /\
               ?out. i.inst_outputs = [out]) insts /\
    run_inst_seq insts s = OK t ==>
    (?vars. t = s with vs_vars := vars) /\
    (!x. EVERY (\i. ~MEM x i.inst_outputs) insts ==>
         FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x)
Proof
  Induct >> rpt gen_tac >> simp[run_inst_seq_def] >> strip_tac
  >- (gvs[] >> qexists_tac `s.vs_vars` >> simp[]) >>
  gvs[EVERY_DEF, AllCaseEqs()] >>
  drule_at (Pat `step_inst_base _ _ = _`) raw_call_cap_step_frame >>
  simp[MEM] >> strip_tac >> gvs[] >>
  first_x_assum drule >> simp[] >> strip_tac >> gvs[] >>
  simp[venom_state_component_equality]
QED

Theorem raw_call_cap_code[local]:
  emit_op RETURNDATASIZE [] sa = (z,s1) /\
  emit_op LT [z;Lit (n2w n)] s1 = (cmp,s2) /\
  compile_select cmp z (Lit (n2w n)) s2 = (cap,sb) ==>
  EVERY (\i. MEM i.inst_opcode [RETURNDATASIZE;LT;XOR;MUL] /\
             ?out. i.inst_outputs = [out]) (emitted_insts sa sb)
Proof
  rpt strip_tac >>
  gvs[builtinSimpleTheory.compile_select_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[emit_op_def, fresh_var_def, fresh_id_def, emit_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[mk_inst_def, MEM]
QED

Theorem raw_call_cap_run_frame[local]:
  !sa z s1 cmp s2 cap sb s t n.
    emit_op RETURNDATASIZE [] sa = (z,s1) /\
    emit_op LT [z;Lit (n2w n)] s1 = (cmp,s2) /\
    compile_select cmp z (Lit (n2w n)) s2 = (cap,sb) /\
    run_inst_seq (emitted_insts sa sb) s = OK t ==>
    (?vars. t = s with vs_vars := vars) /\
    (!x. not_fresh_at sa x ==> FLOOKUP t.vs_vars x = FLOOKUP s.vs_vars x)
Proof
  rpt gen_tac >> strip_tac >> drule_all raw_call_cap_code >> strip_tac >>
  drule_all raw_call_cap_seq_frame >> strip_tac >> conj_tac
  >- (qexists_tac `vars` >> simp[]) >>
  rpt strip_tac >> first_x_assum irule >>
  qpat_x_assum `compile_select _ _ _ _ = _` mp_tac >>
  gvs[builtinSimpleTheory.compile_select_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[emit_op_def, fresh_var_def, fresh_id_def, emit_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  strip_tac >> gvs[] >> simp[emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[mk_inst_def] >> fs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_ADD]
QED

Theorem raw_call_cap_run:
  !sa z s1 cmp s2 cap sb s n.
    emit_op RETURNDATASIZE [] sa = (z,s1) /\
    emit_op LT [z;Lit (n2w n)] s1 = (cmp,s2) /\
    compile_select cmp z (Lit (n2w n)) s2 = (cap,sb) /\
    fresh_vars_wrt sa s /\ n < dimword (:256) /\
    LENGTH s.vs_returndata < dimword (:256) ==>
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand cap t = SOME (n2w (MIN n (LENGTH s.vs_returndata))) /\
      fresh_vars_wrt sb t /\ (?vars. t = s with vs_vars := vars) /\
      (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w)
Proof
  rpt strip_tac >> drule_all raw_call_cap_value_run >> strip_tac >>
  drule_all raw_call_cap_run_frame >> strip_tac >>
  qexists_tac `t` >> simp[] >> metis_tac[]
QED

(* The capped output already occupies the payload region after the oracle
   step.  Writing its length cannot disturb that payload. *)
Theorem raw_call_output_length_memory:
  !s off n data.
    mem_bytes_at (off + 32) (LENGTH (TAKE n data)) s.vs_memory = TAKE n data ==>
    val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV (TAKE n data)) off
      (write_memory_with_expansion off
        (word_to_bytes (n2w (MIN n (LENGTH data)):bytes32) T) s).vs_memory
Proof
  rpt strip_tac >>
  `LENGTH (TAKE n data) = MIN n (LENGTH data)` by
    (simp[LENGTH_TAKE_EQ, arithmeticTheory.MIN_DEF] >> decide_tac) >>
  simp[val_in_memory_def] >>
  conj_tac
  >- (qspecl_then [`off`, `n2w (MIN n (LENGTH data)):bytes32`, `s`] mp_tac
        (Q.GENL [`dst`, `w`, `s`] hash_mload_write_word) >>
      simp[mload_def, mem_word_at_def, LENGTH_TAKE_EQ]) >>
  `mem_bytes_at (off + 32) (MIN n (LENGTH data))
     (write_memory_with_expansion off
       (word_to_bytes (n2w (MIN n (LENGTH data)):bytes32) T) s).vs_memory =
   mem_bytes_at (off + 32) (MIN n (LENGTH data)) s.vs_memory` by
    (irule hash_write_memory_disjoint >> simp[byteTheory.LENGTH_word_to_bytes]) >>
  gvs[LENGTH_TAKE_EQ]
QED

(* The header store is valid even while DALLOCA has temporarily moved FMP. *)
Theorem raw_call_output_store_run[local]:
  !sa sb ptr cap s w n data.
    emit_void MSTORE [ptr;cap] sa = ((),sb) /\
    eval_operand ptr s = SOME w /\
    eval_operand cap s = SOME (n2w (MIN n (LENGTH data))) /\
    fresh_vars_wrt sa s /\
    mem_bytes_at (w2n w + 32) (LENGTH (TAKE n data)) s.vs_memory = TAKE n data ==>
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      t = mstore (w2n w) (n2w (MIN n (LENGTH data))) s /\
      val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV (TAKE n data))
        (w2n w) t.vs_memory /\
      fresh_vars_wrt sb t /\
      (!op v. eval_operand op s = SOME v ==> eval_operand op t = SOME v)
Proof
  rpt strip_tac >> drule_all emit_void_MSTORE_correct >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >>
  drule raw_call_output_length_memory >>
  simp[mstore_def, write_memory_with_expansion_def]
QED

Theorem raw_call_output_store_frame[local]:
  !ctx func cenv cx es s saved inst q b sz w len.
    stmt_state_rel ctx func cenv cx es (s with vs_fmp := saved) /\
    fn_inst_ids_distinct func /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
    b <= w2n w /\ w2n w + 32 <= b + sz ==>
    stmt_state_rel ctx func cenv cx es
      ((mstore (w2n w) len s) with vs_fmp := saved)
Proof
  rpt strip_tac >>
  `((mstore (w2n w) len s) with vs_fmp := saved) =
    write_memory_with_expansion (w2n w) (word_to_bytes len T)
      (s with vs_fmp := saved)` by
    simp[mstore_def, write_memory_with_expansion_def] >>
  asm_rewrite_tac[] >> irule raw_call_outbuf_write_frame >>
  simp[byteTheory.LENGTH_word_to_bytes] >>
  qexistsl_tac [`b`, `inst`, `q`, `sz`] >> simp[]
QED

Theorem raw_call_restore_run[local]:
  !sa sb op s saved.
    emit_void SETFMP [op] sa = ((),sb) /\
    eval_operand op s = SOME saved /\ fresh_vars_wrt sa s ==>
    run_inst_seq (emitted_insts sa sb) s = OK (s with vs_fmp := saved) /\
    fresh_vars_wrt sb (s with vs_fmp := saved) /\
    (!p w. eval_operand p s = SOME w ==>
           eval_operand p (s with vs_fmp := saved) = SOME w)
Proof
  rpt strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >> gvs[] >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def] >>
  drule emit_void_extends >> strip_tac >>
  gvs[fresh_vars_wrt_def, eval_operand_def, lookup_var_def,
      emit_void_def, comp_bind_def, fresh_id_def, emit_def, comp_return_def] >>
  Cases_on `p` >> gvs[eval_operand_def, lookup_var_def]
QED

Theorem raw_call_output_code[local]:
  !sa z s1 cmp s2 cap s3 s4 sb pop dop n.
    emit_op RETURNDATASIZE [] sa = (z,s1) /\
    emit_op LT [z;Lit (n2w n)] s1 = (cmp,s2) /\
    compile_select cmp z (Lit (n2w n)) s2 = (cap,s3) /\
    emit_void MSTORE [pop;cap] s3 = ((),s4) /\
    emit_void SETFMP [dop] s4 = ((),sb) ==>
    sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
    isPREFIX sa.cs_current_insts sb.cs_current_insts /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb)
Proof
  rpt strip_tac >>
  gvs[builtinSimpleTheory.compile_select_def, comp_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  gvs[emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  simp[rich_listTheory.IS_PREFIX_APPEND, emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[mk_inst_def, is_terminator_def]
QED

Theorem raw_call_output_restore_run[local]:
  !sa z s1 cmp s2 cap s3 s4 sb pop dop s w saved n.
    emit_op RETURNDATASIZE [] sa = (z,s1) /\
    emit_op LT [z;Lit (n2w n)] s1 = (cmp,s2) /\
    compile_select cmp z (Lit (n2w n)) s2 = (cap,s3) /\
    emit_void MSTORE [pop;cap] s3 = ((),s4) /\
    emit_void SETFMP [dop] s4 = ((),sb) /\
    fresh_vars_wrt sa s /\ n < dimword (:256) /\
    LENGTH s.vs_returndata < dimword (:256) /\
    eval_operand pop s = SOME w /\ eval_operand dop s = SOME saved /\
    mem_bytes_at (w2n w + 32) (LENGTH (TAKE n s.vs_returndata)) s.vs_memory =
      TAKE n s.vs_returndata ==>
    ?t u. run_inst_seq (emitted_insts sa sb) s = OK t /\
      vars_ext s u /\
      t = (mstore (w2n w) (n2w (MIN n (LENGTH s.vs_returndata))) u)
            with vs_fmp := saved /\
      val_in_memory (BaseTV (BytesT (Dynamic n)))
        (BytesV (TAKE n s.vs_returndata)) (w2n w) t.vs_memory /\
      fresh_vars_wrt sb t /\
      (!op v. eval_operand op s = SOME v ==> eval_operand op t = SOME v)
Proof
  rpt strip_tac >>
  `inst_extends sa s3` by
    (drule compile_select_extends >> strip_tac >>
     irule inst_extends_trans >> qexists_tac `s1` >> conj_tac
     >- (irule inst_extends_emit_op >> goal_assum (drule_at Any)) >>
     irule inst_extends_trans >> qexists_tac `s2` >> conj_tac
     >- (irule inst_extends_emit_op >> goal_assum (drule_at Any)) >>
     simp[inst_extends_def]) >>
  drule_all raw_call_cap_run >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  `vars_ext s u` by
    (simp[varsExtTheory.vars_ext_def, finite_mapTheory.SUBMAP_FLOOKUP_EQN] >>
     rpt strip_tac >>
     qpat_x_assum `!op v. eval_operand op s = SOME v ==> _`
       (qspec_then `Var x` mp_tac) >>
     simp[eval_operand_def, lookup_var_def]) >>
  `eval_operand pop u = SOME w /\ eval_operand dop u = SOME saved` by metis_tac[] >>
  `mem_bytes_at (w2n w + 32) (LENGTH (TAKE n s.vs_returndata)) u.vs_memory =
    TAKE n s.vs_returndata` by gvs[] >>
  drule_all raw_call_output_store_run >>
  disch_then (qx_choose_then `v` strip_assume_tac) >>
  `eval_operand dop v = SOME saved` by metis_tac[] >>
  drule_all raw_call_restore_run >> strip_tac >>
  qexistsl_tac [`v with vs_fmp := saved`, `u`] >>
  conj_tac
  >- (`inst_extends s3 s4 /\ inst_extends s4 sb` by
        (conj_tac >> irule inst_extends_emit_void >> goal_assum (drule_at Any)) >>
      `inst_extends sa s4` by
        (irule inst_extends_trans >> qexists_tac `s3` >> simp[]) >>
      irule run_inst_seq_compose_ok >> qexistsl_tac [`v`, `s4`] >> simp[] >>
      irule run_inst_seq_compose_ok >> qexistsl_tac [`u`, `s3`] >> simp[]) >>
  simp[] >> metis_tac[]
QED

Theorem raw_call_output_restore_frame[local]:
  !ctx func cenv cx es s u t saved inst q b sz w len.
    stmt_state_rel ctx func cenv cx es (s with vs_fmp := saved) /\
    vars_ext s u /\
    t = (mstore (w2n w) len u) with vs_fmp := saved /\
    fn_inst_ids_distinct func /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
    b <= w2n w /\ w2n w + 32 <= b + sz ==>
    stmt_state_rel ctx func cenv cx es t
Proof
  rpt strip_tac >>
  `vars_ext (s with vs_fmp := saved) (u with vs_fmp := saved)` by
    (qpat_x_assum `vars_ext _ _` mp_tac >>
     simp[varsExtTheory.vars_ext_def] >> strip_tac >>
     qpat_x_assum `u = _` SUBST1_TAC >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es (u with vs_fmp := saved)` by
    (irule stmt_state_rel_vars_ext >> goal_assum (drule_at Any) >> simp[]) >>
  gvs[] >> irule raw_call_output_store_frame >> simp[] >>
  qexistsl_tac [`b`, `inst`, `q`, `sz`] >> simp[] >>
  qpat_x_assum `vars_ext s u` mp_tac >>
  simp[varsExtTheory.vars_ext_def] >> strip_tac >>
  qpat_x_assum `u = _` SUBST1_TAC >> simp[]
QED

Theorem raw_call_output_restore_frag[local]:
  !ctx func cenv cx es sa z s1 cmp s2 cap s3 s4 sb pop dop s w saved n inst q b sz.
    emit_op RETURNDATASIZE [] sa = (z,s1) /\
    emit_op LT [z;Lit (n2w n)] s1 = (cmp,s2) /\
    compile_select cmp z (Lit (n2w n)) s2 = (cap,s3) /\
    emit_void MSTORE [pop;cap] s3 = ((),s4) /\
    emit_void SETFMP [dop] s4 = ((),sb) /\
    fresh_vars_wrt sa s /\ n < dimword (:256) /\
    LENGTH s.vs_returndata < dimword (:256) /\
    eval_operand pop s = SOME w /\ eval_operand dop s = SOME saved /\
    mem_bytes_at (w2n w + 32) (LENGTH (TAKE n s.vs_returndata)) s.vs_memory =
      TAKE n s.vs_returndata /\
    stmt_state_rel ctx func cenv cx es (s with vs_fmp := saved) /\
    fn_inst_ids_distinct func /\ MEM inst (fn_insts func) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [q] /\
    not_local_ptr cenv es.scopes q /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
    b <= w2n w /\ w2n w + 32 <= b + sz ==>
    frag_path ctx sa sb (\r. r = s)
      (\r. stmt_state_rel ctx func cenv cx es r /\
        val_in_memory (BaseTV (BytesT (Dynamic n)))
          (BytesV (TAKE n s.vs_returndata)) (w2n w) r.vs_memory /\
        r.vs_fmp = saved /\ fresh_vars_wrt sb r /\
        (!op v. eval_operand op s = SOME v ==> eval_operand op r = SOME v))
      (\r. F)
Proof
  rpt strip_tac >> drule_all raw_call_output_code >> strip_tac >>
  irule frag_path_run_inst_seq >> simp[] >>
  rpt strip_tac >> gvs[] >>
  drule_all raw_call_output_restore_run >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es t` by
    (drule_all raw_call_output_restore_frame >> simp[]) >>
  qexists_tac `t` >>
  simp[stmt_state_rel_inst_idx, fresh_vars_wrt_def,
       instIdxIndepTheory.eval_op_inst_idx] >>
  gvs[fresh_vars_wrt_def]
QED

(* With no output the continuation is just SETFMP; the result is Lit 0w. *)
Theorem raw_call_empty_restore_frag[local]:
  !ctx func cenv cx es sa sb dop s saved.
    emit_void SETFMP [dop] sa = ((),sb) /\
    eval_operand dop s = SOME saved /\ fresh_vars_wrt sa s /\
    stmt_state_rel ctx func cenv cx es (s with vs_fmp := saved) ==>
    frag_path ctx sa sb (\r. r = s)
      (\r. stmt_state_rel ctx func cenv cx es r /\
        r.vs_fmp = saved /\ fresh_vars_wrt sb r /\
        eval_operand (Lit 0w) r = SOME 0w /\
        (!op v. eval_operand op s = SOME v ==> eval_operand op r = SOME v))
      (\r. F)
Proof
  rpt strip_tac >>
  `sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
   isPREFIX sa.cs_current_insts sb.cs_current_insts /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb)` by
    (drule emitted_insts_emit_void >> strip_tac >>
     drule emit_void_extends >> strip_tac >>
     simp[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND, mk_inst_def,
          is_terminator_def] >> gvs[same_blocks_def]) >>
  irule frag_path_run_inst_seq >> simp[] >> rpt strip_tac >> gvs[] >>
  drule_all raw_call_restore_run >> strip_tac >>
  qexists_tac `s with vs_fmp := saved` >>
  simp[stmt_state_rel_inst_idx, fresh_vars_wrt_def, eval_operand_def,
       instIdxIndepTheory.eval_op_inst_idx] >>
  gvs[fresh_vars_wrt_def]
QED

(* Bounded output writes leave protected allocations and local regions alone.
   The cutoff is before output allocation, not the start of the finish code. *)
Theorem raw_call_outbuf_write_regions[local]:
  !ctx func cenv cx es s inst q b sz dst data cutoff.
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    MEM inst (fn_insts func) /\ inst.inst_outputs = [q] /\
    not_local_ptr cenv es.scopes q /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
    cutoff <= inst.inst_id /\ b <= dst /\ dst + LENGTH data <= b + sz ==>
    (!aid off len. aid < cutoff /\
       FLOOKUP s.vs_allocas aid = SOME (off,len) ==>
       mem_bytes_at off len (write_memory_with_expansion dst data s).vs_memory =
       mem_bytes_at off len s.vs_memory) /\
    (!name off len. local_region cenv es.scopes s name off len ==>
       mem_bytes_at off len (write_memory_with_expansion dst data s).vs_memory =
       mem_bytes_at off len s.vs_memory)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (rpt strip_tac >>
      `aid <> inst.inst_id` by decide_tac >>
      `regions_disjoint b sz off len` by
        metis_tac[state_allocations_disjoint] >>
      irule hash_write_memory_disjoint >> gvs[regions_disjoint_def] >> decide_tac) >>
  rpt strip_tac >> drule_all alloca_clear_of_locals >> strip_tac >>
  irule hash_write_memory_disjoint >> decide_tac
QED

Theorem raw_call_outbuf_wb_frame[local]:
  !ctx func cenv cx es es1 sa s0 s inst q b sz dst data.
    wb_frame cenv es es1 sa s0 s /\
    stmt_state_rel ctx func cenv cx es1 s /\ fn_inst_ids_distinct func /\
    MEM inst (fn_insts func) /\ inst.inst_outputs = [q] /\
    not_local_ptr cenv es1.scopes q /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
    sa.cs_next_id <= inst.inst_id /\ b <= dst /\ dst + LENGTH data <= b + sz /\
    local_ptrs_reserved cenv sa /\ MAP FDOM es.scopes = MAP FDOM es1.scopes ==>
    wb_frame cenv es es1 sa s0 (write_memory_with_expansion dst data s)
Proof
  rpt strip_tac >> drule_all raw_call_outbuf_write_regions >> strip_tac >>
  irule wb_frame_allocating_tail >> conj_tac >- simp[] >>
  qexistsl_tac [`s`, `es1.scopes`, `sa`] >>
  gvs[write_memory_with_expansion_def, lookup_var_def] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Theorem raw_call_outbuf_mstore_wb_frame[local]:
  !ctx func cenv cx es es1 sa s0 s inst q b sz dst w.
    wb_frame cenv es es1 sa s0 s /\
    stmt_state_rel ctx func cenv cx es1 s /\ fn_inst_ids_distinct func /\
    MEM inst (fn_insts func) /\ inst.inst_outputs = [q] /\
    not_local_ptr cenv es1.scopes q /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
    sa.cs_next_id <= inst.inst_id /\ b <= dst /\ dst + 32 <= b + sz /\
    local_ptrs_reserved cenv sa /\ MAP FDOM es.scopes = MAP FDOM es1.scopes ==>
    wb_frame cenv es es1 sa s0 (mstore dst w s)
Proof
  rpt strip_tac >>
  `mstore dst w s = write_memory_with_expansion dst (word_to_bytes w T) s` by
    simp[mstore_def, write_memory_with_expansion_def] >>
  pop_assum SUBST1_TAC >>
  `dst + LENGTH (word_to_bytes w T) <= b + sz` by simp[] >>
  drule_all raw_call_outbuf_wb_frame >> simp[]
QED

Theorem calldata_memory_wb_frame[local]:
  !ctx func cenv cx es es1 sf s0 s sa pop len sb t.
    compile_msg_data_to_memory sa = ((pop,len),sb) /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es1 s /\
    EXISTS (\inst. inst.inst_opcode = DALLOCA) (fn_insts func) /\
    wb_frame cenv es es1 sf s0 s /\ local_ptrs_reserved cenv sf /\
    sf.cs_next_var <= sa.cs_next_var /\ sf.cs_next_id <= sa.cs_next_id /\
    MAP FDOM es.scopes = MAP FDOM es1.scopes ==>
    wb_frame cenv es es1 sf s0 t
Proof
  rpt strip_tac >> drule_all calldata_memory_readback >> strip_tac >> gvs[] >>
  `s.vs_alloca_next <= w2n s.vs_fmp` by
    (irule calldata_memory_frontier >> qexistsl_tac [`ctx`, `func`] >>
     gvs[stmt_state_rel_def]) >>
  `!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
     b + sz <= w2n s.vs_fmp` by
    metis_tac[calldata_outbuf_below_fmp] >>
  `!name b sz. local_region cenv es1.scopes s name b sz ==>
     b + sz <= w2n s.vs_fmp` by
    (rpt strip_tac >>
     `local_ptrs_rel func cenv es1.scopes s` by gvs[stmt_state_rel_def, state_rel_def] >>
     qpat_x_assum `local_ptrs_rel _ _ _ _` mp_tac >>
     gvs[local_ptrs_rel_def, local_region_def] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS, optionTheory.SOME_11]) >>
  irule wb_frame_allocating_tail >> conj_tac >- simp[] >>
  qexistsl_tac [`s`, `es1.scopes`, `sa`] >> simp[] >>
  rpt conj_tac >> rpt strip_tac >> first_x_assum irule >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem calldata_outbuf_framed_run[local]:
  !n sa valop ptrop sb ctx func cenv cx es es1 sf s0 s.
    (if n = 0 then 0 else ((n + 31) DIV 32) * 32 + 32) < dimword (:256) /\
    compile_raw_call_outbuf n sa = ((valop,ptrop),sb) /\
    stmt_state_rel ctx func cenv cx es1 s /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\
    MEM (mk_inst sa.cs_next_id ALLOCA
      [Lit (n2w (if n = 0 then 0 else ((n + 31) DIV 32) * 32 + 32))]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) /\
    wb_frame cenv es es1 sf s0 s /\ sf.cs_next_var <= sa.cs_next_var ==>
    ?t w. run_inst_seq (emitted_insts sa sb) s = OK t /\
      stmt_state_rel ctx func cenv cx es1 t /\ wb_frame cenv es es1 sf s0 t /\
      eval_operand valop t = SOME w /\
      eval_operand ptrop t = SOME (if n = 0 then w else w + 32w) /\
      FLOOKUP t.vs_allocas sa.cs_next_id =
        SOME (w2n w,if n = 0 then 0 else ((n + 31) DIV 32) * 32 + 32) /\
      w2n w + (if n = 0 then 0 else ((n + 31) DIV 32) * 32 + 32) < dimword (:256) /\
      t.vs_memory = s.vs_memory /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
         FLOOKUP t.vs_allocas aid = SOME entry)
Proof
  rpt gen_tac >> strip_tac >> Cases_on `n = 0`
  >- (gvs[] >> drule_all calldata_outbuf_zero_run >> strip_tac >>
      `wb_frame cenv es es1 sf s0 t` by
        (irule wb_frame_readonly_tail >> goal_assum (drule_at Any) >>
         qexists_tac `sa` >> simp[]) >>
      qexistsl_tac [`t`, `w`] >> simp[]) >>
  `0 < n` by decide_tac >> gvs[] >>
  drule_all (ONCE_REWRITE_RULE [arithmeticTheory.MULT_COMM]
    calldata_outbuf_positive_run) >> strip_tac >>
  `wb_frame cenv es es1 sf s0 t` by
    (irule wb_frame_readonly_tail >> goal_assum (drule_at Any) >>
     qexists_tac `sa` >> simp[]) >>
  qexistsl_tac [`t`, `w`] >> simp[]
QED

Theorem calldata_write_state_rel[local]:
  !ctx func cenv cx es s data.
    stmt_state_rel ctx func cenv cx es s /\
    EXISTS (\inst. inst.inst_opcode = DALLOCA) (fn_insts func) ==>
    stmt_state_rel ctx func cenv cx es
      (write_memory_with_expansion (w2n s.vs_fmp) data s)
Proof
  rpt strip_tac >>
  `s.vs_alloca_next <= w2n s.vs_fmp` by
    (irule calldata_memory_frontier >> qexistsl_tac [`ctx`, `func`] >>
     gvs[stmt_state_rel_def]) >>
  irule write_memory_stmt_state_rel >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      `local_ptrs_rel func cenv es.scopes s` by gvs[stmt_state_rel_def, state_rel_def] >>
      qpat_x_assum `local_ptrs_rel _ _ _ _` mp_tac >>
      gvs[local_ptrs_rel_def, local_region_def] >>
      metis_tac[arithmeticTheory.LESS_EQ_TRANS, optionTheory.SOME_11]) >>
  irule immutables_rel_mem_agree >> qexists_tac `s` >>
  rpt conj_tac
  >~ [`immutables_rel _ _ _ _ _ s`]
  >- gvs[stmt_state_rel_def, state_rel_def]
  >~ [`_.vs_data_section = _`]
  >- simp[write_memory_with_expansion_def]
  >~ [`LENGTH s.vs_memory <= LENGTH _`]
  >- (simp[write_memory_with_expansion_def] >>
      Cases_on `w2n s.vs_fmp + LENGTH data > LENGTH s.vs_memory` >>
      simp[LENGTH_TAKE, LENGTH_DROP, arithmeticTheory.MIN_DEF] >> decide_tac) >>
  rpt strip_tac >>
  `off + type_memory_size tv <= s.vs_alloca_next` by
    (qpat_x_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
     simp[stmt_state_rel_def, immutable_alloca_sep_def] >> metis_tac[]) >>
  irule hash_write_memory_disjoint >> decide_tac
QED

Theorem calldata_memory_state_rel[local]:
  !ctx func cenv cx es s sa pop len sb t.
    compile_msg_data_to_memory sa = ((pop,len),sb) /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
    EXISTS (\inst. inst.inst_opcode = DALLOCA) (fn_insts func) ==>
    stmt_state_rel ctx func cenv cx es (t with vs_fmp := s.vs_fmp)
Proof
  rpt strip_tac >> drule_all calldata_memory_run >> strip_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac `t.vs_memory = m.vs_memory` >>
  `stmt_state_rel ctx func cenv cx es m` by
    (simp[Abbr `m`] >> irule calldata_write_state_rel >> simp[]) >>
  `t with vs_fmp := s.vs_fmp = m with vs_vars := t.vs_vars` by
    (qpat_x_assum `t = s with <| vs_memory := _; vs_vars := _; vs_fmp := _ |>`
       (fn th => ONCE_REWRITE_TAC [th]) >>
     simp[Abbr `m`, write_memory_with_expansion_def]) >>
  pop_assum SUBST1_TAC >> irule stmt_state_rel_vars_frame >> simp[] >>
  rpt strip_tac >>
  qpat_x_assum `!x. not_fresh_at sa x ==> _` (qspec_then `p` mp_tac) >>
  gvs[local_ptrs_reserved_def, Abbr `m`, write_memory_with_expansion_def,
      lookup_var_def] >> metis_tac[]
QED

Theorem calldata_memory_framed_run[local]:
  !ctx func cenv cx es es1 sf s0 s sa pop len sb.
    compile_msg_data_to_memory sa = ((pop,len),sb) /\
    LENGTH s.vs_call_ctx.cc_calldata < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es1 s /\
    EXISTS (\inst. inst.inst_opcode = DALLOCA) (fn_insts func) /\
    wb_frame cenv es es1 sf s0 s /\ local_ptrs_reserved cenv sf /\
    local_ptrs_reserved cenv sa /\
    sf.cs_next_var <= sa.cs_next_var /\ sf.cs_next_id <= sa.cs_next_id /\
    MAP FDOM es.scopes = MAP FDOM es1.scopes ==>
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      wb_frame cenv es es1 sf s0 t /\
      stmt_state_rel ctx func cenv cx es1 (t with vs_fmp := s.vs_fmp) /\
      eval_operand pop t = SOME s.vs_fmp /\
      eval_operand len t = SOME (n2w (LENGTH s.vs_call_ctx.cc_calldata)) /\
      read_memory (w2n s.vs_fmp) (LENGTH s.vs_call_ctx.cc_calldata) t =
        s.vs_call_ctx.cc_calldata /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
      t.vs_call_ctx = s.vs_call_ctx /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  rpt strip_tac >> drule_all calldata_memory_readback >> strip_tac >>
  `wb_frame cenv es es1 sf s0 t` by
    (drule_all calldata_memory_wb_frame >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es1 (t with vs_fmp := s.vs_fmp)` by
    (drule_all calldata_memory_state_rel >> simp[]) >>
  qexists_tac `t` >> simp[]
QED

Theorem calldata_outbuf_operands:
  compile_raw_call_outbuf n sa = ((valop,ptrop),sb) ==>
  exprSafeOperand$safe_operand sb valop /\
  exprSafeOperand$safe_operand sb ptrop
Proof
  strip_tac >>
  `exprSafeOperand$safe_operand sb valop` by
    (simp[exprSafeOperandTheory.safe_operand_def] >> conj_tac
     >- metis_tac[exprOperandVarTheory.compiler_raw_call_outbuf_var] >>
     drule calldata_outbuf_compile >> strip_tac >>
     metis_tac[exprSafeOperandTheory.alloc_buffer_not_label]) >>
  simp[] >> drule calldata_outbuf_compile >> strip_tac >> Cases_on `n = 0`
  >- gvs[] >>
  gvs[] >> metis_tac[exprSafeOperandTheory.emit_op_safe_operand]
QED

Theorem calldata_prepare_code[local]:
  compile_raw_call_outbuf n sa = ((ov,op),sb) /\
  compile_msg_data_to_memory sb = ((dp,dl),sc) ==>
  same_blocks sa sb /\ same_blocks sb sc /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
  sc.cs_current_insts = sb.cs_current_insts ++ emitted_insts sb sc /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sc)
Proof
  Cases_on `n = 0` >>
  simp[compile_raw_call_outbuf_def, compile_alloc_buffer_def,
       compile_msg_data_to_memory_def, compile_alloc_dynamic_def,
       comp_bind_def, comp_return_def, comp_ignore_bind_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[same_blocks_def, emitted_insts_def,
    rich_listTheory.DROP_APPEND1, rich_listTheory.DROP_APPEND2,
    mk_inst_def, is_terminator_def]
QED

Theorem calldata_buffers_run[local]:
  !n sa ov op sb dp dl sc ctx func cenv cx es es1 sf s0 s.
    compile_raw_call_outbuf n sa = ((ov,op),sb) /\
    compile_msg_data_to_memory sb = ((dp,dl),sc) /\
    (if n = 0 then 0 else ((n + 31) DIV 32) * 32 + 32) < dimword (:256) /\
    LENGTH cx.txn.calldata < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es1 s /\ fn_inst_ids_distinct func /\
    EXISTS (\inst. inst.inst_opcode = DALLOCA) (fn_insts func) /\
    MEM (mk_inst sa.cs_next_id ALLOCA
      [Lit (n2w (if n = 0 then 0 else ((n + 31) DIV 32) * 32 + 32))]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) /\
    local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sf /\
    sf.cs_next_var <= sa.cs_next_var /\ sf.cs_next_id <= sa.cs_next_id /\
    MAP FDOM es.scopes = MAP FDOM es1.scopes /\ wb_frame cenv es es1 sf s0 s ==>
    ?u t w. run_inst_seq (emitted_insts sa sb) s = OK u /\
      run_inst_seq (emitted_insts sa sc) s = OK t /\
      wb_frame cenv es es1 sf s0 t /\
      stmt_state_rel ctx func cenv cx es1 (t with vs_fmp := u.vs_fmp) /\
      eval_operand dp t = SOME u.vs_fmp /\
      eval_operand dl t = SOME (n2w (LENGTH cx.txn.calldata)) /\
      read_memory (w2n u.vs_fmp) (LENGTH cx.txn.calldata) t = cx.txn.calldata /\
      eval_operand ov t = SOME w /\
      eval_operand op t = SOME (if n = 0 then w else w + 32w) /\
      FLOOKUP t.vs_allocas sa.cs_next_id =
        SOME (w2n w,if n = 0 then 0 else ((n + 31) DIV 32) * 32 + 32) /\
      w2n w + (if n = 0 then 0 else ((n + 31) DIV 32) * 32 + 32) < dimword (:256) /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  rpt gen_tac >> strip_tac >>
  `ci_mono sa sb` by metis_tac[ci_mono_compile_raw_call_outbuf, SND] >>
  `local_ptrs_reserved cenv sb` by
    metis_tac[exprOperandVarTheory.compiler_ci_mono_reserved] >>
  `sf.cs_next_var <= sb.cs_next_var /\ sf.cs_next_id <= sb.cs_next_id` by
    (fs[ci_mono_def] >> decide_tac) >>
  drule_all calldata_prepare_code >> strip_tac >>
  drule_all calldata_outbuf_framed_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sb) s = OK u` >>
  `u.vs_call_ctx.cc_calldata = cx.txn.calldata` by
    gvs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  `LENGTH u.vs_call_ctx.cc_calldata < dimword (:256)` by simp[] >>
  drule_all calldata_memory_framed_run >> strip_tac >>
  `eval_operand ov t = eval_operand ov u /\
   eval_operand op t = eval_operand op u` by
    (drule calldata_outbuf_operands >> strip_tac >> conj_tac >>
     Cases_on `ov` >> Cases_on `op` >>
     gvs[eval_operand_def, exprSafeOperandTheory.safe_operand_def] >>
     qpat_x_assum `!x. not_fresh_at sb x ==> _` irule >> simp[]) >>
  drule_all run_inst_seq_chain >> strip_tac >>
  qexistsl_tac [`u`, `t`, `w`] >> simp[] >> conj_tac
  >- (qpat_x_assum `read_memory _ _ t = _` mp_tac >> simp[]) >>
  rpt strip_tac >>
  `not_fresh_at sb x` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >>
     gvs[ci_mono_def]) >>
  qpat_x_assum `!x. not_fresh_at sb x ==> _` (qspec_then `x` mp_tac) >>
  qpat_x_assum `!x. not_fresh_at sa x ==> _` (qspec_then `x` mp_tac) >> simp[]

QED

Theorem calldata_gas_framed_run[local]:
  !go sa gas sb ctx func cenv cx es es1 sf s0 s.
    (case go of SOME g => (g,sa) | NONE => emit_op GAS [] sa) = (gas,sb) /\
    local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es1 s /\
    wb_frame cenv es es1 sf s0 s /\ sf.cs_next_var <= sa.cs_next_var ==>
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      stmt_state_rel ctx func cenv cx es1 t /\ wb_frame cenv es es1 sf s0 t /\
      eval_operand gas t =
        (case go of SOME g => eval_operand g s | NONE => SOME (HD (s.vs_gas_readings ++ [0w]))) /\
      t.vs_fmp = s.vs_fmp /\ t.vs_call_ctx = s.vs_call_ctx /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s)
Proof
  rpt gen_tac >> Cases_on `go`
  >- (simp[] >> strip_tac >> drule_all calldata_default_gas >> strip_tac >>
      `t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
       t.vs_fmp = s.vs_fmp /\ t.vs_call_ctx = s.vs_call_ctx` by
        (qpat_x_assum `t = s with <| vs_vars := _; vs_gas_readings := _ |>`
          (fn th => ONCE_REWRITE_TAC [th]) >> simp[]) >>
      `wb_frame cenv es es1 sf s0 t` by
        (irule wb_frame_readonly_tail >>
         qexistsl_tac [`sa`, `s`] >> simp[]) >>
      qexists_tac `t` >> simp[]) >>
  simp[] >> strip_tac >> gvs[] >> qexists_tac `s` >>
  simp[emitted_insts_refl, run_inst_seq_def]
QED

Theorem calldata_outbuf_fmp[local]:
  !n sa ov op sb s u.
    compile_raw_call_outbuf n sa = ((ov,op),sb) /\
    run_inst_seq (emitted_insts sa sb) s = OK u ==>
    u.vs_fmp = s.vs_fmp
Proof
  rpt gen_tac >> Cases_on `n = 0` >>
  simp[compile_raw_call_outbuf_def, compile_alloc_buffer_def,
       comp_bind_def, comp_return_def, comp_ignore_bind_def, emit_op_def,
       fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[emitted_insts_def, rich_listTheory.DROP_APPEND1] >>
  gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
      eval_operand_def, exec_alloca_def, AllCaseEqs(),
      exec_pure2_def, bind_outputs_def, update_var_def, lookup_var_def]
QED

Theorem raw_call_safe_operand_drop_fresh[local]:
  safe_operand sa p ==> eval_operand p (drop_fresh sa s) = eval_operand p s
Proof
  Cases_on `p` >> simp[safe_operand_def, eval_operand_def,
    lookup_var_drop_fresh, drop_fresh_def]
QED

Theorem raw_call_eval_vars_ext[local]:
  vars_ext s t /\ eval_operand p s = SOME w ==> eval_operand p t = SOME w
Proof
  rpt strip_tac >> fs[vars_ext_def] >>
  qpat_x_assum `t = s with vs_vars := _`
    (fn th => ONCE_REWRITE_TAC [th]) >>
  simp[eval_operand_vars_ext]
QED

Theorem raw_call_cap_arbitrary_run[local]:
  !sa z s1 cmp s2 cap sb s n.
    emit_op RETURNDATASIZE [] sa = (z,s1) /\
    emit_op LT [z;Lit (n2w n)] s1 = (cmp,s2) /\
    compile_select cmp z (Lit (n2w n)) s2 = (cap,sb) /\
    n < dimword (:256) /\ LENGTH s.vs_returndata < dimword (:256) ==>
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      eval_operand cap t = SOME (n2w (MIN n (LENGTH s.vs_returndata))) /\
      (?vars. t = s with vs_vars := vars) /\
      (!p. safe_operand sa p ==> eval_operand p t = eval_operand p s)
Proof
  rpt gen_tac >> strip_tac >>
  `fresh_vars_wrt sa (drop_fresh sa s)` by simp[fresh_vars_wrt_drop_fresh] >>
  `LENGTH (drop_fresh sa s).vs_returndata < dimword (:256)` by
    simp[drop_fresh_def] >>
  drule_all raw_call_cap_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sb) (drop_fresh sa s) = OK u` >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
       ~is_ext_call_op i.inst_opcode) (emitted_insts sa sb)` by
    (drule_all raw_call_cap_code >> rewrite_tac[EVERY_MEM] >> disch_tac >>
     gen_tac >> strip_tac >> first_x_assum drule >> simp[MEM] >> strip_tac >>
     gvs[is_terminator_def, is_ext_call_op_def]) >>
  `vars_ext_result (run_inst_seq (emitted_insts sa sb) (drop_fresh sa s))
    (run_inst_seq (emitted_insts sa sb) s)` by
    (irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh]) >>
  gvs[vars_ext_result_def] >> rename1 `vars_ext u t` >>
  drule_all raw_call_cap_run_frame >> strip_tac >>
  simp[] >> conj_tac
  >- (irule raw_call_eval_vars_ext >> qexists_tac `u` >>
      fs[drop_fresh_def]) >>
  conj_tac >- (qexists_tac `vars` >> simp[]) >>
  rpt strip_tac >> Cases_on `p` >>
  gvs[safe_operand_def, eval_operand_def, lookup_var_def]
QED

Definition calldata_prepared_def[local]:
  calldata_prepared ctx func cenv cx es es1 sf s0 entry sp sa n ov op dp dl t <=>
    wb_frame cenv es es1 sf s0 t /\
    stmt_state_rel ctx func cenv cx es1 (t with vs_fmp := entry.vs_fmp) /\
    eval_operand dp t = SOME entry.vs_fmp /\
    eval_operand dl t = SOME (n2w (LENGTH cx.txn.calldata)) /\
    read_memory (w2n entry.vs_fmp) (LENGTH cx.txn.calldata) t = cx.txn.calldata /\
    (?w. eval_operand ov t = SOME w /\
      eval_operand op t = SOME (if n = 0 then w else w + 32w) /\
      FLOOKUP t.vs_allocas sa.cs_next_id =
        SOME (w2n w,if n = 0 then 0 else ((n + 31) DIV 32) * 32 + 32) /\
      w2n w + (if n = 0 then 0 else ((n + 31) DIV 32) * 32 + 32) < dimword (:256)) /\
    (!p. safe_operand sp p ==> eval_operand p t = eval_operand p entry)
End

Theorem calldata_prepared_inst_idx[local]:
  calldata_prepared ctx func cenv cx es es1 sf s0 entry sp sa n ov op dp dl
    (t with vs_inst_idx := k) <=>
  calldata_prepared ctx func cenv cx es es1 sf s0 entry sp sa n ov op dp dl t
Proof
  simp[calldata_prepared_def, wb_frame_def, lookup_var_def,
       hash_eval_operand_inst_idx, read_memory_def,
       stmt_state_rel_inst_idx]
QED

Theorem calldata_buffers_prepared_run[local]:
  !n sa ov op sb dp dl sc ctx func cenv cx es es1 sf s0 s.
    compile_raw_call_outbuf n sa = ((ov,op),sb) /\
    compile_msg_data_to_memory sb = ((dp,dl),sc) /\
    (if n = 0 then 0 else ((n + 31) DIV 32) * 32 + 32) < dimword (:256) /\
    LENGTH cx.txn.calldata < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es1 s /\ fn_inst_ids_distinct func /\
    EXISTS (\inst. inst.inst_opcode = DALLOCA) (fn_insts func) /\
    MEM (mk_inst sa.cs_next_id ALLOCA
      [Lit (n2w (if n = 0 then 0 else ((n + 31) DIV 32) * 32 + 32))]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) /\
    local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sf /\
    sf.cs_next_var <= sa.cs_next_var /\ sf.cs_next_id <= sa.cs_next_id /\
    MAP FDOM es.scopes = MAP FDOM es1.scopes /\ wb_frame cenv es es1 sf s0 s ==>
    ?t. run_inst_seq (emitted_insts sa sc) s = OK t /\
      calldata_prepared ctx func cenv cx es es1 sf s0 s sa sa n ov op dp dl t
Proof
  rpt gen_tac >> strip_tac >> drule_all calldata_buffers_run >> strip_tac >>
  `u.vs_fmp = s.vs_fmp` by (drule_all calldata_outbuf_fmp >> simp[]) >>
  fs[] >> simp[calldata_prepared_def] >>
  rpt strip_tac >> Cases_on `p` >>
  gvs[safe_operand_def, eval_operand_def]
QED

Theorem calldata_gas_code[local]:
  (case go of SOME g => (g,sa) | NONE => emit_op GAS [] sa) = (gas,sg) ==>
  ci_mono sa sg /\ same_blocks sa sg /\
  sg.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sg /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sg) /\
  ((case go of NONE => T | SOME g => safe_operand sa g) ==> safe_operand sg gas)
Proof
  Cases_on `go` >>
  simp[emit_op_def, fresh_var_def, fresh_id_def, emit_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt strip_tac >> gvs[ci_mono_def, cs_extends_def, same_blocks_def, emitted_insts_def,
    rich_listTheory.DROP_APPEND1, mk_inst_def, is_terminator_def,
    safe_operand_def, not_fresh_at_def, ASCIInumbersTheory.toString_11]
QED

Theorem calldata_prepared_entry[local]:
  calldata_prepared ctx func cenv cx es es1 sf s0 mid sa sa n ov op dp dl t /\
  mid.vs_fmp = entry.vs_fmp /\ sp.cs_next_var <= sa.cs_next_var /\
  (!p. safe_operand sp p ==> eval_operand p mid = eval_operand p entry) ==>
  calldata_prepared ctx func cenv cx es es1 sf s0 entry sp sa n ov op dp dl t
Proof
  simp[calldata_prepared_def] >> rpt strip_tac >> simp[] >>
  metis_tac[safe_operand_mono]
QED

Definition calldata_prepare_pre_def[local]:
  calldata_prepare_pre ctx func cenv cx es es1 sf s0 sa sg n go s <=>
    (if n = 0 then 0 else ((n + 31) DIV 32) * 32 + 32) < dimword (:256) /\
    LENGTH cx.txn.calldata < dimword (:256) /\
    stmt_state_rel ctx func cenv cx es1 s /\ fn_inst_ids_distinct func /\
    EXISTS (\inst. inst.inst_opcode = DALLOCA) (fn_insts func) /\
    MEM (mk_inst sg.cs_next_id ALLOCA
      [Lit (n2w (if n = 0 then 0 else ((n + 31) DIV 32) * 32 + 32))]
      [STRING #"%" (toString sg.cs_next_var)]) (fn_insts func) /\
    local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sf /\
    sf.cs_next_var <= sa.cs_next_var /\ sf.cs_next_id <= sa.cs_next_id /\
    MAP FDOM es.scopes = MAP FDOM es1.scopes /\ wb_frame cenv es es1 sf s0 s /\
    (case go of NONE => T | SOME g => safe_operand sa g)
End

Theorem calldata_prepare_run[local]:
  (case go of SOME g => (g,sa) | NONE => emit_op GAS [] sa) = (gas,sg) /\
  compile_raw_call_outbuf n sg = ((ov,op),sb) /\
  compile_msg_data_to_memory sb = ((dp,dl),sc) /\
  calldata_prepare_pre ctx func cenv cx es es1 sf s0 sa sg n go s ==>
  ?t. run_inst_seq (emitted_insts sa sc) s = OK t /\
    calldata_prepared ctx func cenv cx es es1 sf s0 s sa sg n ov op dp dl t /\
    eval_operand gas t =
      (case go of SOME g => eval_operand g s | NONE => SOME (HD (s.vs_gas_readings ++ [0w])))
Proof
  strip_tac >> fs[calldata_prepare_pre_def] >>
  drule calldata_gas_code >> strip_tac >>
  `local_ptrs_reserved cenv sg` by
    metis_tac[exprOperandVarTheory.compiler_ci_mono_reserved] >>
  `sf.cs_next_var <= sg.cs_next_var /\ sf.cs_next_id <= sg.cs_next_id` by
    (fs[ci_mono_def] >> decide_tac) >>
  drule_all calldata_gas_framed_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sg) s = OK u` >>
  `!p. safe_operand sa p ==> eval_operand p u = eval_operand p s` by
    (rpt strip_tac >> Cases_on `p` >> gvs[safe_operand_def, eval_operand_def]) >>
  drule_all (ONCE_REWRITE_RULE [arithmeticTheory.MULT_COMM]
    calldata_buffers_prepared_run) >> strip_tac >>
  `calldata_prepared ctx func cenv cx es es1 sf s0 s sa sg n ov op dp dl t` by
    (irule calldata_prepared_entry >> conj_tac
     >- fs[ci_mono_def] >> qexists_tac `u` >> simp[]) >>
  `eval_operand gas t = eval_operand gas u` by
    (qpat_x_assum `calldata_prepared _ _ _ _ _ _ _ _ u _ _ _ _ _ _ _ t` mp_tac >>
     simp[calldata_prepared_def] >> strip_tac >>
     qpat_x_assum `!p. safe_operand sg p ==> _` irule >> simp[]) >>
  drule_all calldata_prepare_code >> strip_tac >>
  `emitted_insts sg sc = emitted_insts sg sb ++ emitted_insts sb sc` by
    (irule emitted_insts_append >> simp[]) >>
  `sc.cs_current_insts = sg.cs_current_insts ++ emitted_insts sg sc` by
    simp[APPEND_ASSOC] >>
  drule_all run_inst_seq_chain >> strip_tac >>
  qexists_tac `t` >> simp[]
QED

Theorem calldata_prepare_shape[local]:
  (case go of SOME g => (g,sa) | NONE => emit_op GAS [] sa) = (gas,sg) /\
  compile_raw_call_outbuf n sg = ((ov,op),sb) /\
  compile_msg_data_to_memory sb = ((dp,dl),sc) ==>
  same_blocks sa sc /\
  sc.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sc /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sc)
Proof
  strip_tac >> drule calldata_gas_code >> strip_tac >>
  drule_all calldata_prepare_code >> strip_tac >>
  `emitted_insts sg sc = emitted_insts sg sb ++ emitted_insts sb sc` by
    (irule emitted_insts_append >> simp[]) >>
  `sc.cs_current_insts = sg.cs_current_insts ++ emitted_insts sg sc` by
    simp[APPEND_ASSOC] >>
  `emitted_insts sa sc = emitted_insts sa sg ++ emitted_insts sg sc` by
    (irule emitted_insts_append >> simp[]) >>
  fs[same_blocks_def, EVERY_APPEND, APPEND_ASSOC]
QED

Theorem calldata_prepare_frag[local]:
  (case go of SOME g => (g,sa) | NONE => emit_op GAS [] sa) = (gas,sg) /\
  compile_raw_call_outbuf n sg = ((ov,op),sb) /\
  compile_msg_data_to_memory sb = ((dp,dl),sc) ==>
  frag_path vctx sa sc
    (\s. s = entry /\ calldata_prepare_pre ctx func cenv cx es es1 sf s0 sa sg n go s)
    (\t. calldata_prepared ctx func cenv cx es es1 sf s0 entry sa sg n ov op dp dl t /\
      eval_operand gas t =
        (case go of SOME g => eval_operand g entry |
          NONE => SOME (HD (entry.vs_gas_readings ++ [0w])))) R
Proof
  strip_tac >> drule_all calldata_prepare_shape >> strip_tac >>
  fs[same_blocks_def] >> irule frag_path_run_inst_seq >> simp[] >>
  rpt strip_tac >> gvs[] >> disj1_tac >>
  drule_all calldata_prepare_run >> strip_tac >>
  qexists_tac `t` >> simp[calldata_prepared_inst_idx]
QED

Theorem raw_call_restore_arbitrary_run[local]:
  emit_void SETFMP [op] sa = ((),sb) /\ eval_operand op s = SOME saved ==>
  run_inst_seq (emitted_insts sa sb) s = OK (s with vs_fmp := saved) /\
  (!p. eval_operand p (s with vs_fmp := saved) = eval_operand p s)
Proof
  strip_tac >> drule emitted_insts_emit_void >> strip_tac >> gvs[] >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def] >>
  Cases_on `p` >> simp[eval_operand_def, lookup_var_def]
QED

Theorem raw_call_output_store_arbitrary_run[local]:
  !sa sb ptr cap s w n data.
  emit_void MSTORE [ptr;cap] sa = ((),sb) /\
  eval_operand ptr s = SOME w /\
  eval_operand cap s = SOME (n2w (MIN n (LENGTH data))) /\
  mem_bytes_at (w2n w + 32) (LENGTH (TAKE n data)) s.vs_memory = TAKE n data ==>
  run_inst_seq (emitted_insts sa sb) s =
    OK (mstore (w2n w) (n2w (MIN n (LENGTH data))) s) /\
  val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV (TAKE n data))
    (w2n w) (mstore (w2n w) (n2w (MIN n (LENGTH data))) s).vs_memory /\
  (!p. eval_operand p (mstore (w2n w) (n2w (MIN n (LENGTH data))) s) =
       eval_operand p s)
Proof
  rpt gen_tac >> strip_tac >> drule emitted_insts_emit_void >> strip_tac >> gvs[] >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_write2_def] >>
  drule raw_call_output_length_memory >>
  simp[mstore_def, write_memory_with_expansion_def]
QED

Theorem raw_call_output_prefix_run[local]:
  !sa z s1 cmp s2 cap s3 sb pop s w n.
    emit_op RETURNDATASIZE [] sa = (z,s1) /\
    emit_op LT [z;Lit (n2w n)] s1 = (cmp,s2) /\
    compile_select cmp z (Lit (n2w n)) s2 = (cap,s3) /\
    emit_void MSTORE [pop;cap] s3 = ((),sb) /\
    safe_operand sa pop /\ n < dimword (:256) /\
    LENGTH s.vs_returndata < dimword (:256) /\ eval_operand pop s = SOME w /\
    mem_bytes_at (w2n w + 32) (LENGTH (TAKE n s.vs_returndata)) s.vs_memory =
      TAKE n s.vs_returndata ==>
    ?t u. run_inst_seq (emitted_insts sa sb) s = OK t /\
      (?vars. u = s with vs_vars := vars) /\
      t = mstore (w2n w) (n2w (MIN n (LENGTH s.vs_returndata))) u /\
      val_in_memory (BaseTV (BytesT (Dynamic n)))
        (BytesV (TAKE n s.vs_returndata)) (w2n w) t.vs_memory /\
      (!p. safe_operand sa p ==> eval_operand p u = eval_operand p s) /\
      (!p. safe_operand sa p ==> eval_operand p t = eval_operand p s)
Proof
  rpt gen_tac >> strip_tac >> drule_all raw_call_cap_arbitrary_run >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  `eval_operand pop u = SOME w` by simp[] >>
  `u.vs_memory = s.vs_memory /\ u.vs_returndata = s.vs_returndata` by
    (qpat_x_assum `u = s with vs_vars := _` SUBST1_TAC >> simp[]) >>
  `mem_bytes_at (w2n w + 32) (LENGTH (TAKE n s.vs_returndata)) u.vs_memory =
    TAKE n s.vs_returndata` by simp[] >>
  drule_all raw_call_output_store_arbitrary_run >> strip_tac >>
  qexistsl_tac [`mstore (w2n w) (n2w (MIN n (LENGTH s.vs_returndata))) u`, `u`] >>
  simp[] >> conj_tac
  >- (`inst_extends sa s3` by
        (drule compile_select_extends >> strip_tac >>
         irule inst_extends_trans >> qexists_tac `s1` >> conj_tac
         >- (irule inst_extends_emit_op >> goal_assum (drule_at Any)) >>
         irule inst_extends_trans >> qexists_tac `s2` >> conj_tac
         >- (irule inst_extends_emit_op >> goal_assum (drule_at Any)) >>
         simp[inst_extends_def]) >>
      `inst_extends s3 sb` by
        (irule inst_extends_emit_void >> goal_assum (drule_at Any)) >>
      irule run_inst_seq_compose_ok >> qexistsl_tac [`u`, `s3`] >> simp[]) >>
  qexists_tac `vars` >> simp[]
QED

Theorem raw_call_output_restore_arbitrary_run[local]:
  !sa z s1 cmp s2 cap s3 s4 sb pop dop s w saved n.
    emit_op RETURNDATASIZE [] sa = (z,s1) /\
    emit_op LT [z;Lit (n2w n)] s1 = (cmp,s2) /\
    compile_select cmp z (Lit (n2w n)) s2 = (cap,s3) /\
    emit_void MSTORE [pop;cap] s3 = ((),s4) /\
    emit_void SETFMP [dop] s4 = ((),sb) /\
    safe_operand sa pop /\ safe_operand sa dop /\ n < dimword (:256) /\
    LENGTH s.vs_returndata < dimword (:256) /\
    eval_operand pop s = SOME w /\ eval_operand dop s = SOME saved /\
    mem_bytes_at (w2n w + 32) (LENGTH (TAKE n s.vs_returndata)) s.vs_memory =
      TAKE n s.vs_returndata ==>
    ?t u. run_inst_seq (emitted_insts sa sb) s = OK t /\
      (?vars. u = s with vs_vars := vars) /\
      t = (mstore (w2n w) (n2w (MIN n (LENGTH s.vs_returndata))) u)
        with vs_fmp := saved /\
      val_in_memory (BaseTV (BytesT (Dynamic n)))
        (BytesV (TAKE n s.vs_returndata)) (w2n w) t.vs_memory /\
      (!p v. safe_operand sa p /\ eval_operand p s = SOME v ==>
        eval_operand p u = SOME v) /\
      (!p v. safe_operand sa p /\ eval_operand p s = SOME v ==>
        eval_operand p t = SOME v)
Proof
  rpt gen_tac >> strip_tac >> drule_all raw_call_output_prefix_run >> strip_tac >>
  `eval_operand dop t = SOME saved` by simp[] >>
  drule_all raw_call_restore_arbitrary_run >> strip_tac >>
  qexistsl_tac [`t with vs_fmp := saved`, `u`] >> simp[] >>
  conj_tac
  >- (`inst_extends sa s4` by
        (irule inst_extends_trans >> qexists_tac `s3` >> conj_tac
         >- (drule compile_select_extends >> strip_tac >>
             irule inst_extends_trans >> qexists_tac `s1` >> conj_tac
             >- (irule inst_extends_emit_op >> goal_assum (drule_at Any)) >>
             irule inst_extends_trans >> qexists_tac `s2` >> conj_tac
             >- (irule inst_extends_emit_op >> goal_assum (drule_at Any)) >>
             simp[inst_extends_def]) >>
         irule inst_extends_emit_void >> goal_assum (drule_at Any)) >>
      `inst_extends s4 sb` by
        (irule inst_extends_emit_void >> goal_assum (drule_at Any)) >>
      irule run_inst_seq_compose_ok >> qexistsl_tac [`t`,`s4`] >> simp[]) >>
  conj_tac >- (qexists_tac `vars` >> simp[]) >> gvs[]
QED

Theorem raw_call_reserved_vars_frame:
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  (!p v. safe_operand sa p /\ eval_operand p s = SOME v ==>
    eval_operand p (s with vs_vars := V) = SOME v) ==>
  stmt_state_rel ctx func cenv cx es (s with vs_vars := V)
Proof
  strip_tac >> irule stmt_state_rel_vars_frame >> simp[] >> rpt strip_tac >>
  `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
  `?w. lookup_var p s = SOME w` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def,
        immutable_base_zero_def, eval_operand_def] >> metis_tac[]) >>
  `eval_operand (Var p) (s with vs_vars := V) = SOME w` by
    (first_x_assum irule >> simp[safe_operand_def, eval_operand_def]) >>
  fs[eval_operand_def]
QED

Theorem raw_call_output_restore_arbitrary_frame[local]:
  !ctx func cenv cx es sa s u t saved inst q b sz w len.
    stmt_state_rel ctx func cenv cx es (s with vs_fmp := saved) /\
    local_ptrs_reserved cenv sa /\ (?V. u = s with vs_vars := V) /\
    (!p v. safe_operand sa p /\ eval_operand p s = SOME v ==>
      eval_operand p u = SOME v) /\
    t = (mstore (w2n w) len u) with vs_fmp := saved /\
    fn_inst_ids_distinct func /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
    b <= w2n w /\ w2n w + 32 <= b + sz ==>
    stmt_state_rel ctx func cenv cx es t
Proof
  rpt gen_tac >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es (u with vs_fmp := saved)` by
    (qpat_assum `u = _` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >>
       SUBST1_TAC th) >>
     `(s with vs_vars := V) with vs_fmp := saved =
      (s with vs_fmp := saved) with vs_vars := V` by simp[] >>
     pop_assum SUBST1_TAC >> irule raw_call_reserved_vars_frame >>
     simp[] >> qexists_tac `sa` >> simp[] >> rpt strip_tac >>
     Cases_on `p` >> gvs[eval_operand_def, lookup_var_def] >>
     rename1 `FLOOKUP V x = SOME v` >>
     qpat_x_assum `!p v. safe_operand sa p /\ _ ==> _`
       (qspec_then `Var x` mp_tac) >>
     simp[eval_operand_def, lookup_var_def, safe_operand_def]) >>
  gvs[] >> irule raw_call_output_store_frame >> simp[] >>
  qexistsl_tac [`b`, `inst`, `q`, `sz`] >> simp[]
QED

Theorem raw_call_vars_restore_wb_frame[local]:
  wb_frame cenv es es' sf s0 s /\ sf.cs_next_var <= sa.cs_next_var /\
  (?V. u = s with vs_vars := V) /\
  (!p v. safe_operand sa p /\ eval_operand p s = SOME v ==>
    eval_operand p u = SOME v) ==>
  wb_frame cenv es es' sf s0 (u with vs_fmp := saved)
Proof
  strip_tac >> irule wb_frame_readonly_tail >>
  qexistsl_tac [`sa`, `s`] >> simp[] >> rpt strip_tac >>
  `eval_operand (Var z) u = SOME w` by
    (first_x_assum irule >> simp[safe_operand_def, eval_operand_def]) >>
  gvs[eval_operand_def, lookup_var_def]
QED

Theorem raw_call_output_restore_wb_frame[local]:
  !ctx func cenv cx es es1 sf sa s0 s u t saved inst q b sz dst len.
    wb_frame cenv es es1 sf s0 s /\ sf.cs_next_var <= sa.cs_next_var /\
    (?V. u = s with vs_vars := V) /\
    (!p v. safe_operand sa p /\ eval_operand p s = SOME v ==>
      eval_operand p u = SOME v) /\
    stmt_state_rel ctx func cenv cx es1 (u with vs_fmp := saved) /\
    t = (mstore dst len u) with vs_fmp := saved /\
    fn_inst_ids_distinct func /\ MEM inst (fn_insts func) /\
    inst.inst_outputs = [q] /\ not_local_ptr cenv es1.scopes q /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
    sf.cs_next_id <= inst.inst_id /\ b <= dst /\ dst + 32 <= b + sz /\
    local_ptrs_reserved cenv sf /\ MAP FDOM es.scopes = MAP FDOM es1.scopes ==>
    wb_frame cenv es es1 sf s0 t
Proof
  rpt gen_tac >> strip_tac >>
  `wb_frame cenv es es1 sf s0 (u with vs_fmp := saved)` by
    (irule raw_call_vars_restore_wb_frame >> qexistsl_tac [`s`, `sa`] >> simp[] >>
     qexists_tac `V` >> simp[]) >>
  `t = mstore dst len (u with vs_fmp := saved)` by
    simp[mstore_def, write_memory_with_expansion_def] >>
  pop_assum SUBST1_TAC >> irule raw_call_outbuf_mstore_wb_frame >> simp[] >>
  qexistsl_tac [`b`, `ctx`, `cx`, `func`, `inst`, `q`, `sz`] >>
  gvs[]
QED

Theorem raw_call_wb_frame_inst_idx:
  wb_frame cenv es es' sf s0 (s with vs_inst_idx := k) = wb_frame cenv es es' sf s0 s
Proof
  simp[wb_frame_def, locals_kept_def, popped_kept_def, lookup_var_def]
QED

Theorem raw_call_empty_restore_arbitrary_frag[local]:
  !ctx func cenv cx es es0 sf s0 sa sb dop s saved.
    emit_void SETFMP [dop] sa = ((),sb) /\
    eval_operand dop s = SOME saved /\ wb_frame cenv es0 es sf s0 s /\
    stmt_state_rel ctx func cenv cx es (s with vs_fmp := saved) ==>
    frag_path ctx sa sb (\r. r = s)
      (\r. stmt_state_rel ctx func cenv cx es r /\ wb_frame cenv es0 es sf s0 r /\
        r.vs_fmp = saved /\ eval_operand (Lit 0w) r = SOME 0w /\
        (!op. eval_operand op r = eval_operand op s)) (\r. F)
Proof
  rpt strip_tac >>
  `sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
   isPREFIX sa.cs_current_insts sb.cs_current_insts /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb)` by
    (drule emitted_insts_emit_void >> strip_tac >>
     drule emit_void_extends >> strip_tac >>
     simp[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND, mk_inst_def,
          is_terminator_def] >> gvs[same_blocks_def]) >>
  irule frag_path_run_inst_seq >> simp[] >> rpt strip_tac >> gvs[] >>
  drule_all raw_call_restore_arbitrary_run >> strip_tac >>
  `!k. wb_frame cenv es0 es sf s0 (s with <|vs_inst_idx := k; vs_fmp := saved|>)` by
    (gen_tac >> irule wb_frame_readonly_tail >> qexistsl_tac [`sf`, `s`] >>
     simp[lookup_var_def]) >>
  qexists_tac `s with vs_fmp := saved` >>
  simp[stmt_state_rel_inst_idx, eval_operand_def,
       instIdxIndepTheory.eval_op_inst_idx]
QED

Theorem raw_call_output_prefix_ready:
  !ctx func cenv cx es es0 sf s0 sa z s1 cmp s2 cap s3 sb pop s w saved n inst q b sz.
    emit_op RETURNDATASIZE [] sa = (z,s1) /\
    emit_op LT [z;Lit (n2w n)] s1 = (cmp,s2) /\
    compile_select cmp z (Lit (n2w n)) s2 = (cap,s3) /\
    emit_void MSTORE [pop;cap] s3 = ((),sb) /\
    safe_operand sa pop /\ n < dimword (:256) /\
    LENGTH s.vs_returndata < dimword (:256) /\ eval_operand pop s = SOME w /\
    mem_bytes_at (w2n w + 32) (LENGTH (TAKE n s.vs_returndata)) s.vs_memory =
      TAKE n s.vs_returndata /\
    stmt_state_rel ctx func cenv cx es (s with vs_fmp := saved) /\
    local_ptrs_reserved cenv sa /\ wb_frame cenv es0 es sf s0 s /\
    sf.cs_next_var <= sa.cs_next_var /\ local_ptrs_reserved cenv sf /\
    MAP FDOM es0.scopes = MAP FDOM es.scopes /\ sf.cs_next_id <= inst.inst_id /\
    fn_inst_ids_distinct func /\ MEM inst (fn_insts func) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [q] /\
    not_local_ptr cenv es.scopes q /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
    b <= w2n w /\ w2n w + 32 <= b + sz ==>
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      stmt_state_rel ctx func cenv cx es (t with vs_fmp := saved) /\
      wb_frame cenv es0 es sf s0 t /\
      val_in_memory (BaseTV (BytesT (Dynamic n)))
        (BytesV (TAKE n s.vs_returndata)) (w2n w) t.vs_memory /\
      t.vs_fmp = s.vs_fmp /\ t.vs_allocas = s.vs_allocas /\
      (!p. safe_operand sa p ==> eval_operand p t = eval_operand p s)
Proof
  rpt gen_tac >> strip_tac >> drule_all raw_call_output_prefix_run >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es (u with vs_fmp := saved)` by
    (qpat_assum `u = _` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >>
       SUBST1_TAC th) >>
     `(s with vs_vars := vars) with vs_fmp := saved =
      (s with vs_fmp := saved) with vs_vars := vars` by simp[] >>
     pop_assum SUBST1_TAC >> irule raw_call_reserved_vars_frame >>
     simp[] >> qexists_tac `sa` >> simp[] >> rpt strip_tac >>
     Cases_on `p` >> gvs[eval_operand_def, lookup_var_def] >>
     rename1 `FLOOKUP vars x = SOME v` >>
     qpat_x_assum `!p. safe_operand sa p ==> eval_operand p (s with vs_vars := vars) = _`
       (qspec_then `Var x` mp_tac) >>
     simp[eval_operand_def, lookup_var_def, safe_operand_def]) >>
  `stmt_state_rel ctx func cenv cx es (t with vs_fmp := saved)` by
    (gvs[] >> irule raw_call_output_store_frame >> simp[] >>
     qexistsl_tac [`b`,`inst`,`q`,`sz`] >> simp[]) >>
  `!p v. safe_operand sa p /\ eval_operand p s = SOME v ==>
     eval_operand p u = SOME v` by simp[] >>
  `wb_frame cenv es0 es sf s0 (t with vs_fmp := saved)` by
    (`t with vs_fmp := saved =
       (mstore (w2n w) (n2w (MIN n (LENGTH s.vs_returndata))) u) with vs_fmp := saved`
       by simp[] >>
     qsuff_tac `?V. u = s with vs_vars := V`
     >- (disch_tac >> drule_all raw_call_output_restore_wb_frame >> simp[]) >>
     qexists_tac `vars` >> simp[]) >>
  `wb_frame cenv es0 es sf s0 (t with vs_fmp := saved) = wb_frame cenv es0 es sf s0 t` by
    simp[NoAsms, wb_frame_def, locals_kept_def, popped_kept_def, lookup_var_def] >>
  `t.vs_fmp = s.vs_fmp /\ t.vs_allocas = s.vs_allocas` by
    gvs[mstore_def, write_memory_with_expansion_def] >>
  qexists_tac `t` >> simp[] >> gvs[]
QED

Theorem raw_call_output_restore_allocas_frag[local]:
  !ctx func cenv cx es es0 sf s0 sa z s1 cmp s2 cap s3 s4 sb pop dop s w saved n inst q b sz.
    emit_op RETURNDATASIZE [] sa = (z,s1) /\
    emit_op LT [z;Lit (n2w n)] s1 = (cmp,s2) /\
    compile_select cmp z (Lit (n2w n)) s2 = (cap,s3) /\
    emit_void MSTORE [pop;cap] s3 = ((),s4) /\
    emit_void SETFMP [dop] s4 = ((),sb) /\
    safe_operand sa pop /\ safe_operand sa dop /\ n < dimword (:256) /\
    LENGTH s.vs_returndata < dimword (:256) /\
    eval_operand pop s = SOME w /\ eval_operand dop s = SOME saved /\
    mem_bytes_at (w2n w + 32) (LENGTH (TAKE n s.vs_returndata)) s.vs_memory =
      TAKE n s.vs_returndata /\
    stmt_state_rel ctx func cenv cx es (s with vs_fmp := saved) /\
    local_ptrs_reserved cenv sa /\ wb_frame cenv es0 es sf s0 s /\
    sf.cs_next_var <= sa.cs_next_var /\ local_ptrs_reserved cenv sf /\
    MAP FDOM es0.scopes = MAP FDOM es.scopes /\ sf.cs_next_id <= inst.inst_id /\
    fn_inst_ids_distinct func /\ MEM inst (fn_insts func) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [q] /\
    not_local_ptr cenv es.scopes q /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
    b <= w2n w /\ w2n w + 32 <= b + sz ==>
    frag_path ctx sa sb (\r. r = s)
      (\r. stmt_state_rel ctx func cenv cx es r /\ wb_frame cenv es0 es sf s0 r /\
        val_in_memory (BaseTV (BytesT (Dynamic n)))
          (BytesV (TAKE n s.vs_returndata)) (w2n w) r.vs_memory /\
        r.vs_fmp = saved /\ r.vs_allocas = s.vs_allocas /\
        (!p v. safe_operand sa p /\ eval_operand p s = SOME v ==>
          eval_operand p r = SOME v)) (\r. F)
Proof
  rpt strip_tac >> drule_all raw_call_output_code >> strip_tac >>
  irule frag_path_run_inst_seq >> simp[] >> rpt strip_tac >> gvs[] >>
  drule_all raw_call_output_restore_arbitrary_run >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es (u with vs_fmp := saved)` by
    (qpat_assum `u = _` (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th]) >>
       SUBST1_TAC th) >>
     `(s with vs_vars := vars) with vs_fmp := saved =
      (s with vs_fmp := saved) with vs_vars := vars` by simp[] >>
     pop_assum SUBST1_TAC >> irule raw_call_reserved_vars_frame >>
     simp[] >> qexists_tac `sa` >> simp[] >> rpt strip_tac >>
     Cases_on `p` >> gvs[eval_operand_def, lookup_var_def] >>
     rename1 `FLOOKUP vars x = SOME v` >>
     qpat_x_assum `!p v. safe_operand sa p /\ _ ==> eval_operand p (s with vs_vars := vars) = _`
       (qspec_then `Var x` mp_tac) >>
     simp[eval_operand_def, lookup_var_def]) >>
  `stmt_state_rel ctx func cenv cx es t` by
    (qsuff_tac `?V. u = s with vs_vars := V`
     >- (disch_tac >> drule_all raw_call_output_restore_arbitrary_frame >> simp[]) >>
     qexists_tac `vars` >> simp[]) >>
  `wb_frame cenv es0 es sf s0 t` by
    (qsuff_tac `?V. u = s with vs_vars := V`
     >- (disch_tac >> drule_all raw_call_output_restore_wb_frame >> simp[]) >>
     qexists_tac `vars` >> simp[]) >>
  `t.vs_fmp = saved` by simp[] >>
  `t.vs_allocas = s.vs_allocas` by
    gvs[mstore_def, write_memory_with_expansion_def] >>
  qexists_tac `t` >>
  simp[stmt_state_rel_inst_idx, raw_call_wb_frame_inst_idx,
       instIdxIndepTheory.eval_op_inst_idx]
QED

Theorem raw_call_output_restore_arbitrary_frag[local]:
  !ctx func cenv cx es es0 sf s0 sa z s1 cmp s2 cap s3 s4 sb pop dop s w saved n inst q b sz.
    emit_op RETURNDATASIZE [] sa = (z,s1) /\
    emit_op LT [z;Lit (n2w n)] s1 = (cmp,s2) /\
    compile_select cmp z (Lit (n2w n)) s2 = (cap,s3) /\
    emit_void MSTORE [pop;cap] s3 = ((),s4) /\
    emit_void SETFMP [dop] s4 = ((),sb) /\
    safe_operand sa pop /\ safe_operand sa dop /\ n < dimword (:256) /\
    LENGTH s.vs_returndata < dimword (:256) /\
    eval_operand pop s = SOME w /\ eval_operand dop s = SOME saved /\
    mem_bytes_at (w2n w + 32) (LENGTH (TAKE n s.vs_returndata)) s.vs_memory =
      TAKE n s.vs_returndata /\
    stmt_state_rel ctx func cenv cx es (s with vs_fmp := saved) /\
    local_ptrs_reserved cenv sa /\ wb_frame cenv es0 es sf s0 s /\
    sf.cs_next_var <= sa.cs_next_var /\ local_ptrs_reserved cenv sf /\
    MAP FDOM es0.scopes = MAP FDOM es.scopes /\ sf.cs_next_id <= inst.inst_id /\
    fn_inst_ids_distinct func /\ MEM inst (fn_insts func) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [q] /\
    not_local_ptr cenv es.scopes q /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
    b <= w2n w /\ w2n w + 32 <= b + sz ==>
    frag_path ctx sa sb (\r. r = s)
      (\r. stmt_state_rel ctx func cenv cx es r /\ wb_frame cenv es0 es sf s0 r /\
        val_in_memory (BaseTV (BytesT (Dynamic n)))
          (BytesV (TAKE n s.vs_returndata)) (w2n w) r.vs_memory /\
        r.vs_fmp = saved /\
        (!p v. safe_operand sa p /\ eval_operand p s = SOME v ==>
          eval_operand p r = SOME v)) (\r. F)
Proof
  rpt strip_tac >> drule_all raw_call_output_restore_allocas_frag >> strip_tac >>
  irule frag_path_conseq >> goal_assum (drule_at (Pat `frag_path _ _ _ _ _ _`)) >>
  simp[] >> metis_tac[]
QED

Definition raw_call_buffer_frame_def[local]:
  raw_call_buffer_frame ctx func cenv cx es0 es sf s0 saved ai (w:bytes32) n s <=>
    stmt_state_rel ctx func cenv cx es (s with vs_fmp := saved) /\
    wb_frame cenv es0 es sf s0 s /\
    FLOOKUP s.vs_allocas ai =
      SOME (w2n w,if n = 0 then 0 else ((n + 31) DIV 32) * 32 + 32) /\
    w2n w + (if n = 0 then 0 else ((n + 31) DIV 32) * 32 + 32) < dimword (:256)
End

Theorem raw_call_take_adopt_fields:
  take_call_outcome addr data value es = (INL (rq,outcome),es1) ==>
    (SND (adopt_call_outcome rq outcome es1)).scopes = es.scopes /\
    (SND (adopt_call_outcome rq outcome es1)).immutables = es.immutables
Proof
  strip_tac >> drule take_call_outcome_frame >> strip_tac >>
  Cases_on `adopt_call_outcome rq outcome es1` >>
  drule_all adopt_call_outcome_frame >> strip_tac >> gvs[] >>
  qmatch_goalsub_rename_tac `post.scopes` >>
  qpat_x_assum `post = _` (fn th => ONCE_REWRITE_TAC [th]) >> simp[] >>
  qpat_x_assum `es1 = _` (fn th => ONCE_REWRITE_TAC [th]) >> simp[]
QED

Theorem raw_call_write_saved_fmp[local]:
  write_memory_with_expansion dst data (s with vs_fmp := saved) =
    (write_memory_with_expansion dst data s) with vs_fmp := saved
Proof
  simp[write_memory_with_expansion_def]
QED

Theorem raw_call_wb_frame_fmp[local]:
  wb_frame cenv es es' sf s0 (s with vs_fmp := saved) <=> wb_frame cenv es es' sf s0 s
Proof
  simp[wb_frame_def, locals_kept_def, popped_kept_def, lookup_var_def, local_region_def]
QED

Theorem raw_call_buffer_write[local]:
  raw_call_buffer_frame ctx func cenv cx es0 es sf s0 saved ai w n s /\
  fn_inst_ids_distinct func /\ MEM alloc (fn_insts func) /\
  alloc.inst_opcode = ALLOCA /\ alloc.inst_outputs = [q] /\ alloc.inst_id = ai /\
  not_local_ptr cenv es.scopes q /\ sf.cs_next_id <= ai /\
  local_ptrs_reserved cenv sf /\ MAP FDOM es0.scopes = MAP FDOM es.scopes ==>
  raw_call_buffer_frame ctx func cenv cx es0 es sf s0 saved ai w n
    (write_memory_with_expansion (w2n (if n = 0 then w else w + 32w))
      (TAKE n data) s)
Proof
  rewrite_tac[raw_call_buffer_frame_def] >> strip_tac >>
  `w2n (if n = 0 then w else w + 32w) =
    w2n w + (if n = 0 then 0 else 32)` by
    (Cases_on `n = 0` >> simp[] >> irule buffer_offset_no_wrap >>
     qexists_tac `((n + 31) DIV 32) * 32 + 32` >> simp[]) >>
  `LENGTH (TAKE n data) <= (if n = 0 then 0 else ((n + 31) DIV 32) * 32)` by
    (Cases_on `n = 0` >> simp[] >>
     qspec_then `n` mp_tac le_word_size_mul >>
     simp[vfmConstantsTheory.word_size_def, LENGTH_TAKE_EQ,
          arithmeticTheory.MIN_DEF] >> rpt strip_tac >> gvs[] >> decide_tac) >>
  `stmt_state_rel ctx func cenv cx es
    ((write_memory_with_expansion (w2n (if n = 0 then w else w + 32w))
      (TAKE n data) s) with vs_fmp := saved)` by
    (rewrite_tac[GSYM raw_call_write_saved_fmp] >>
     irule raw_call_outbuf_write_frame >> simp[] >>
     qexistsl_tac [`w2n w`, `alloc`, `q`,
       `if n = 0 then 0 else ((n + 31) DIV 32) * 32 + 32`] >> simp[]) >>
  `wb_frame cenv es0 es sf s0
    (write_memory_with_expansion (w2n (if n = 0 then w else w + 32w))
      (TAKE n data) (s with vs_fmp := saved))` by
    (irule raw_call_outbuf_wb_frame >> simp[raw_call_wb_frame_fmp] >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >> simp[] >>
     goal_assum (drule_at (Pat `MEM _ (fn_insts _)`)) >> simp[] >>
     goal_assum (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >> simp[]) >>
  gvs[raw_call_write_saved_fmp, raw_call_wb_frame_fmp]
QED

Theorem raw_call_buffer_oracle_fields[local]:
  raw_call_buffer_frame ctx func cenv cx es0 es sf s0 saved ai w n s /\
  state_rel func cenv cx es1 (t with vs_fmp := saved) /\
  es1.scopes = es.scopes /\ es1.immutables = es.immutables /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  t.vs_vars = s.vs_vars /\ t.vs_memory = s.vs_memory /\
  t.vs_labels = s.vs_labels ==>
  raw_call_buffer_frame ctx func cenv cx es0 es1 sf s0 saved ai w n t
Proof
  rewrite_tac[raw_call_buffer_frame_def] >> strip_tac >> simp[] >>
  `immutable_alloca_sep func cenv cx es1 (t with vs_fmp := saved)` by
    (irule immutable_alloca_sep_fields >>
     qexistsl_tac [`s with vs_fmp := saved`, `es`] >> simp[] >> conj_tac
     >- (simp[local_region_def, lookup_var_def] >> metis_tac[]) >>
     fs[stmt_state_rel_def]) >>
  conj_tac
  >- (irule stmt_state_rel_allocas_frame >> simp[] >> conj_tac
      >- (irule immutable_base_zero_frame >>
          qexists_tac `s with vs_fmp := saved` >>
          fs[stmt_state_rel_def, lookup_var_def]) >>
      qexistsl_tac [`es`, `s with vs_fmp := saved`] >> simp[]) >>
  irule wb_frame_readonly_tail >> qexistsl_tac [`sf`, `s`] >>
  simp[lookup_var_def] >>
  qpat_x_assum `wb_frame cenv es0 es sf s0 s` mp_tac >>
  pure_rewrite_tac[wb_frame_def, locals_kept_def, popped_kept_def] >>
  qpat_x_assum `es1.scopes = _` (fn th => pure_rewrite_tac[th]) >>
  disch_then ACCEPT_TAC
QED

Theorem raw_call_state_rel_fmp[local]:
  state_rel func cenv cx es (s with vs_fmp := saved) <=> state_rel func cenv cx es s
Proof
  simp[state_rel_def, local_ptrs_rel_def, local_region_def, local_backed_def,
       lookup_var_def, immutables_rel_def, storage_rel_def, transient_rel_def,
       accounts_rel_def, logs_rel_def, contract_storage_def, contract_transient_def]
QED

Theorem raw_call_buffer_update[local]:
  raw_call_buffer_frame ctx func cenv cx es0 es sf s0 saved ai w n s /\
  local_ptrs_reserved cenv sc /\ sf.cs_next_var <= sc.cs_next_var ==>
  raw_call_buffer_frame ctx func cenv cx es0 es sf s0 saved ai w n
    (update_var (STRING #"%" (toString sc.cs_next_var)) v s)
Proof
  rewrite_tac[raw_call_buffer_frame_def] >> strip_tac >> conj_tac
  >- (`(update_var (STRING #"%" (toString sc.cs_next_var)) v s)
         with vs_fmp := saved =
       update_var (STRING #"%" (toString sc.cs_next_var)) v
         (s with vs_fmp := saved)` by simp[update_var_def] >>
      pop_assum SUBST1_TAC >> irule stmt_state_rel_update_var >> simp[] >>
      irule local_ptrs_reserved_fresh >> qexists_tac `sc` >> simp[]) >>
  simp[update_var_def] >>
  irule wb_frame_readonly_tail >> qexistsl_tac [`sc`, `s`] >>
  simp[lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >> rpt strip_tac >>
  gvs[not_fresh_at_def]
QED

Theorem raw_call_buffer_frame_inst_idx[local]:
  raw_call_buffer_frame ctx func cenv cx es0 es sf s0 saved ai w n
    (s with vs_inst_idx := k) <=>
  raw_call_buffer_frame ctx func cenv cx es0 es sf s0 saved ai w n s
Proof
  simp[raw_call_buffer_frame_def, wb_frame_def, lookup_var_def,
       stmt_state_rel_inst_idx]
QED

Theorem calldata_prepared_buffer_frame[local]:
  calldata_prepared ctx func cenv cx es0 es sf s0 entry sp sa n ov op dp dl s ==>
  ?w. eval_operand ov s = SOME w /\
    eval_operand op s = SOME (if n = 0 then w else w + 32w) /\
    raw_call_buffer_frame ctx func cenv cx es0 es sf s0 entry.vs_fmp
      sa.cs_next_id w n s
Proof
  simp[calldata_prepared_def, raw_call_buffer_frame_def] >> metis_tac[]
QED

Theorem raw_call_oracle_framed_step[local]:
  !ctx func cenv cx es0 es es1 sf s0 saved ai w n s sc alloc q
    inst out gop aop vop iop zop rop cop gas aw vw ip iz stat rq outcome.
  raw_call_buffer_frame ctx func cenv cx es0 es sf s0 saved ai w n s /\
  inst.inst_outputs = [out] /\
  inst.inst_opcode = (if stat then STATICCALL else CALL) /\
  inst.inst_operands = (if stat then [gop;aop;iop;zop;rop;cop]
    else [gop;aop;vop;iop;zop;rop;cop]) /\
  eval_operand gop s = SOME gas /\ eval_operand aop s = SOME aw /\
  eval_operand vop s = SOME vw /\ eval_operand iop s = SOME ip /\
  eval_operand zop s = SOME iz /\
  eval_operand rop s = SOME (if n = 0 then w else w + 32w) /\
  eval_operand cop s = SOME (n2w n) /\
  take_call_outcome (w2w aw) (read_memory (w2n ip) (w2n iz) s)
    (if stat then NONE else SOME (w2n vw)) es = (INL (rq,outcome),es1) /\
  fn_inst_ids_distinct func /\ MEM alloc (fn_insts func) /\
  alloc.inst_opcode = ALLOCA /\ alloc.inst_outputs = [q] /\ alloc.inst_id = ai /\
  not_local_ptr cenv es.scopes q /\ sf.cs_next_id <= ai /\
  local_ptrs_reserved cenv sf /\ local_ptrs_reserved cenv sc /\
  sf.cs_next_var <= sc.cs_next_var /\ MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  n < dimword (:256) /\ out = STRING #"%" (toString sc.cs_next_var) ==>
  ?u. step_inst_base inst s = OK u /\
    raw_call_buffer_frame ctx func cenv cx es0
      (SND (adopt_call_outcome rq outcome es1)) sf s0 saved ai w n u /\
    eval_operand (Var out) u = SOME (if outcome.co_success then 1w else 0w) /\
    u.vs_returndata = outcome.co_returnData /\ u.vs_fmp = s.vs_fmp /\
    (!p. safe_operand sc p ==> eval_operand p u = eval_operand p s) /\
    (0 < n ==> mem_bytes_at (w2n w + 32) (LENGTH (TAKE n outcome.co_returnData))
      u.vs_memory = TAKE n outcome.co_returnData)
Proof
  rpt gen_tac >> strip_tac >>
  `raw_call_buffer_frame ctx func cenv cx es0 es sf s0 saved ai w n
    (write_memory_with_expansion (w2n (if n = 0 then w else w + 32w))
      (TAKE n outcome.co_returnData) s)` by
    (drule_all raw_call_buffer_write >> simp[]) >>
  `state_rel func cenv cx es s` by
    fs[raw_call_buffer_frame_def, stmt_state_rel_def, raw_call_state_rel_fmp] >>
  `local_ptrs_rel func cenv es.scopes
    (write_memory_with_expansion (w2n (if n = 0 then w else w + 32w))
      (TAKE (w2n (n2w n : bytes32)) outcome.co_returnData) s) /\
   immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es
    (write_memory_with_expansion (w2n (if n = 0 then w else w + 32w))
      (TAKE (w2n (n2w n : bytes32)) outcome.co_returnData) s)` by
    fs[raw_call_buffer_frame_def, stmt_state_rel_def, raw_call_state_rel_fmp,
       state_rel_def] >>
  drule_all raw_call_oracle_step >> strip_tac >>
  `t.vs_alloca_next = s.vs_alloca_next` by
    (qspecl_then [`inst`, `s`,
       `update_var out (if outcome.co_success then 1w else 0w) t`]
       mp_tac venomMemPropsTheory.step_inst_base_preserves_alloca_next >>
     simp[update_var_def] >> Cases_on `stat` >> simp[]) >>
  `t.vs_labels = s.vs_labels` by
    (qpat_x_assum `step_inst_base inst s = _` mp_tac >>
     `inst.inst_opcode <> INVOKE` by (Cases_on `stat` >> simp[]) >>
     drule_then (qspecl_then [`0`, `ctx`, `s`] assume_tac) step_inst_non_invoke >>
     disch_tac >>
     `step_inst 0 ctx inst s = OK
        (update_var out (if outcome.co_success then 1w else 0w) t)` by simp[] >>
     drule venomExecPropsTheory.step_inst_preserves_labels_always >>
     simp[update_var_def]) >>
  drule_all raw_call_take_adopt_fields >> strip_tac >>
  `raw_call_buffer_frame ctx func cenv cx es0
    (SND (adopt_call_outcome rq outcome es1)) sf s0 saved ai w n t` by
    (qpat_assum `raw_call_buffer_frame _ _ _ _ _ _ _ _ _ _ _ _
       (write_memory_with_expansion _ _ _)`
       (mp_then Any irule raw_call_buffer_oracle_fields) >>
     simp[raw_call_state_rel_fmp, write_memory_with_expansion_def]) >>
  qexists_tac `update_var out (if outcome.co_success then 1w else 0w) t` >>
  simp[] >> conj_tac
  >- (gvs[] >> irule raw_call_buffer_update >> goal_assum (drule_at Any) >> simp[]) >>
  simp[eval_operand_def, lookup_var_def, update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >> conj_tac
  >- (rpt strip_tac >> Cases_on `p` >>
      gvs[safe_operand_def, eval_operand_def, lookup_var_def, not_fresh_at_def,
          finite_mapTheory.FLOOKUP_UPDATE] >>
      first_x_assum (qspec_then `sc.cs_next_var` mp_tac) >> simp[] ) >>
  strip_tac >>
  `w2n w + (((n + 31) DIV 32) * 32 + 32) < dimword (:256)` by
    fs[raw_call_buffer_frame_def] >>
  drule raw_call_outbuf_write_contents >>
  disch_then (qspecl_then [`outcome.co_returnData`, `s`] mp_tac) >>
  strip_tac >> gvs[]
QED

Theorem raw_call_oracle_framed_frag[local]:
  emit_op (if stat then STATICCALL else CALL)
    (if stat then [gop;aop;dp;dl;op;Lit (n2w n)]
     else [gop;aop;vop;dp;dl;op;Lit (n2w n)]) sc = (cond,sd) /\
  raw_call_buffer_frame ctx func cenv cx es0 es sf s0 saved ai w n s /\
  eval_operand gop s = SOME gas /\ eval_operand aop s = SOME aw /\
  eval_operand vop s = SOME vw /\ eval_operand dp s = SOME ip /\
  eval_operand dl s = SOME iz /\
  eval_operand op s = SOME (if n = 0 then w else w + 32w) /\
  take_call_outcome (w2w aw) (read_memory (w2n ip) (w2n iz) s)
    (if stat then NONE else SOME (w2n vw)) es = (INL (rq,outcome),es1) /\
  fn_inst_ids_distinct func /\ MEM alloc (fn_insts func) /\
  alloc.inst_opcode = ALLOCA /\ alloc.inst_outputs = [q] /\ alloc.inst_id = ai /\
  not_local_ptr cenv es.scopes q /\ sf.cs_next_id <= ai /\
  local_ptrs_reserved cenv sf /\ local_ptrs_reserved cenv sc /\
  sf.cs_next_var <= sc.cs_next_var /\ MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  n < dimword (:256) ==>
  frag_path ctx sc sd (\u. u = s)
    (\u. raw_call_buffer_frame ctx func cenv cx es0
       (SND (adopt_call_outcome rq outcome es1)) sf s0 saved ai w n u /\
      eval_operand cond u = SOME (if outcome.co_success then 1w else 0w) /\
      u.vs_returndata = outcome.co_returnData /\ u.vs_fmp = s.vs_fmp /\
      (!p. safe_operand sc p ==> eval_operand p u = eval_operand p s) /\
      (0 < n ==> mem_bytes_at (w2n w + 32) (LENGTH (TAKE n outcome.co_returnData))
        u.vs_memory = TAKE n outcome.co_returnData)) R
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  irule frag_path_run_inst_seq >>
  fs[same_blocks_def] >>
  simp[rich_listTheory.IS_PREFIX_APPEND, raw_call_buffer_frame_inst_idx] >>
  conj_tac
  >- (rpt strip_tac >> gvs[] >> disj1_tac >>
      qmatch_goalsub_abbrev_tac `run_inst_seq [inst] s` >>
      `inst.inst_outputs = [STRING #"%" (toString sc.cs_next_var)] /\
       inst.inst_opcode = (if stat then STATICCALL else CALL) /\
       inst.inst_operands = (if stat then [gop;aop;dp;dl;op;Lit (n2w n)]
          else [gop;aop;vop;dp;dl;op;Lit (n2w n)])` by
        simp[Abbr `inst`, mk_inst_def] >>
      `eval_operand (Lit (n2w n)) s = SOME (n2w n)` by simp[eval_operand_def] >>
      drule_all (SRULE [] raw_call_oracle_framed_step) >>
      strip_tac >> qexists_tac `u` >> simp[run_inst_seq_def] >>
      Cases_on `stat` >> gvs[mk_inst_def, is_terminator_def]) >>
  Cases_on `stat` >> simp[mk_inst_def, is_terminator_def]
QED

(* The branch boundary is independent of the origin of the input bytes and
   of the success continuation's chosen value representation. *)
Theorem raw_call_finish_branch_guarded_frag:
  !ctx sa sx sf sz sp sc se sk sb cond ok fl x y z rb s success Q R.
    emit_inst JNZ [cond;Label ok;Label fl] [] sa = ((),sx) /\
    new_block fl sx = (x,sf) /\
    emit_op RETURNDATASIZE [] sf = (z,sz) /\
    compile_alloc_buffer 0 sz = (rb,sp) /\
    emit_void RETURNDATACOPY [rb.buf_operand;Lit 0w;z] sp = ((),sc) /\
    emit_inst REVERT [rb.buf_operand;z] [] sc = ((),se) /\
    new_block ok se = (y,sk) /\
    cs_extends sf se /\ cs_extends sk sb /\
    eval_operand cond s = SOME (if success then 1w else 0w) /\
    LENGTH s.vs_returndata < dimword (:256) /\
    (~success ==> !t. t.vs_returndata = s.vs_returndata ==> R (Abort Revert_abort t)) /\
    (success ==> frag_path ctx sk sb (\u. u = jump_to ok s) Q R) ==>
    frag_path ctx sa sb (\u. u = s) Q R
Proof
  rpt gen_tac >> strip_tac >> Cases_on `success`
  >- (gvs[] >> drule_all raw_call_success_jnz_frag >> simp[])
  >> gvs[] >>
  `cs_extends se sk` by metis_tac[cs_extends_new_block] >>
  `cs_extends se sb` by metis_tac[cs_extends_trans] >>
  `frag_path ctx sf se (\u. u = jump_to fl s) (\u. F) R` by
    (irule raw_call_revert_frag >> conj_tac
     >- (rpt strip_tac >> gvs[jump_to_def]) >>
     goal_assum (drule_at (Pat `emit_op RETURNDATASIZE _ _ = _`)) >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  irule frag_path_conseq >>
  qexistsl_tac [`\u. u = s`, `\u. F`, `R`] >> simp[] >>
  drule_all raw_call_failed_jnz_frag >> simp[]
QED

Theorem raw_call_finish_branch_frag[local]:
  !ctx sa sx sf sz sp sc se sk sb cond ok fl x y z rb s success Q R.
    emit_inst JNZ [cond;Label ok;Label fl] [] sa = ((),sx) /\
    new_block fl sx = (x,sf) /\
    emit_op RETURNDATASIZE [] sf = (z,sz) /\
    compile_alloc_buffer 0 sz = (rb,sp) /\
    emit_void RETURNDATACOPY [rb.buf_operand;Lit 0w;z] sp = ((),sc) /\
    emit_inst REVERT [rb.buf_operand;z] [] sc = ((),se) /\
    new_block ok se = (y,sk) /\
    cs_extends sf se /\ cs_extends sk sb /\
    eval_operand cond s = SOME (if success then 1w else 0w) /\
    LENGTH s.vs_returndata < dimword (:256) /\
    (!t. t.vs_returndata = s.vs_returndata ==> R (Abort Revert_abort t)) /\
    (success ==> frag_path ctx sk sb (\u. u = jump_to ok s) Q R) ==>
    frag_path ctx sa sb (\u. u = s) Q R
Proof
  rpt strip_tac >>
  `~success ==> !t. t.vs_returndata = s.vs_returndata ==> R (Abort Revert_abort t)` by simp[] >>
  drule_all raw_call_finish_branch_guarded_frag >> simp[]
QED


Theorem raw_call_success_suffix_mono[local]:
  !n ov sa.
    ci_mono sa (SND ((if 0 < n then do
      z <- emit_op RETURNDATASIZE [];
      c <- emit_op LT [z;Lit (n2w n)];
      cap <- compile_select c z (Lit (n2w n));
      emit_void MSTORE [ov;cap]; comp_return ov od
    else comp_return (Lit 0w)) sa))
Proof
  rpt gen_tac >> Cases_on `0 < n` >> simp[ci_mono_comp_return] >>
  irule ci_mono_bind >> simp[ci_mono_emit_op] >>
  rpt gen_tac >> irule ci_mono_bind >> simp[ci_mono_emit_op] >>
  rpt gen_tac >> irule ci_mono_bind >> simp[ci_mono_compile_select] >>
  rpt gen_tac >> irule ci_mono_ignore_bind >>
  simp[ci_mono_emit_void, ci_mono_comp_return]
QED

Theorem raw_call_finish_certificates[local]:
  compile_raw_call_finish aop dp dl gop vop call_ty n T ov op sc = (result,se) /\
  emit_void SETFMP [dp] se = ((),sb) ==>
  ?success s1 fl s2 ok s3 s4 x4 s5 z s6 rb s7 s8 s9 x9 sk.
    (case call_ty of
       DelegateCall => emit_op DELEGATECALL [gop;aop;dp;dl;op;Lit (n2w n)] sc
     | StaticCall => emit_op STATICCALL [gop;aop;dp;dl;op;Lit (n2w n)] sc
     | RegularCall => emit_op CALL [gop;aop;vop;dp;dl;op;Lit (n2w n)] sc) = (success,s1) /\
    fresh_label "call_failed" s1 = (fl,s2) /\
    fresh_label "call_ok" s2 = (ok,s3) /\
    emit_inst JNZ [success;Label ok;Label fl] [] s3 = ((),s4) /\
    new_block fl s4 = (x4,s5) /\
    emit_op RETURNDATASIZE [] s5 = (z,s6) /\
    compile_alloc_buffer 0 s6 = (rb,s7) /\
    emit_void RETURNDATACOPY [rb.buf_operand;Lit 0w;z] s7 = ((),s8) /\
    emit_inst REVERT [rb.buf_operand;z] [] s8 = ((),s9) /\
    new_block ok s9 = (x9,sk) /\
    (if 0 < n then do
      z <- emit_op RETURNDATASIZE []; c <- emit_op LT [z;Lit (n2w n)];
      cap <- compile_select c z (Lit (n2w n));
      emit_void MSTORE [ov;cap]; comp_return ov od
     else comp_return (Lit 0w)) sk = (result,se) /\
    ci_mono sc s3 /\ ci_mono sc sk /\ cs_extends s3 sb /\
    cs_extends s5 s9 /\ cs_extends sk sb
Proof
  strip_tac >> drule raw_call_finish_revert_compile >> strip_tac >>
  `ci_mono sc s1` by
    (Cases_on `call_ty` >> gvs[] >> metis_tac[ci_mono_emit_op, pairTheory.SND]) >>
  `ci_mono s1 s2 /\ ci_mono s2 s3 /\
   ci_mono s3 s4 /\ ci_mono s4 s5 /\ ci_mono s5 s6 /\
   ci_mono s6 s7 /\ ci_mono s7 s8 /\ ci_mono s8 s9 /\ ci_mono s9 s10` by
    (rpt conj_tac >> metis_tac[ci_mono_emit_inst, ci_mono_emit_op,
       ci_mono_emit_void, ci_mono_compile_alloc_buffer, ci_mono_new_block,
       ci_mono_fresh_label, pairTheory.SND]) >>
  `ci_mono s10 se` by
    (qspecl_then [`n`,`ov`,`s10`] mp_tac raw_call_success_suffix_mono >> fs[arithmeticTheory.GREATER_DEF]) >>
  `ci_mono se sb` by metis_tac[ci_mono_emit_void, pairTheory.SND] >>
  qexistsl_tac [`success`,`s1`,`fail'`,`s2`,`ok`,`s3`,`s4`,`x4`,`s5`,
    `rds`,`s6`,`rbuf`,`s7`,`s8`,`s9`,`x9`,`s10`] >> simp[] >>
  fs[ci_mono_def, arithmeticTheory.GREATER_DEF] >>
  rpt conj_tac >> metis_tac[cs_extends_trans]
QED

Theorem raw_call_success_restore_allocas_frag[local]:
  (if 0 < n then do
     z <- emit_op RETURNDATASIZE []; c <- emit_op LT [z;Lit (n2w n)];
     cap <- compile_select c z (Lit (n2w n));
     emit_void MSTORE [ov;cap]; comp_return ov od
   else comp_return (Lit 0w)) sk = (result,se) /\
  emit_void SETFMP [dp] se = ((),sb) /\ ci_mono sc sk /\
  raw_call_buffer_frame ctx func cenv cx es0 es sf s0 saved ai w n t /\
  fn_inst_ids_distinct func /\ MEM alloc (fn_insts func) /\
  alloc.inst_opcode = ALLOCA /\ alloc.inst_outputs = [q] /\ alloc.inst_id = ai /\
  not_local_ptr cenv es.scopes q /\ sf.cs_next_id <= ai /\
  local_ptrs_reserved cenv sf /\ local_ptrs_reserved cenv sc /\
  sf.cs_next_var <= sc.cs_next_var /\ MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  safe_operand sc ov /\ safe_operand sc dp /\
  eval_operand ov t = SOME w /\ eval_operand dp t = SOME saved /\
  n < dimword (:256) /\ LENGTH t.vs_returndata < dimword (:256) /\
  (0 < n ==> mem_bytes_at (w2n w + 32) (LENGTH (TAKE n t.vs_returndata))
     t.vs_memory = TAKE n t.vs_returndata) ==>
  frag_path ctx sk sb (\u. u = jump_to ok t)
    (\u. stmt_state_rel ctx func cenv cx es u /\ wb_frame cenv es0 es sf s0 u /\
      u.vs_fmp = saved /\
      (0 < n ==> FLOOKUP u.vs_allocas ai = SOME (w2n w, ((n+31) DIV 32)*32+32)) /\
      (!p v. safe_operand sc p /\ eval_operand p t = SOME v ==>
        eval_operand p u = SOME v) /\
      (if n = 0 then eval_operand result u = SOME 0w
       else eval_operand result u = SOME w /\
         val_in_memory (BaseTV (BytesT (Dynamic n)))
           (BytesV (TAKE n t.vs_returndata)) (w2n w) u.vs_memory)) R
Proof
  strip_tac >>
  `safe_operand sk ov /\ safe_operand sk dp /\
   local_ptrs_reserved cenv sk /\ sf.cs_next_var <= sk.cs_next_var` by
    (fs[ci_mono_def] >> metis_tac[safe_operand_mono, local_ptrs_reserved_next_var]) >>
  `raw_call_buffer_frame ctx func cenv cx es0 es sf s0 saved ai w n (jump_to ok t)` by
    ( `jump_to ok t with vs_fmp := saved = jump_to ok (t with vs_fmp := saved)` by
        simp[jump_to_def] >>
      fs[raw_call_buffer_frame_def, stmt_state_rel_jump_to] >>
      `wb_frame cenv es0 es sf s0 (jump_to ok t)` by
        (irule wb_frame_readonly_tail >> qexistsl_tac [`sf`, `t`] >>
         simp[jump_to_def, lookup_var_def]) >>
      simp[] >> fs[jump_to_def]) >>
  Cases_on `n = 0`
  >- (gvs[comp_return_def] >>
      `eval_operand dp (jump_to ok t) = SOME saved` by simp[jump_to_def, eval_operand_def] >>
      fs[raw_call_buffer_frame_def] >>
      qpat_x_assum `wb_frame cenv es0 es sf s0 t` kall_tac >>
      `eval_operand dp (jump_to ok t) = SOME saved` by simp[jump_to_def, eval_operand_def] >>
      drule_all raw_call_empty_restore_arbitrary_frag >> strip_tac >>
      irule frag_path_conseq >>
      goal_assum (drule_at (Pat `frag_path _ _ _ _ _ _`)) >>
      simp[jump_to_def, eval_operand_def] >> metis_tac[]) >>
  gvs[raw_call_buffer_frame_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, pairTheory.EXISTS_PROD] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  `eval_operand ov (jump_to ok t) = SOME w /\
   eval_operand dp (jump_to ok t) = SOME saved /\
   LENGTH (jump_to ok t).vs_returndata < dimword (:256) /\
   mem_bytes_at (w2n w + 32) (LENGTH (TAKE n (jump_to ok t).vs_returndata))
     (jump_to ok t).vs_memory = TAKE n (jump_to ok t).vs_returndata` by
    simp[jump_to_def, eval_operand_def] >>
  `w2n w <= w2n w /\ w2n w + 32 <= w2n w + (32 * ((n+31) DIV 32) + 32)` by simp[] >>
  qpat_x_assum `wb_frame cenv es0 es sf s0 t` kall_tac >>
  drule_all raw_call_output_restore_allocas_frag >> strip_tac >>
  irule frag_path_conseq >>
  goal_assum (drule_at (Pat `frag_path _ _ _ _ _ _`)) >>
  simp[jump_to_def] >> rpt strip_tac >>
  `safe_operand sk p` by (fs[ci_mono_def] >> metis_tac[safe_operand_mono]) >>
  metis_tac[]
QED

Theorem raw_call_success_restore_frag[local]:
  (if 0 < n then do
     z <- emit_op RETURNDATASIZE []; c <- emit_op LT [z;Lit (n2w n)];
     cap <- compile_select c z (Lit (n2w n));
     emit_void MSTORE [ov;cap]; comp_return ov od
   else comp_return (Lit 0w)) sk = (result,se) /\
  emit_void SETFMP [dp] se = ((),sb) /\ ci_mono sc sk /\
  raw_call_buffer_frame ctx func cenv cx es0 es sf s0 saved ai w n t /\
  fn_inst_ids_distinct func /\ MEM alloc (fn_insts func) /\
  alloc.inst_opcode = ALLOCA /\ alloc.inst_outputs = [q] /\ alloc.inst_id = ai /\
  not_local_ptr cenv es.scopes q /\ sf.cs_next_id <= ai /\
  local_ptrs_reserved cenv sf /\ local_ptrs_reserved cenv sc /\
  sf.cs_next_var <= sc.cs_next_var /\ MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  safe_operand sc ov /\ safe_operand sc dp /\
  eval_operand ov t = SOME w /\ eval_operand dp t = SOME saved /\
  n < dimword (:256) /\ LENGTH t.vs_returndata < dimword (:256) /\
  (0 < n ==> mem_bytes_at (w2n w + 32) (LENGTH (TAKE n t.vs_returndata))
     t.vs_memory = TAKE n t.vs_returndata) ==>
  frag_path ctx sk sb (\u. u = jump_to ok t)
    (\u. stmt_state_rel ctx func cenv cx es u /\ wb_frame cenv es0 es sf s0 u /\
      u.vs_fmp = saved /\
      (!p v. safe_operand sc p /\ eval_operand p t = SOME v ==>
        eval_operand p u = SOME v) /\
      (if n = 0 then eval_operand result u = SOME 0w
       else eval_operand result u = SOME w /\
         val_in_memory (BaseTV (BytesT (Dynamic n)))
           (BytesV (TAKE n t.vs_returndata)) (w2n w) u.vs_memory)) R
Proof
  strip_tac >> drule_all raw_call_success_restore_allocas_frag >>
  disch_then (qspec_then `ok` (qspec_then `R` assume_tac)) >>
  irule frag_path_conseq >> goal_assum (drule_at (Pat `frag_path _ _ _ _ _ _`)) >>
  simp[] >> metis_tac[]
QED

Theorem raw_call_finish_success_allocas_frag[local]:
  compile_raw_call_finish aop dp dl gop vop call_ty n T ov op sc = (result,se) /\
  emit_void SETFMP [dp] se = ((),sb) /\
  (call_ty = StaticCall \/ call_ty = RegularCall) /\
  raw_call_buffer_frame ctx func cenv cx es0 es sf s0 saved ai w n s /\
  fn_inst_ids_distinct func /\ MEM alloc (fn_insts func) /\
  alloc.inst_opcode = ALLOCA /\ alloc.inst_outputs = [q] /\ alloc.inst_id = ai /\
  not_local_ptr cenv es.scopes q /\ sf.cs_next_id <= ai /\
  local_ptrs_reserved cenv sf /\ local_ptrs_reserved cenv sc /\
  sf.cs_next_var <= sc.cs_next_var /\ MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  safe_operand sc ov /\ safe_operand sc dp /\
  eval_operand ov s = SOME w /\ eval_operand dp s = SOME saved /\
  eval_operand op s = SOME (if n = 0 then w else w + 32w) /\
  eval_operand gop s = SOME gas /\ eval_operand aop s = SOME aw /\
  eval_operand vop s = SOME vw /\ eval_operand dl s = SOME iz /\
  take_call_outcome (w2w aw) (read_memory (w2n saved) (w2n iz) s)
    (if call_ty = StaticCall then NONE else SOME (w2n vw)) es =
      (INL (rq,outcome),es1) /\
  n < dimword (:256) /\ LENGTH outcome.co_returnData < dimword (:256) /\
  (~outcome.co_success ==> !t. t.vs_returndata = outcome.co_returnData ==> R (Abort Revert_abort t)) ==>
  frag_path ctx sc sb (\u. u = s)
    (\u. outcome.co_success /\
      stmt_state_rel ctx func cenv cx (SND (adopt_call_outcome rq outcome es1)) u /\
      wb_frame cenv es0 (SND (adopt_call_outcome rq outcome es1)) sf s0 u /\ u.vs_fmp = saved /\
      (0 < n ==> FLOOKUP u.vs_allocas ai = SOME (w2n w, ((n+31) DIV 32)*32+32)) /\
      (!p v. safe_operand sc p /\ eval_operand p s = SOME v ==>
        eval_operand p u = SOME v) /\
      (if n = 0 then eval_operand result u = SOME 0w
       else eval_operand result u = SOME w /\
         val_in_memory (BaseTV (BytesT (Dynamic n)))
           (BytesV (TAKE n outcome.co_returnData)) (w2n w) u.vs_memory)) R
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all raw_call_finish_certificates >> strip_tac >>
  `emit_op (if call_ty = StaticCall then STATICCALL else CALL)
    (if call_ty = StaticCall then [gop;aop;dp;dl;op;Lit (n2w n)]
     else [gop;aop;vop;dp;dl;op;Lit (n2w n)]) sc = (success,s1)` by
    (Cases_on `call_ty` >> gvs[]) >>
  `frag_path ctx sc s1 (\u. u = s)
    (\u. raw_call_buffer_frame ctx func cenv cx es0
       (SND (adopt_call_outcome rq outcome es1)) sf s0 saved ai w n u /\
      eval_operand success u = SOME (if outcome.co_success then 1w else 0w) /\
      u.vs_returndata = outcome.co_returnData /\ u.vs_fmp = s.vs_fmp /\
      (!p. safe_operand sc p ==> eval_operand p u = eval_operand p s) /\
      (0 < n ==> mem_bytes_at (w2n w + 32) (LENGTH (TAKE n outcome.co_returnData))
        u.vs_memory = TAKE n outcome.co_returnData)) R` by
    (drule_all raw_call_oracle_framed_frag >> simp[]) >>
  qpat_x_assum `call_ty = StaticCall \/ call_ty = RegularCall` kall_tac >>
  imp_res_tac fresh_label_props >>
  dxrule_all frag_path_fresh_label >> disch_tac >>
  dxrule_all frag_path_fresh_label >> disch_tac >>
  qpat_x_assum `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ _ = _` kall_tac >>
  `not_local_ptr cenv (SND (adopt_call_outcome rq outcome es1)).scopes q /\
   MAP FDOM es0.scopes = MAP FDOM (SND (adopt_call_outcome rq outcome es1)).scopes` by
    (drule raw_call_take_adopt_fields >> simp[]) >>
  qpat_x_assum `take_call_outcome _ _ _ _ = _` kall_tac >>
  qpat_x_assum `raw_call_buffer_frame _ _ _ _ _ es _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `not_local_ptr cenv es.scopes q` kall_tac >>
  qpat_x_assum `MAP FDOM es0.scopes = MAP FDOM es.scopes` kall_tac >>
  qmatch_goalsub_abbrev_tac `stmt_state_rel ctx func cenv cx adopted` >>
  drule frag_path_then >> disch_then irule >>
  reverse conj_tac
  >- fs[ci_mono_def] >>
  qpat_x_assum `frag_path ctx sc s3 _ _ _` kall_tac >>
  qpat_x_assum `(case call_ty of RegularCall => _ | DelegateCall => _ | StaticCall => _) = _` kall_tac >>
  qpat_x_assum `emit_op (if _ then _ else _) _ sc = _` kall_tac >>

  gen_tac >> disch_then (strip_assume_tac o BETA_RULE) >>
  irule raw_call_finish_branch_guarded_frag >> simp[] >>
  goal_assum (drule_at (Pat `emit_inst JNZ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `new_block fl _ = _`)) >>
  goal_assum (drule_at (Pat `emit_op RETURNDATASIZE _ _ = _`)) >>
  goal_assum (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_void RETURNDATACOPY _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_inst REVERT _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `new_block ok _ = _`)) >>
  simp[] >> qexists_tac `outcome.co_success` >> simp[] >> strip_tac >>
  `eval_operand ov t = SOME w /\ eval_operand dp t = SOME saved /\
   LENGTH t.vs_returndata < dimword (:256)` by simp[] >>
  `0 < n ==> mem_bytes_at (w2n w + 32) (LENGTH (TAKE n t.vs_returndata))
    t.vs_memory = TAKE n t.vs_returndata` by simp[] >>
  drule_all raw_call_success_restore_allocas_frag >>
  disch_then (qspec_then `ok` (qspec_then `R` assume_tac)) >>
  irule frag_path_conseq >>
  goal_assum (drule_at (Pat `frag_path _ _ _ _ _ _`)) >>
  simp[] >> metis_tac[]
QED

Theorem raw_call_finish_allocas_frag[local]:
  compile_raw_call_finish aop dp dl gop vop call_ty n T ov op sc = (result,se) /\
  emit_void SETFMP [dp] se = ((),sb) /\
  (call_ty = StaticCall \/ call_ty = RegularCall) /\
  raw_call_buffer_frame ctx func cenv cx es0 es sf s0 saved ai w n s /\
  fn_inst_ids_distinct func /\ MEM alloc (fn_insts func) /\
  alloc.inst_opcode = ALLOCA /\ alloc.inst_outputs = [q] /\ alloc.inst_id = ai /\
  not_local_ptr cenv es.scopes q /\ sf.cs_next_id <= ai /\
  local_ptrs_reserved cenv sf /\ local_ptrs_reserved cenv sc /\
  sf.cs_next_var <= sc.cs_next_var /\ MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  safe_operand sc ov /\ safe_operand sc dp /\
  eval_operand ov s = SOME w /\ eval_operand dp s = SOME saved /\
  eval_operand op s = SOME (if n = 0 then w else w + 32w) /\
  eval_operand gop s = SOME gas /\ eval_operand aop s = SOME aw /\
  eval_operand vop s = SOME vw /\ eval_operand dl s = SOME iz /\
  take_call_outcome (w2w aw) (read_memory (w2n saved) (w2n iz) s)
    (if call_ty = StaticCall then NONE else SOME (w2n vw)) es =
      (INL (rq,outcome),es1) /\
  n < dimword (:256) /\ LENGTH outcome.co_returnData < dimword (:256) /\
  (~outcome.co_success ==> !t. t.vs_returndata = outcome.co_returnData ==> R (Abort Revert_abort t)) ==>
  frag_path ctx sc sb (\u. u = s)
    (\u. stmt_state_rel ctx func cenv cx (SND (adopt_call_outcome rq outcome es1)) u /\
      wb_frame cenv es0 (SND (adopt_call_outcome rq outcome es1)) sf s0 u /\ u.vs_fmp = saved /\
      (0 < n ==> FLOOKUP u.vs_allocas ai = SOME (w2n w, ((n+31) DIV 32)*32+32)) /\
      (!p v. safe_operand sc p /\ eval_operand p s = SOME v ==>
        eval_operand p u = SOME v) /\
      (if n = 0 then eval_operand result u = SOME 0w
       else eval_operand result u = SOME w /\
         val_in_memory (BaseTV (BytesT (Dynamic n)))
           (BytesV (TAKE n outcome.co_returnData)) (w2n w) u.vs_memory)) R
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all raw_call_finish_success_allocas_frag >> strip_tac >>
  irule frag_path_conseq >> goal_assum (drule_at Any) >> simp[]
QED

Theorem raw_call_finish_guarded_frag[local]:
  compile_raw_call_finish aop dp dl gop vop call_ty n T ov op sc = (result,se) /\
  emit_void SETFMP [dp] se = ((),sb) /\
  (call_ty = StaticCall \/ call_ty = RegularCall) /\
  raw_call_buffer_frame ctx func cenv cx es0 es sf s0 saved ai w n s /\
  fn_inst_ids_distinct func /\ MEM alloc (fn_insts func) /\
  alloc.inst_opcode = ALLOCA /\ alloc.inst_outputs = [q] /\ alloc.inst_id = ai /\
  not_local_ptr cenv es.scopes q /\ sf.cs_next_id <= ai /\
  local_ptrs_reserved cenv sf /\ local_ptrs_reserved cenv sc /\
  sf.cs_next_var <= sc.cs_next_var /\ MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  safe_operand sc ov /\ safe_operand sc dp /\
  eval_operand ov s = SOME w /\ eval_operand dp s = SOME saved /\
  eval_operand op s = SOME (if n = 0 then w else w + 32w) /\
  eval_operand gop s = SOME gas /\ eval_operand aop s = SOME aw /\
  eval_operand vop s = SOME vw /\ eval_operand dl s = SOME iz /\
  take_call_outcome (w2w aw) (read_memory (w2n saved) (w2n iz) s)
    (if call_ty = StaticCall then NONE else SOME (w2n vw)) es =
      (INL (rq,outcome),es1) /\
  n < dimword (:256) /\ LENGTH outcome.co_returnData < dimword (:256) /\
  (~outcome.co_success ==> !t. t.vs_returndata = outcome.co_returnData ==> R (Abort Revert_abort t)) ==>
  frag_path ctx sc sb (\u. u = s)
    (\u. stmt_state_rel ctx func cenv cx (SND (adopt_call_outcome rq outcome es1)) u /\
      wb_frame cenv es0 (SND (adopt_call_outcome rq outcome es1)) sf s0 u /\ u.vs_fmp = saved /\
      (!p v. safe_operand sc p /\ eval_operand p s = SOME v ==>
        eval_operand p u = SOME v) /\
      (if n = 0 then eval_operand result u = SOME 0w
       else eval_operand result u = SOME w /\
         val_in_memory (BaseTV (BytesT (Dynamic n)))
           (BytesV (TAKE n outcome.co_returnData)) (w2n w) u.vs_memory)) R
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all raw_call_finish_allocas_frag >> strip_tac >>
  irule frag_path_conseq >> goal_assum (drule_at (Pat `frag_path _ _ _ _ _ _`)) >>
  simp[] >> metis_tac[]
QED

Theorem raw_call_finish_framed_frag[local]:
  compile_raw_call_finish aop dp dl gop vop call_ty n T ov op sc = (result,se) /\
  emit_void SETFMP [dp] se = ((),sb) /\
  (call_ty = StaticCall \/ call_ty = RegularCall) /\
  raw_call_buffer_frame ctx func cenv cx es0 es sf s0 saved ai w n s /\
  fn_inst_ids_distinct func /\ MEM alloc (fn_insts func) /\
  alloc.inst_opcode = ALLOCA /\ alloc.inst_outputs = [q] /\ alloc.inst_id = ai /\
  not_local_ptr cenv es.scopes q /\ sf.cs_next_id <= ai /\
  local_ptrs_reserved cenv sf /\ local_ptrs_reserved cenv sc /\
  sf.cs_next_var <= sc.cs_next_var /\ MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  safe_operand sc ov /\ safe_operand sc dp /\
  eval_operand ov s = SOME w /\ eval_operand dp s = SOME saved /\
  eval_operand op s = SOME (if n = 0 then w else w + 32w) /\
  eval_operand gop s = SOME gas /\ eval_operand aop s = SOME aw /\
  eval_operand vop s = SOME vw /\ eval_operand dl s = SOME iz /\
  take_call_outcome (w2w aw) (read_memory (w2n saved) (w2n iz) s)
    (if call_ty = StaticCall then NONE else SOME (w2n vw)) es =
      (INL (rq,outcome),es1) /\
  n < dimword (:256) /\ LENGTH outcome.co_returnData < dimword (:256) /\
  (!t. t.vs_returndata = outcome.co_returnData ==> R (Abort Revert_abort t)) ==>
  frag_path ctx sc sb (\u. u = s)
    (\u. stmt_state_rel ctx func cenv cx (SND (adopt_call_outcome rq outcome es1)) u /\
      wb_frame cenv es0 (SND (adopt_call_outcome rq outcome es1)) sf s0 u /\ u.vs_fmp = saved /\
      (!p v. safe_operand sc p /\ eval_operand p s = SOME v ==>
        eval_operand p u = SOME v) /\
      (if n = 0 then eval_operand result u = SOME 0w
       else eval_operand result u = SOME w /\
         val_in_memory (BaseTV (BytesT (Dynamic n)))
           (BytesV (TAKE n outcome.co_returnData)) (w2n w) u.vs_memory)) R
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~outcome.co_success ==> !t. t.vs_returndata = outcome.co_returnData ==>
    R (Abort Revert_abort t)` by simp[] >>
  drule_all raw_call_finish_guarded_frag >> simp[]
QED

Theorem calldata_prepare_members[local]:
  compile_raw_call_outbuf n sa = ((ov,op),sb) /\
  compile_msg_data_to_memory sb = ((dp,dl),sc) /\
  fn_has_code sa sc func ==>
  MEM (mk_inst sa.cs_next_id ALLOCA
    [Lit (n2w (if n = 0 then 0 else ((n + 31) DIV 32) * 32 + 32))]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) /\
  EXISTS (\inst. inst.inst_opcode = DALLOCA) (fn_insts func)
Proof
  strip_tac >> drule_all calldata_prepare_code >> strip_tac >>
  `?inst. MEM inst (emitted_insts sa sc) /\ inst.inst_opcode = DALLOCA` by
    (qpat_x_assum `fn_has_code _ _ _` kall_tac >>
     qpat_x_assum `sb.cs_current_insts = _` kall_tac >>
     qpat_x_assum `sc.cs_current_insts = _` kall_tac >>
     qpat_x_assum `EVERY _ _` kall_tac >>
     Cases_on `n = 0` >>
     gvs[compile_raw_call_outbuf_def, compile_alloc_buffer_def,
       compile_msg_data_to_memory_def, compile_alloc_dynamic_def,
       comp_bind_def, comp_return_def, comp_ignore_bind_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
       emitted_insts_def, rich_listTheory.DROP_APPEND1, rich_listTheory.DROP_APPEND2,
       mk_inst_def] >>
     simp[LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM]) >>
  reverse conj_tac
  >- (simp[listTheory.EXISTS_MEM] >>
      qexists_tac `inst` >> simp[] >> irule hash_emitted_inst_mem >>
      goal_assum (drule_at Any) >> simp[]) >>
  irule hash_emitted_inst_mem >> goal_assum (drule_at Any) >>
  qpat_x_assum `sb.cs_current_insts = _` kall_tac >>
  qpat_x_assum `sc.cs_current_insts = _` kall_tac >>
  qpat_x_assum `EVERY _ _` kall_tac >>
  Cases_on `n = 0` >>
  gvs[compile_raw_call_outbuf_def, compile_alloc_buffer_def,
    compile_msg_data_to_memory_def, compile_alloc_dynamic_def,
    comp_bind_def, comp_return_def, comp_ignore_bind_def,
    emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
    emitted_insts_def, rich_listTheory.DROP_APPEND1, rich_listTheory.DROP_APPEND2,
    mk_inst_def]
QED

Theorem calldata_kwarg_safe[local]:
  !ks ops. EVERY (safe_operand sc) ops ==>
    (case ext_call_kwarg k ks ops of NONE => T | SOME p => safe_operand sc p)
Proof
  Induct >> Cases_on `ops` >> simp[ext_call_kwarg_def] >>
  rpt strip_tac >> IF_CASES_TAC >> gvs[]
QED

Theorem calldata_call_prepare_pre[local]:
  expr_body_pre cenv cx env (Call ann (RawCallCalldataTarget flags) (addr::kws) NONE) es /\
  eval_exprs cx (addr::kws) es = (INL vs,es1) /\
  typed_args_post ctx func cenv cx es sa s0 es1 (addr::kws) (aop::ops) vs entry /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sp.cs_next_var /\
  sa.cs_next_id <= sp.cs_next_id /\ EVERY (safe_operand sp) ops /\
  fn_inst_ids_distinct func /\
  MEM (mk_inst sg.cs_next_id ALLOCA
    [Lit (n2w (if flags.rcf_max_outsize = 0 then 0
      else ((flags.rcf_max_outsize + 31) DIV 32) * 32 + 32))]
    [STRING #"%" (toString sg.cs_next_var)]) (fn_insts func) /\
  EXISTS (\inst. inst.inst_opcode = DALLOCA) (fn_insts func) ==>
  calldata_prepare_pre ctx func cenv cx es es1 sa s0 sp sg
    flags.rcf_max_outsize (ext_call_kwarg EKGas flags.rcf_kws ops) entry
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es1 entry /\ wb_frame cenv es es1 sa s0 entry` by
    fs[typed_args_post_def] >>
  `LENGTH cx.txn.calldata < dimword (:256)` by
    fs[expr_body_pre_def, expr_sim_inv_def,
       context_well_typed_def, wordsTheory.dimword_def] >>
  `MAP FDOM es.scopes = MAP FDOM es1.scopes` by
    metis_tac[eval_exprs_preserves_scopes_dom] >>
  `local_ptrs_reserved cenv sp` by metis_tac[local_ptrs_reserved_next_var] >>
  simp[calldata_prepare_pre_def] >> conj_tac
  >- (Cases_on `flags.rcf_max_outsize = 0` >> simp[] >>
      `0 < flags.rcf_max_outsize` by simp[] >>
      drule_all calldata_outbuf_size >>
      simp[wordsTheory.dimword_def] >> decide_tac) >>
  irule calldata_kwarg_safe >> simp[]
QED

Theorem calldata_call_args_values[local]:
  expr_body_pre cenv cx env (Call ann (RawCallCalldataTarget flags) args dflt) es /\
  typed_args_ready ctx func cenv cx expr_type (expr_sim_inv cenv cx env) args /\
  eval_exprs cx args es = (INL vs,es1) ==>
  expr_sim_inv cenv cx env es1 /\
  LIST_REL (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    value_has_type tv v) args vs
Proof
  strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  conj_tac >- metis_tac[typed_args_ready_inv] >>
  irule stack_args_values_typed_body >> goal_assum (drule_at Any) >>
  qexists_tac `es1` >> simp[] >>
  drule calldata_call_pre >> strip_tac >> gvs[] >>
  `EVERY (\e. expr_type e = BaseT (UintT 256)) kws` by
    (irule raw_call_kw_types >> qexists_tac `flags.rcf_kws` >>
     gvs[raw_call_kws_ok_def]) >>
  rpt gen_tac >> disch_tac >> conj_tac
  >- (irule calldata_call_arg_pre >> fs[] >>
      goal_assum (drule_at (Pat `expr_body_pre _ _ _ _ _`)) >> simp[]) >>
  fs[listTheory.EVERY_MEM] >>
  Cases_on `e = addr` >> gvs[is_word_type_def] >> first_x_assum drule >>
  simp[is_word_type_def]
QED

Theorem calldata_kwarg_rel[local]:
  !ks xs ys. LIST_REL R xs ys ==>
    (case ext_call_kwarg k ks xs of
     NONE => ext_call_kwarg k ks ys = NONE
     | SOME x => ?y. ext_call_kwarg k ks ys = SOME y /\ R x y)
Proof
  Induct >> Cases_on `xs` >> Cases_on `ys` >>
  simp[ext_call_kwarg_def] >> rpt strip_tac >>
  IF_CASES_TAC >> gvs[] >> first_x_assum irule >> simp[]
QED

Theorem calldata_kwarg_value[local]:
  LIST_REL (\v p. value_has_type (BaseTV (UintT 256)) v /\
    eval_operand p s = SOME (typed_val_to_w256 (BaseTV (UintT 256)) v)) vals ops ==>
  ?amount. raw_call_value ks vals = SOME amount /\ amount < dimword (:256) /\
    eval_operand (case ext_call_kwarg EKValue ks ops of
      NONE => Lit 0w | SOME p => p) s = SOME (n2w amount)
Proof
  strip_tac >>
  `case ext_call_kwarg EKValue ks vals of
     NONE => ext_call_kwarg EKValue ks ops = NONE
   | SOME v => ?p. ext_call_kwarg EKValue ks ops = SOME p /\
       value_has_type (BaseTV (UintT 256)) v /\
       eval_operand p s = SOME (typed_val_to_w256 (BaseTV (UintT 256)) v)` by
    (drule (calldata_kwarg_rel |> INST_TYPE [alpha |-> ``:ext_call_kw``]
      |> Q.INST [`k` |-> `EKValue`]) >>
     disch_then (qspec_then `ks` mp_tac) >> simp[]) >>
  Cases_on `ext_call_kwarg EKValue ks vals` >> gvs[raw_call_value_def]
  >- simp[eval_operand_def, wordsTheory.dimword_def] >>
  drule uint256_typed_dest >> strip_tac >>
  qexists_tac `w2n (typed_val_to_w256 (BaseTV (UintT 256)) x)` >>
  simp[wordsTheory.w2n_lt]
QED

Theorem calldata_kwarg_words[local]:
  !kws vals ops.
  EVERY (\e. expr_type e = BaseT (UintT 256)) kws /\
  LIST_REL (\e v. ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    value_has_type tv v) kws vals /\
  LIST_REL (\p ev. eval_operand p s = SOME
    (typed_val_to_w256 (THE (evaluate_type (get_tenv cx) (expr_type (FST ev))))
      (SND ev))) ops (ZIP (kws,vals)) ==>
  LIST_REL (\v p. value_has_type (BaseTV (UintT 256)) v /\
    eval_operand p s = SOME (typed_val_to_w256 (BaseTV (UintT 256)) v)) vals ops
Proof
  Induct >> Cases_on `vals` >> Cases_on `ops` >>
  simp[evaluate_type_def] >> rpt strip_tac >> gvs[evaluate_type_def] >>
  first_x_assum irule >> simp[]
QED

Theorem calldata_call_source_args[local]:
  expr_body_pre cenv cx env (Call ann (RawCallCalldataTarget flags) (addr::kws) NONE) es /\
  typed_args_ready ctx func cenv cx expr_type (expr_sim_inv cenv cx env) (addr::kws) /\
  eval_exprs cx (addr::kws) es = (INL vs,es1) /\
  typed_args_post ctx func cenv cx es sa s0 es1 (addr::kws) (aop::ops) vs entry ==>
  expr_sim_inv cenv cx env es1 /\
  ?aw amount vals. eval_operand aop entry = SOME aw /\
    amount < dimword (:256) /\ (flags.rcf_is_static ==> amount = 0) /\
    eval_operand (case ext_call_kwarg EKValue flags.rcf_kws ops of
      NONE => Lit 0w | SOME p => p) entry = SOME (n2w amount) /\
    eval_expr cx (Call ann (RawCallCalldataTarget flags) (addr::kws) NONE) es =
      eval_raw_call cx flags (w2w aw) cx.txn.calldata amount
        (forwarded_gas default_evm_gas_limit (ext_call_kwarg EKGas flags.rcf_kws vals)) es1
Proof
  strip_tac >> drule_all calldata_call_args_values >> strip_tac >> simp[] >>
  drule calldata_call_pre >> strip_tac >> gvs[] >>
  `EVERY (\e. expr_type e = BaseT (UintT 256)) kws` by
    (irule raw_call_kw_types >> qexists_tac `flags.rcf_kws` >>
     gvs[raw_call_kws_ok_def]) >>
  gvs[typed_args_post_def, evaluate_type_def] >>
  drule_all calldata_kwarg_words >> strip_tac >>
  drule calldata_kwarg_value >>
  disch_then (qspec_then `flags.rcf_kws` strip_assume_tac) >>
  drule address_typed_dest >> strip_tac >>
  `flags.rcf_is_static ==> amount = 0` by
    (strip_tac >>
     `~MEM EKValue flags.rcf_kws` by fs[raw_call_kws_ok_def] >>
     fs[raw_call_value_def, ext_call_kwarg_not_mem]) >>
  rename1 `eval_exprs cx (addr::kws) es = (INL (v::vals),es1)` >>
  qexistsl_tac [`amount`,`vals`] >> simp[] >>
  irule calldata_call_eval >> simp[] >> goal_assum (drule_at Any) >> simp[]
QED

(* The non-reverting result is an inline pair, not a pair of pointers.
   Padding in the bytes buffer is irrelevant to this representation. *)
Theorem raw_call_tuple_memory[local]:
  mem_word_at p mem = (if success then 1w else 0w) /\
  val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) (p + 32) mem ==>
  val_in_memory (TupleTV [BaseTV BoolT; BaseTV (BytesT (Dynamic n))])
    (ArrayV (TupleV [BoolV success; BytesV bs])) p mem
Proof
  simp[val_in_memory_def, type_memory_size_def, val_to_w256_def]
QED

Theorem raw_call_tuple_copy:
  mem_word_at p s.vs_memory = (if success then 1w else 0w) /\
  val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) src s.vs_memory /\
  val_wf (BaseTV (BytesT (Dynamic n))) (BytesV bs) /\
  type_memory_size (BaseTV (BytesT (Dynamic n))) <= sz ==>
  val_in_memory (TupleTV [BaseTV BoolT; BaseTV (BytesT (Dynamic n))])
    (ArrayV (TupleV [BoolV success; BytesV bs])) p
    (mcopy (p + 32) src sz s).vs_memory
Proof
  strip_tac >>
  `val_in_memory (BaseTV BoolT) (BoolV success) p s.vs_memory` by
    simp[val_in_memory_def, val_to_w256_def] >>
  `val_in_memory (BaseTV BoolT) (BoolV success) p
    (mcopy (p + 32) src sz s).vs_memory` by
    (irule mcopy_preserves_val_in_memory >>
     simp[val_wf_def, type_memory_size_def]) >>
  irule raw_call_tuple_memory >> conj_tac
  >- fs[val_in_memory_def, val_to_w256_def] >>
  irule mcopy_establishes_val_in_memory >> simp[]
QED

Theorem raw_call_tuple_copy_frame:
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (p,32 + sz) /\
  mem_word_at p s.vs_memory = (if success then 1w else 0w) /\
  val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) src s.vs_memory /\
  val_wf (BaseTV (BytesT (Dynamic n))) (BytesV bs) /\
  type_memory_size (BaseTV (BytesT (Dynamic n))) <= sz ==>
  stmt_state_rel ctx func cenv cx es (mcopy (p + 32) src sz s) /\
  val_in_memory (TupleTV [BaseTV BoolT; BaseTV (BytesT (Dynamic n))])
    (ArrayV (TupleV [BoolV success; BytesV bs])) p
    (mcopy (p + 32) src sz s).vs_memory
Proof
  strip_tac >> conj_tac
  >- (simp[mcopy_def] >> irule raw_call_outbuf_write_frame >> simp[] >>
      qexistsl_tac [`p`, `inst`, `q`, `32 + sz`] >>
      simp[read_memory_def, LENGTH_TAKE_EQ, LENGTH_DROP]) >>
  irule raw_call_tuple_copy >> simp[]
QED

Theorem raw_call_bool_result:
  ~flags.rcf_revert_on_failure /\ flags.rcf_max_outsize = 0 /\
  eval_operand op s = SOME (if success then 1w else 0w) ==>
  expr_val_rel cx (raw_call_return_type flags) (BoolV success) op s
Proof
  simp[raw_call_return_type_def, expr_val_rel_def, is_word_type_def,
       evaluate_type_def, typed_val_to_w256_def, val_to_w256_def]
QED

Theorem raw_call_tuple_result:
  ~flags.rcf_revert_on_failure /\ 0 < flags.rcf_max_outsize /\
  eval_operand op s = SOME w /\
  mem_word_at (w2n w) s.vs_memory = (if success then 1w else 0w) /\
  val_in_memory (BaseTV (BytesT (Dynamic flags.rcf_max_outsize)))
    (BytesV (TAKE flags.rcf_max_outsize data)) (w2n w + 32) s.vs_memory ==>
  expr_val_rel cx (raw_call_return_type flags)
    (ArrayV (TupleV [BoolV success; BytesV (TAKE flags.rcf_max_outsize data)])) op s
Proof
  strip_tac >>
  simp[expr_val_rel_def, raw_call_return_type_def, is_word_type_def,
       evaluate_type_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  irule raw_call_tuple_memory >> simp[]
QED

Theorem raw_call_tuple_dst_run:
  !sa sb pop dst s w.
  emit_op ADD [pop;Lit 32w] sa = (dst,sb) /\
  eval_operand pop s = SOME w ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand dst t = SOME (w + 32w) /\
    (?vars. t = s with vs_vars := vars) /\
    (!p. safe_operand sa p ==> eval_operand p t = eval_operand p s)
Proof
  rpt gen_tac >> strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  gvs[] >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
       exec_pure2_def, eval_operand_def, bind_outputs_def] >>
  simp[lookup_var_update_var, update_var_def] >>
  conj_tac >- (qexists_tac `s.vs_vars |+ (STRING #"%" (toString sa.cs_next_var), w + 32w)` >> simp[]) >>
  Cases >> simp[safe_operand_def, eval_operand_def, lookup_var_def,
                not_fresh_at_def] >> rpt strip_tac >>
  first_x_assum (qspec_then `sa.cs_next_var` mp_tac) >>
  simp[finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem raw_call_tuple_copy_restore_run[local]:
  !sa sb sc sd pop dst src dop s w a saved sz.
  emit_op ADD [pop;Lit 32w] sa = (dst,sb) /\
  emit_void MCOPY [dst;src;Lit (n2w sz)] sb = ((),sc) /\
  emit_void SETFMP [dop] sc = ((),sd) /\
  safe_operand sa pop /\ safe_operand sa src /\ safe_operand sa dop /\
  eval_operand pop s = SOME w /\ eval_operand src s = SOME a /\
  eval_operand dop s = SOME saved /\ sz < dimword (:256) ==>
  ?u t. run_inst_seq (emitted_insts sa sd) s = OK t /\
    (?vars. u = s with vs_vars := vars) /\
    (!p. safe_operand sa p ==> eval_operand p u = eval_operand p s) /\
    t = (mcopy (w2n (w + 32w)) (w2n a) sz u) with vs_fmp := saved /\
    (!p. safe_operand sa p ==> eval_operand p t = eval_operand p s)
Proof
  rpt gen_tac >> strip_tac >> drule_all raw_call_tuple_dst_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sb) s = OK u` >>
  `eval_operand src u = SOME a /\ eval_operand dop u = SOME saved` by simp[] >>
  drule_all emit_mcopy_run >> strip_tac >>
  `eval_operand dop (mcopy (w2n (w + 32w)) (w2n a) sz u) = SOME saved` by
    (Cases_on `dop` >> gvs[mcopy_def, write_memory_with_expansion_def,
                           eval_operand_def, lookup_var_def]) >>
  drule_all raw_call_restore_arbitrary_run >> strip_tac >>
  qexistsl_tac [`u`, `(mcopy (w2n (w + 32w)) (w2n a) sz u) with vs_fmp := saved`] >>
  simp[] >> conj_tac
  >- (`inst_extends sa sb /\ inst_extends sb sc /\ inst_extends sc sd` by
        (conj_tac
         >- (irule inst_extends_emit_op >> goal_assum (drule_at Any)) >>
         conj_tac >> irule inst_extends_emit_void >> goal_assum (drule_at Any)) >>
      `inst_extends sa sc` by
        (irule inst_extends_trans >> qexists_tac `sb` >> simp[]) >>
      irule run_inst_seq_compose_ok >>
      qexistsl_tac [`mcopy (w2n (w + 32w)) (w2n a) sz u`, `sc`] >> simp[] >>
      irule run_inst_seq_compose_ok >> qexistsl_tac [`u`, `sb`] >> simp[]) >>
  conj_tac >- (qexists_tac `vars` >> simp[]) >>
  qx_gen_tac `p` >> strip_tac >>
  `eval_operand p u = eval_operand p s` by simp[] >>
  Cases_on `p` >> gvs[mcopy_def, write_memory_with_expansion_def,
                       eval_operand_def, lookup_var_def]
QED

Theorem raw_call_alloca_saved_fmp[local]:
  !inst s sz saved u.
  exec_alloca inst (s with vs_fmp := saved) sz = OK u ==>
  exec_alloca inst s sz = OK (u with vs_fmp := s.vs_fmp) /\
  u.vs_fmp = saved
Proof
  rpt gen_tac >> simp[exec_alloca_def, update_var_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >> simp[venom_state_component_equality]
QED

Theorem raw_call_buffer_saved_fmp_run[local]:
  !sa sb buf sz s saved u.
  compile_alloc_buffer sz sa = (buf,sb) /\
  run_inst_seq (emitted_insts sa sb) (s with vs_fmp := saved) = OK u ==>
  run_inst_seq (emitted_insts sa sb) s = OK (u with vs_fmp := s.vs_fmp) /\
  u.vs_fmp = saved
Proof
  rpt gen_tac >> strip_tac >>
  gvs[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >>
  drule emitted_insts_emit_op >> strip_tac >> gvs[] >>
  gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def,
      eval_operand_def] >>
  gvs[AllCaseEqs()] >> drule raw_call_alloca_saved_fmp >> simp[]
QED

Theorem raw_call_alloc_buffer_run[local]:
  !func cenv cx es sa sm buf sz s ctx saved.
  compile_alloc_buffer sz sa = (buf,sm) /\
  stmt_state_rel ctx func cenv cx es (s with vs_fmp := saved) /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\ sz < dimword (:256) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) ==>
  ?t w. run_inst_seq (emitted_insts sa sm) s = OK t /\
    stmt_state_rel ctx func cenv cx es (t with vs_fmp := saved) /\
    t.vs_fmp = s.vs_fmp /\ eval_operand buf.buf_operand t = SOME w /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
    w2n w + sz < dimword (:256) /\ t.vs_memory = s.vs_memory /\
    sa.cs_next_id < sm.cs_next_id /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
       regions_disjoint (w2n w) sz b len) /\
    (!name b len. local_region cenv es.scopes t name b len ==>
       regions_disjoint (w2n w) sz b len) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sm p)
Proof
  rpt gen_tac >> strip_tac >> drule_all literal_alloc_buffer_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) (s with vs_fmp := saved) = OK u` >>
  drule_all raw_call_buffer_saved_fmp_run >> strip_tac >>
  qexistsl_tac [`u with vs_fmp := s.vs_fmp`, `w`] >>
  `u with vs_fmp := saved = u` by simp[venom_state_component_equality] >>
  gvs[lookup_var_def, local_region_def, eval_operand_def] >>
  metis_tac[]
QED

Theorem raw_call_alloc_buffer_wb[local]:
  wb_frame cenv es0 es sf s0 s /\
  sf.cs_next_var <= sa.cs_next_var /\ sf.cs_next_id <= sa.cs_next_id /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
     FLOOKUP t.vs_allocas aid = SOME entry) /\
  t.vs_memory = s.vs_memory /\ local_ptrs_reserved cenv sf /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes ==>
  wb_frame cenv es0 es sf s0 t
Proof
  strip_tac >> irule wb_frame_allocating_tail >> simp[] >>
  qexistsl_tac [`s`, `es.scopes`, `sa`] >> simp[]
QED

Theorem raw_call_tuple_flag_ready[local]:
  stmt_state_rel ctx func cenv cx es (s with vs_fmp := saved) /\
  wb_frame cenv es0 es sf s0 s /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w,32 + sz) /\
  sf.cs_next_id <= inst.inst_id /\ local_ptrs_reserved cenv sf /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  val_in_memory ty v off s.vs_memory /\ val_wf ty v /\
  type_memory_size ty <= len /\ regions_disjoint (w2n w) (32 + sz) off len /\
  emit_void MSTORE [pop;ok] sa = ((),sb) /\
  eval_operand pop s = SOME w /\ eval_operand ok s = SOME flag ==>
  run_inst_seq (emitted_insts sa sb) s = OK (mstore (w2n w) flag s) /\
  stmt_state_rel ctx func cenv cx es
    ((mstore (w2n w) flag s) with vs_fmp := saved) /\
  wb_frame cenv es0 es sf s0 (mstore (w2n w) flag s) /\
  val_in_memory ty v off (mstore (w2n w) flag s).vs_memory /\
  mem_word_at (w2n w) (mstore (w2n w) flag s).vs_memory = flag
Proof
  strip_tac >> conj_tac
  >- (drule_all emit_mstore_run >> simp[]) >>
  conj_tac
  >- (irule raw_call_output_store_frame >> simp[] >>
      goal_assum (drule_at (Pat `MEM _ (fn_insts _)`)) >> simp[]) >>
  conj_tac
  >- (`mstore (w2n w) flag (s with vs_fmp := saved) =
         (mstore (w2n w) flag s) with vs_fmp := saved` by
        simp[mstore_def, write_memory_with_expansion_def] >>
      `wb_frame cenv es0 es sf s0
         (mstore (w2n w) flag (s with vs_fmp := saved))` suffices_by
        asm_rewrite_tac[raw_call_wb_frame_fmp] >>
      irule raw_call_outbuf_mstore_wb_frame >> simp[raw_call_wb_frame_fmp] >>
      goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >> simp[] >>
      goal_assum (drule_at (Pat `MEM _ (fn_insts _)`)) >> simp[] >>
      goal_assum (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >> simp[]) >>
  conj_tac
  >- (irule mstore_keeps_val_in_memory >> simp[] >>
      gvs[regions_disjoint_def] >> decide_tac) >>
  simp[mstore_mem_word_at_same]
QED

Theorem raw_call_tuple_alloc_ready:
  compile_alloc_buffer (32 + sz) sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand;ok] sm = ((),sb) /\
  stmt_state_rel ctx func cenv cx es (s with vs_fmp := saved) /\
  wb_frame cenv es0 es sf s0 s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sf /\
  sf.cs_next_var <= sa.cs_next_var /\ sf.cs_next_id <= sa.cs_next_id /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\ 32 + sz < dimword (:256) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w (32 + sz))]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) /\
  srcid < sa.cs_next_id /\ FLOOKUP s.vs_allocas srcid = SOME (off,len) /\
  val_in_memory ty v off s.vs_memory /\ val_wf ty v /\
  type_memory_size ty <= len /\ safe_operand sa ok /\
  eval_operand ok s = SOME (if success then 1w else 0w) ==>
  ?t w. run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel ctx func cenv cx es (t with vs_fmp := saved) /\
    wb_frame cenv es0 es sf s0 t /\ t.vs_fmp = s.vs_fmp /\
    eval_operand buf.buf_operand t = SOME w /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,32 + sz) /\
    FLOOKUP t.vs_allocas srcid = SOME (off,len) /\
    w2n w + (32 + sz) < dimword (:256) /\
    regions_disjoint (w2n w) (32 + sz) off len /\
    val_in_memory ty v off t.vs_memory /\
    mem_word_at (w2n w) t.vs_memory = (if success then 1w else 0w) /\
    (!p. safe_operand sa p ==> eval_operand p t = eval_operand p s) /\
    (?q. buf.buf_operand = Var q /\ not_fresh_at sm q)
Proof
  strip_tac >> drule_all raw_call_alloc_buffer_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sm) s = OK u` >>
  `wb_frame cenv es0 es sf s0 u` by
    (drule_all raw_call_alloc_buffer_wb >> simp[]) >>
  `!p. safe_operand sa p ==> eval_operand p u = eval_operand p s` by
    (Cases >> simp[safe_operand_def, eval_operand_def]) >>
  `not_local_ptr cenv es.scopes (STRING #"%" (toString sa.cs_next_var))` by
    (irule fresh_not_local_ptr >> qexists_tac `sa` >> simp[not_fresh_at_def]) >>
  `regions_disjoint (w2n w) (32 + sz) off len` by metis_tac[] >>
  `eval_operand ok u = SOME (if success then 1w else 0w)` by simp[] >>
  `val_in_memory ty v off u.vs_memory` by simp[] >>
  drule_at (Pat `MEM _ (fn_insts _)`) raw_call_tuple_flag_ready >>
  simp[mk_inst_def] >> disch_then drule >> simp[] >> strip_tac >>
  fs[arithmeticTheory.ADD_COMM] >> first_x_assum drule_all >> strip_tac >>
  qexistsl_tac [`mstore (w2n w) (if success then 1w else 0w) u`, `w`] >>
  simp[] >> conj_tac
  >- (`inst_extends sa sm` by
        (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
         simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
         pairarg_tac >> strip_tac >> gvs[] >> drule inst_extends_emit_op >> simp[]) >>
      `inst_extends sm sb` by
        (irule inst_extends_emit_void >> goal_assum (drule_at Any)) >>
      irule run_inst_seq_compose_ok >> qexistsl_tac [`u`, `sm`] >> simp[]) >>
  simp[mstore_def, write_memory_with_expansion_def, eval_operand_def, lookup_var_def] >>
  metis_tac[]
QED

Theorem raw_call_bool_restore_frag[local]:
  emit_void SETFMP [dop] sa = ((),sb) /\
  eval_operand dop s = SOME saved /\ wb_frame cenv es0 es sf s0 s /\
  stmt_state_rel ctx func cenv cx es (s with vs_fmp := saved) /\
  ~flags.rcf_revert_on_failure /\ flags.rcf_max_outsize = 0 /\
  eval_operand op s = SOME (if success then 1w else 0w) ==>
  frag_path ctx sa sb (\r. r = s)
    (\r. stmt_state_rel ctx func cenv cx es r /\ wb_frame cenv es0 es sf s0 r /\
      r.vs_fmp = saved /\
      expr_val_rel cx (raw_call_return_type flags) (BoolV success) op r /\
      (!p. eval_operand p r = eval_operand p s)) (\r. F)
Proof
  strip_tac >> drule_all raw_call_empty_restore_arbitrary_frag >> strip_tac >>
  irule frag_path_conseq >> goal_assum (drule_at (Pat `frag_path _ _ _ _ _ _`)) >>
  simp[NoAsms] >> rpt strip_tac >> simp[] >>
  irule raw_call_bool_result >> simp[]
QED

Theorem raw_call_tuple_copy_wb:
  wb_frame cenv es0 es sf s0 s /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [q] /\
  not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (p,32 + sz) /\
  sf.cs_next_id <= inst.inst_id /\ local_ptrs_reserved cenv sf /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes ==>
  wb_frame cenv es0 es sf s0 (mcopy (p + 32) src sz s)
Proof
  strip_tac >> simp[mcopy_def] >> irule raw_call_outbuf_wb_frame >>
  simp[read_memory_def, LENGTH_TAKE_EQ, LENGTH_DROP] >>
  goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >> simp[] >>
  goal_assum (drule_at (Pat `MEM _ (fn_insts _)`)) >> simp[] >>
  goal_assum (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >> simp[]
QED

Theorem raw_call_tuple_copy_restored[local]:
  stmt_state_rel ctx func cenv cx es (s with vs_fmp := saved) /\
  wb_frame cenv es0 es sf s0 s /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (p,32 + sz) /\
  sf.cs_next_id <= inst.inst_id /\ local_ptrs_reserved cenv sf /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  mem_word_at p s.vs_memory = (if success then 1w else 0w) /\
  val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) src s.vs_memory /\
  val_wf (BaseTV (BytesT (Dynamic n))) (BytesV bs) /\
  type_memory_size (BaseTV (BytesT (Dynamic n))) <= sz ==>
  stmt_state_rel ctx func cenv cx es
    ((mcopy (p + 32) src sz s) with vs_fmp := saved) /\
  wb_frame cenv es0 es sf s0 ((mcopy (p + 32) src sz s) with vs_fmp := saved) /\
  val_in_memory (TupleTV [BaseTV BoolT; BaseTV (BytesT (Dynamic n))])
    (ArrayV (TupleV [BoolV success; BytesV bs])) p
    (mcopy (p + 32) src sz s).vs_memory
Proof
  strip_tac >>
  `mcopy (p + 32) src sz (s with vs_fmp := saved) =
     (mcopy (p + 32) src sz s) with vs_fmp := saved` by
    simp[mcopy_def, read_memory_def, write_memory_with_expansion_def] >>
  `FLOOKUP (s with vs_fmp := saved).vs_allocas inst.inst_id = SOME (p,32 + sz)` by simp[] >>
  `mem_word_at p (s with vs_fmp := saved).vs_memory = (if success then 1w else 0w)` by simp[] >>
  `val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) src
      (s with vs_fmp := saved).vs_memory` by simp[] >>
  drule_all raw_call_tuple_copy_frame >> strip_tac >>
  `wb_frame cenv es0 es sf s0 (s with vs_fmp := saved)` by simp[raw_call_wb_frame_fmp] >>
  drule_all raw_call_tuple_copy_wb >> disch_then (qspec_then `src` mp_tac) >> gvs[]
QED

Theorem raw_call_tuple_tail_ready[local]:
  emit_op ADD [pop;Lit 32w] sa = (dst,sb) /\
  emit_void MCOPY [dst;src;Lit (n2w sz)] sb = ((),sc) /\
  emit_void SETFMP [dop] sc = ((),sd) /\
  safe_operand sa pop /\ safe_operand sa src /\ safe_operand sa dop /\
  eval_operand pop s = SOME w /\ eval_operand src s = SOME a /\
  eval_operand dop s = SOME saved /\ sz < dimword (:256) /\
  w2n w + (32 + sz) < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es (s with vs_fmp := saved) /\
  wb_frame cenv es0 es sf s0 s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ sf.cs_next_var <= sa.cs_next_var /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w,32 + sz) /\
  sf.cs_next_id <= inst.inst_id /\ local_ptrs_reserved cenv sf /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  mem_word_at (w2n w) s.vs_memory = (if success then 1w else 0w) /\
  val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) (w2n a) s.vs_memory /\
  val_wf (BaseTV (BytesT (Dynamic n))) (BytesV bs) /\
  type_memory_size (BaseTV (BytesT (Dynamic n))) <= sz ==>
  ?t. run_inst_seq (emitted_insts sa sd) s = OK t /\
    stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es0 es sf s0 t /\
    t.vs_fmp = saved /\ eval_operand pop t = SOME w /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (w2n w,32 + sz) /\
    val_in_memory (TupleTV [BaseTV BoolT; BaseTV (BytesT (Dynamic n))])
      (ArrayV (TupleV [BoolV success; BytesV bs])) (w2n w) t.vs_memory /\
    (!p. safe_operand sa p ==> eval_operand p t = eval_operand p s)
Proof
  strip_tac >> drule_all raw_call_tuple_copy_restore_run >> strip_tac >>
  `w2n (w + 32w) = w2n w + 32` by
    (irule buffer_offset_no_wrap >> qexists_tac `32 + sz` >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es (u with vs_fmp := saved)` by
    (qpat_assum `u = _` SUBST1_TAC >>
     `(s with vs_vars := vars) with vs_fmp := saved =
        (s with vs_fmp := saved) with vs_vars := vars` by simp[] >>
     pop_assum SUBST1_TAC >> irule raw_call_reserved_vars_frame >> simp[] >>
     qexists_tac `sa` >> simp[] >> rpt strip_tac >>
     qpat_x_assum `!p. safe_operand sa p ==> _` drule >>
     Cases_on `p` >> gvs[eval_operand_def, lookup_var_def,
       mcopy_def, write_memory_with_expansion_def]) >>
  `wb_frame cenv es0 es sf s0 u` by
    (`wb_frame cenv es0 es sf s0 (u with vs_fmp := saved)` suffices_by
       simp[raw_call_wb_frame_fmp] >>
     irule raw_call_vars_restore_wb_frame >>
     qexistsl_tac [`s`, `sa`] >> simp[] >> metis_tac[]) >>
  `u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas` by gvs[] >>
  `mem_word_at (w2n w) u.vs_memory = (if success then 1w else 0w)` by simp[] >>
  `val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) (w2n a) u.vs_memory` by simp[] >>
  `FLOOKUP u.vs_allocas inst.inst_id = SOME (w2n w,32 + sz)` by simp[] >>
  drule_all raw_call_tuple_copy_restored >> strip_tac >>
  qexists_tac `t` >> simp[] >>
  gvs[mcopy_def, write_memory_with_expansion_def]
QED

Theorem raw_call_tuple_tail_code[local]:
  emit_op ADD [pop;Lit 32w] sa = (dst,sb) /\
  emit_void MCOPY [dst;src;Lit (n2w sz)] sb = ((),sc) /\
  emit_void SETFMP [dop] sc = ((),sd) ==>
  sd.cs_blocks = sa.cs_blocks /\ sd.cs_current_bb = sa.cs_current_bb /\
  isPREFIX sa.cs_current_insts sd.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sd)
Proof
  rpt strip_tac >>
  gvs[emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  simp[rich_listTheory.IS_PREFIX_APPEND, emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[mk_inst_def, is_terminator_def]
QED


Theorem raw_call_tuple_build_run[local]:
  compile_alloc_buffer (32 + sz) sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand;ok] sm = ((),sn) /\
  emit_op ADD [buf.buf_operand;Lit 32w] sn = (dst,sb) /\
  emit_void MCOPY [dst;src;Lit (n2w sz)] sb = ((),sc) /\
  emit_void SETFMP [dop] sc = ((),sd) /\
  stmt_state_rel ctx func cenv cx es (s with vs_fmp := saved) /\
  wb_frame cenv es0 es sf s0 s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sf /\
  sf.cs_next_var <= sa.cs_next_var /\ sf.cs_next_id <= sa.cs_next_id /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\ 32 + sz < dimword (:256) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w (32 + sz))]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) /\
  srcid < sa.cs_next_id /\ FLOOKUP s.vs_allocas srcid = SOME (w2n a,len) /\
  val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) (w2n a) s.vs_memory /\
  val_wf (BaseTV (BytesT (Dynamic n))) (BytesV bs) /\
  type_memory_size (BaseTV (BytesT (Dynamic n))) <= len /\
  type_memory_size (BaseTV (BytesT (Dynamic n))) <= sz /\
  safe_operand sa ok /\ safe_operand sa src /\ safe_operand sa dop /\
  eval_operand ok s = SOME (if success then 1w else 0w) /\
  eval_operand src s = SOME a /\ eval_operand dop s = SOME saved ==>
  ?t w. run_inst_seq (emitted_insts sa sd) s = OK t /\
    stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es0 es sf s0 t /\
    t.vs_fmp = saved /\ eval_operand buf.buf_operand t = SOME w /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,32 + sz) /\
    w2n w + (32 + sz) < dimword (:256) /\
    val_in_memory (TupleTV [BaseTV BoolT; BaseTV (BytesT (Dynamic n))])
      (ArrayV (TupleV [BoolV success; BytesV bs])) (w2n w) t.vs_memory /\
    (!p. safe_operand sa p ==> eval_operand p t = eval_operand p s)
Proof
  strip_tac >> drule_all raw_call_tuple_alloc_ready >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sn) s = OK u` >>
  `ci_mono sa sm` by metis_tac[ci_mono_compile_alloc_buffer, SND] >>
  `ci_mono sm sn` by metis_tac[ci_mono_emit_void, SND] >>
  `sa.cs_next_var <= sn.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var` by
    (fs[ci_mono_def] >> decide_tac) >>
  `local_ptrs_reserved cenv sn /\ sf.cs_next_var <= sn.cs_next_var` by
    metis_tac[local_ptrs_reserved_next_var, arithmeticTheory.LESS_EQ_TRANS] >>
  `safe_operand sn buf.buf_operand /\ safe_operand sn src /\ safe_operand sn dop` by
    (fs[safe_operand_def] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `eval_operand src u = SOME a /\ eval_operand dop u = SOME saved` by simp[] >>
  `not_local_ptr cenv es.scopes (STRING #"%" (toString sa.cs_next_var))` by
    (irule fresh_not_local_ptr >> qexists_tac `sa` >> simp[not_fresh_at_def]) >>
  `sz < dimword (:256)` by decide_tac >>
  drule_at (Pat `MEM _ (fn_insts _)`) raw_call_tuple_tail_ready >>
  simp[mk_inst_def] >> disch_then drule >> simp[] >> strip_tac >>
  fs[arithmeticTheory.ADD_COMM] >> first_x_assum drule_all >> strip_tac >>
  qexistsl_tac [`t`, `w`] >> simp[] >> conj_tac
  >- (`inst_extends sa sm` by
        (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
         simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
         pairarg_tac >> strip_tac >> gvs[] >> drule inst_extends_emit_op >> simp[]) >>
      `inst_extends sm sn` by
        (irule inst_extends_emit_void >> goal_assum (drule_at Any)) >>
      `inst_extends sa sn` by
        (irule inst_extends_trans >> qexists_tac `sm` >> simp[]) >>
      `inst_extends sn sb /\ inst_extends sb sc /\ inst_extends sc sd` by
        (rpt conj_tac
         >- (irule inst_extends_emit_op >> goal_assum (drule_at Any)) >>
         irule inst_extends_emit_void >> goal_assum (drule_at Any)) >>
      `inst_extends sn sd` by metis_tac[inst_extends_trans] >>
      irule run_inst_seq_compose_ok >> qexistsl_tac [`u`, `sn`] >> simp[]) >>
  metis_tac[safe_operand_mono]
QED

Theorem raw_call_nonrevert_suffix_code[local]:
  (do result <- (if n > 0 then
       do z <- emit_op RETURNDATASIZE [];
          cmp <- emit_op LT [z;Lit (n2w n)];
          cap <- compile_select cmp z (Lit (n2w n));
          emit_void MSTORE [out_val;cap];
          buf <- compile_alloc_buffer (64 + ((n + 31) DIV 32) * 32);
          emit_void MSTORE [buf.buf_operand;ok];
          dst <- emit_op ADD [buf.buf_operand;Lit 32w];
          emit_void MCOPY [dst;out_val;Lit (n2w (32 + ((n + 31) DIV 32) * 32))];
          return buf.buf_operand od
     else return ok);
     emit_void SETFMP [dp]; return result od) sa = (result,sb) /\ 0 < n ==>
  ?z s1 cmp s2 cap s3 s4 buf s5 s6 dst s7 s8.
    emit_op RETURNDATASIZE [] sa = (z,s1) /\
    emit_op LT [z;Lit (n2w n)] s1 = (cmp,s2) /\
    compile_select cmp z (Lit (n2w n)) s2 = (cap,s3) /\
    emit_void MSTORE [out_val;cap] s3 = ((),s4) /\
    compile_alloc_buffer (64 + ((n + 31) DIV 32) * 32) s4 = (buf,s5) /\
    emit_void MSTORE [buf.buf_operand;ok] s5 = ((),s6) /\
    emit_op ADD [buf.buf_operand;Lit 32w] s6 = (dst,s7) /\
    emit_void MCOPY [dst;out_val;Lit (n2w (32 + ((n + 31) DIV 32) * 32))]
      s7 = ((),s8) /\ emit_void SETFMP [dp] s8 = ((),sb) /\
    result = buf.buf_operand /\ ci_mono sa s4 /\ inst_extends sa s4 /\
    inst_extends s4 sb /\ s4.cs_next_id < sb.cs_next_id /\
    MEM (mk_inst s4.cs_next_id ALLOCA
      [Lit (n2w (64 + ((n + 31) DIV 32) * 32))]
      [STRING #"%" (toString s4.cs_next_var)]) (emitted_insts sa sb) /\
    sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
    isPREFIX sa.cs_current_insts sb.cs_current_insts /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb)
Proof
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  gvs[builtinSimpleTheory.compile_select_def, compile_alloc_buffer_def,
      emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  simp[ci_mono_def, inst_extends_def, emitted_insts_def,
       rich_listTheory.IS_PREFIX_APPEND] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[mk_inst_def, is_terminator_def, cs_extends_def, same_blocks_def,
       rich_listTheory.IS_PREFIX_APPEND, rich_listTheory.DROP_APPEND]
QED

Theorem raw_call_nonrevert_suffix_frag[local]:
  (do result <- (if n > 0 then
       do z <- emit_op RETURNDATASIZE [];
          cmp <- emit_op LT [z;Lit (n2w n)];
          cap <- compile_select cmp z (Lit (n2w n));
          emit_void MSTORE [out_val;cap];
          buf <- compile_alloc_buffer (64 + ((n + 31) DIV 32) * 32);
          emit_void MSTORE [buf.buf_operand;ok];
          dst <- emit_op ADD [buf.buf_operand;Lit 32w];
          emit_void MCOPY [dst;out_val;Lit (n2w (32 + ((n + 31) DIV 32) * 32))];
          return buf.buf_operand od
     else return ok);
     emit_void SETFMP [dp]; return result od) sa = (result,sb) /\
  raw_call_buffer_frame ctx func cenv cx es0 es sf s0 saved ai w n s /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  MEM alloc (fn_insts func) /\ alloc.inst_opcode = ALLOCA /\
  alloc.inst_outputs = [q] /\ alloc.inst_id = ai /\ not_local_ptr cenv es.scopes q /\
  local_ptrs_reserved cenv sf /\ local_ptrs_reserved cenv sa /\
  sf.cs_next_var <= sa.cs_next_var /\ sf.cs_next_id <= ai /\ ai < sa.cs_next_id /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  safe_operand sa out_val /\ safe_operand sa ok /\ safe_operand sa dp /\
  eval_operand out_val s = SOME w /\ eval_operand ok s = SOME (if success then 1w else 0w) /\
  eval_operand dp s = SOME saved /\ LENGTH s.vs_returndata < dimword (:256) /\
  (0 < n ==> mem_bytes_at (w2n w + 32) (LENGTH (TAKE n s.vs_returndata))
    s.vs_memory = TAKE n s.vs_returndata) /\
  64 + ((n + 31) DIV 32) * 32 < dimword (:256) /\ n < dimword (:256) /\
  ~flags.rcf_revert_on_failure /\ flags.rcf_max_outsize = n ==>
  frag_path ctx sa sb (\u. u = s)
    (\t. stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es0 es sf s0 t /\
      t.vs_fmp = saved /\
      (!p. safe_operand sa p ==> eval_operand p t = eval_operand p s) /\
      expr_val_rel cx (raw_call_return_type flags)
        (if n = 0 then BoolV success else
          ArrayV (TupleV [BoolV success; BytesV (TAKE n s.vs_returndata)])) result t /\
      (0 < n ==> ?ti tw. sf.cs_next_id <= ti /\ ti < sb.cs_next_id /\
        eval_operand result t = SOME tw /\
        FLOOKUP t.vs_allocas ti = SOME (w2n tw,64 + ((n + 31) DIV 32) * 32) /\
        w2n tw + (64 + ((n + 31) DIV 32) * 32) < dimword (:256) /\
        val_in_memory (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))])
          (ArrayV (TupleV [BoolV success;BytesV (TAKE n s.vs_returndata)]))
          (w2n tw) t.vs_memory /\
        (!k lb lsz. local_region cenv es.scopes t k lb lsz ==>
          w2n tw + (64 + ((n + 31) DIV 32) * 32) <= lb \/
          lb + lsz <= w2n tw))) (\r. F)
Proof
  strip_tac >> Cases_on `n = 0`
  >- (gvs[comp_bind_def, comp_ignore_bind_def, comp_return_def,
          raw_call_buffer_frame_def] >>
      pairarg_tac >> gvs[] >>
      rename1 `emit_void SETFMP [dp] sa = (unit,sb)` >>
      Cases_on `unit` >> gvs[] >>
      drule_all raw_call_bool_restore_frag >> strip_tac >>
      irule frag_path_conseq >> goal_assum (drule_at (Pat `frag_path _ _ _ _ _ _`)) >>
      simp[NoAsms] >> rpt strip_tac >> simp[]) >>
  suspend "positive"
QED

Resume raw_call_nonrevert_suffix_frag[positive]:
  `0 < n` by decide_tac >> drule_all raw_call_nonrevert_suffix_code >> strip_tac >>
  gvs[raw_call_buffer_frame_def] >>
  qpat_x_assum `do _ <- _; _ od sa = _` kall_tac >>
  drule_at (Pat `MEM _ (fn_insts _)`) raw_call_output_prefix_ready >>
  simp[] >> disch_then drule >> simp[] >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >> simp[] >>
  disch_then drule_all >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa s4) s = OK u` >>
  `local_ptrs_reserved cenv s4 /\ sf.cs_next_var <= s4.cs_next_var /\
   sf.cs_next_id <= s4.cs_next_id /\ alloc.inst_id < s4.cs_next_id /\
   safe_operand s4 ok /\ safe_operand s4 out_val /\ safe_operand s4 dp` by
    (fs[ci_mono_def] >> metis_tac[local_ptrs_reserved_next_var,
       safe_operand_mono, arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  `MEM (mk_inst s4.cs_next_id ALLOCA
     [Lit (n2w (64 + ((flags.rcf_max_outsize + 31) DIV 32) * 32))]
     [STRING #"%" (toString s4.cs_next_var)]) (fn_insts func)` by
    (irule hash_emitted_inst_mem >> goal_assum (drule_at Any) >> simp[]) >>
  `eval_operand ok u = SOME (if success then 1w else 0w) /\
   eval_operand out_val u = SOME w /\ eval_operand dp u = SOME saved` by metis_tac[] >>
  `FLOOKUP u.vs_allocas alloc.inst_id =
     SOME (w2n w,32 + ((flags.rcf_max_outsize + 31) DIV 32) * 32)` by simp[] >>
  `val_wf (BaseTV (BytesT (Dynamic flags.rcf_max_outsize)))
     (BytesV (TAKE flags.rcf_max_outsize s.vs_returndata))` by
    (irule (cj 1 valueEncodingTypingTheory.value_has_type_val_wf) >>
     simp[value_has_type_def, LENGTH_TAKE_EQ]) >>
  suspend "tuple_build"
QED

Resume raw_call_nonrevert_suffix_frag[tuple_build]:
  `compile_alloc_buffer (64 + ((flags.rcf_max_outsize + 31) DIV 32) * 32)
     s4 = (buf,s5)` by simp[] >>
  `emit_void MCOPY [dst;out_val;
      Lit (n2w (32 + ((flags.rcf_max_outsize + 31) DIV 32) * 32))]
     s7 = ((),s8)` by simp[] >>
  drule_at (Pat `MEM _ (fn_insts _)`)
    (raw_call_tuple_build_run |> SPEC_ALL |> Q.INST
      [`sz` |-> `32 + ((flags.rcf_max_outsize + 31) DIV 32) * 32`]
      |> SRULE [arithmeticTheory.ADD_ASSOC]) >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then drule >> disch_then drule >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  simp[NoAsms, type_memory_size_def, vfmConstantsTheory.word_size_def] >>
  disch_then drule_all >> strip_tac >>
  `run_inst_seq (emitted_insts sa sb) s = OK t` by
    (irule run_inst_seq_compose_ok >> qexistsl_tac [`u`, `s4`] >> simp[]) >>
  `expr_val_rel cx (raw_call_return_type flags)
     (ArrayV (TupleV [BoolV success;BytesV (TAKE flags.rcf_max_outsize s.vs_returndata)]))
     buf.buf_operand t` by
    (simp[expr_val_rel_def, raw_call_return_type_def, is_word_type_def,
          evaluate_type_def] >> rpt strip_tac >> gvs[AllCaseEqs()]) >>
  `!p. safe_operand sa p ==> eval_operand p t = eval_operand p s` by
    (rpt strip_tac >>
     `safe_operand s4 p` by (irule safe_operand_mono >> qexists_tac `sa` >> fs[ci_mono_def]) >>
     metis_tac[]) >>
  suspend "fragment_post"
QED

Resume raw_call_nonrevert_suffix_frag[fragment_post]:
  irule frag_path_run_inst_seq >> simp[] >> rpt strip_tac >>
  simp[stmt_state_rel_inst_idx, raw_call_wb_frame_inst_idx,
       hash_eval_operand_inst_idx]
  >- (qpat_x_assum `expr_val_rel _ _ _ _ t` mp_tac >>
      simp[expr_val_rel_def, hash_eval_operand_inst_idx]) >>
  qexists_tac `s4.cs_next_id` >> simp[] >>
  rpt strip_tac >>
  `not_local_ptr cenv es.scopes (STRING #"%" (toString s4.cs_next_var))` by
    (irule local_ptrs_reserved_fresh >> qexists_tac `s4` >>
     simp[fresh_var_def, comp_return_def]) >>
  `local_region cenv es.scopes t k lb lsz` by
    fs[local_region_def, lookup_var_def] >>
  irule alloca_clear_of_locals >>
  goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `MEM _ (fn_insts _)`)) >>
  simp[mk_inst_def] >> goal_assum (drule_at Any) >> simp[]
QED

Finalise raw_call_nonrevert_suffix_frag

Theorem calldata_call_source_outcome[local]:
  expr_body_pre cenv cx env (Call ann (RawCallCalldataTarget flags) (addr::kws) NONE) es /\
  typed_args_ready ctx func cenv cx expr_type (expr_sim_inv cenv cx env) (addr::kws) /\
  eval_exprs cx (addr::kws) es = (INL vs,es1) /\
  typed_args_post ctx func cenv cx es sa s0 es1 (addr::kws) (aop::ops) vs entry /\
  eval_expr cx (Call ann (RawCallCalldataTarget flags) (addr::kws) NONE) es = (res,es2) ==>
  ?aw amount rq outcome consumed.
    eval_operand aop entry = SOME aw /\ amount < dimword (:256) /\
    (flags.rcf_is_static ==> amount = 0) /\
    eval_operand (case ext_call_kwarg EKValue flags.rcf_kws ops of
      NONE => Lit 0w | SOME p => p) entry = SOME (n2w amount) /\
    take_call_outcome (w2w aw) cx.txn.calldata
      (if flags.rcf_is_static then NONE else SOME amount) es1 =
      (INL (rq,outcome),consumed) /\
    adopt_call_outcome rq outcome consumed = (INL (),es2) /\
    res = (if flags.rcf_revert_on_failure /\ ~outcome.co_success then
      INR (Error (RevertData outcome.co_returnData))
      else INL (Value (if flags.rcf_revert_on_failure then
        if flags.rcf_max_outsize = 0 then NoneV
        else BytesV (TAKE flags.rcf_max_outsize outcome.co_returnData)
      else if flags.rcf_max_outsize = 0 then BoolV outcome.co_success
      else ArrayV (TupleV [BoolV outcome.co_success;
        BytesV (TAKE flags.rcf_max_outsize outcome.co_returnData)]))))
Proof
  strip_tac >> drule_all calldata_call_source_args >> strip_tac >>
  `IS_SOME es1.outcomes /\ outcomes_accounts_typed es1.outcomes /\
    accounts_runtime_well_typed es1.accounts` by
    fs[expr_sim_inv_def,
      vyperTypeExtCallCoreTheory.accounts_runtime_well_typed_accounts_well_typed] >>
  drule_all raw_call_typed_outcome >>
  disch_then (qspecl_then [`w2w aw`,`cx.txn.calldata`,
    `if flags.rcf_is_static then NONE else SOME amount`] strip_assume_tac) >>
  `?adopted. adopt_call_outcome rq outcome es1' = (INL (),adopted)` by
    simp[adopt_call_outcome_equation] >>
  `~cx.txn.is_static` by
    fs[typed_args_post_def, stmt_state_rel_def, state_rel_def] >>
  drule calldata_call_pre >> strip_tac >> gvs[] >>
  drule_all raw_call_oracle_result >>
  disch_then (qspecl_then [
    `forwarded_gas default_evm_gas_limit (ext_call_kwarg EKGas flags.rcf_kws vals)`] mp_tac) >>
  Cases_on `flags.rcf_revert_on_failure` >> Cases_on `outcome.co_success` >>
  gvs[] >> strip_tac >> gvs[] >>
  qexistsl_tac [`amount`,`rq`,`outcome`,`es1'`] >> simp[]
QED

Theorem calldata_take_outcome_bound[local]:
  EVERY (\oc. LENGTH oc.co_returnData < dimword(:256)) os /\
  take_outcome rq os = (oc,rest) ==>
  LENGTH oc.co_returnData < dimword(:256)
Proof
  strip_tac >> Cases_on `os`
  >- gvs[extCallOracleTheory.take_outcome_def, extCallOracleTheory.failed_outcome_def] >>
  Cases_on `computed_precompile rq`
  >- (gvs[extCallOracleTheory.take_outcome_def] >>
      Cases_on `precompile_result rq.cr_target rq.cr_data`
      >- gvs[extCallOracleTheory.failed_outcome_def] >>
      rename1 `_ = SOME result` >> Cases_on `result`
      >- gvs[extCallOracleTheory.failed_outcome_def] >>
      gvs[AllCaseEqs(), extCallOracleTheory.failed_outcome_def] >>
      drule precompile_result_length >> simp[wordsTheory.dimword_def]) >>
  gvs[extCallOracleTheory.take_outcome_def]
QED

Theorem calldata_take_call_outcome_bound:
  outcomes_accounts_typed es.outcomes /\
  take_call_outcome target data amount es = (INL (rq,oc),consumed) ==>
  LENGTH oc.co_returnData < dimword(:256)
Proof
  Cases_on `es.outcomes` >>
  simp[vyperCallOutcomeTheory.take_call_outcome_def, vyperCallOutcomeTheory.take_request_outcome_def] >>
  pairarg_tac >> simp[] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  irule calldata_take_outcome_bound >>
  goal_assum (drule_at Any) >>
  gvs[outcomes_accounts_typed_def, EVERY_MEM]
QED

Theorem calldata_call_returndata_bound[local]:
  expr_sim_inv cenv cx env es /\
  take_call_outcome target data amount es = (INL (rq,oc),consumed) ==>
  LENGTH oc.co_returnData < dimword(:256)
Proof
  strip_tac >> irule calldata_take_call_outcome_bound >>
  goal_assum (drule_at Any) >> fs[expr_sim_inv_def]
QED

Theorem calldata_call_gas[local]:
  expr_body_pre cenv cx env (Call ann (RawCallCalldataTarget flags) (addr::kws) NONE) es /\
  typed_args_ready ctx func cenv cx expr_type (expr_sim_inv cenv cx env) (addr::kws) /\
  eval_exprs cx (addr::kws) es = (INL vs,es1) /\
  typed_args_post ctx func cenv cx es sa s0 es1 (addr::kws) (aop::ops) vs entry ==>
  ?gw. (case ext_call_kwarg EKGas flags.rcf_kws ops of
    NONE => SOME (HD (entry.vs_gas_readings ++ [0w]))
  | SOME p => eval_operand p entry) = SOME gw
Proof
  strip_tac >> drule_all calldata_call_args_values >> strip_tac >>
  drule calldata_call_pre >> strip_tac >> gvs[] >>
  `EVERY (\e. expr_type e = BaseT (UintT 256)) kws` by
    (irule raw_call_kw_types >> qexists_tac `flags.rcf_kws` >>
     gvs[raw_call_kws_ok_def]) >>
  gvs[typed_args_post_def, evaluate_type_def] >>
  drule_all calldata_kwarg_words >> strip_tac >>
  drule (calldata_kwarg_rel |> INST_TYPE [alpha |-> ``:ext_call_kw``]
    |> Q.INST [`k` |-> `EKGas`]) >>
  disch_then (qspec_then `flags.rcf_kws` mp_tac) >>
  rename1 `LIST_REL _ vals ops` >>
  Cases_on `ext_call_kwarg EKGas flags.rcf_kws vals` >> simp[] >>
  strip_tac >> gvs[]
QED




Theorem calldata_call_prepare_fragment[local]:
  expr_body_pre cenv cx env
    (Call ann (RawCallCalldataTarget flags) (addr::kws) NONE) es /\
  eval_exprs cx (addr::kws) es = (INL vs,es1) /\
  typed_args_post ctx func cenv cx es sa s0 es1 (addr::kws) (aop::ops) vs entry /\
  local_ptrs_reserved cenv sa /\ fn_inst_ids_distinct func /\
  fn_has_code sa sb func /\ cs_extends sa sp /\ cs_extends sc sb /\
  sa.cs_next_var <= sp.cs_next_var /\ sa.cs_next_id <= sp.cs_next_id /\
  EVERY (safe_operand sp) ops /\
  (case ext_call_kwarg EKGas flags.rcf_kws ops of
    NONE => emit_op GAS [] sp | SOME g => (g,sp)) = (gop,sg) /\
  compile_raw_call_outbuf flags.rcf_max_outsize sg = ((ov,op),so) /\
  compile_msg_data_to_memory so = ((dp,dl),sc) ==>
  frag_path ctx sp sc (\s. s = entry)
    (\t. calldata_prepared ctx func cenv cx es es1 sa s0 entry sp sg
       flags.rcf_max_outsize ov op dp dl t /\
      eval_operand gop t =
        (case ext_call_kwarg EKGas flags.rcf_kws ops of
         SOME g => eval_operand g entry | NONE => SOME (HD (entry.vs_gas_readings ++ [0w])))) R
Proof
  strip_tac >> drule calldata_gas_code >> strip_tac >>
  `ci_mono sg so` by metis_tac[ci_mono_compile_raw_call_outbuf, pairTheory.SND] >>
  `ci_mono so sc` by metis_tac[ci_mono_compile_msg_data_to_memory, pairTheory.SND] >>
  `fn_has_code sg sc func` by
    (irule fn_has_code_mid >>
     conj_tac >- (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
     qexistsl_tac [`sb`,`sa`] >> fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  drule_all calldata_prepare_members >> strip_tac >>
  `calldata_prepare_pre ctx func cenv cx es es1 sa s0 sp sg
    flags.rcf_max_outsize (ext_call_kwarg EKGas flags.rcf_kws ops) entry` by
    (irule calldata_call_prepare_pre >> simp[] >>
     goal_assum (drule_at (Pat `typed_args_post _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `expr_body_pre _ _ _ _ _`)) >> simp[]) >>
  irule frag_path_conseq >> irule_at (Pat `frag_path _ _ _ _ _ _`) calldata_prepare_frag >>
  goal_assum (drule_at (Pat `compile_raw_call_outbuf _ _ = _`)) >>
  goal_assum (drule_at (Pat `compile_msg_data_to_memory _ = _`)) >> simp[] >>
  goal_assum (drule_at (Pat `calldata_prepare_pre _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  qexistsl_tac [`gop`,`R`] >> simp[]
QED

Theorem raw_call_value_vv_post[local]:
  n < dimword (:256) /\ flags.rcf_max_outsize = n /\
  post_value_type cenv e = expr_type e /\
  expr_type e = raw_call_return_type flags /\
  v = (if flags.rcf_revert_on_failure then
    if n = 0 then NoneV else BytesV (TAKE n data)
    else if n = 0 then BoolV success
    else ArrayV (TupleV [BoolV success;BytesV (TAKE n data)])) /\
  stmt_state_rel ctx func cenv cx es1 s /\ wb_frame cenv es es1 sa s0 s /\
  (if n = 0 then eval_operand result s =
      SOME (if flags.rcf_revert_on_failure then 0w else if success then 1w else 0w)
   else eval_operand result s = SOME w /\
     val_in_memory (if flags.rcf_revert_on_failure then BaseTV (BytesT (Dynamic n))
       else TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))]) v
       (w2n w) s.vs_memory /\
     FLOOKUP s.vs_allocas aid = SOME (w2n w, ((n+31) DIV 32)*32 +
       (if flags.rcf_revert_on_failure then 32 else 64)) /\
     sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
     (!k lb lsz. local_region cenv es1.scopes s k lb lsz ==>
       w2n w + (((n+31) DIV 32)*32 +
         (if flags.rcf_revert_on_failure then 32 else 64)) <= lb \/
       lb + lsz <= w2n w)) ==>
  vv_post ctx func cenv cx e es sa sb s0 es1 (Value v)
    (if n = 0 then StackValue (expr_type e) result
     else LocatedValue (expr_type e) (mk_ptr result LocMemory)) s
Proof
  strip_tac >> Cases_on `n = 0`
  >- (gvs[] >> irule vv_post_frame_intro >>
      Cases_on `flags.rcf_revert_on_failure` >>
      simp[raw_call_return_type_def, vv_holds_def, vv_at_def,
        expr_val_rel_def, expr_val_at_def, read_result_def, return_def,
        evaluate_type_def, is_word_type_def, typed_val_to_w256_def,
        val_to_w256_def, val_in_memory_def, val_wf_def, val_footprint_def, type_memory_size_def]) >>
  `LENGTH (TAKE n data) <= 32 * ((n+31) DIV 32)` by
    (qspec_then `n` mp_tac le_word_size_mul >>
     simp[vfmConstantsTheory.word_size_def, listTheory.LENGTH_TAKE_EQ,
       arithmeticTheory.MIN_DEF] >> decide_tac) >>
  gvs[] >>
  qpat_assum `expr_type e = _` (fn th => pure_once_rewrite_tac [GSYM th]) >>
  irule vv_post_allocated_memory_intro >>
  Cases_on `flags.rcf_revert_on_failure` >>
  simp[raw_call_return_type_def, is_word_type_def, evaluate_type_def, mk_ptr_def] >>
  qexistsl_tac [`aid`,`w2n w`,
    `32 * ((flags.rcf_max_outsize+31) DIV 32) +
      (if flags.rcf_revert_on_failure then 32 else 64)`] >>
  gvs[] >> simp[val_footprint_def, val_wf_def, type_memory_size_def,
    vfmConstantsTheory.word_size_def,
    vyperTypeExtCallSoundnessTheory.raw_call_bytes_slot_size_bound] >>
  metis_tac[]
QED

Theorem raw_call_finish_vv_frag[local]:
  compile_raw_call_finish aop dp dl gop vop call_ty n flags.rcf_revert_on_failure ov op sc = (result,se) /\
  emit_void SETFMP [dp] se = ((),sb) /\
  (call_ty = StaticCall \/ call_ty = RegularCall) /\
  raw_call_buffer_frame ctx func cenv cx es0 es_in sf s0 saved ai w n s /\
  fn_inst_ids_distinct func /\ MEM alloc (fn_insts func) /\
  alloc.inst_opcode = ALLOCA /\ alloc.inst_outputs = [q] /\ alloc.inst_id = ai /\
  not_local_ptr cenv es_in.scopes q /\ sf.cs_next_id <= ai /\
  local_ptrs_reserved cenv sf /\ local_ptrs_reserved cenv sc /\
  sf.cs_next_var <= sc.cs_next_var /\ MAP FDOM es0.scopes = MAP FDOM es_in.scopes /\
  safe_operand sc ov /\ safe_operand sc dp /\
  eval_operand ov s = SOME w /\ eval_operand dp s = SOME saved /\
  eval_operand op s = SOME (if n = 0 then w else w + 32w) /\
  eval_operand gop s = SOME gas /\ eval_operand aop s = SOME aw /\
  eval_operand vop s = SOME vw /\ eval_operand dl s = SOME iz /\
  take_call_outcome (w2w aw) (read_memory (w2n saved) (w2n iz) s)
    (if call_ty = StaticCall then NONE else SOME (w2n vw)) es_in =
      (INL (rq,outcome),es_consumed) /\
  n < dimword (:256) /\ LENGTH outcome.co_returnData < dimword (:256) /\
  (flags.rcf_revert_on_failure /\ ~outcome.co_success ==>
    !t. t.vs_returndata = outcome.co_returnData ==> R (Abort Revert_abort t)) /\
  post_value_type cenv e = expr_type e /\
  expr_type e = raw_call_return_type flags /\ flags.rcf_max_outsize = n /\
  fn_has_code sc sb func /\ ai < sc.cs_next_id /\
  64 + ((n+31) DIV 32)*32 < dimword (:256) /\ ai < sb.cs_next_id ==>
  frag_path ctx sc sb (\u. u=s)
    (\u. (flags.rcf_revert_on_failure ==> outcome.co_success) /\
      vv_post ctx func cenv cx e es0 sf sb s0
        (SND (adopt_call_outcome rq outcome es_consumed))
        (Value (if flags.rcf_revert_on_failure then
           if n=0 then NoneV else BytesV (TAKE n outcome.co_returnData)
         else if n=0 then BoolV outcome.co_success
         else ArrayV (TupleV [BoolV outcome.co_success;BytesV (TAKE n outcome.co_returnData)])))
        (if n=0 then StackValue (expr_type e) result
         else LocatedValue (expr_type e) (mk_ptr result LocMemory)) u) R
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `flags.rcf_revert_on_failure`
  >- suspend "reverting" >>
  suspend "nonreverting"
QED

Resume raw_call_finish_vv_frag[reverting]:
  `compile_raw_call_finish aop dp dl gop vop call_ty n T ov op sc = (result,se)` by
    (qpat_x_assum `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >> simp[]) >>
  `~outcome.co_success ==> !t. t.vs_returndata = outcome.co_returnData ==>
    R (Abort Revert_abort t)` by simp[] >>
  drule_all raw_call_finish_success_allocas_frag >> strip_tac >>
  drule raw_call_take_adopt_fields >> strip_tac >>
  irule frag_path_conseq >>
  goal_assum (drule_at (Pat `frag_path _ _ _ _ _ _`)) >>
  simp[NoAsms] >> gen_tac >> strip_tac >>
  qpat_x_assum `frag_path _ _ _ _ _ _` kall_tac >>
  irule raw_call_value_vv_post >> simp[] >>
  qexistsl_tac [`ai`,`outcome.co_returnData`,`flags`,`outcome.co_success`,`w`] >>
  simp[] >> Cases_on `flags.rcf_max_outsize = 0` >> gvs[] >>
  rpt strip_tac >> irule alloca_clear_of_locals >>
  goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `MEM _ (fn_insts _)`)) >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Resume raw_call_finish_vv_frag[nonreverting]:
  `compile_raw_call_finish aop dp dl gop vop call_ty n F ov op sc = (result,se)` by
    (qpat_x_assum `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >> simp[]) >>
  drule raw_call_finish_nonrevert_compile >> strip_tac >>
  `emit_op (if call_ty = StaticCall then STATICCALL else CALL)
    (if call_ty = StaticCall then [gop;aop;dp;dl;op;Lit (n2w n)]
     else [gop;aop;vop;dp;dl;op;Lit (n2w n)]) sc = (success,s1)` by
    (Cases_on `call_ty` >> gvs[]) >>
  drule_all raw_call_oracle_framed_frag >>
  disch_then (qspec_then `R` assume_tac) >>
  `ci_mono sc s1` by metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `ci_mono se sb` by metis_tac[ci_mono_emit_void, pairTheory.SND] >>
  `cs_extends s1 sb` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  drule frag_path_then >> disch_then irule >>
  reverse conj_tac >- fs[ci_mono_def] >>
  qpat_x_assum `frag_path _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `(case call_ty of RegularCall => _ | DelegateCall => _ | StaticCall => _) = _` kall_tac >>
  suspend "suffix"
QED

Resume raw_call_finish_vv_frag[suffix]:
  gen_tac >> simp[] >> strip_tac >>
  drule raw_call_take_adopt_fields >> strip_tac >>
  `fn_has_code s1 sb func` by
    (irule fn_has_code_mid >> simp[] >> qexistsl_tac [`sb`,`sc`] >>
     fs[ci_mono_def] >> simp[cs_extends_refl]) >>
  `local_ptrs_reserved cenv s1 /\ sf.cs_next_var <= s1.cs_next_var /\
   ai < s1.cs_next_id /\ safe_operand s1 ov /\ safe_operand s1 dp` by
    (fs[ci_mono_def] >> metis_tac[local_ptrs_reserved_next_var,
      safe_operand_mono, arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  `safe_operand s1 success` by metis_tac[emit_op_safe_operand] >>
  qmatch_asmsub_abbrev_tac `tail s1 = (result,se)` >>
  `(do r <- tail; emit_void SETFMP [dp]; return r od) s1 = (result,sb)` by
    simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  qunabbrev_tac `tail` >>
  `eval_operand ov t = SOME w /\ eval_operand dp t = SOME saved` by metis_tac[] >>
  `not_local_ptr cenv (SND (adopt_call_outcome rq outcome es_consumed)).scopes q /\
   MAP FDOM es0.scopes = MAP FDOM (SND (adopt_call_outcome rq outcome es_consumed)).scopes` by simp[] >>
  `LENGTH t.vs_returndata < dimword (:256) /\
   (0 < n ==> mem_bytes_at (w2n w + 32) (LENGTH (TAKE n t.vs_returndata))
     t.vs_memory = TAKE n t.vs_returndata)` by simp[] >>
  drule_all raw_call_nonrevert_suffix_frag >> strip_tac >>
  qpat_x_assum `frag_path _ _ _ _ _ _` mp_tac >>
  qpat_x_assum `post_value_type cenv e = expr_type e` mp_tac >>
  qpat_x_assum `expr_type e = _` mp_tac >>
  qpat_x_assum `flags.rcf_max_outsize = n` mp_tac >>
  qpat_x_assum `~flags.rcf_revert_on_failure` mp_tac >>
  qpat_x_assum `n < dimword (:256)` mp_tac >>
  qpat_x_assum `t.vs_returndata = _` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
  suspend "suffix_value"
QED

Resume raw_call_finish_vv_frag[suffix_value]:
  irule frag_path_conseq >>
  goal_assum (drule_at (Pat `frag_path _ _ _ _ _ _`)) >>
  simp[NoAsms] >> gen_tac >> strip_tac >>
  qpat_x_assum `frag_path _ _ _ _ _ _` kall_tac >>
  qpat_assum `expr_type e = _` (fn th => pure_once_rewrite_tac [GSYM th]) >>
  irule raw_call_value_vv_post >> simp[] >>
  Cases_on `n = 0`
  >- (qexistsl_tac [`0`,`outcome.co_returnData`,`flags`,`outcome.co_success`,`0w`] >>
      gvs[raw_call_return_type_def, expr_val_rel_def, typed_val_to_w256_def,
        val_to_w256_def, is_word_type_def, evaluate_type_def]) >>
  `0 < n` by decide_tac >> fs[] >>
  qexistsl_tac [`ti`,`outcome.co_returnData`,`flags`,`outcome.co_success`] >>
  simp[] >> gvs[] >> metis_tac[]
QED

Finalise raw_call_finish_vv_frag

Theorem calldata_outbuf_id_growth[local]:
  compile_raw_call_outbuf n sa = ((ov,op),sb) ==> sa.cs_next_id < sb.cs_next_id
Proof
  Cases_on `n = 0` >>
  simp[compile_raw_call_outbuf_def, compile_alloc_buffer_def,
    comp_bind_def, comp_return_def, comp_ignore_bind_def, emit_op_def, fresh_var_def,
    fresh_id_def, emit_def] >> strip_tac >> gvs[]
QED

Theorem calldata_finish_compile_certificates[local]:
  fn_has_code sa sb func /\ local_ptrs_reserved cenv sa /\ cs_extends sa sp /\
  sa.cs_next_var <= sp.cs_next_var /\ sa.cs_next_id <= sp.cs_next_id /\
  (case go of NONE => emit_op GAS [] sp | SOME g => (g,sp)) = (gop,sg) /\
  compile_raw_call_outbuf n sg = ((ov,op),so) /\
  compile_msg_data_to_memory so = ((dp,dl),sc) /\
  compile_raw_call_finish aop dp dl gop vop call_ty n rof ov op sc = (result,se) /\
  emit_void SETFMP [dp] se = ((),sb) ==>
  MEM (mk_inst sg.cs_next_id ALLOCA
    [Lit (n2w (if n=0 then 0 else ((n+31) DIV 32)*32+32))]
    [STRING #"%" (toString sg.cs_next_var)]) (fn_insts func) /\
  local_ptrs_reserved cenv sg /\ local_ptrs_reserved cenv sc /\
  sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sg.cs_next_id /\
  sg.cs_next_id < sb.cs_next_id /\ safe_operand sc ov /\ safe_operand sc dp /\
  fn_has_code sc sb func /\ sg.cs_next_id < sc.cs_next_id
Proof
  strip_tac >> drule calldata_gas_code >> strip_tac >>
  `ci_mono sg so` by metis_tac[ci_mono_compile_raw_call_outbuf, pairTheory.SND] >>
  `ci_mono so sc` by metis_tac[ci_mono_compile_msg_data_to_memory, pairTheory.SND] >>
  `ci_mono sc se` by metis_tac[ci_mono_compile_raw_call_finish, pairTheory.SND] >>
  `ci_mono se sb` by metis_tac[ci_mono_emit_void, pairTheory.SND] >>
  `fn_has_code sg sc func` by
    (irule fn_has_code_mid >>
     conj_tac >- (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
     qexistsl_tac [`sb`,`sa`] >> fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sc sb func` by
    (irule fn_has_code_mid >>
     conj_tac >- (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
     qexistsl_tac [`sb`,`sa`] >> fs[ci_mono_def] >>
     metis_tac[cs_extends_trans, cs_extends_refl]) >>
  drule_all calldata_prepare_members >> strip_tac >>
  drule calldata_outbuf_id_growth >> disch_tac >>
  drule calldata_outbuf_operands >> strip_tac >>
  `safe_operand sc dp` by
    (qpat_x_assum `compile_msg_data_to_memory _ = _` mp_tac >>
     simp[compile_msg_data_to_memory_def, compile_alloc_dynamic_def,
       comp_bind_def, comp_return_def, comp_ignore_bind_def,
       emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
     strip_tac >> gvs[safe_operand_def, not_fresh_at_def,
       ASCIInumbersTheory.toString_11]) >>
  fs[ci_mono_def] >> rpt conj_tac
  >- (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) 
  >- (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[])
  >- (irule safe_operand_mono >> goal_assum (drule_at Any) >> simp[]) >>
  decide_tac
QED

Theorem calldata_finish_size_bound[local]:
  expr_body_pre cenv cx env
    (Call (raw_call_return_type flags) (RawCallCalldataTarget flags) args dflt) es ==>
  64 + ((flags.rcf_max_outsize + 31) DIV 32)*32 < dimword (:256)
Proof
  strip_tac >>
  `type_alloc_ok cenv (raw_call_return_type flags)` by
    fs[expr_body_pre_def, alloc_limits_expr_def] >>
  Cases_on `flags.rcf_max_outsize = 0` >- simp[wordsTheory.dimword_def] >>
  Cases_on `flags.rcf_revert_on_failure` >>
  gvs[type_alloc_ok_def, raw_call_return_type_def, is_word_type_def,
    type_memory_bytes_def, wordsTheory.dimword_def] >> decide_tac
QED

Theorem calldata_prepared_finish[local]:
  expr_body_pre cenv cx env
    (Call ann (RawCallCalldataTarget flags) (addr::kws) NONE) es /\
  typed_args_ready ctx func cenv cx expr_type (expr_sim_inv cenv cx env) (addr::kws) /\
  eval_exprs cx (addr::kws) es = (INL vs,es1) /\
  typed_args_post ctx func cenv cx es sa s0 es1 (addr::kws) (aop::ops) vs entry /\
  eval_expr cx (Call ann (RawCallCalldataTarget flags) (addr::kws) NONE) es = (res,es2) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  cs_extends sa sp /\ sa.cs_next_var <= sp.cs_next_var /\ sa.cs_next_id <= sp.cs_next_id /\
  EVERY (safe_operand sp) (aop::ops) /\
  (case ext_call_kwarg EKGas flags.rcf_kws ops of
    NONE => emit_op GAS [] sp | SOME g => (g,sp)) = (gop,sg) /\
  compile_raw_call_outbuf flags.rcf_max_outsize sg = ((ov,op),so) /\
  compile_msg_data_to_memory so = ((dp,dl),sc) /\
  compile_raw_call_finish aop dp dl gop
    (case ext_call_kwarg EKValue flags.rcf_kws ops of NONE => Lit 0w | SOME p => p)
    (if flags.rcf_is_static then StaticCall else RegularCall)
    flags.rcf_max_outsize flags.rcf_revert_on_failure ov op sc = (result,se) /\
  emit_void SETFMP [dp] se = ((),sb) /\
  calldata_prepared ctx func cenv cx es es1 sa s0 entry sp sg
    flags.rcf_max_outsize ov op dp dl t /\
  eval_operand gop t = (case ext_call_kwarg EKGas flags.rcf_kws ops of
    NONE => SOME (HD (entry.vs_gas_readings ++ [0w])) | SOME g => eval_operand g entry) ==>
  frag_path ctx sc sb (\s. s = t)
    (\s. ?tv. res = INL tv /\
      vv_post ctx func cenv cx
        (Call ann (RawCallCalldataTarget flags) (addr::kws) NONE)
        es sa sb s0 es2 tv
        (if flags.rcf_max_outsize = 0 then StackValue ann result
         else LocatedValue ann (mk_ptr result LocMemory)) s) (expr_exit res)
Proof
  strip_tac >>
  drule_all calldata_call_args_values >> strip_tac >>
  drule_all calldata_call_source_outcome >> strip_tac >>
  drule_all calldata_call_returndata_bound >> disch_tac >>
  drule_all calldata_call_gas >> strip_tac >>
  drule calldata_prepared_buffer_frame >> strip_tac >>
  drule calldata_call_pre >> strip_tac >> gvs[] >>
  drule calldata_finish_size_bound >> disch_tac >>
  drule_all calldata_finish_compile_certificates >> strip_tac >>
  `not_local_ptr cenv es1.scopes (STRING #"%" (toString sg.cs_next_var))` by
    (irule local_ptrs_reserved_fresh >> qexists_tac `sg` >>
     simp[fresh_var_def, comp_return_def]) >>
  `MAP FDOM es.scopes = MAP FDOM es1.scopes` by
    metis_tac[eval_exprs_preserves_scopes_dom] >>
  `LENGTH cx.txn.calldata < dimword (:256)` by
    fs[expr_sim_inv_def, context_well_typed_def, wordsTheory.dimword_def] >>
  `safe_operand sp (case ext_call_kwarg EKValue flags.rcf_kws ops of
    NONE => Lit 0w | SOME p => p)` by
    (drule (calldata_kwarg_safe |> INST_TYPE [alpha |-> ``:ext_call_kw``]
       |> Q.INST [`k` |-> `EKValue`]) >>
     disch_then (qspec_then `flags.rcf_kws` mp_tac) >>
     Cases_on `ext_call_kwarg EKValue flags.rcf_kws ops` >>
     simp[safe_operand_def]) >>
  `eval_operand aop t = SOME aw /\
   eval_operand (case ext_call_kwarg EKValue flags.rcf_kws ops of
     NONE => Lit 0w | SOME p => p) t = SOME (n2w amount)` by
    (fs[calldata_prepared_def] >> metis_tac[]) >>
  qpat_x_assum `calldata_prepared _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[calldata_prepared_def] >> strip_tac >>
  irule frag_path_conseq >>
  irule_at (Pat `frag_path _ _ _ _ _ _`) raw_call_finish_vv_frag >>
  goal_assum (drule_at (Pat `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_void SETFMP _ _ = _`)) >> simp[] >>
  goal_assum (drule_at (Pat `MEM _ (fn_insts _)`)) >> simp[mk_inst_def] >>
  goal_assum (drule_at (Pat `raw_call_buffer_frame _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> qexistsl_tac [`rq`,`outcome`,`consumed`] >>
  qmatch_goalsub_abbrev_tac `expr_exit source_result` >>
  qexists_tac `Call (raw_call_return_type flags) (RawCallCalldataTarget flags) (addr::kws) NONE` >>
  qexists_tac `expr_exit source_result` >>
  simp[Abbr `source_result`, expr_type_def, raw_call_return_type_def] >>
  Cases_on `flags.rcf_is_static` >> fs[expr_exit_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem calldata_call_success_frag[local]:
  exprs_case nocalls ctx func cenv cx (addr::kws) /\
  (nocalls ==> int_calls_expr
    (Call ann (RawCallCalldataTarget flags) (addr::kws) NONE) = []) /\
  expr_body_pre cenv cx env
    (Call ann (RawCallCalldataTarget flags) (addr::kws) NONE) es /\
  compile_expr cenv ty
    (Call ann (RawCallCalldataTarget flags) (addr::kws) NONE) sa = (vv,sb) /\
  lower_word_args cenv expr_type (addr::kws) sa = (addr_op::ops,sp) /\
  eval_exprs cx (addr::kws) es = (INL vs,es1) /\
  eval_expr cx (Call ann (RawCallCalldataTarget flags) (addr::kws) NONE) es = (res,es2) /\
  expr_vv_res_ok res /\ fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  typed_args_post ctx func cenv cx es sa s0 es1 (addr::kws) (addr_op::ops) vs entry ==>
  frag_path ctx sp sb (\s. s = entry)
    (\s. ?tv. res = INL tv /\
      vv_post ctx func cenv cx
        (Call ann (RawCallCalldataTarget flags) (addr::kws) NONE)
        es sa sb s0 es2 tv vv s) (expr_exit res)
Proof
  strip_tac >> drule calldata_call_pre >> strip_tac >> gvs[] >>
  drule calldata_call_compile >> strip_tac >> gvs[] >>
  drule_all calldata_call_prefix_lower >> strip_tac >> gvs[] >>
  drule_all calldata_call_args_ready >> strip_tac >>
  drule_all lower_word_args_shape_ready >> strip_tac >>
  `ci_mono s5 s6` by metis_tac[ci_mono_compile_raw_call_finish, pairTheory.SND] >>
  `ci_mono s6 sb` by metis_tac[ci_mono_emit_void, pairTheory.SND] >>
  `cs_extends s5 sb` by (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `EVERY (safe_operand s2) ops` by
    (fs[listTheory.EVERY_MEM, safe_operand_def] >>
     rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `frag_path ctx s2 s5 (\s. s = entry)
    (\t. calldata_prepared ctx func cenv cx es es1 sa s0 entry s2 s3
      flags.rcf_max_outsize out_val out_ptr data_ptr data_len t /\
      eval_operand gas_op t =
        (case ext_call_kwarg EKGas flags.rcf_kws ops of
         SOME g => eval_operand g entry | NONE => SOME (HD (entry.vs_gas_readings ++ [0w]))))
    (expr_exit res)` by
    (irule calldata_call_prepare_fragment >> simp[] >>
     rpt conj_tac >> goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  drule frag_path_then >> disch_then irule >>
  reverse conj_tac >-
    (drule_all calldata_prepare_shape >> strip_tac >>
     fs[cs_extends_def, same_blocks_def, rich_listTheory.IS_PREFIX_APPEND]) >>
  qpat_x_assum `frag_path _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `compile_expr _ _ _ _ = _` kall_tac >>
  qpat_x_assum `compile_ext_call_kwargs _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` kall_tac >>
  gen_tac >> disch_then (strip_assume_tac o BETA_RULE) >>
  irule calldata_prepared_finish >>
  simp[] >> conj_tac
  >- (qexists_tac `env` >> simp[]) >>
  goal_assum (drule_at (Pat `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `calldata_prepared _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >> fs[safe_operand_def]
QED

(* ===== The counted composition ===== *)

(* wb_frame and vv_post read the start state's scopes only. *)
Theorem calldata_typed_args_post_gas_obs[local]:
  typed_args_post ctx func cenv cx (es with gas_obs := g) sa s0 es' args xs vs s <=>
  typed_args_post ctx func cenv cx es sa s0 es' args xs vs s
Proof
  simp[typed_args_post_def, wb_frame_def, locals_kept_def, popped_kept_def]
QED

Theorem calldata_vv_post_gas_obs[local]:
  vv_post ctx func cenv cx e (es with gas_obs := g) sa sb s0 es' tv vv s <=>
  vv_post ctx func cenv cx e es sa sb s0 es' tv vv s
Proof
  simp[vv_post_def, locals_kept_def, popped_kept_def]
QED

Theorem calldata_gas_explicit_false[local]:
  !n gs. gas_explicit (REPLICATE n F) gs = []
Proof
  Induct >> gen_tac >> Cases_on `gs` >>
  simp[rich_listTheory.REPLICATE, gas_explicit_cons]
QED

(* In oracle mode raw_call reads no gas observation. *)
Theorem calldata_take_call_outcome_gas_obs[local]:
  !target cd vo st g.
    take_call_outcome target cd vo (st with gas_obs := g) =
      (FST (take_call_outcome target cd vo st),
       SND (take_call_outcome target cd vo st) with gas_obs := g) /\
    (SND (take_call_outcome target cd vo st)).gas_obs = st.gas_obs
Proof
  rpt gen_tac >> simp[take_call_outcome_def, take_request_outcome_def, call_outcome_request_def] >>
  Cases_on `st.outcomes` >> simp[LET_THM, UNCURRY] >> rw[]
QED

Theorem calldata_adopt_call_outcome_gas_obs[local]:
  !rq oc st g.
    adopt_call_outcome rq oc (st with gas_obs := g) =
      (FST (adopt_call_outcome rq oc st),
       SND (adopt_call_outcome rq oc st) with gas_obs := g) /\
    (SND (adopt_call_outcome rq oc st)).gas_obs = st.gas_obs
Proof
  simp[adopt_call_outcome_equation] >> rw[]
QED

Theorem calldata_raw_call_gas_obs:
  !cx flags target data amount gas st g.
    ~cx.txn.is_static /\ ~flags.rcf_is_delegate /\ IS_SOME st.outcomes ==>
    eval_raw_call cx flags target data amount gas (st with gas_obs := g) =
      (FST (eval_raw_call cx flags target data amount gas st),
       SND (eval_raw_call cx flags target data amount gas st) with gas_obs := g) /\
    (SND (eval_raw_call cx flags target data amount gas st)).gas_obs = st.gas_obs
Proof
  rpt gen_tac >> strip_tac >>
  simp[eval_raw_call_def, frame_call_value_def, bind_def, ignore_bind_def,
       type_check_def, assert_def, vyperStateTheory.return_def, raise_def] >>
  IF_CASES_TAC >> simp[raise_def] >>
  qmatch_goalsub_abbrev_tac `take_call_outcome target data vo` >>
  qspecl_then [`target`, `data`, `vo`, `st`, `g`] mp_tac
    calldata_take_call_outcome_gas_obs >>
  Cases_on `take_call_outcome target data vo st` >> rename1 `_ = (q, st1)` >>
  reverse (Cases_on `q`) >> simp[] >> strip_tac >>
  rename1 `INL rqoc` >> PairCases_on `rqoc` >> simp[] >>
  qspecl_then [`rqoc0`, `rqoc1`, `st1`, `g`] mp_tac
    calldata_adopt_call_outcome_gas_obs >>
  Cases_on `adopt_call_outcome rqoc0 rqoc1 st1` >> rename1 `_ = (q2, st2)` >>
  Cases_on `q2` >> simp[] >> strip_tac >>
  rw[vyperStateTheory.return_def, raise_def, bind_def, ignore_bind_def]
QED

Theorem calldata_call_source_gas_obs[local]:
  ~cx.txn.is_static /\ ~flags.rcf_is_delegate /\ IS_SOME mid.outcomes /\
  (!tail. eval_exprs cx args (es with gas_obs := xs ++ tail) =
          (INL vs, mid with gas_obs := tail)) /\
  eval_expr cx (Call ann (RawCallCalldataTarget flags) args dflt)
    (es with gas_obs := xs) = (res, fin) ==>
  fin.gas_obs = [] /\
  !tail. eval_expr cx (Call ann (RawCallCalldataTarget flags) args dflt)
           (es with gas_obs := xs ++ tail) = (res, fin with gas_obs := tail)
Proof
  strip_tac >>
  `eval_exprs cx args (es with gas_obs := xs) = (INL vs, mid with gas_obs := [])` by
    (first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
  simp[calldata_call_action, bind_def, ignore_bind_def, type_check_def,
       assert_def, lift_option_type_def, vyperStateTheory.return_def,
       raise_def] >>
  IF_CASES_TAC >> simp[raise_def] >>
  Cases_on `dest_AddressV (HD vs)` >> simp[raise_def, vyperStateTheory.return_def] >>
  Cases_on `raw_call_value flags.rcf_kws (DROP 1 vs)` >>
  simp[raise_def, vyperStateTheory.return_def] >>
  rpt strip_tac >> gvs[] >>
  qmatch_asmsub_rename_tac
    `eval_raw_call _ _ tg _ am gw (mid with gas_obs := []) = _` >>
  qspecl_then [`cx`, `flags`, `tg`, `cx.txn.calldata`, `am`, `gw`,
    `mid with gas_obs := []`] mp_tac calldata_raw_call_gas_obs >>
  simp[] >> rpt strip_tac >> gvs[]
QED

(* The operands' marked run, then the tail's path, whose only GAS read is
   a target-only one and so takes F marks. *)
Theorem calldata_call_normal[local]:
  exprs_case nocalls ctx func cenv cx (addr::kws) /\
  (nocalls ==> int_calls_expr
    (Call ann (RawCallCalldataTarget flags) (addr::kws) NONE) = []) /\
  expr_body_pre cenv cx env
    (Call ann (RawCallCalldataTarget flags) (addr::kws) NONE) es /\
  compile_expr cenv ty
    (Call ann (RawCallCalldataTarget flags) (addr::kws) NONE) sa = (vv,sb) /\
  lower_word_args cenv expr_type (addr::kws) sa = (addr_op::ops,sp) /\
  fn_has_code sa sb func /\ fn_has_code sp sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  gas_admissible
    (eval_expr cx (Call ann (RawCallCalldataTarget flags) (addr::kws) NONE))
    expr_vv_res_ok es /\
  gas_marked_exec F (ctx,func) (eval_exprs cx (addr::kws)) (es,s0) marks
    (INL vs) es_end (OK entry) /\
  typed_args_post ctx func cenv cx es sa s0 (es_end with gas_obs := [])
    (addr::kws) (addr_op::ops) vs entry /\
  entry.vs_current_bb = sp.cs_current_bb /\
  entry.vs_inst_idx = LENGTH sp.cs_current_insts ==>
  gas_outcome F tops (ctx,func)
    (eval_expr cx (Call ann (RawCallCalldataTarget flags) (addr::kws) NONE))
    (es,s0)
    (\res ee t. ?tv. res = INL tv /\
       vv_post ctx func cenv cx
         (Call ann (RawCallCalldataTarget flags) (addr::kws) NONE)
         es sa sb s0 ee tv vv t /\
       t.vs_current_bb = sb.cs_current_bb /\
       t.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  drule calldata_call_pre >> strip_tac >> gvs[] >>
  qabbrev_tac `xs = gas_explicit marks s0.vs_gas_readings` >>
  `gas_path ctx func s0 (LENGTH marks) (OK entry)` by
    fs[gas_marked_exec_def, gas_marked_path_def] >>
  `~entry.vs_halted` by metis_tac[gas_path_normal] >>
  `!tail. eval_exprs cx (addr::kws) (es with gas_obs := xs ++ tail) =
          (INL vs, es_end with gas_obs := tail)` by
    fs[gas_marked_exec_def, Abbr `xs`] >>
  `eval_exprs cx (addr::kws) (es with gas_obs := xs) =
     (INL vs, es_end with gas_obs := [])` by
    (first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  Cases_on `eval_expr cx (Call (raw_call_return_type flags)
              (RawCallCalldataTarget flags) (addr::kws) NONE)
              (es with gas_obs := xs)` >>
  rename1 `_ = (res, es2)` >>
  `expr_vv_res_ok res` by (fs[gas_admissible_def] >> metis_tac[]) >>
  `~cx.txn.is_static /\ IS_SOME es_end.outcomes` by
    fs[typed_args_post_def, stmt_state_rel_def, state_rel_def] >>
  `es2.gas_obs = [] /\
   !tail. eval_expr cx (Call (raw_call_return_type flags)
            (RawCallCalldataTarget flags) (addr::kws) NONE)
            (es with gas_obs := xs ++ tail) = (res, es2 with gas_obs := tail)` by
    (irule calldata_call_source_gas_obs >> simp[] >>
     qexistsl_tac [`es_end`, `vs`] >> simp[]) >>
  mp_tac (Q.INST [`es` |-> `es with gas_obs := xs`,
                  `es1` |-> `es_end with gas_obs := []`,
                  `ann` |-> `raw_call_return_type flags`]
            calldata_call_success_frag) >>
  impl_tac >- simp[calldata_typed_args_post_gas_obs] >>
  simp[frag_path_def] >>
  disch_then (qspec_then `func` mp_tac) >> simp[] >> strip_tac >>
  simp[gas_outcome_def] >> qexists_tac `marks ++ REPLICATE n F` >> disj1_tac >>
  simp[gas_summary_at_def, gas_marked_exec_def] >>
  qexistsl_tac [`res`, `es2`, `r`] >>
  `es2 with gas_obs := [] = es2` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  drule gas_explicit_append_path >>
  disch_then (qspec_then `REPLICATE n F` SUBST1_TAC) >>
  simp[calldata_gas_explicit_false, gas_marked_path_def] >>
  `gas_path ctx func s0 (n + LENGTH marks) r` by
    metis_tac[gas_path_then, arithmeticTheory.ADD_COMM] >>
  gvs[calldata_vv_post_gas_obs]
QED

Theorem calldata_call_exempt_cert[local]:
  gas_exempt_cert memory tops p
    (ignore_bind (eval_exprs cx args) (return ())) start marks out endpoint ==>
  gas_exempt_cert memory tops p
    (ignore_bind (eval_expr cx (Call ann (RawCallCalldataTarget flags) args dflt))
      (return ())) start marks out endpoint
Proof
  strip_tac >> rewrite_tac[calldata_call_action] >>
  PairCases_on `p` >> PairCases_on `start` >>
  PairCases_on `out` >> PairCases_on `endpoint` >>
  qmatch_goalsub_abbrev_tac `ignore_bind (bind _ k) _` >>
  `ignore_bind (bind (eval_exprs cx args) k) (return ()) =
   bind (eval_exprs cx args) (\vs. ignore_bind (k vs) (return ()))` by
    simp[ignore_bind_def, vyperStateTheory.bind_assoc] >>
  pop_assum SUBST1_TAC >> irule gas_exempt_cert_error_values >> simp[]
QED

Theorem calldata_call_vv_sim[local]:
  exprs_case nocalls ctx func cenv cx args /\
  expr_body_pre cenv cx env (Call ann (RawCallCalldataTarget flags) args dflt) es /\
  (nocalls ==> int_calls_expr (Call ann (RawCallCalldataTarget flags) args dflt) = []) ==>
  expr_vv_sim ctx func cenv cx ty (Call ann (RawCallCalldataTarget flags) args dflt) es
Proof
  strip_tac >> drule calldata_call_pre >> strip_tac >> gvs[] >>
  rewrite_tac[expr_vv_sim_def] >> rpt gen_tac >> strip_tac >>
  drule calldata_call_compile >> strip_tac >> gvs[] >>
  drule_all calldata_call_args_ready >> strip_tac >>
  drule_all calldata_call_prefix_lower >> strip_tac >>
  drule_all lower_word_args_shape_ready >> strip_tac >>
  `ci_mono s5 s6` by metis_tac[ci_mono_compile_raw_call_finish, pairTheory.SND] >>
  `ci_mono s6 sb` by metis_tac[ci_mono_emit_void, pairTheory.SND] >>
  drule_all calldata_prepare_shape >> strip_tac >>
  `cs_extends s2 s5` by
    fs[cs_extends_def, same_blocks_def, rich_listTheory.IS_PREFIX_APPEND] >>
  `cs_extends s2 sb` by (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sa s2 func /\ fn_has_code s2 sb func` by
    metis_tac[fn_has_code_split] >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  qspecl_then [`addr::kws`, `ctx`, `func`, `cenv`, `cx`, `expr_type`,
    `expr_sim_inv cenv cx env`, `es`, `sa`, `addr_op::ops`, `s2`, `s0`]
    mp_tac lower_typed_args_sim >>
  (impl_tac >- simp[]) >>
  disch_then (strip_assume_tac o REWRITE_RULE [gas_outcome_def])
  >- (pop_assum (strip_assume_tac o BETA_RULE o REWRITE_RULE [gas_summary_at_def])
      >- (gvs[] >> irule calldata_call_normal >> simp[] >> rpt conj_tac
          >- (qexists_tac `ty` >> simp[])
          >- (qexists_tac `env` >> simp[])
          >- (qexists_tac `nocalls` >> simp[]) >>
          qexistsl_tac [`t`, `es_end`, `marks`, `vs`] >> simp[]) >>
      Cases_on `res` >> gvs[wb_args_exit_def] >>
      simp[gas_outcome_def] >> qexists_tac `marks` >> disj1_tac >>
      simp[gas_summary_at_def] >>
      qexistsl_tac [`INR y`, `es_end`, `r`] >> simp[] >>
      rewrite_tac[calldata_call_action] >>
      conj_tac >- (irule gas_marked_exec_bind_exception >> simp[]) >>
      qpat_x_assum `expr_exit _ _` mp_tac >>
      Cases_on `r` >> simp[expr_exit_def] >>
      Cases_on `y` >> simp[expr_exit_def] >>
      rename1 `Error ee` >> Cases_on `ee` >> simp[expr_exit_def]) >>
  simp[gas_outcome_def] >> qexists_tac `marks` >> disj2_tac >>
  metis_tac[calldata_call_exempt_cert]
QED

Theorem compile_raw_call_calldata_case:
  !nocalls ctx func cenv cx ann flags args dflt.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_sim_case nocalls ctx func cenv cx
      (Call ann (RawCallCalldataTarget flags) args dflt) /\
    expr_vv_case nocalls ctx func cenv cx
      (Call ann (RawCallCalldataTarget flags) args dflt)
Proof
  rpt gen_tac >> strip_tac >>
  `expr_vv_case nocalls ctx func cenv cx
     (Call ann (RawCallCalldataTarget flags) args dflt)`
    suffices_by simp[expr_sim_case_of_vv] >>
  rw[expr_vv_case_def] >> irule calldata_call_vv_sim >> simp[] >>
  conj_tac >- (qexists_tac `env` >> simp[]) >>
  qexists_tac `nocalls` >> simp[]
QED
