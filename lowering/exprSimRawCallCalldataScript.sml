(*
 * raw_call(to, msg.data, ...) and raw_call result lemmas (#636, Calls row 3)
 *
 * raw_call(to, msg.data, [value=], [gas=], [max_outsize=],
 * [is_static_call=], [revert_on_failure=]) lowers (compile_call's
 * RawCallCalldataTarget clause) to the address with lower_value, the
 * value= and gas= keyword operands in source order, GAS without gas=, the
 * output buffer (compile_raw_call_outbuf), a copy of all calldata into a
 * fresh DALLOCA region at vs_fmp (compile_msg_data_to_memory) and the call
 * (compile_raw_call_finish).
 * In oracle mode a non-delegate source raw_call takes the same outcome as
 * the lowered CALL/STATICCALL (eval_raw_call's take_call_outcome and
 * adopt_call_outcome; extCallOracleStep's exec_ext_call_oracle_step).
 *
 * This theory keeps the oracle-step, output-buffer, finish, revert and
 * result-tuple lemmas the raw_call memory and body simulations use.
 *)

Theory exprSimRawCallCalldata
Ancestors
  dallocaCalldata rawCallOutbufCompile[qualified,ignore_grammar]
  ptrDiscipline exprSimHashBoundary
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
  vyperStorageTrace vyperStorageFootprint vyperFiniteStoragePreservation
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

Theorem raw_call_typed_outcome:
  !target data vo es gas_cap.
  IS_SOME es.outcomes /\ outcomes_accounts_typed es.outcomes /\
  accounts_runtime_well_typed es.accounts ==>
  (es.outcomes = SOME [] /\ take_call_outcome gas_cap target data vo es =
    (INR (Error (RuntimeError "take_call_outcome")),es)) \/
  ?rq outcome es1. take_call_outcome gas_cap target data vo es =
    (INL (rq,outcome),es1)
Proof
  rpt strip_tac >>
  Cases_on `es.outcomes = SOME []`
  >- simp[take_call_outcome_def, take_request_outcome_def] >>
  disj2_tac >>
  `FST (take_call_outcome gas_cap target data vo es) <>
    INR (Error (RuntimeError "call outcome accounts"))` by
    metis_tac[take_call_outcome_typed] >>
  Cases_on `es.outcomes` >> gvs[] >>
  rename1 `es.outcomes = SOME os` >> Cases_on `os` >> gvs[] >>
  qpat_x_assum `FST _ <> _` mp_tac >>
  simp[take_call_outcome_def, take_request_outcome_def] >> pairarg_tac >> simp[] >>
  IF_CASES_TAC >> simp[]
QED

Theorem raw_call_oracle_result:
  !cx flags target data amount gas es es1 es2 rq outcome.
  (cx.txn.is_static ==> amount = 0) /\ ~flags.rcf_is_delegate /\
  (flags.rcf_is_static ==> amount = 0) /\ IS_SOME es.outcomes /\
  take_call_outcome (OPTION_BIND gas dest_NumV) target data
    (if flags.rcf_is_static \/ cx.txn.is_static then NONE else SOME amount) es =
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
  `frame_call_value cx (if flags.rcf_is_static then NONE else SOME amount) es =
    (INL (if flags.rcf_is_static \/ cx.txn.is_static then NONE else SOME amount), es)` by
    (Cases_on `cx.txn.is_static` >> Cases_on `flags.rcf_is_static` >>
     gvs[frame_call_value_def, check_def, assert_def, ignore_bind_def,
         bind_def, vyperStateTheory.return_def]) >>
  simp[eval_raw_call_def, update_pending_deletions_def, bind_def, ignore_bind_def,
       type_check_def, assert_def, vyperStateTheory.return_def, raise_def] >>
  Cases_on `flags.rcf_revert_on_failure` >>
  Cases_on `call_outcome_success outcome` >>
  simp[vyperStateTheory.return_def, raise_def, COND_RATOR] >>
  Cases_on `flags.rcf_max_outsize = 0` >>
  simp[bind_def, vyperStateTheory.return_def, raise_def]
QED

Theorem raw_call_static_value_abort:
  cx.txn.is_static /\ ~flags.rcf_is_delegate /\ ~flags.rcf_is_static /\
  amount <> 0 ==>
  eval_raw_call cx flags target data amount gas es =
    (INR (Error (RuntimeError "write in static context")), es)
Proof
  simp[eval_raw_call_def, frame_call_value_def, type_check_def,
       check_def, assert_def, bind_def, ignore_bind_def, vyperStateTheory.return_def]
QED

(* TOP-LEVEL *)
(* An oracle's bounded return write stays within its own fresh ALLOCA. *)
Theorem raw_call_outbuf_write_frame:
  !ctx func cenv cx es s inst q b sz dst data.
    stmt_state_rel H ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
    b <= dst /\ dst + LENGTH data <= b + sz ==>
    stmt_state_rel H ctx func cenv cx es (write_memory_with_expansion dst data s)
Proof
  rpt gen_tac >> strip_tac >>
  `!src. src = cenv.ce_module \/ IS_SOME (ALOOKUP cenv.ce_modules src) ==>
    immutables_rel cenv cx.txn.target src cenv.ce_is_ctor es
      (write_memory_with_expansion dst data s)` by
    (gen_tac >> disch_tac >>
     irule immutables_rel_mem_agree >> qexists_tac `s` >>
     conj_tac >- simp[immutableMemoryFrameTheory.immutable_write_memory_capacity] >>
     conj_tac >- simp[write_memory_with_expansion_def] >>
     reverse conj_tac
     >- (fs[stmt_state_rel_def, state_rel_def, optionTheory.IS_SOME_EXISTS] >>
         metis_tac[]) >>
     rpt strip_tac >>
     `immutable_alloca_sep func (cenv with ce_module := src) cx es s` by
       (fs[stmt_state_rel_def, optionTheory.IS_SOME_EXISTS] >>
        Cases_on `src = cenv.ce_module` >>
        gvs[compileEnvTheory.compile_env_component_equality] >> metis_tac[]) >>
     qpat_x_assum `immutable_alloca_sep _ _ _ _ _` mp_tac >>
     simp[immutable_alloca_sep_def] >>
     disch_then (drule_all o CONJUNCT2) >> strip_tac >>
     `regions_disjoint off (type_memory_size tv) b sz` by
       (qpat_x_assum `!inst b sz. _` drule_all >> simp[]) >>
     irule hash_write_memory_disjoint >>
     fs[regions_disjoint_def] >> decide_tac) >>
  irule write_memory_stmt_state_rel >> simp[] >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >> drule_all alloca_clear_of_locals >> decide_tac
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
    state_rel H func cenv cx es s /\ inst.inst_outputs = [out] /\
    inst.inst_opcode = (if stat then STATICCALL else CALL) /\
    inst.inst_operands =
      (if stat then [gop;aop;iop;zop;rop;cop]
       else [gop;aop;vop;iop;zop;rop;cop]) /\
    eval_operand gop s = SOME gas /\ eval_operand aop s = SOME aw /\
    eval_operand vop s = SOME vw /\ eval_operand iop s = SOME ip /\
    eval_operand zop s = SOME iz /\ eval_operand rop s = SOME rp /\
    eval_operand cop s = SOME cap /\
  (cx.txn.is_static ==> stat \/ vw = 0w) /\
    (!g. gas_cap = SOME g ==> g = w2n gas) /\
  take_call_outcome gas_cap (w2w aw) (read_memory (w2n ip) (w2n iz) s)
      (if stat \/ cx.txn.is_static then NONE else SOME (w2n vw)) es = (INL (rq,outcome),es1) /\
    local_ptrs_rel func cenv es.scopes
      (write_memory_with_expansion (w2n rp) (TAKE (w2n cap) outcome.co_returnData) s) /\
    (!src. src = cenv.ce_module \/ IS_SOME (ALOOKUP cenv.ce_modules src) ==>
      immutables_rel cenv cx.txn.target src cenv.ce_is_ctor es
        (write_memory_with_expansion (w2n rp) (TAKE (w2n cap) outcome.co_returnData) s)) ==>
    ?t. step_inst_base inst s =
          OK (update_var out (if outcome.co_success then 1w else 0w) t) /\
        state_rel H func cenv cx (SND (adopt_call_outcome rq outcome es1)) t /\
        t.vs_returndata = outcome.co_returnData /\
        t.vs_memory = (write_memory_with_expansion (w2n rp)
                        (TAKE (w2n cap) outcome.co_returnData) s).vs_memory /\
        t.vs_fmp = s.vs_fmp /\ t.vs_allocas = s.vs_allocas /\
        t.vs_vars = s.vs_vars /\ t.vs_inst_idx = s.vs_inst_idx /\
        t.vs_data_section = s.vs_data_section
Proof
  rpt gen_tac >> strip_tac >>
  `s.vs_call_ctx.cc_static = cx.txn.is_static` by
    gvs[state_rel_def, call_ctx_rel_def] >>
  `?t. exec_ext_call inst s gas aw (if stat then 0w else vw) ip iz rp cap
      (stat \/ cx.txn.is_static) =
      OK (update_var out (if outcome.co_success then 1w else 0w) t) /\
    t = s with <| vs_outcomes := t.vs_outcomes; vs_requests := t.vs_requests;
      vs_accounts := t.vs_accounts; vs_transient := t.vs_transient;
      vs_logs := t.vs_logs; vs_pending_deletions := t.vs_pending_deletions;
      vs_returndata := t.vs_returndata; vs_memory := t.vs_memory |> /\
    t.vs_memory = (write_memory_with_expansion (w2n rp)
      (TAKE (w2n cap) outcome.co_returnData) s).vs_memory /\
    t.vs_returndata = outcome.co_returnData /\
    (local_ptrs_rel func cenv es.scopes t /\
     (!src. src = cenv.ce_module \/ IS_SOME (ALOOKUP cenv.ce_modules src) ==>
       immutables_rel cenv cx.txn.target src cenv.ce_is_ctor es t) ==>
     state_rel H func cenv cx (SND (adopt_call_outcome rq outcome es1)) t)` by
    (irule exec_ext_call_oracle_step >> simp[] >>
     qexistsl_tac [`gas_cap`,
       `if stat \/ cx.txn.is_static then NONE else SOME (w2n vw)`] >>
     Cases_on `stat` >> Cases_on `cx.txn.is_static` >> gvs[]) >>
  `write_memory_with_expansion (w2n rp)
      (TAKE (w2n cap) outcome.co_returnData) s = s with vs_memory := t.vs_memory` by
    (qpat_x_assum `t.vs_memory = _` (fn th => REWRITE_TAC [th]) >>
     simp[write_memory_with_expansion_def]) >>
  `local_ptrs_rel func cenv es.scopes t /\
   (!src. src = cenv.ce_module \/ IS_SOME (ALOOKUP cenv.ce_modules src) ==>
     immutables_rel cenv cx.txn.target src cenv.ce_is_ctor es t)` by
    (qpat_x_assum `local_ptrs_rel _ _ _ (write_memory_with_expansion _ _ _)` mp_tac >>
     qpat_x_assum `!src. _ ==> immutables_rel _ _ _ _ _ (write_memory_with_expansion _ _ _)` mp_tac >>
     qpat_x_assum `write_memory_with_expansion _ _ _ = _`
       (fn th => ONCE_REWRITE_TAC [th]) >>
     qpat_x_assum `t = _` mp_tac >> rpt (pop_assum kall_tac) >>
     disch_then (fn th => ONCE_REWRITE_TAC [th]) >>
     simp[local_ptrs_rel_def, local_region_def, local_backed_def,
          lookup_var_def, immutables_rel_def] >> metis_tac[]) >>
  qexists_tac `t` >> conj_tac
  >- (qpat_x_assum `t = _` kall_tac >>
      qpat_x_assum `write_memory_with_expansion _ _ _ = _` kall_tac >>
      Cases_on `stat` >> Cases_on `cx.txn.is_static` >> gvs[] >>
      qpat_assum `inst.inst_opcode = _` (fn opcode =>
        let
          val rule = valOf (get_first (fn clause => total (MATCH_MP clause) opcode)
            (CONJUNCTS step_inst_base_opcode_eqs))
        in
          PURE_ONCE_REWRITE_TAC [rule]
        end) >>
      qpat_assum `inst.inst_operands = _`
        (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
      simp_tac bool_ss [list_case_def] >>
      FILTER_ASM_REWRITE_TAC (can (match_term ``eval_operand _ _ = SOME _``)) [] >>
      simp_tac bool_ss [pair_case_def, optionTheory.option_case_def] >>
      asm_rewrite_tac[]) >>
  conj_tac >- (first_x_assum irule >> simp[NoAsms] >>
               conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `t = _` mp_tac >> rpt (pop_assum kall_tac) >>
  disch_then (fn th => ONCE_REWRITE_TAC [th]) >> simp[]
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

Theorem raw_call_finish_prefix:
  compile_raw_call_finish aop dp dl gop vop call_ty n rev ov op sa =
    (result,sb) ==>
  ?success sc.
    (case call_ty of
       RegularCall => emit_op CALL [gop;aop;vop;dp;dl;op;Lit (n2w n)]
     | StaticCall => emit_op STATICCALL [gop;aop;dp;dl;op;Lit (n2w n)]
     | DelegateCall => emit_op DELEGATECALL [gop;aop;dp;dl;op;Lit (n2w n)]) sa =
    (success,sc) /\ cs_extends sc sb
Proof
  Cases_on `call_ty` >>
  rewrite_tac[compile_raw_call_finish_def] >>
  simp[Once comp_bind_def] >> pairarg_tac >> simp[] >> strip_tac >>
  rename1 `emit_op opc _ sa = (success,sc)` >>
  qmatch_asmsub_abbrev_tac `tail sc = (result,sb)` >>
  `ci_mono sc (SND (tail sc))` by
    (qunabbrev_tac `tail` >> rpt (pop_assum kall_tac) >>
     rpt (FIRST [
       CHANGED_TAC (simp[LET_THM, pairTheory.FORALL_PROD, pairTheory.UNCURRY_DEF,
         ci_mono_emit_op, ci_mono_emit_void, ci_mono_emit_inst,
         ci_mono_compile_alloc_buffer, ci_mono_fresh_label, ci_mono_new_block,
         ci_mono_compile_select, ci_mono_comp_return]),
       gen_tac, ho_match_mp_tac ci_mono_bind >> conj_tac,
       ho_match_mp_tac ci_mono_ignore_bind >> conj_tac, IF_CASES_TAC])) >>
  gvs[ci_mono_def]
QED



Theorem raw_call_exhausted:
  (cx.txn.is_static ==> amount = 0) /\ ~flags.rcf_is_delegate /\
  (flags.rcf_is_static ==> amount = 0) /\ es.outcomes = SOME [] ==>
  eval_raw_call cx flags target data amount gas es =
    (INR (Error (RuntimeError "take_call_outcome")),es)
Proof
  strip_tac >>
  Cases_on `cx.txn.is_static` >> Cases_on `flags.rcf_is_static` >>
  gvs[eval_raw_call_def, frame_call_value_def, take_call_outcome_def,
      take_request_outcome_def, bind_def, ignore_bind_def, type_check_def,
      check_def, assert_def, return_def]
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
Theorem raw_call_output_store_frame[local]:
  !ctx func cenv cx es s saved inst q b sz (w:bytes32) len.
    stmt_state_rel H ctx func cenv cx es (s with vs_fmp := saved) /\
    fn_inst_ids_distinct func /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
    b <= w2n w /\ w2n w + 32 <= b + sz ==>
    stmt_state_rel H ctx func cenv cx es
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

(* Bounded output writes leave protected allocations and local regions alone.
   The cutoff is before output allocation, not the start of the finish code. *)
Theorem raw_call_outbuf_write_regions[local]:
  !ctx func cenv cx es s inst q b sz dst data cutoff.
    stmt_state_rel H ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
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
    stmt_state_rel H ctx func cenv cx es1 s /\ fn_inst_ids_distinct func /\
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
    stmt_state_rel H ctx func cenv cx es1 s /\ fn_inst_ids_distinct func /\
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

Theorem raw_call_reserved_vars_frame:
  stmt_state_rel H ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  (!p v. safe_operand sa p /\ eval_operand p s = SOME v ==>
    eval_operand p (s with vs_vars := V) = SOME v) ==>
  stmt_state_rel H ctx func cenv cx es (s with vs_vars := V)
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
    stmt_state_rel H ctx func cenv cx es1 (u with vs_fmp := saved) /\
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
  qexistsl_tac [`H`, `b`, `ctx`, `cx`, `func`, `inst`, `q`, `sz`] >>
  gvs[]
QED

Theorem raw_call_wb_frame_inst_idx:
  wb_frame cenv es es' sf s0 (s with vs_inst_idx := k) = wb_frame cenv es es' sf s0 s
Proof
  simp[wb_frame_def, locals_kept_def, popped_kept_def, lookup_var_def]
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
    stmt_state_rel H ctx func cenv cx es (s with vs_fmp := saved) /\
    local_ptrs_reserved cenv sa /\ wb_frame cenv es0 es sf s0 s /\
    sf.cs_next_var <= sa.cs_next_var /\ local_ptrs_reserved cenv sf /\
    MAP FDOM es0.scopes = MAP FDOM es.scopes /\ sf.cs_next_id <= inst.inst_id /\
    fn_inst_ids_distinct func /\ MEM inst (fn_insts func) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [q] /\
    not_local_ptr cenv es.scopes q /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
    b <= w2n w /\ w2n w + 32 <= b + sz ==>
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      stmt_state_rel H ctx func cenv cx es (t with vs_fmp := saved) /\
      wb_frame cenv es0 es sf s0 t /\
      val_in_memory (BaseTV (BytesT (Dynamic n)))
        (BytesV (TAKE n s.vs_returndata)) (w2n w) t.vs_memory /\
      t.vs_fmp = s.vs_fmp /\ t.vs_allocas = s.vs_allocas /\
      (!p. safe_operand sa p ==> eval_operand p t = eval_operand p s)
Proof
  rpt gen_tac >> strip_tac >> drule_all raw_call_output_prefix_run >> strip_tac >>
  `stmt_state_rel H ctx func cenv cx es (u with vs_fmp := saved)` by
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
  `stmt_state_rel H ctx func cenv cx es (t with vs_fmp := saved)` by
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

Theorem raw_call_take_adopt_fields:
  take_call_outcome gas_cap addr data value es = (INL (rq,outcome),es1) ==>
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

Theorem raw_call_wb_frame_fmp[local]:
  wb_frame cenv es es' sf s0 (s with vs_fmp := saved) <=> wb_frame cenv es es' sf s0 s
Proof
  simp[wb_frame_def, locals_kept_def, popped_kept_def, lookup_var_def, local_region_def]
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
  stmt_state_rel H ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (p,32 + sz) /\
  mem_word_at p s.vs_memory = (if success then 1w else 0w) /\
  val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) src s.vs_memory /\
  val_wf (BaseTV (BytesT (Dynamic n))) (BytesV bs) /\
  type_memory_size (BaseTV (BytesT (Dynamic n))) <= sz ==>
  stmt_state_rel H ctx func cenv cx es (mcopy (p + 32) src sz s) /\
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

Theorem raw_call_alloc_buffer_run:
  !func cenv cx es sa sm buf sz s ctx saved.
  compile_alloc_buffer sz sa = (buf,sm) /\
  stmt_state_rel H ctx func cenv cx es (s with vs_fmp := saved) /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\ sz < dimword (:256) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) ==>
  ?t w. run_inst_seq (emitted_insts sa sm) s = OK t /\
    stmt_state_rel H ctx func cenv cx es (t with vs_fmp := saved) /\
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
  stmt_state_rel H ctx func cenv cx es (s with vs_fmp := saved) /\
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
  stmt_state_rel H ctx func cenv cx es
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
      goal_assum (drule_at (Pat `stmt_state_rel H _ _ _ _ _ _`)) >> simp[] >>
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
  stmt_state_rel H ctx func cenv cx es (s with vs_fmp := saved) /\
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
    stmt_state_rel H ctx func cenv cx es (t with vs_fmp := saved) /\
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

Theorem raw_call_tuple_copy_wb:
  wb_frame cenv es0 es sf s0 s /\
  stmt_state_rel H ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [q] /\
  not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (p,32 + sz) /\
  sf.cs_next_id <= inst.inst_id /\ local_ptrs_reserved cenv sf /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes ==>
  wb_frame cenv es0 es sf s0 (mcopy (p + 32) src sz s)
Proof
  strip_tac >> simp[mcopy_def] >> irule raw_call_outbuf_wb_frame >>
  simp[read_memory_def, LENGTH_TAKE_EQ, LENGTH_DROP] >>
  goal_assum (drule_at (Pat `stmt_state_rel H _ _ _ _ _ _`)) >> simp[] >>
  goal_assum (drule_at (Pat `MEM _ (fn_insts _)`)) >> simp[] >>
  goal_assum (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >> simp[]
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
  take_call_outcome gas_cap target data amount es = (INL (rq,oc),consumed) ==>
  LENGTH oc.co_returnData < dimword(:256)
Proof
  Cases_on `es.outcomes` >>
  simp[vyperCallOutcomeTheory.take_call_outcome_def, vyperCallOutcomeTheory.take_request_outcome_def] >>
  rename1 `es.outcomes = SOME os` >> Cases_on `os` >> simp[] >>
  pairarg_tac >> simp[] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >>
  irule calldata_take_outcome_bound >>
  goal_assum (drule_at Any) >>
  gvs[outcomes_accounts_typed_def, EVERY_MEM]
QED

(* ===== The counted composition ===== *)

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
    ~flags.rcf_is_delegate /\ IS_SOME st.outcomes ==>
    eval_raw_call cx flags target data amount gas (st with gas_obs := g) =
      (FST (eval_raw_call cx flags target data amount gas st),
       SND (eval_raw_call cx flags target data amount gas st) with gas_obs := g) /\
    (SND (eval_raw_call cx flags target data amount gas st)).gas_obs = st.gas_obs
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `flags.rcf_is_static /\ amount <> 0`
  >- fs[eval_raw_call_def, type_check_def, assert_def, ignore_bind_def,
        bind_def, raise_def] >>
  Cases_on `cx.txn.is_static /\ amount <> 0`
  >- (fs[] >> simp[raw_call_static_value_abort]) >>
  `cx.txn.is_static ==> amount = 0` by fs[] >>
  `flags.rcf_is_static ==> amount = 0` by fs[] >>
  `!st. frame_call_value cx (if flags.rcf_is_static then NONE else SOME amount) st =
    (INL (if flags.rcf_is_static \/ cx.txn.is_static then NONE else SOME amount), st)` by
    (Cases_on `cx.txn.is_static` >> Cases_on `flags.rcf_is_static` >>
     gvs[frame_call_value_def, check_def, assert_def, ignore_bind_def,
         bind_def, vyperStateTheory.return_def]) >>
  simp[eval_raw_call_def, update_pending_deletions_def, bind_def, ignore_bind_def,
       type_check_def, assert_def, vyperStateTheory.return_def, raise_def] >>
  qmatch_goalsub_abbrev_tac `take_call_outcome gas_cap target data vo` >>
  mp_tac (CONJ
    (Q.INST [`calldata` |-> `data`, `value_opt` |-> `vo`, `readings` |-> `g`]
       vyperCallOutcomePropsTheory.take_call_outcome_gas_obs)
    (Q.INST [`calldata` |-> `data`, `value_opt` |-> `vo`]
       (CONJUNCT2 (CONJUNCT2 (CONJUNCT2 (CONJUNCT2
          vyperCallOutcomePropsTheory.take_call_outcome_preserved_fields)))))) >>
  Cases_on `take_call_outcome gas_cap target data vo st` >> rename1 `_ = (q, st1)` >>
  reverse (Cases_on `q`) >> simp[] >> strip_tac >>
  rename1 `INL rqoc` >> PairCases_on `rqoc` >> simp[] >>
  qspecl_then [`rqoc0`, `rqoc1`, `st1`, `g`] mp_tac
    calldata_adopt_call_outcome_gas_obs >>
  Cases_on `adopt_call_outcome rqoc0 rqoc1 st1` >> rename1 `_ = (q2, st2)` >>
  Cases_on `q2` >> simp[] >> strip_tac >>
  rw[vyperStateTheory.return_def, raise_def, bind_def, ignore_bind_def]
QED

Theorem raw_delegate_call_source_tail:
  flags.rcf_is_delegate /\ ~flags.rcf_is_static /\
  IS_SOME es.outcomes /\ outcomes_accounts_typed es.outcomes ==>
  (es.outcomes = SOME [] /\
   eval_raw_call cx flags target data 0 gas es =
     (INR (Error (RuntimeError "take_call_outcome")),es)) \/
  ?rq outcome es1 es2.
    take_delegate_outcome (OPTION_BIND gas dest_NumV) target data
      (if cx.txn.is_static then NONE else SOME 0) es =
        (INL (rq,outcome),es1) /\
    adopt_call_outcome rq outcome es1 = (INL (),es2) /\
    eval_raw_call cx flags target data 0 gas es =
      (if flags.rcf_revert_on_failure /\ ~outcome.co_success then
         INR (Error (RevertData outcome.co_returnData))
       else INL (Value
         (if flags.rcf_revert_on_failure then
            if flags.rcf_max_outsize = 0 then NoneV
            else BytesV (TAKE flags.rcf_max_outsize outcome.co_returnData)
          else if flags.rcf_max_outsize = 0 then BoolV outcome.co_success
          else ArrayV (TupleV [BoolV outcome.co_success;
            BytesV (TAKE flags.rcf_max_outsize outcome.co_returnData)]))),es2) /\
    es2.gas_obs = es.gas_obs /\ LENGTH outcome.co_returnData < dimword (:256) /\
    (!gs. eval_raw_call cx flags target data 0 gas (es with gas_obs := gs) =
      (FST (eval_raw_call cx flags target data 0 gas es),es2 with gas_obs := gs))
Proof
  strip_tac >>
  qabbrev_tac `vo = if cx.txn.is_static then NONE else SOME 0` >>
  qabbrev_tac `gas_cap = OPTION_BIND gas dest_NumV` >>
  `!s. frame_call_value cx (SOME 0) s = (INL vo,s)` by
    (Cases_on `cx.txn.is_static` >>
     simp[Abbr `vo`, frame_call_value_def, check_def, assert_def,
          ignore_bind_def, bind_def, vyperStateTheory.return_def]) >>
  Cases_on `es.outcomes` >> fs[] >>
  rename1 `es.outcomes = SOME os` >> Cases_on `os`
  >- simp[eval_raw_call_def, take_delegate_outcome_def,
         take_request_outcome_def, type_check_def, assert_def, bind_def,
         ignore_bind_def, raise_def, vyperStateTheory.return_def] >>
  rename1 `es.outcomes = SOME (outcome::rest)` >>
  fs[outcomes_accounts_typed_def] >>
  qabbrev_tac `rq = delegate_outcome_request target data vo es with
    cr_gas := gas_cap` >>
  qabbrev_tac `es1 = es with <| outcomes := SOME rest;
      requests := record_request rq es.requests;
      storage_trace := es.storage_trace ++ [StorageOutcome rq outcome] |>` >>
  `rq.cr_kind = DelegateMessageCall /\ ~computed_precompile rq` by
    simp[Abbr `rq`, delegate_outcome_request_def, computed_precompile_def] >>
  `!g. take_delegate_outcome gas_cap target data vo (es with gas_obs := g) =
      (INL (rq,outcome),es1 with gas_obs := g)` by
    (gen_tac >>
     `(delegate_outcome_request target data vo (es with gas_obs := g) with
       cr_gas := gas_cap) = rq` by
       simp[Abbr `rq`, delegate_outcome_request_def, call_outcome_request_def] >>
     PURE_REWRITE_TAC [take_delegate_outcome_def] >>
     qpat_x_assum `(delegate_outcome_request _ _ _ _ with cr_gas := _) = rq`
       (fn th => PURE_ONCE_REWRITE_TAC [th]) >>
     simp[take_request_outcome_def, take_outcome_def,
          Abbr `es1`, evaluation_state_component_equality]) >>
  `take_delegate_outcome gas_cap target data vo es = (INL (rq,outcome),es1)` by
    (PURE_REWRITE_TAC [take_delegate_outcome_def] >>
     qpat_assum `Abbrev (rq = _)`
       (fn th => PURE_ONCE_REWRITE_TAC [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
     simp[take_request_outcome_def, take_outcome_def, Abbr `es1`]) >>
  qabbrev_tac `es2 = SND (adopt_call_outcome rq outcome es1)` >>
  `adopt_call_outcome rq outcome es1 = (INL (),es2)` by
    (simp[Abbr `es2`, adopt_call_outcome_equation] >>
     Cases_on `rq.cr_static` >> Cases_on `outcome.co_success` >> simp[]) >>
  `!g. adopt_call_outcome rq outcome (es1 with gas_obs := g) =
      (INL (),es2 with gas_obs := g)` by
    metis_tac[calldata_adopt_call_outcome_gas_obs, pairTheory.FST, pairTheory.SND] >>
  `es2.gas_obs = es.gas_obs` by
    (Cases_on `rq.cr_static` >> Cases_on `outcome.co_success` >>
     simp[Abbr `es2`, Abbr `es1`, adopt_call_outcome_equation]) >>
  qexistsl_tac [`rq`,`outcome`,`es1`,`es2`] >>
  qpat_assum `Abbrev (gas_cap = _)` (fn gas_eq =>
    qpat_assum `Abbrev (vo = _)` (fn value_eq =>
      simp[GSYM (REWRITE_RULE [markerTheory.Abbrev_def] gas_eq),
           GSYM (REWRITE_RULE [markerTheory.Abbrev_def] value_eq),
           eval_raw_call_def, type_check_def, assert_def, bind_def,
           ignore_bind_def, vyperStateTheory.return_def, raise_def])) >>
  Cases_on `flags.rcf_revert_on_failure` >> Cases_on `outcome.co_success` >>
  Cases_on `flags.rcf_max_outsize = 0` >>
  simp[vyperStateTheory.return_def, raise_def, bind_def, ignore_bind_def]
QED
