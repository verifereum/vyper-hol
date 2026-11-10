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
 * expr_sim_pre and expr_body_pre exclude delegate raw_calls
 * (~expr_has_evm_run), so those hold vacuously.  Without revert_on_failure
 * the result is the success flag, or for max_outsize > 0 a fresh
 * (bool, Bytes[max_outsize]) tuple buffer: the flag word, then the bytes
 * value (length and data) inline, as val_in_memory lays out a tuple.
 *
 * TOP-LEVEL:
 *   compile_raw_call_case — raw_call's expr_sim_case and expr_vv_case from
 *     its operands' exprs_case, for compile_expr_sim and the body
 *     simulation
 *)

Theory exprSimRawCall
Ancestors
  exprSimSource exprSimHypsDefs exprSimDefs exprSimStack loweringPosts
  exprSimProps exprSimVVFrame exprSimAttributeFields
  gasOutcome gasSummary gasSummaryCompose gasExemptCert
  allocLimits freshWrites varsExt builtinSimple builtinProps
  list pair vyperMisc fragExec loweringSlice exprSimHyps exprSimWordArgs
  exprSimPrecompiles exprSimOperators exprSimOperands exprSimAccounts
  exprSimRawCallCalldata rawCallFragPath valueCopy valueTypingMemoryProps
  extCallOracleStep exprCallbackContracts exprCallBounds exprLowering
  exprLoweringProps emitHelper emitHelperProps compileEnv loweringStateRelDefs localPtrsProps valueEncoding valueEncodingDefs
  vyperAST vyperInterpreter vyperState vyperValue vyperTyping
  vyperTypeSystem vyperTypeCallGraph vyperCallOutcome extCallOracle
  vyperTypeExtCallSoundness vyperTypeEvalSoundness exprSimECArith exprSimUnwrap
  vyperRuntimeAccounts vyperTypeInvariants vyperEvalExprPreservesScopesDom
  venomExecSemantics venomInst venomState exprSimSend
  exprSimHash exprSimHashBoundary exprSimAlloc exprSimBuffer builtinSystem exprWordOperand exprSafeOperand exprOperandVar
Libs
  pairLib

(* The nonreverting result stores the flag inline before the bytes value. *)

Theorem raw_call_tuple_memory_encoding[local]:
  val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV (TAKE n data)) src s.vs_memory /\
  (p + 32 <= src \/ src + (32 + 32 * word_size n) <= p) ==>
  val_in_memory (TupleTV [BaseTV BoolT; BaseTV (BytesT (Dynamic n))])
    (ArrayV (TupleV [BoolV success; BytesV (TAKE n data)])) p
    (mcopy (p + 32) src (32 + 32 * word_size n)
      (mstore p (bool_to_word success) s)).vs_memory
Proof
  disch_then (CONJUNCTS_THEN assume_tac) >>
  irule exprSimRawCallCalldataTheory.raw_call_tuple_copy >>
  simp[valueEncodingPropsTheory.mstore_mem_word_at_same,
       type_memory_size_def] >>
  qspec_then `n` assume_tac word_size_capacity >>
  simp[val_wf_def, type_memory_size_def, LENGTH_TAKE_EQ] >>
  conj_tac >- (Cases_on `success` >> simp[bool_to_word_def]) >>

  `LENGTH (TAKE n data) <= 32 * word_size n` by
    (qspec_then `n` assume_tac word_size_capacity >>
     simp[LENGTH_TAKE_EQ] >> decide_tac) >>
  `mem_word_at src (mstore p (bool_to_word success) s).vs_memory =
      mem_word_at src s.vs_memory` by
    (irule valueEncodingPropsTheory.mstore_mem_word_at_disjoint >> decide_tac) >>
  `mem_bytes_at (src + 32) (LENGTH (TAKE n data))
      (mstore p (bool_to_word success) s).vs_memory =
    mem_bytes_at (src + 32) (LENGTH (TAKE n data)) s.vs_memory` by
    (irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >> decide_tac) >>
  gvs[val_in_memory_def]
QED

Theorem raw_call_tuple_memory_frame[local]:
  (a + len <= p \/ p + (64 + 32 * word_size n) <= a) ==>
  mem_bytes_at a len
    (mcopy (p + 32) src (32 + 32 * word_size n)
      (mstore p success s)).vs_memory = mem_bytes_at a len s.vs_memory
Proof
  strip_tac >>
  `mem_bytes_at a len
    (mcopy (p + 32) src (32 + 32 * word_size n)
      (mstore p success s)).vs_memory =
    mem_bytes_at a len (mstore p success s).vs_memory` by
    (irule mem_bytes_at_mcopy_disjoint >> decide_tac) >>
  simp[] >> irule valueEncodingPropsTheory.mstore_mem_bytes_at_disjoint >> decide_tac
QED

Theorem raw_call_tuple_copy_seq_run[local]:
  emit_op ADD [pop;Lit 32w] sa = (dst,sb) /\
  emit_void MCOPY [dst;src;Lit (n2w sz)] sb = ((),sc) /\
  safe_operand sa pop /\ safe_operand sa src /\
  eval_operand pop s = SOME w /\ eval_operand src s = SOME a /\
  sz < dimword (:256) ==>
  ?u t. run_inst_seq (emitted_insts sa sc) s = OK t /\
    t = mcopy (w2n (w + 32w)) (w2n a) sz u /\
    (?vars. u = s with vs_vars := vars) /\
    (!p. safe_operand sa p ==> eval_operand p u = eval_operand p s) /\
    (!p. safe_operand sa p ==> eval_operand p t = eval_operand p s)
Proof
  strip_tac >> drule_all raw_call_tuple_dst_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sb) s = OK u` >>
  `eval_operand src u = SOME a` by simp[] >>
  drule_all emit_mcopy_run >> strip_tac >>
  qexistsl_tac [`u`, `mcopy (w2n (w + 32w)) (w2n a) sz u`] >>
  simp[] >> conj_tac
  >- (irule run_inst_seq_compose_ok >> qexistsl_tac [`u`, `sb`] >>
      simp[] >> conj_tac
      >- (irule inst_extends_emit_op >> goal_assum (drule_at Any)) >>
      irule inst_extends_emit_void >> goal_assum (drule_at Any)) >>
  conj_tac >- (qexists_tac `vars` >> simp[]) >>
  rpt strip_tac >>
  `eval_operand p u = eval_operand p s` by simp[] >>
  Cases_on `p` >>
  gvs[mcopy_def, write_memory_with_expansion_def, eval_operand_def, lookup_var_def]
QED

Theorem raw_call_tuple_copy_tail_run[local]:
  emit_op ADD [pop;Lit 32w] sa = (dst,sb) /\
  emit_void MCOPY [dst;src;Lit (n2w sz)] sb = ((),sc) /\
  safe_operand sa pop /\ safe_operand sa src /\
  eval_operand pop s = SOME w /\ eval_operand src s = SOME a /\
  sz < dimword (:256) /\ w2n w + (32 + sz) < dimword (:256) /\
  stmt_state_rel ctx func cenv cx es s /\
  wb_frame cenv es0 sf s0 s /\ fn_inst_ids_distinct func /\
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
  ?t. run_inst_seq (emitted_insts sa sc) s = OK t /\
    stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es0 sf s0 t /\
    t.vs_fmp = s.vs_fmp /\ eval_operand pop t = SOME w /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (w2n w,32 + sz) /\
    val_in_memory (TupleTV [BaseTV BoolT; BaseTV (BytesT (Dynamic n))])
      (ArrayV (TupleV [BoolV success; BytesV bs])) (w2n w) t.vs_memory /\
    (!p. safe_operand sa p ==> eval_operand p t = eval_operand p s)
Proof
  strip_tac >> drule_all raw_call_tuple_copy_seq_run >> strip_tac >>
  `w2n (w + 32w) = w2n w + 32` by
    (irule buffer_offset_no_wrap >> qexists_tac `32 + sz` >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es u` by
    (qpat_assum `u = _` SUBST1_TAC >>
     irule raw_call_reserved_vars_frame >> simp[] >>
     qexists_tac `sa` >> simp[] >> rpt strip_tac >>
     `eval_operand p u = eval_operand p s` by simp[] >> gvs[]) >>
  `wb_frame cenv es0 sf s0 u` by
    (irule wb_frame_readonly_tail >> qexistsl_tac [`sa`, `s`] >>
     simp[] >> rpt strip_tac >>
     `eval_operand (Var z) u = eval_operand (Var z) s` by
       (first_x_assum irule >> simp[safe_operand_def]) >>
     gvs[eval_operand_def]) >>
  `u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas` by gvs[] >>
  `mem_word_at (w2n w) u.vs_memory = (if success then 1w else 0w)` by simp[] >>
  `val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) (w2n a) u.vs_memory` by simp[] >>
  `FLOOKUP u.vs_allocas inst.inst_id = SOME (w2n w,32 + sz)` by simp[] >>
  drule_all raw_call_tuple_copy_frame >> strip_tac >>
  drule_all raw_call_tuple_copy_wb >> disch_then (qspec_then `w2n a` assume_tac) >>
  qexists_tac `t` >> simp[] >>
  gvs[mcopy_def, write_memory_with_expansion_def]
QED

Theorem raw_call_tuple_build_no_restore_run[local]:
  compile_alloc_buffer (32 + sz) sa = (buf,sm) /\
  emit_void MSTORE [buf.buf_operand;ok] sm = ((),sn) /\
  emit_op ADD [buf.buf_operand;Lit 32w] sn = (dst,sb) /\
  emit_void MCOPY [dst;src;Lit (n2w sz)] sb = ((),sc) /\
  stmt_state_rel ctx func cenv cx es s /\
  wb_frame cenv es0 sf s0 s /\ fn_inst_ids_distinct func /\
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
  safe_operand sa ok /\ safe_operand sa src /\
  eval_operand ok s = SOME (if success then 1w else 0w) /\
  eval_operand src s = SOME a ==>
  ?t w. run_inst_seq (emitted_insts sa sc) s = OK t /\
    stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es0 sf s0 t /\
    t.vs_fmp = s.vs_fmp /\ eval_operand buf.buf_operand t = SOME w /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,32 + sz) /\
    w2n w + (32 + sz) < dimword (:256) /\
    val_in_memory (TupleTV [BaseTV BoolT; BaseTV (BytesT (Dynamic n))])
      (ArrayV (TupleV [BoolV success; BytesV bs])) (w2n w) t.vs_memory /\
    (!p. safe_operand sa p ==> eval_operand p t = eval_operand p s) /\
    (!name lb lsz. local_region cenv es.scopes t name lb lsz ==>
      w2n w + (32 + sz) <= lb \/ lb + lsz <= w2n w)
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es (s with vs_fmp := s.vs_fmp)` by simp[] >>
  drule_all raw_call_tuple_alloc_ready >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa sn) s = OK u` >>
  `u with vs_fmp := s.vs_fmp = u` by
    (qpat_assum `u.vs_fmp = _` (SUBST1_TAC o SYM) >> simp[]) >>
  fs[] >>
  `ci_mono sa sm` by metis_tac[ci_mono_compile_alloc_buffer, SND] >>
  `ci_mono sm sn` by metis_tac[ci_mono_emit_void, SND] >>
  `sa.cs_next_var <= sn.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var` by
    (fs[ci_mono_def] >> decide_tac) >>
  `local_ptrs_reserved cenv sn /\ sf.cs_next_var <= sn.cs_next_var` by
    metis_tac[local_ptrs_reserved_next_var, arithmeticTheory.LESS_EQ_TRANS] >>
  `safe_operand sn buf.buf_operand /\ safe_operand sn src` by
    (fs[safe_operand_def] >> metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `eval_operand src u = SOME a` by simp[] >>
  `not_local_ptr cenv es.scopes (STRING #"%" (toString sa.cs_next_var))` by
    (irule fresh_not_local_ptr >> qexists_tac `sa` >> simp[not_fresh_at_def]) >>
  `sz < dimword (:256)` by (simp[wordsTheory.dimword_def] >> decide_tac) >>
  drule_at (Pat `MEM _ (fn_insts _)`) raw_call_tuple_copy_tail_run >>
  simp[mk_inst_def] >> disch_then drule >> simp[] >> strip_tac >>
  fs[arithmeticTheory.ADD_COMM] >>
  `safe_operand sn (Var q)` by gvs[] >>
  qpat_x_assum `!w sz success. _` drule_all >> strip_tac >>
  suspend "separation"
QED

Resume raw_call_tuple_build_no_restore_run[separation]:
  `!name lb lsz. local_region cenv es.scopes t name lb lsz ==>
     w2n w + (32 + sz) <= lb \/ lb + lsz <= w2n w` by
    (rpt strip_tac >>
     `regions_disjoint (w2n w) (32 + sz) lb lsz` suffices_by
       simp[loweringStateRelDefsTheory.regions_disjoint_def] >>
     irule local_ptrs_rel_alloca_disjoint >>
     goal_assum (drule_at (Pat `MEM _ (fn_insts _)`)) >>
     simp[mk_inst_def] >>
     goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
     fs[stmt_state_rel_def, state_rel_def]) >>
  qexistsl_tac [`t`, `w`] >> simp[] >> conj_tac
  >- (`inst_extends sa sm` by
        (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
         simp[contextTheory.compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
         pairarg_tac >> strip_tac >> gvs[] >> drule inst_extends_emit_op >> simp[]) >>
      `inst_extends sm sn` by
        (irule inst_extends_emit_void >> goal_assum (drule_at Any)) >>
      `inst_extends sa sn` by
        (irule inst_extends_trans >> qexists_tac `sm` >> simp[]) >>
      `inst_extends sn sb` by
        (irule inst_extends_emit_op >> goal_assum (drule_at Any)) >>
      `inst_extends sb sc` by
        (irule inst_extends_emit_void >> goal_assum (drule_at Any)) >>
      `inst_extends sn sc` by
        (irule inst_extends_trans >> qexists_tac `sb` >> simp[]) >>
      irule run_inst_seq_compose_ok >> qexistsl_tac [`u`, `sn`] >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `safe_operand sn p` by
        (irule safe_operand_mono >> qexists_tac `sa` >> simp[]) >>
      simp[]) >>
  rpt strip_tac >> first_x_assum drule >> decide_tac
QED

Finalise raw_call_tuple_build_no_restore_run

Theorem raw_call_nonrevert_finish_code[local]:
  compile_raw_call_finish to_op dp dl gas val call_ty n F ov op sa = (result,sb) ==>
  ?ok sc. (case call_ty of
      DelegateCall => emit_op DELEGATECALL [gas;to_op;dp;dl;op;Lit (n2w n)]
    | StaticCall => emit_op STATICCALL [gas;to_op;dp;dl;op;Lit (n2w n)]
    | RegularCall => emit_op CALL [gas;to_op;val;dp;dl;op;Lit (n2w n)]) sa = (ok,sc) /\
    (if n > 0 then
       do z <- emit_op RETURNDATASIZE [];
          cmp <- emit_op LT [z;Lit (n2w n)];
          cap <- compile_select cmp z (Lit (n2w n));
          emit_void MSTORE [ov;cap];
          buf <- compile_alloc_buffer (64 + ((n + 31) DIV 32) * 32);
          emit_void MSTORE [buf.buf_operand;ok];
          dst <- emit_op ADD [buf.buf_operand;Lit 32w];
          emit_void MCOPY [dst;ov;Lit (n2w (32 + ((n + 31) DIV 32) * 32))];
          return buf.buf_operand od
     else return ok) sc = (result,sb)
Proof
  simp[compile_raw_call_finish_def, comp_bind_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  qexistsl_tac [`success`, `s'`] >>
  gvs[comp_ignore_bind_def, comp_bind_def, arithmeticTheory.ADD_ASSOC]
QED

Theorem raw_call_nonrevert_suffix_code[local]:
  (if n > 0 then
       do z <- emit_op RETURNDATASIZE [];
          cmp <- emit_op LT [z;Lit (n2w n)];
          cap <- compile_select cmp z (Lit (n2w n));
          emit_void MSTORE [ov;cap];
          buf <- compile_alloc_buffer (64 + ((n + 31) DIV 32) * 32);
          emit_void MSTORE [buf.buf_operand;ok];
          dst <- emit_op ADD [buf.buf_operand;Lit 32w];
          emit_void MCOPY [dst;ov;Lit (n2w (32 + ((n + 31) DIV 32) * 32))];
          return buf.buf_operand od
     else return ok) sa = (result,sb) /\ 0 < n ==>
  ?z s1 cmp s2 cap s3 s4 buf s5 s6 dst s7.
    emit_op RETURNDATASIZE [] sa = (z,s1) /\
    emit_op LT [z;Lit (n2w n)] s1 = (cmp,s2) /\
    compile_select cmp z (Lit (n2w n)) s2 = (cap,s3) /\
    emit_void MSTORE [ov;cap] s3 = ((),s4) /\
    compile_alloc_buffer (64 + ((n + 31) DIV 32) * 32) s4 = (buf,s5) /\
    emit_void MSTORE [buf.buf_operand;ok] s5 = ((),s6) /\
    emit_op ADD [buf.buf_operand;Lit 32w] s6 = (dst,s7) /\
    emit_void MCOPY [dst;ov;Lit (n2w (32 + ((n + 31) DIV 32) * 32))]
      s7 = ((),sb) /\
    result = buf.buf_operand /\ ci_mono sa s4 /\ inst_extends sa s4 /\
    cs_extends sa s4 /\ cs_extends s4 sb /\
    inst_extends s4 sb /\ s4.cs_next_id < sb.cs_next_id /\ 
    MEM (mk_inst s4.cs_next_id ALLOCA
      [Lit (n2w (64 + ((n + 31) DIV 32) * 32))]
      [STRING #"%" (toString s4.cs_next_var)]) (emitted_insts s4 sb) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
    sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
    isPREFIX sa.cs_current_insts sb.cs_current_insts
Proof
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  gvs[builtinSimpleTheory.compile_select_def, contextTheory.compile_alloc_buffer_def,
      emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  simp[ci_mono_def, inst_extends_def, emitted_insts_def,
       rich_listTheory.IS_PREFIX_APPEND] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[mk_inst_def, is_terminator_def, cs_extends_def, same_blocks_def,
       rich_listTheory.IS_PREFIX_APPEND, rich_listTheory.DROP_APPEND]
QED

Theorem raw_call_tuple_alloc_size_norm[local]:
  !k:num. 32 + (32 + k * 32) = 32 * k + 64
Proof
  decide_tac
QED

Theorem raw_call_tuple_copy_size_norm[local]:
  !k:num. 32 + k * 32 = 32 * k + 32
Proof
  decide_tac
QED

Theorem raw_call_nonrevert_positive_run[local]:
  (if n > 0 then
       do z <- emit_op RETURNDATASIZE [];
          cmp <- emit_op LT [z;Lit (n2w n)];
          cap <- compile_select cmp z (Lit (n2w n));
          emit_void MSTORE [ov;cap];
          buf <- compile_alloc_buffer (64 + ((n + 31) DIV 32) * 32);
          emit_void MSTORE [buf.buf_operand;ok];
          dst <- emit_op ADD [buf.buf_operand;Lit 32w];
          emit_void MCOPY [dst;ov;Lit (n2w (32 + ((n + 31) DIV 32) * 32))];
          return buf.buf_operand od
     else return ok) sa = (result,sb) /\ 0 < n /\
  stmt_state_rel ctx func cenv cx es s /\ wb_frame cenv es0 sf s0 s /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  MEM alloc (fn_insts func) /\ alloc.inst_opcode = ALLOCA /\
  alloc.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas alloc.inst_id = SOME (w2n w,32 + ((n + 31) DIV 32) * 32) /\
  local_ptrs_reserved cenv sf /\ local_ptrs_reserved cenv sa /\
  sf.cs_next_var <= sa.cs_next_var /\ sf.cs_next_id <= alloc.inst_id /\
  alloc.inst_id < sa.cs_next_id /\ MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  safe_operand sa ov /\ safe_operand sa ok /\
  eval_operand ov s = SOME w /\ eval_operand ok s = SOME (if success then 1w else 0w) /\
  LENGTH s.vs_returndata < dimword (:256) /\
  mem_bytes_at (w2n w + 32) (LENGTH (TAKE n s.vs_returndata)) s.vs_memory =
    TAKE n s.vs_returndata /\
  64 + ((n + 31) DIV 32) * 32 < dimword (:256) /\ n < dimword (:256) ==>
  ?t tw ti. run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es0 sf s0 t /\
    t.vs_fmp = s.vs_fmp /\
    (!p. safe_operand sa p ==> eval_operand p t = eval_operand p s) /\
    sf.cs_next_id <= ti /\ ti < sb.cs_next_id /\
    eval_operand result t = SOME tw /\
    FLOOKUP t.vs_allocas ti = SOME (w2n tw,64 + ((n + 31) DIV 32) * 32) /\
    w2n tw + (64 + ((n + 31) DIV 32) * 32) < dimword (:256) /\
    val_in_memory (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))])
      (ArrayV (TupleV [BoolV success;BytesV (TAKE n s.vs_returndata)]))
      (w2n tw) t.vs_memory /\
    (!name lb lsz. local_region cenv es.scopes t name lb lsz ==>
      w2n tw + (64 + ((n + 31) DIV 32) * 32) <= lb \/ lb + lsz <= w2n tw)
Proof
  strip_tac >> drule_all raw_call_nonrevert_suffix_code >> strip_tac >>
  qpat_x_assum `(if _ then _ else _) _ = _` kall_tac >>
  `stmt_state_rel ctx func cenv cx es (s with vs_fmp := s.vs_fmp)` by simp[] >>
  drule_at (Pat `MEM _ (fn_insts _)`) raw_call_output_prefix_ready >>
  simp[] >> disch_then drule >> simp[] >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >> simp[] >>
  fs[wordsTheory.dimword_def] >>
  `stmt_state_rel ctx func cenv cx es (s with vs_fmp := s.vs_fmp)` by simp[] >>
  disch_then drule_all >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sa s4) s = OK u` >>
  `u with vs_fmp := s.vs_fmp = u` by
    (qpat_assum `u.vs_fmp = _` (SUBST1_TAC o SYM) >> simp[]) >> fs[] >>
  suspend "tuple"
QED

Resume raw_call_nonrevert_positive_run[tuple]:
  `local_ptrs_reserved cenv s4 /\ sf.cs_next_var <= s4.cs_next_var /\
   sf.cs_next_id <= s4.cs_next_id /\ alloc.inst_id < s4.cs_next_id /\
   safe_operand s4 ok /\ safe_operand s4 ov` by
    (fs[ci_mono_def] >> metis_tac[local_ptrs_reserved_next_var,
       safe_operand_mono, arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  `fn_has_code s4 sb func` by
    (mp_tac (Q.SPECL [`sa`,`s4`,`sb`,`func`] fn_has_code_split) >>
     impl_tac >- simp[] >> simp[]) >>
  `MEM (mk_inst s4.cs_next_id ALLOCA
     [Lit (n2w (64 + ((n + 31) DIV 32) * 32))]
     [STRING #"%" (toString s4.cs_next_var)]) (fn_insts func)` by
    (irule hash_emitted_inst_mem >> goal_assum (drule_at Any) >> simp[]) >>
  `eval_operand ok u = SOME (if success then 1w else 0w) /\
   eval_operand ov u = SOME w` by metis_tac[] >>
  `FLOOKUP u.vs_allocas alloc.inst_id = SOME (w2n w,32 + ((n + 31) DIV 32) * 32)` by simp[] >>
  `val_wf (BaseTV (BytesT (Dynamic n))) (BytesV (TAKE n s.vs_returndata))` by
    (qspec_then `n` mp_tac le_word_size_mul >>
     simp[val_wf_def, type_memory_size_def, LENGTH_TAKE_EQ] >> decide_tac) >>
  `type_memory_size (BaseTV (BytesT (Dynamic n))) =
     32 + ((n + 31) DIV 32) * 32` by
    simp[type_memory_size_def, vfmConstantsTheory.word_size_def] >>
  fs[] >>
  drule_at (Pat `MEM _ (fn_insts _)`)
    (raw_call_tuple_build_no_restore_run |> SPEC_ALL |> Q.INST
      [`sz` |-> `32 + ((n + 31) DIV 32) * 32`]
      |> PURE_REWRITE_RULE [raw_call_tuple_alloc_size_norm]
      |> PURE_REWRITE_RULE [raw_call_tuple_copy_size_norm]
      |> PURE_REWRITE_RULE [wordsTheory.dimword_def,
           fcpLib.INDEX_CONV ``dimindex(:256)``,
           EVAL ``(2:num) ** 256``]) >>
  simp[] >>
  disch_then (drule_at (Pat `emit_void MSTORE _ _ = _`)) >>
  disch_then (drule_at (Pat `emit_op ADD _ _ = _`)) >>
  disch_then (drule_at (Pat `emit_void MCOPY _ _ = _`)) >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  simp[] >> disch_then (qspec_then `success` mp_tac) >> simp[] >>
  disch_then drule_all >> strip_tac >>
  drule_all run_inst_seq_compose_ok >> strip_tac >>
  qexistsl_tac [`t`,`w'`,`s4.cs_next_id`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      `safe_operand s4 p` by
        (irule safe_operand_mono >> goal_assum (drule_at Any) >> fs[ci_mono_def]) >>
      metis_tac[]) >>
  qpat_x_assum `!name lb lsz. local_region _ _ _ name lb lsz ==> _` mp_tac >>
  simp[arithmeticTheory.ADD_COMM]
QED

Finalise raw_call_nonrevert_positive_run

Theorem raw_call_nonrevert_no_restore_frag[local]:
  (if n > 0 then
       do z <- emit_op RETURNDATASIZE [];
          cmp <- emit_op LT [z;Lit (n2w n)];
          cap <- compile_select cmp z (Lit (n2w n));
          emit_void MSTORE [ov;cap];
          buf <- compile_alloc_buffer (64 + ((n + 31) DIV 32) * 32);
          emit_void MSTORE [buf.buf_operand;ok];
          dst <- emit_op ADD [buf.buf_operand;Lit 32w];
          emit_void MCOPY [dst;ov;Lit (n2w (32 + ((n + 31) DIV 32) * 32))];
          return buf.buf_operand od
     else return ok) sa = (result,sb) /\
  stmt_state_rel ctx func cenv cx es s /\ wb_frame cenv es0 sf s0 s /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  MEM alloc (fn_insts func) /\ alloc.inst_opcode = ALLOCA /\
  alloc.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas alloc.inst_id = SOME (w2n w,32 + ((n + 31) DIV 32) * 32) /\
  local_ptrs_reserved cenv sf /\ local_ptrs_reserved cenv sa /\
  sf.cs_next_var <= sa.cs_next_var /\ sf.cs_next_id <= alloc.inst_id /\
  alloc.inst_id < sa.cs_next_id /\ MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  safe_operand sa ov /\ safe_operand sa ok /\
  eval_operand ov s = SOME w /\ eval_operand ok s = SOME (if success then 1w else 0w) /\
  LENGTH s.vs_returndata < dimword (:256) /\
  (0 < n ==> mem_bytes_at (w2n w + 32) (LENGTH (TAKE n s.vs_returndata)) s.vs_memory =
    TAKE n s.vs_returndata) /\
  64 + ((n + 31) DIV 32) * 32 < dimword (:256) /\ n < dimword (:256) /\
  ~flags.rcf_revert_on_failure /\ flags.rcf_max_outsize = n ==>
  frag_path ctx sa sb (\u. u = s)
    (\t. stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es0 sf s0 t /\
      t.vs_fmp = s.vs_fmp /\
      (!p. safe_operand sa p ==> eval_operand p t = eval_operand p s) /\
      expr_val_rel cx (raw_call_return_type flags)
        (if n = 0 then BoolV success else
          ArrayV (TupleV [BoolV success;BytesV (TAKE n s.vs_returndata)])) result t /\
      (0 < n ==> ?ti tw. sf.cs_next_id <= ti /\ ti < sb.cs_next_id /\
        eval_operand result t = SOME tw /\
        FLOOKUP t.vs_allocas ti = SOME (w2n tw,64 + ((n + 31) DIV 32) * 32) /\
        w2n tw + (64 + ((n + 31) DIV 32) * 32) < dimword (:256) /\
        val_in_memory (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))])
          (ArrayV (TupleV [BoolV success;BytesV (TAKE n s.vs_returndata)]))
          (w2n tw) t.vs_memory /\
        (!name lb lsz. local_region cenv es.scopes t name lb lsz ==>
          w2n tw + (64 + ((n + 31) DIV 32) * 32) <= lb \/ lb + lsz <= w2n tw))) (\r. F)
Proof
  strip_tac >> Cases_on `n = 0`
  >- (gvs[comp_return_def] >>
      irule frag_path_run_inst_seq >>
      simp[emitted_insts_def, run_inst_seq_def] >>
      simp[stmt_state_rel_inst_idx, raw_call_wb_frame_inst_idx, eval_operand_def, lookup_var_def] >>
      irule raw_call_bool_result >> simp[eval_operand_def, lookup_var_def]) >>
  `0 < n` by decide_tac >>
  `mem_bytes_at (w2n w + 32) (LENGTH (TAKE n s.vs_returndata)) s.vs_memory =
    TAKE n s.vs_returndata` by simp[] >>
  drule_all raw_call_nonrevert_positive_run >> strip_tac >>
  drule_all raw_call_nonrevert_suffix_code >> strip_tac >>
  irule frag_path_run_inst_seq >> simp[] >>
  simp[stmt_state_rel_inst_idx, raw_call_wb_frame_inst_idx] >>
  conj_tac
  >- (simp[expr_val_rel_def, raw_call_return_type_def, is_word_type_def,
           evaluate_type_def, eval_operand_def, lookup_var_def] >>
      qexists_tac `tw` >> fs[] >> rpt strip_tac >> gvs[AllCaseEqs()]) >>
  qexistsl_tac [`ti`,`tw`] >> fs[] >> rpt strip_tac >>
  first_x_assum irule >>
  fs[local_region_def, lookup_var_def] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem raw_call_values_outcome_bind[local]:
  gas_outcome memory tops (ctx,func)
    (a : evaluation_state -> value list evaluation_result) (es,s0) P E /\
  (!rr ee r. E rr ee r ==> ?exc. rr = INR exc /\ R (INR exc) ee r) /\
  (!rr ee t. P rr ee t ==> ?v. rr = INL v) /\
  (!gs v ee t. a (es with gas_obs := gs) = (INL v,ee) /\
     ee.gas_obs = [] /\ P (INL v) ee t ==>
     gas_outcome memory tops (ctx,func) (k v) (ee,t) Q R) ==>
  gas_outcome memory tops (ctx,func) (bind a k) (es,s0) Q R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_def])
  >- (gvs[gas_summary_at_def]
      >- (qpat_x_assum `!rr ee t. P rr ee t ==> _` drule >> strip_tac >> gvs[] >>
          `a (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
             (INL v, es_end with gas_obs := [])` by
            (fs[gas_marked_exec_def] >>
             first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
          qpat_x_assum `!gs v ee t. _ ==> gas_outcome _ _ _ _ _ _ _` drule >>
          simp[] >> disch_then drule >> strip_tac >>
          qpat_x_assum `gas_outcome _ _ _ _ _ _ _`
            (strip_assume_tac o REWRITE_RULE [gas_outcome_def])
          >- (fs[gas_summary_at_def] >>
              drule_all gas_marked_exec_bind_normal >> strip_tac >>
              simp[gas_outcome_def, gas_summary_at_def] >>
              metis_tac[]) >>
          simp[gas_outcome_def] >>
          qexists_tac `marks ++ marks'` >> disj2_tac >>
          fs[ignore_bind_def, bind_assoc] >>
          irule_at Any gas_exempt_cert_bind_values >>
          goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
      qpat_x_assum `!rr ee r. E rr ee r ==> _` drule >>
      strip_tac >> gvs[] >>
      simp[gas_outcome_def, gas_summary_at_def] >>
      qexists_tac `marks` >> disj1_tac >>
      qexistsl_tac [`INR exc`, `es_end`, `r`] >>
      conj_tac >- (irule gas_marked_exec_bind_exception >> goal_assum (drule_at Any)) >>
      simp[]) >>
  simp[gas_outcome_def] >> qexists_tac `marks` >> disj2_tac >>
  fs[ignore_bind_def, bind_assoc] >>
  irule_at Any gas_exempt_cert_error_values >>
  fs[ignore_bind_def] >> goal_assum (drule_at Any)
QED

Theorem raw_call_value_outcome_bind[local]:
  gas_outcome memory tops (ctx,func)
    (a : evaluation_state -> value evaluation_result) (es,s0) P E /\
  (!rr ee r. E rr ee r ==> ?exc. rr = INR exc /\ R (INR exc) ee r) /\
  (!rr ee t. P rr ee t ==> ?v. rr = INL v) /\
  (!gs v ee t. a (es with gas_obs := gs) = (INL v,ee) /\
     ee.gas_obs = [] /\ P (INL v) ee t ==>
     gas_outcome memory tops (ctx,func) (k v) (ee,t) Q R) ==>
  gas_outcome memory tops (ctx,func) (bind a k) (es,s0) Q R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_def])
  >- (gvs[gas_summary_at_def]
      >- (qpat_x_assum `!rr ee t. P rr ee t ==> _` drule >> strip_tac >> gvs[] >>
          `a (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
             (INL v, es_end with gas_obs := [])` by
            (fs[gas_marked_exec_def] >>
             first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
          qpat_x_assum `!gs v ee t. _ ==> gas_outcome _ _ _ _ _ _ _` drule >>
          simp[] >> disch_then drule >> strip_tac >>
          qpat_x_assum `gas_outcome _ _ _ _ _ _ _`
            (strip_assume_tac o REWRITE_RULE [gas_outcome_def])
          >- (fs[gas_summary_at_def] >>
              drule_all gas_marked_exec_bind_normal >> strip_tac >>
              simp[gas_outcome_def, gas_summary_at_def] >>
              metis_tac[]) >>
          simp[gas_outcome_def] >>
          qexists_tac `marks ++ marks'` >> disj2_tac >>
          fs[ignore_bind_def, bind_assoc] >>
          irule_at Any gas_exempt_cert_bind_value >>
          goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
      qpat_x_assum `!rr ee r. E rr ee r ==> _` drule >>
      strip_tac >> gvs[] >>
      simp[gas_outcome_def, gas_summary_at_def] >>
      qexists_tac `marks` >> disj1_tac >>
      qexistsl_tac [`INR exc`, `es_end`, `r`] >>
      conj_tac >- (irule gas_marked_exec_bind_exception >> goal_assum (drule_at Any)) >>
      simp[]) >>
  simp[gas_outcome_def] >> qexists_tac `marks` >> disj2_tac >>
  fs[ignore_bind_def, bind_assoc] >>
  irule_at Any gas_exempt_cert_error_value >>
  fs[ignore_bind_def] >> goal_assum (drule_at Any)
QED

Theorem raw_call_outcome_normal[local]:
  gas_outcome memory tops (ctx,func) a (es,s0) P E ==>
  gas_outcome memory tops (ctx,func) a (es,s0)
    (\res ee t. P res ee t /\ ~t.vs_halted) E
Proof
  simp[gas_outcome_def, gas_summary_at_def] >> strip_tac >>
  qexists_tac `marks` >>
  metis_tac[gas_marked_exec_def, fragGasModeTheory.gas_marked_path_exec,
            fragGasPathTheory.gas_path_normal]
QED

Theorem raw_call_typed_args_suffix[local]:
  typed_args_ready ctx func cenv cx arg_ty Inv args /\ Inv es /\
  (!es gs. Inv es ==> Inv (es with gas_obs := gs)) /\
  wb_args_shape cenv arg_ty args /\
  lower_word_args cenv arg_ty args sa = (xs,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!exc ee r. wb_args_exit (INR exc) r ==> R (INR exc) ee r) /\
  (!gs vs ee t.
     eval_exprs cx args (es with gas_obs := gs) = (INL vs,ee) /\
     ee.gas_obs = [] /\
     typed_args_post ctx func cenv cx es sa s0 ee args xs vs t /\ ~t.vs_halted /\
     t.vs_current_bb = sb.cs_current_bb /\
     t.vs_inst_idx = LENGTH sb.cs_current_insts ==>
     gas_outcome F (cx_tops cx) (ctx,func) (k vs) (ee,t) Q R) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (eval_exprs cx args) k) (es,s0) Q R
Proof
  strip_tac >> drule_all lower_typed_args_sim >>
  disch_then (mp_tac o MATCH_MP raw_call_outcome_normal) >> disch_tac >>
  irule raw_call_values_outcome_bind >> goal_assum (drule_at Any) >>
  conj_tac >- (rpt gen_tac >> Cases_on `rr` >> simp[wb_args_exit_def] >>
               metis_tac[wb_args_exit_def]) >>
  conj_tac >- (simp[] >> metis_tac[]) >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem raw_call_operand_suffix[local]:
  expr_sim ctx func cenv cx ty e es /\
  lower_value compile_expr cenv ty e sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!exc ee r. expr_exit (INR exc : value + exception) r ==> R (INR exc) ee r) /\
  (!gs v ee t.
     bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,ee) /\
     ee.gas_obs = [] /\ expr_post ctx func cenv cx e es sa sb s0 ee v op t /\
     ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
     t.vs_inst_idx = LENGTH sb.cs_current_insts ==>
     gas_outcome F (cx_tops cx) (ctx,func) (k v) (ee,t) Q R) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (bind (eval_expr cx e) (read_result cx)) k) (es,s0) Q R
Proof
  strip_tac >> fs[expr_sim_def] >>
  first_x_assum drule_all >>
  disch_then (mp_tac o MATCH_MP raw_call_outcome_normal) >> disch_tac >>
  irule raw_call_value_outcome_bind >> goal_assum (drule_at Any) >>
  conj_tac >- (rpt gen_tac >> Cases_on `rr` >>
               simp[expr_exit_def] >> metis_tac[expr_exit_def]) >>
  conj_tac >- (simp[] >> metis_tac[]) >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem raw_call_eval_args_action[local]:
  eval_exprs cx (a::d::kws) =
    bind (bind (eval_expr cx a) (read_result cx)) (\av.
    bind (bind (eval_expr cx d) (read_result cx)) (\dv.
    bind (eval_exprs cx kws) (\kvs. return (av::dv::kvs))))
Proof
  simp[Once evaluate_def] >> simp[Once evaluate_def] >>
  simp[bind_assoc, bind_return]
QED

Theorem raw_call_eval_action[local]:
  eval_expr cx (Call ann (RawCallTarget flags) (a::d::kws) dflt) =
    bind (bind (eval_expr cx a) (read_result cx)) (\av.
    bind (bind (eval_expr cx d) (read_result cx)) (\dv.
    bind (eval_exprs cx kws) (\kvs.
      do
        type_check (LENGTH (av::dv::kvs) = 2 + LENGTH flags.rcf_kws) "raw_call args";
        target <- lift_option_type (dest_AddressV av) "raw_call target";
        data <- lift_option_type (dest_BytesV dv) "raw_call data";
        amount <- lift_option_type (raw_call_value flags.rcf_kws kvs) "raw_call value";
        eval_raw_call cx flags target data amount
          (forwarded_gas default_evm_gas_limit (ext_call_kwarg EKGas flags.rcf_kws kvs))
      od)))
Proof
  simp[Once evaluate_def, raw_call_eval_args_action, bind_assoc, bind_return]
QED

(* Counted prefix consumer contract (source replacements are sequential):
   quantify gsA av esA tA gsD bs esD tD.  The address continuation receives
     bind (eval_expr cx a) (read_result cx) (es with gas_obs := gsA) =
       (INL av,esA), esA.gas_obs = [],
     expr_post ctx func cenv cx a es sa s1 s0 esA av addr tA;
   the data continuation receives
     bind (eval_expr cx d) (read_result cx) (esA with gas_obs := gsD) =
       (INL (BytesV bs),esD), esD.gas_obs = [],
     expr_post ctx func cenv cx d esA s1 s2 tA esD (BytesV bs) data tD.
   Each operand endpoint has current_bb/inst_idx aligned with s1 or s2;
   the live address fact is expr_val_rel cx (BaseT AddressT) av addr tD.
   The final premise is gas_outcome F (cx_tops cx) (ctx,func)
     (k av (BytesV bs)) (esD,tD) Q R, not gas_summary_at.

   Consumer mapping: raw_call_eval_action exposes the two forced-value
   binds for raw_call_value_outcome_bind.  Project data expr_post only
   after retaining the post and esA/tA/esD/tD witnesses.  At MLOAD/ADD,
   raw_call_addr_data_post supplies run_inst_seq, data pointer b, length,
   payload, bounds and frame.  raw_call_data_prefix_placement transports
   expr_val_at from tD through the same run; endpoint-index adjustment
   preserves it as in the old keywords Resume.  This retains the fresh
   allocation/local_region disjunction, not just the payload.  At the
   keyword boundary use raw_call_typed_args_suffix, preserving its Inv
   gas_obs stability premise.  Its typed_args_post supplies wb_frame to
   raw_call_kwargs_payload with es=esD, sd=s2, sk=s4; the transported
   expr_val_at and s2.next_id <= s4.next_id establish payload survival.
   The optional-GAS and oracle/output continuations must then construct
   a counted outcome.  No equation at the original gas_obs is inferred
   from the independent gsA/gsD replacement equations. *)

(* raw_call's data operand is a dynamic Bytes value (the lowering reads it
   as a memory pointer); RawCallCalldataTarget has no data operand. *)
Theorem raw_call_typed_data_dynamic[local]:
  well_typed_expr env (Call ty (RawCallTarget flags) args drv) ==>
  ?n. expr_type (EL 1 args) = BaseT (BytesT (Dynamic n))
Proof
  pure_rewrite_tac [well_typed_expr_def] >> strip_tac >>
  `1 < LENGTH args` by decide_tac >>
  fs[listTheory.EL_MAP]
QED

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
  ~flags.rcf_is_delegate /\
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
     byte_widths_expr_def, alloc_limits_expr_def,
     supportedExprTraverseTheory.supported_expr_exists_def,
     supportedExprTraverseTheory.supported_exprs_exists_every, EXISTS_MEM] >>
  imp_res_tac int_calls_exprs_every_mem >>
  gvs[supportedExprTraverseTheory.expr_has_evm_run_thm, listTheory.EXISTS_MEM] >>
  metis_tac[well_typed_exprs_member, byte_widths_exprs_mem,
            alloc_limits_exprs_mem, call_evaluation_safe_exprs_mem]
QED

(* Oracle execution after operand evaluation; keep adoption explicit so both
   the successful and failing source states are retained by consumers. *)

Theorem raw_call_kwargs_sim[local]:
  EVERY (\k. k = EKValue \/ k = EKGas) ks /\ LENGTH es = LENGTH ks /\
  typed_args_ready ctx func cenv cx (K (BaseT (UintT 256))) Inv es /\ Inv st /\
  (!ee gs. Inv ee ==> Inv (ee with gas_obs := gs)) /\
  wb_args_shape cenv (K (BaseT (UintT 256))) es /\
  compile_ext_call_kwargs compile_expr cenv NoneT ks es sa = ((vo,go,d),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx st s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx, func) (eval_exprs cx es) (st,s0)
    (\rr ee s. ?xs vs. rr = INL vs /\
       typed_args_post ctx func cenv cx st sa s0 ee es xs vs s /\
       vo = ext_call_kwarg EKValue ks xs /\
       go = ext_call_kwarg EKGas ks xs /\ d = NONE /\
       s.vs_current_bb = sb.cs_current_bb /\
       s.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\rr ee r. wb_args_exit rr r)
Proof
  strip_tac >> drule_all raw_call_kwargs_word_args >> strip_tac >>
  drule_all lower_typed_args_sim >>
  simp[gasOutcomeTheory.gas_outcome_def, gasSummaryTheory.gas_summary_at_def] >>
  metis_tac[]
QED

(* The failure copy needs no allocation-capacity or destination-end bound:
   it expands memory, and the exit judgment does not observe that memory. *)
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
  Cases_on `flags.rcf_revert_on_failure` >>
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
    (!name b sz. local_region cenv es.scopes t name b sz ==>
      regions_disjoint (w2n w) 0 b sz) /\
    (cenv.ce_is_ctor ==> !name tv v off.
      FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
      regions_disjoint off (type_memory_size tv) (w2n w) 0) /\
    (!x. ov = Var x ==> not_fresh_at sb x)
Proof
  simp[compile_raw_call_outbuf_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  drule_all buffer_alloc_code >> strip_tac >>
  `0 < dimword (:256)` by simp[] >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  qexistsl_tac [`t`, `w`] >> simp[wb_frame_def, locals_kept_def] >>
  fs[] >> conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >>
  qpat_assum `stmt_state_rel ctx func cenv cx es t` mp_tac >>
  pure_rewrite_tac[stmt_state_rel_def, immutable_alloca_sep_def] >> strip_tac >>
  qpat_x_assum `cenv.ce_is_ctor ==> _` drule >>
  disch_then drule_all >> strip_tac >>
  qpat_x_assum `!inst b sz. MEM inst _ /\ _ ==> _`
    (qspec_then `mk_inst sa.cs_next_id ALLOCA [Lit 0w]
      [STRING #"%" (toString sa.cs_next_var)]` mp_tac) >>
  fs[mk_inst_def]
QED

Theorem raw_call_zero_alloca_sep[local]:
  stmt_state_rel ctx func cenv cx es t /\
  FLOOKUP t.vs_allocas fresh = SOME (b,0) /\ cutoff <= fresh ==>
  !aid lb sz. aid < cutoff /\ FLOOKUP t.vs_allocas aid = SOME (lb,sz) ==>
    regions_disjoint b 0 lb sz
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `aid <> fresh` by decide_tac >>
  qpat_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def,
    venomMemDefsTheory.allocas_non_overlapping_def] >>
  strip_tac >> first_x_assum drule_all >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
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

Theorem raw_call_outbuf_positive_id_growth[local]:
  0 < cap /\ compile_raw_call_outbuf cap sa = ((ov,op),sm) ==>
  sa.cs_next_id < sm.cs_next_id
Proof
  strip_tac >> qpat_x_assum `compile_raw_call_outbuf _ _ = _` mp_tac >>
  simp[compile_raw_call_outbuf_def, contextTheory.compile_alloc_buffer_def,
    emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[]
QED

Theorem raw_call_outbuf_positive_code[local]:
  0 < cap /\ compile_raw_call_outbuf cap sa = ((ov,op),sm) ==>
  sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
  (!i. MEM i (emitted_insts sa sm) ==> ~is_terminator i.inst_opcode) /\
  MEM (mk_inst sa.cs_next_id ALLOCA
    [Lit (n2w (((cap+31) DIV 32)*32+32))]
    [STRING #"%" (toString sa.cs_next_var)]) (emitted_insts sa sm)
Proof
  strip_tac >> qpat_x_assum `compile_raw_call_outbuf _ _ = _` mp_tac >>
  simp[compile_raw_call_outbuf_def, contextTheory.compile_alloc_buffer_def,
    emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
  pure_rewrite_tac[emitted_insts_def] >> simp[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[rich_listTheory.DROP_LENGTH_APPEND, mk_inst_def, is_terminator_def] >>
  rpt strip_tac >> gvs[mk_inst_def, is_terminator_def]
QED

Theorem raw_call_outbuf_positive_straight[local]:
  0 < cap /\ compile_raw_call_outbuf cap sa = ((ov,op),sm) ==>
  sm.cs_blocks = sa.cs_blocks /\ sm.cs_current_bb = sa.cs_current_bb /\
  EVERY (\i. i.inst_opcode <> INVOKE) (emitted_insts sa sm)
Proof
  strip_tac >> qpat_x_assum `compile_raw_call_outbuf _ _ = _` mp_tac >>
  simp[compile_raw_call_outbuf_def, contextTheory.compile_alloc_buffer_def,
    emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
    fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
  pure_rewrite_tac[emitted_insts_def] >> simp[] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[rich_listTheory.DROP_LENGTH_APPEND, mk_inst_def]
QED

Theorem raw_call_outbuf_positive_labels[local]:
  0 < cap /\ compile_raw_call_outbuf cap sa = ((ov,op),sm) /\
  run_inst_seq (emitted_insts sa sm) s = OK t ==>
  t.vs_labels = s.vs_labels
Proof
  strip_tac >> drule_all raw_call_outbuf_positive_code >> strip_tac >>
  irule (BETA_RULE (Q.ISPEC `\s:venom_state. s.vs_labels` run_inst_seq_preserves_field)) >>
  qexists_tac `emitted_insts sa sm` >> simp[] >> rpt strip_tac >>
  `~is_terminator i.inst_opcode` by metis_tac[] >>
  drule_all venomInstProofs1Theory.step_inst_base_preserves_all >> simp[]
QED

(* Count the actual allocation instructions; retain the run endpoint so that
   allocation witnesses from either allocation theorem survive unchanged. *)
Theorem raw_call_outbuf_path[local]:
  compile_raw_call_outbuf cap sa = ((ov,op),sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  frag_path ctx sa sb (\u. u = s)
    (\u. u = t with vs_inst_idx := LENGTH sb.cs_current_insts) (\r. F)
Proof
  strip_tac >> irule frag_path_run_inst_seq >> simp[] >>
  Cases_on `cap = 0`
  >- (qpat_x_assum `compile_raw_call_outbuf _ _ = _` mp_tac >>
      simp[compile_raw_call_outbuf_def, contextTheory.compile_alloc_buffer_def,
        emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_id_def, fresh_var_def, emit_def] >> strip_tac >> gvs[] >>
      simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND,
        rich_listTheory.IS_PREFIX_APPEND, mk_inst_def, is_terminator_def]) >>
  `0 < cap` by decide_tac >>
  drule_all raw_call_outbuf_positive_code >> strip_tac >>
  drule_all raw_call_outbuf_positive_straight >> strip_tac >>
  fs[rich_listTheory.IS_PREFIX_APPEND, EVERY_MEM]
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
  `32 * ((cap + 31) DIV 32) + 32 < dimword(:256)` by fs[] >>
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
     qexists_tac `name` >> irule exprSimPropsTheory.local_region_frame >>
     conj_tac >- (qexists_tac `func` >> fs[stmt_state_rel_def, state_rel_def]) >>
     qexistsl_tac [`sm`, `es.scopes`, `final`] >> simp[]) >>
  qpat_x_assum `w2n w + _ < dimword(:256)` (assume_tac o SRULE []) >>
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

(* Common allocation interface for the two result policies.  In particular the
   zero-cap case still exposes its zero-sized ALLOCA, rather than erasing it. *)
Theorem raw_call_outbuf_alloc_path[local]:
  compile_raw_call_outbuf cap sa = ((ov,op),sb) /\
  (0 < cap ==> ((cap+31) DIV 32)*32+32 < dimword (:256)) /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ fn_has_code sa sb func ==>
  frag_path ctx sa sb (\u. u = s)
    (\u. stmt_state_rel ctx func cenv cx es u /\
      wb_frame cenv es sa s u /\ u.vs_memory = s.vs_memory /\
      (!p v. safe_operand sa p /\ eval_operand p s = SOME v ==>
        eval_operand p u = SOME v) /\
      (?w. eval_operand ov u = SOME w /\
        eval_operand op u = SOME (if cap = 0 then w else w+32w) /\
        FLOOKUP u.vs_allocas sa.cs_next_id =
          SOME (w2n w, if cap = 0 then 0 else ((cap+31) DIV 32)*32+32) /\
        w2n w + (if cap = 0 then 0 else ((cap+31) DIV 32)*32+32) < dimword (:256) /\
        (0 < cap ==> w2n (w+32w) = w2n w+32) /\
        (!name b sz. local_region cenv es.scopes u name b sz ==>
          regions_disjoint (w2n w) (if cap=0 then 0 else ((cap+31) DIV 32)*32+32) b sz) /\
        (cenv.ce_is_ctor ==> !name tv v off.
          FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
          FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
            | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
          regions_disjoint off (type_memory_size tv) (w2n w)
            (if cap=0 then 0 else ((cap+31) DIV 32)*32+32))) /\
      safe_operand sb ov /\ safe_operand sb op /\
      (!x. ov = Var x \/ op = Var x ==> not_fresh_at sb x)) (\r. F)
Proof
  strip_tac >> drule calldata_outbuf_operands >> strip_tac >>
  Cases_on `cap = 0`
  >- suspend "zero" >> suspend "positive"
QED

Resume raw_call_outbuf_alloc_path[zero]:
  gvs[] >> drule_all raw_call_outbuf_zero_run >> strip_tac >>
  drule_all raw_call_outbuf_path >>
  disch_then (qspec_then `ctx` (mp_then Any irule frag_path_conseq)) >> simp[] >>
  simp[stmt_state_rel_inst_idx, raw_call_wb_frame_inst_idx,
    instIdxIndepTheory.eval_op_inst_idx] >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `p` >>
      gvs[safe_operand_def, eval_operand_def] >>
      irule wb_frame_vars >> qexistsl_tac [`cenv`, `es`, `s`, `sa`] >> simp[]) >>
  gvs[local_region_def, lookup_var_def] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Resume raw_call_outbuf_alloc_path[positive]:
  `0 < cap` by decide_tac >>
  `((cap+31) DIV 32)*32+32 < dimword (:256)` by simp[] >>
  drule_all raw_call_outbuf_positive_run >> strip_tac >>
  drule_all raw_call_outbuf_path >>
  disch_then (qspec_then `ctx` (mp_then Any irule frag_path_conseq)) >> simp[] >>
  simp[stmt_state_rel_inst_idx, raw_call_wb_frame_inst_idx,
    instIdxIndepTheory.eval_op_inst_idx] >>
  conj_tac
  >- (rpt strip_tac >> Cases_on `p` >>
      gvs[safe_operand_def, eval_operand_def] >>
      irule wb_frame_vars >> qexistsl_tac [`cenv`, `es`, `s`, `sa`] >> simp[]) >>
  fs[local_region_def, lookup_var_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise raw_call_outbuf_alloc_path

Theorem raw_call_frame_footprint[local]:
  expr_sim_inv cenv cx env es /\
  expr_val_at cenv cx (BaseT (BytesT (Dynamic cap))) sa sb es (BytesV bs) op s /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic cap))) =
    SOME (BaseTV (BytesT (Dynamic cap))) /\
  eval_operand op s = SOME w /\ sb.cs_next_id <= sk.cs_next_id /\
  wb_frame cenv es sk s t ==>
  mem_bytes_at (w2n w) (val_footprint (BaseTV (BytesT (Dynamic cap))) (BytesV bs)) t.vs_memory =
  mem_bytes_at (w2n w) (val_footprint (BaseTV (BytesT (Dynamic cap))) (BytesV bs)) s.vs_memory
Proof
  strip_tac >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def, is_word_type_def] >> strip_tac >> gvs[]
  >- (fs[wb_frame_def] >>
      `aid < sk.cs_next_id` by decide_tac >>
      qpat_x_assum `!aid off sz. _ ==> mem_bytes_at _ _ _ = _` drule_all >>
      disch_then (mp_tac o cj 1 o MATCH_MP valueEncodingProofsTheory.mem_bytes_at_agree_window) >>
      disch_then (qspecl_then [`w2n w`, `val_footprint (BaseTV (BytesT (Dynamic cap))) (BytesV bs)`] mp_tac) >>
      simp[])
  >- (fs[wb_frame_def, locals_kept_def] >>
      qpat_x_assum `!n b sz off len. _ ==> _` irule >>
      qexistsl_tac [`b`, `n`, `sz`] >> simp[] >> rpt strip_tac >>
      `dynarray_free (BaseTV (BytesT (Dynamic cap)))` by
        simp[exprSimPropsTheory.dynarray_free_base] >>
      drule_all exprSimAttributeFieldsTheory.local_val_at_dynarray_apart >>
      decide_tac)
  >> simp[mem_bytes_at_def]
QED

Theorem raw_call_frame_bytes[local]:
  expr_sim_inv cenv cx env es /\
  expr_val_at cenv cx (BaseT (BytesT (Dynamic cap))) sa sb es (BytesV bs) op s /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic cap))) =
    SOME (BaseTV (BytesT (Dynamic cap))) /\
  eval_operand op s = SOME (n2w b) /\ b < dimword (:256) /\
  sb.cs_next_id <= sk.cs_next_id /\ wb_frame cenv es sk s t /\
  mem_bytes_at (b+32) (LENGTH bs) s.vs_memory = bs ==>
  mem_bytes_at (b+32) (LENGTH bs) t.vs_memory = bs
Proof
  strip_tac >>
  drule_all raw_call_frame_footprint >>
  simp[val_footprint_def, wordsTheory.w2n_n2w] >> strip_tac >>
  drule (cj 1 valueEncodingProofsTheory.mem_bytes_at_agree_window) >>
  disch_then (qspecl_then [`b+32`, `LENGTH bs`] mp_tac) >> simp[]
QED

Theorem raw_call_kwargs_payload[local]:
  expr_sim_inv cenv cx env es /\
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
     irule exprBopSimPropsTheory.eval_operand_frame >> simp[] >>
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

(* Legacy uncounted prefix proof retained while its consumers are ported.
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
*)

Theorem raw_call_addr_data_sim[local]:
  exprs_case nocalls ctx func cenv cx (a::d::kws) /\
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) dflt) es /\
  (nocalls ==> int_calls_expr (Call ann (RawCallTarget flags) (a::d::kws) dflt) = []) /\
  lower_value compile_expr cenv (BaseT AddressT) a sa = (addr,s1) /\
  lower_value compile_expr cenv (expr_type d) d s1 = (data,s2) /\
  fn_has_code sa s2 func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!exc ee r. expr_exit (INR exc : value + exception) r ==> R (INR exc) ee r) /\
  (!gsA av esA tA gsD bs esD tD.
    bind (eval_expr cx a) (read_result cx) (es with gas_obs := gsA) = (INL av,esA) /\
    esA.gas_obs = [] /\
    expr_post ctx func cenv cx a es sa s1 s0 esA av addr tA /\
    bind (eval_expr cx d) (read_result cx) (esA with gas_obs := gsD) =
      (INL (BytesV bs),esD) /\ esD.gas_obs = [] /\
    expr_post ctx func cenv cx d esA s1 s2 tA esD (BytesV bs) data tD /\
    ~tD.vs_halted /\ tD.vs_current_bb = s2.cs_current_bb /\
    tD.vs_inst_idx = LENGTH s2.cs_current_insts /\
    expr_sim_inv cenv cx env esD ==>
    gas_outcome F (cx_tops cx) (ctx,func) (k av (BytesV bs)) (esD,tD) Q R) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (bind (eval_expr cx a) (read_result cx)) (\av.
     bind (bind (eval_expr cx d) (read_result cx)) (k av))) (es,s0) Q R
Proof
  strip_tac >> drule raw_call_pre_operands >> strip_tac >> gvs[] >>
  `ci_mono sa s1 /\ ci_mono s1 s2` by
    (metis_tac[ci_mono_lower_value_cfn, compile_expr_ci_mono, pairTheory.SND]) >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func` by
    metis_tac[fn_has_code_split, ci_mono_def] >>
  `expr_body_pre cenv cx env a es` by
    (irule expr_body_pre_raw_call_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >>
     fs[expr_body_pre_def]) >>
  `nocalls ==> int_calls_expr a = []` by
    (fs[int_calls_expr_def] >> metis_tac[int_calls_exprs_mem, MEM]) >>
  `expr_sim ctx func cenv cx (BaseT AddressT) a es` by
    (fs[exprs_case_def, expr_sim_case_def] >> metis_tac[]) >>
  `gas_admissible (bind (eval_expr cx a) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  irule raw_call_operand_suffix >>
  qpat_assum `lower_value _ _ _ a sa = _` (irule_at Any) >> simp[] >>
  rpt strip_tac >> suspend "data"
QED

Resume raw_call_addr_data_sim[data]:
  `expr_body_pre cenv cx env a (es with gas_obs := gs)` by simp[] >>
  `expr_sim_inv cenv cx env ee` by
    (irule (cj 1 expr_body_pre_base_result) >>
     goal_assum (drule_at Any) >> simp[ETA_THM] >>
     qexists_tac `INL v` >> fs[bind_def]) >>
  `expr_body_pre cenv cx env d ee` by
    (irule expr_body_pre_raw_call_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
  `nocalls ==> int_calls_expr d = []` by
    (fs[int_calls_expr_def] >> metis_tac[int_calls_exprs_mem, MEM]) >>
  `exprs_case nocalls ctx func cenv cx (d::kws)` by
    (qpat_x_assum `bind _ _ (es with gas_obs := gs) = _` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> strip_tac >>
     fs[exprs_case_def] >> metis_tac[]) >>
  `expr_sim ctx func cenv cx (expr_type d) d ee` by
    (fs[exprs_case_def, expr_sim_case_def] >> metis_tac[]) >>
  `gas_admissible (bind (eval_expr cx d) (read_result cx)) expr_res_ok ee` by
    metis_tac[expr_body_pre_gas_admissible] >>
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> fs[ci_mono_def]) >>
  gvs[] >> irule raw_call_operand_suffix >>
  qpat_assum `lower_value _ _ _ d s1 = _` (irule_at Any) >>
  simp[] >> suspend "data_apply"
QED

Resume raw_call_addr_data_sim[data_apply]:
  simp[] >> reverse conj_tac >- fs[expr_post_def] >>
  rpt strip_tac >> suspend "values"
QED

Resume raw_call_addr_data_sim[values]:
  `expr_body_pre cenv cx env d (ee with gas_obs := gs')` by simp[] >>
  `expr_sim_inv cenv cx env ee'` by
    (irule (cj 1 expr_body_pre_base_result) >>
     goal_assum (drule_at Any) >> simp[] >>
     qexists_tac `INL v'` >> fs[bind_def]) >>
  `value_has_type (BaseTV (BytesT (Dynamic n))) v'` by
    (irule (cj 3 expr_body_pre_base_result) >>
     goal_assum (drule_at Any) >> simp[] >>
     qexists_tac `ee'` >> fs[bind_def]) >>
  Cases_on `v'` >> gvs[value_has_type_def] >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl_tac [`gs`, `gs'`] >> simp[]
QED

Finalise raw_call_addr_data_sim

Theorem raw_call_implicit_path_suffix[local]:
  gas_marked_path F ctx func s n (OK t) /\ es.gas_obs = [] /\
  gas_outcome F tops (ctx,func) k (es,t) Q R ==>
  gas_outcome F tops (ctx,func) k (es,s) Q R
Proof
  strip_tac >>
  `es with gas_obs := [] = es` by simp[evaluation_state_component_equality] >>
  `gas_marked_exec F (ctx,func) (return ()) (es,s) (REPLICATE n F) (INL ()) es (OK t)` by
    simp[gas_marked_exec_def, return_def] >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  simp[gas_outcome_def] >> strip_tac
  >- (fs[gas_summary_at_def] >>
      `gas_marked_exec F (ctx,func) (bind (return ()) (\u. k))
         (es,s) (REPLICATE n F ++ marks) res es_end r` by
        (irule gas_marked_exec_bind_normal >>
         qexistsl_tac [`es`, `t`, `()`] >> gvs[]) >>
      qexists_tac `REPLICATE n F ++ marks` >> disj1_tac >>
      fs[bind_return] >> simp[gas_summary_at_def] >> metis_tac[]) >>
  `gas_exempt_cert F tops (ctx,func)
     (bind (return ()) (\u. ignore_bind k (return ())))
     (es,s) (REPLICATE n F ++ marks) (err,ee) (leaf,finish')` by
    (irule gas_exempt_cert_bind_unit >>
     qexistsl_tac [`es`, `t`, `()`] >> simp[]) >>
  qexists_tac `REPLICATE n F ++ marks` >> disj2_tac >> fs[bind_return] >> metis_tac[]
QED

(* The bytes header read and pointer arithmetic have no GAS observations. *)
Theorem raw_call_data_path[local]:
  emit_op MLOAD [data] sd = (len,sl) /\
  emit_op ADD [data; Lit 32w] sl = (ptr_op,sm) /\
  fn_has_code sd sm func /\ ~u.vs_halted /\
  u.vs_current_bb = sd.cs_current_bb /\
  u.vs_inst_idx = LENGTH sd.cs_current_insts /\
  run_inst_seq (emitted_insts sd sm) u = OK t ==>
  gas_marked_path F ctx func u 0
    (OK (t with vs_inst_idx := LENGTH sm.cs_current_insts)) /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb
Proof
  strip_tac >>
  `sm.cs_current_bb = sd.cs_current_bb /\
   sm.cs_current_insts = sd.cs_current_insts ++ emitted_insts sd sm /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sd sm) /\
   FILTER (\i. i.inst_opcode = GAS) (emitted_insts sd sm) = []` by
    (qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
     qpat_x_assum `emit_op MLOAD _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
          fresh_id_def, fresh_var_def, emit_def] >>
     rpt strip_tac >> gvs[] >>
     `LENGTH sd.cs_current_insts - (LENGTH sd.cs_current_insts + 1) = 0` by decide_tac >>
     simp[emitted_insts_def, DROP_APPEND, is_terminator_def, mk_inst_def]) >>
  drule_all hash_run_path >> simp[]
QED

Theorem raw_call_optional_gas_path[local]:
  (case go of SOME g => (g,sa) | NONE => emit_op GAS [] sa) = (gas,sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  gas_marked_path F ctx func s (if IS_NONE go then 1 else 0)
    (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
  ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sb) /\
   LENGTH (FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb)) =
     (if IS_NONE go then 1 else 0)` by
    (qpat_x_assum `(case go of SOME g => (g,sa) | NONE => emit_op GAS [] sa) = (gas,sb)` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `go` >>
     simp[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
          fresh_id_def, fresh_var_def, emit_def] >>
     rpt strip_tac >> gvs[] >>
     simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND,
          is_terminator_def, mk_inst_def]) >>
  drule_all hash_run_path >> simp[]
QED

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
      qabbrev_tac `u = s with vs_gas_readings := DROP 1 s.vs_gas_readings` >>
      qabbrev_tac `t = update_var (STRING #"%" (toString sa.cs_next_var))
        (HD (s.vs_gas_readings ++ [0w])) u` >>
      `run_inst_seq (emitted_insts sa sb) s = OK t` by
        simp[Abbr `t`, Abbr `u`, run_inst_seq_def, step_inst_def, step_GAS] >>
      `!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s` by
        (simp[Abbr `t`, Abbr `u`, emitHelperPropsTheory.lookup_var_update_var,
              lookup_var_def] >>
         rpt strip_tac >> gvs[not_fresh_at_def]) >>
      `(t with vs_vars := u.vs_vars) = u` by simp[Abbr `t`, update_var_def] >>
      `stmt_state_rel ctx func cenv cx es t` by
        (irule hash_readonly_state_rel >> qexists_tac `u` >>
         simp[Abbr `u`, hash_gas_readings_state_rel] >>
         qexists_tac `sa` >> simp[lookup_var_def]) >>
      qexists_tac `t` >> simp[Abbr `t`, Abbr `u`, update_var_def, eval_operand_def,
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

(* Legacy fixed-result prefix retained during counted port.
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
  `expr_sim_inv cenv cx env es2` by fs[expr_body_pre_def] >>
  `evaluate_type (get_tenv cx) (expr_type d) = SOME (BaseTV (BytesT (Dynamic cap)))` by
    (drule_at (Pat `expr_body_pre _ _ _ d _`) expr_body_pre_type_evaluates >>
     simp[vyperValueTheory.evaluate_type_def]) >>
  drule_all hash_dynamic_post_view >> strip_tac >>
  `b < dimword (:256) /\ b' < dimword (:256)` by (fs[] >> decide_tac) >>
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
  `b < dimword(:256)` by fs[] >>
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

*)
Theorem raw_call_kwarg_mem[local]:
  !ks (ops : operand list) g.
    ext_call_kwarg key ks ops = SOME g ==> MEM g ops
Proof
  Induct_on `ks` >> Cases_on `ops` >>
  simp[ext_call_kwarg_def] >> rpt strip_tac >>
  rename1 `(if k = key then SOME op else _) = SOME g` >>
  Cases_on `k = key` >> gvs[] >> metis_tac[]
QED

(* Legacy prefix continuation.
Resume raw_call_prefix_sim[gas_run]:
  gvs[] >>
  `stmt_state_rel ctx func cenv cx es' t' /\ wb_frame cenv es2 s4 t t'` by
    fs[typed_args_post_def] >>
  `local_ptrs_reserved cenv s5` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `s4` >> simp[]) >>
  `!g. ext_call_kwarg EKGas flags.rcf_kws xs = SOME g ==>
       ?w. eval_operand g t' = SOME w` by
    (rpt strip_tac >>
     `MEM g xs` by metis_tac[raw_call_kwarg_mem] >>
     qpat_x_assum `typed_args_post _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[typed_args_post_def] >> strip_tac >>
     drule_all LIST_REL_MEM_IMP >> simp[] >> metis_tac[]) >>
  drule_all raw_call_optional_gas_run >> strip_tac >>
  suspend "gas_pack"
QED

Resume raw_call_prefix_sim[gas_pack]:
  `mem_bytes_at (b+32) (LENGTH bs) t.vs_memory = bs` by simp[] >>
  `b < dimword (:256)` by (fs[] >> decide_tac) >>
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
     `MEM g xs` by metis_tac[raw_call_kwarg_mem] >>
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
*)

Theorem raw_call_data_slice_placement[local]:
  expr_post ctx func cenv cx d esA s1 s2 tA esD (BytesV bs) data tD /\
  expr_type d = BaseT (BytesT (Dynamic cap)) /\
  evaluate_type (get_tenv cx) (expr_type d) = SOME (BaseTV (BytesT (Dynamic cap))) /\
  emit_op MLOAD [data] s2 = (len,s3) /\
  emit_op ADD [data; Lit 32w] s3 = (ptr_op,s4) /\
  (!x. data = Var x ==> not_fresh_at s2 x) /\ local_ptrs_reserved cenv s2 /\
  eval_operand data tD = SOME (n2w b) /\ b < dimword (:256) /\
  run_inst_seq (emitted_insts s2 s4) tD = OK t ==>
  expr_val_at cenv cx (BaseT (BytesT (Dynamic cap))) s1 s2 esD (BytesV bs) data
    (t with vs_inst_idx := idx) /\
  eval_operand data (t with vs_inst_idx := idx) = SOME (n2w b)
Proof
  strip_tac >> drule_all hash_dynamic_post_view >> strip_tac >>
  `b' < dimword (:256)` by decide_tac >>
  `b = b'` by
    (`(n2w b : bytes32) = n2w b'` by metis_tac[optionTheory.SOME_11] >>
     fs[wordsTheory.n2w_11] >> metis_tac[arithmeticTheory.LESS_MOD]) >>
  gvs[] >>
  `post_value_type cenv d = BaseT (BytesT (Dynamic cap))` by
    (`is_bytestring_type (expr_type d)` by simp[is_bytestring_type_def] >>
     drule post_value_type_bytestring >> simp[]) >>
  `expr_val_at cenv cx (BaseT (BytesT (Dynamic cap))) s1 s2 esD (BytesV bs) data tD` by
    fs[expr_post_def] >>
  `b < dimword (:256)` by (fs[] >> decide_tac) >>
  drule_all raw_call_data_prefix_placement >> strip_tac >>
  Cases_on `data` >>
  gvs[expr_val_at_def, eval_operand_def, lookup_var_def, local_region_def]
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
  fn_has_code sa s6 func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx func cenv cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!exc ee r. expr_exit (INR exc : value + exception) r ==> R (INR exc) ee r) /\
  (!gsA av esA tA gsD bs esD tD gsK kvs esK tm tk t xs b gw.
    bind (eval_expr cx a) (read_result cx) (es with gas_obs := gsA) =
      (INL av,esA) /\ esA.gas_obs = [] /\
    expr_post ctx func cenv cx a es sa s1 s0 esA av addr tA /\
    bind (eval_expr cx d) (read_result cx) (esA with gas_obs := gsD) =
      (INL (BytesV bs),esD) /\ esD.gas_obs = [] /\
    expr_post ctx func cenv cx d esA s1 s2 tA esD (BytesV bs) data tD /\
    eval_exprs cx kws (esD with gas_obs := gsK) = (INL kvs,esK) /\
    esK.gas_obs = [] /\ expr_sim_inv cenv cx env esK /\
    typed_args_post ctx func cenv cx esD s4 tm esK kws xs kvs tk /\
    vo = ext_call_kwarg EKValue flags.rcf_kws xs /\
    go = ext_call_kwarg EKGas flags.rcf_kws xs /\ ignored = NONE /\
    expr_val_rel cx (BaseT AddressT) av addr t /\
    (!op w. MEM op xs /\ eval_operand op tk = SOME w ==>
       eval_operand op t = SOME w) /\
    eval_operand len t = SOME (n2w (LENGTH bs)) /\
    eval_operand ptr_op t = SOME (n2w (b+32)) /\
    eval_operand gas t = SOME gw /\
    mem_bytes_at (b+32) (LENGTH bs) t.vs_memory = bs /\
    b+32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
    stmt_state_rel ctx func cenv cx esK t /\ wb_frame cenv es sa s0 t /\
    ~t.vs_halted /\ t.vs_current_bb = s6.cs_current_bb /\
    t.vs_inst_idx = LENGTH s6.cs_current_insts /\
    (!x. addr = Var x \/ len = Var x \/ ptr_op = Var x \/ gas = Var x \/
         MEM (Var x) xs ==> not_fresh_at s6 x) /\
    safe_operand s6 addr /\ safe_operand s6 len /\ safe_operand s6 ptr_op /\
    safe_operand s6 gas /\ safe_operand s6
      (case ext_call_kwarg EKValue flags.rcf_kws xs of NONE => Lit 0w | SOME v => v) ==>
    gas_outcome F (cx_tops cx) (ctx,func) (k av (BytesV bs) kvs) (esK,t) Q R) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (bind (eval_expr cx a) (read_result cx)) (\av.
     bind (bind (eval_expr cx d) (read_result cx)) (\dv.
     bind (eval_exprs cx kws) (k av dv)))) (es,s0) Q R
Proof
  strip_tac >>
  `ci_mono sa s1 /\ ci_mono s1 s2` by
    metis_tac[ci_mono_lower_value_cfn, compile_expr_ci_mono, pairTheory.SND] >>
  `ci_mono s2 s3 /\ ci_mono s3 s4` by
    metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  `cs_extends sa s4` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  drule raw_call_pre_flags >> strip_tac >>
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
  `ci_mono s5 s6` by
    (Cases_on `go` >> gvs[]
     >- metis_tac[ci_mono_emit_op, pairTheory.SND] >> simp[ci_mono_refl]) >>
  `cs_extends s4 s6` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sa s2 func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split, cs_extends_trans]) >>
  ho_match_mp_tac raw_call_addr_data_sim >>
  qpat_assum `lower_value _ _ _ a sa = _` (irule_at Any) >>
  qpat_assum `lower_value _ _ _ d s1 = _` (irule_at Any) >> simp[] >>
  rpt strip_tac >> suspend "data"
QED

Resume raw_call_prefix_sim[data]:
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> fs[ci_mono_def]) >>
  `expr_type a = BaseT AddressT /\
   ?cap. expr_type d = BaseT (BytesT (Dynamic cap))` by
    (drule raw_call_pre_operands >> simp[] >> metis_tac[]) >>
  `expr_body_pre cenv cx env a es` by
    (irule expr_body_pre_raw_call_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >>
     fs[expr_body_pre_def]) >>
  `safe_operand s1 addr` by
    (irule lower_value_word_safe_operand >>
     first_assum (irule_at (Pat `lower_value _ _ _ _ _ = _`)) >>
     qexists_tac `env` >>
     drule_at (Pat `expr_body_pre _ _ _ a _`) expr_body_pre_var_types_well_formed >>
     fs[expr_body_pre_def, is_word_type_def]) >>
  `(!x. addr = Var x ==> not_fresh_at s1 x) /\ (!l. addr <> Label l)` by
    fs[safe_operand_def] >>
  drule_all expr_post_operand_word >> strip_tac >>
  `expr_val_rel cx (BaseT AddressT) av addr tD` by
    (fs[expr_post_def, expr_val_rel_def] >>
     gvs[is_word_type_def, vyperValueTheory.evaluate_type_def]) >>
  `expr_body_pre cenv cx env d esD` by
    (irule expr_body_pre_raw_call_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
  `evaluate_type (get_tenv cx) (expr_type d) = SOME (BaseTV (BytesT (Dynamic cap)))` by
    (drule_at (Pat `expr_body_pre _ _ _ d _`) expr_body_pre_type_evaluates >>
     simp[vyperValueTheory.evaluate_type_def]) >>
  `!x. addr = Var x \/ data = Var x ==> not_fresh_at s2 x` by
    (rpt strip_tac
     >- (irule freshWritesTheory.not_fresh_at_mono >>
         qexists_tac `s1` >> fs[ci_mono_def]) >>
     metis_tac[compile_lower_value_var]) >>
  `local_ptrs_reserved cenv s2` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
     fs[ci_mono_def] >> decide_tac) >>
  drule_all raw_call_addr_data_post >> strip_tac >>
  suspend "data_path"
QED

Resume raw_call_prefix_sim[data_path]:
  `cs_extends s2 s4` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sa s4 func /\ fn_has_code s4 s6 func` by
    metis_tac[fn_has_code_split] >>
  `cs_extends sa s2` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code s2 s4 func` by metis_tac[fn_has_code_split] >>
  drule_all raw_call_data_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_marked_path F ctx func tD 0 (OK tm)` >>
  irule raw_call_implicit_path_suffix >>
  simp[] >> qexistsl_tac [`0`, `tm`] >> simp[] >>
  `exprs_case nocalls ctx func cenv cx kws` by
    (qpat_x_assum `bind _ _ (es with gas_obs := gsA) = _` mp_tac >>
     qpat_x_assum `bind _ _ (esA with gas_obs := gsD) = _` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> rpt strip_tac >>
     fs[exprs_case_def] >> metis_tac[]) >>
  suspend "keyword_setup"
QED

Resume raw_call_prefix_sim[keyword_setup]:
  drule_all raw_call_kwargs_ready >> strip_tac >>
  `wb_args_shape cenv (K (BaseT (UintT 256))) kws` by
    (irule typed_stack_args_shape >> qexistsl_tac [`cx`, `env`, `esD`] >>
     simp[] >> rpt gen_tac >> strip_tac >> conj_tac
     >- (irule expr_body_pre_raw_call_arg >>
         first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
     fs[EVERY_MEM, is_word_type_def]) >>
  `local_ptrs_reserved cenv s4` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
     fs[ci_mono_def] >> decide_tac) >>
  `fn_has_code s4 s5 func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split]) >>
  `stmt_state_rel ctx func cenv cx esD tm /\ ~tm.vs_halted /\
   tm.vs_current_bb = s4.cs_current_bb /\
   tm.vs_inst_idx = LENGTH s4.cs_current_insts` by
    simp[Abbr `tm`, stmt_state_rel_inst_idx] >>
  irule raw_call_typed_args_suffix >>
  qpat_assum `typed_args_ready _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `lower_word_args _ _ _ _ = _` (irule_at Any) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> fs[wb_args_exit_def] >> metis_tac[]) >>
  rpt strip_tac >> suspend "keyword_endpoint"
QED

Resume raw_call_prefix_sim[keyword_endpoint]:
  `expr_sim_inv cenv cx env (esD with gas_obs := gs)` by simp[] >>
  `expr_sim_inv cenv cx env ee` by
    (drule_all typed_args_ready_inv >> simp[]) >>
  `b < dimword (:256)` by (fs[] >> decide_tac) >>
  `!x. data = Var x ==> not_fresh_at s2 x` by simp[] >>
  `expr_val_at cenv cx (BaseT (BytesT (Dynamic cap))) s1 s2 esD (BytesV bs) data tm /\
   eval_operand data tm = SOME (n2w b)` by
    (simp[Abbr `tm`] >> drule_all raw_call_data_slice_placement >> simp[]) >>
  `mem_bytes_at (b+32) (LENGTH bs) tm.vs_memory = bs` by fs[Abbr `tm`] >>
  `s2.cs_next_id <= s4.cs_next_id` by (fs[ci_mono_def] >> decide_tac) >>
  `evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic cap))) =
    SOME (BaseTV (BytesT (Dynamic cap)))` by
    (qpat_x_assum `evaluate_type _ (expr_type d) = _` mp_tac >> simp[]) >>
  `mem_bytes_at (b+32) (LENGTH bs) t'.vs_memory = bs` by
    (drule_all raw_call_kwargs_payload >> simp[]) >>
  `stmt_state_rel ctx func cenv cx ee t' /\ wb_frame cenv esD s4 tm t'` by
    fs[typed_args_post_def] >>
  `local_ptrs_reserved cenv s5` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `s4` >> simp[]) >>
  `!g. go = SOME g ==> ?w. eval_operand g t' = SOME w` by
    (rpt strip_tac >>
     `MEM g xs` by metis_tac[raw_call_kwarg_mem] >>
     qpat_x_assum `typed_args_post _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[typed_args_post_def] >> strip_tac >>
     drule_all LIST_REL_MEM_IMP >> simp[] >> metis_tac[]) >>
  drule_all raw_call_optional_gas_run >> strip_tac >>
  suspend "optional_path"
QED

Resume raw_call_prefix_sim[optional_path]:
  `fn_has_code s5 s6 func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split, cs_extends_trans]) >>
  drule_all raw_call_optional_gas_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qabbrev_tac `tf = t'' with vs_inst_idx := LENGTH s6.cs_current_insts` >>
  irule raw_call_implicit_path_suffix >> simp[] >>
  qexistsl_tac [`if IS_NONE go then 1 else 0`,`tf`] >> simp[Abbr `tf`] >>
  suspend "final_endpoint"
QED

Resume raw_call_prefix_sim[final_endpoint]:
  `!x. not_fresh_at s4 x ==> not_fresh_at s5 x` by
    (fs[not_fresh_at_def] >> decide_tac) >>
  `!op w. (!x. op = Var x ==> not_fresh_at s4 x) /\
           (!l. op <> Label l) /\ eval_operand op tm = SOME w ==>
           eval_operand op t'' = SOME w` by
    (qpat_x_assum `wb_frame cenv esD s4 tm t'` mp_tac >>
     qpat_x_assum `wb_frame cenv ee s5 t' t''` mp_tac >>
     qpat_x_assum `!x. not_fresh_at s4 x ==> _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     Cases_on `op` >> gvs[eval_operand_def] >>
     fs[wb_frame_def] >> metis_tac[]) >>
  `!op w. MEM op xs /\ eval_operand op t' = SOME w ==>
          eval_operand op t'' = SOME w` by
    (qpat_x_assum `EVERY _ xs` mp_tac >>
     qpat_x_assum `wb_frame cenv ee s5 t' t''` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[EVERY_MEM] >> rpt strip_tac >>
     first_x_assum drule >> strip_tac >>
     Cases_on `op` >> gvs[eval_operand_def] >> metis_tac[wb_frame_vars]) >>
  suspend "frames"
QED

Resume raw_call_prefix_sim[frames]:
  `MAP FDOM es.scopes = MAP FDOM esA.scopes` by
    (qpat_x_assum `bind (eval_expr cx a) _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[bind_def, AllCaseEqs()] >> strip_tac >>
     imp_res_tac read_result_state >> gvs[] >>
     drule eval_expr_preserves_scopes_dom >> simp[]) >>
  `MAP FDOM esA.scopes = MAP FDOM esD.scopes` by
    (qpat_x_assum `bind (eval_expr cx d) _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[bind_def, AllCaseEqs()] >> strip_tac >>
     imp_res_tac read_result_state >> gvs[] >>
     drule eval_expr_preserves_scopes_dom >> simp[]) >>
  `MAP FDOM esD.scopes = MAP FDOM ee.scopes` by
    (drule eval_exprs_preserves_scopes_dom >> simp[]) >>
  `wb_frame cenv es sa s0 tA /\ wb_frame cenv esA s1 tA tD` by
    (qpat_x_assum `expr_post _ _ _ _ a _ _ _ _ _ _ _ _` mp_tac >>
     qpat_x_assum `expr_post _ _ _ _ d _ _ _ _ _ _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[expr_post_def, wb_frame_def] >>
     rpt strip_tac >> first_x_assum irule >> simp[] >> metis_tac[]) >>
  `wb_frame cenv es sa s0 tD` by
    (irule wb_frame_trans >> simp[] >> reverse conj_tac
     >- (goal_assum (drule_at Any)) >>
     qexistsl_tac [`esA`,`s1`,`tA`] >> fs[ci_mono_def]) >>
  suspend "frame_slice"
QED

Resume raw_call_prefix_sim[frame_slice]:
  `wb_frame cenv esD s2 tD tm` by
    (simp[Abbr `tm`, wb_frame_def, locals_kept_def, lookup_var_def] >>
     fs[wb_frame_def, locals_kept_def, lookup_var_def]) >>
  `wb_frame cenv es sa s0 tm` by
    (irule wb_frame_trans >> simp[] >> reverse conj_tac
     >- (goal_assum (drule_at Any)) >>
     qexistsl_tac [`esD`,`s2`,`tD`] >> fs[ci_mono_def] >> decide_tac) >>
  `wb_frame cenv es sa s0 t'` by
    (irule wb_frame_trans >> simp[] >> reverse conj_tac
     >- (goal_assum (drule_at Any)) >>
     qexistsl_tac [`esD`,`s4`,`tm`] >> fs[ci_mono_def] >> decide_tac) >>
  `wb_frame cenv es sa s0 t''` by
    (irule wb_frame_trans >> simp[] >> reverse conj_tac
     >- (goal_assum (drule_at Any)) >>
     qexistsl_tac [`ee`,`s5`,`t'`] >> fs[ci_mono_def] >> decide_tac) >>
  suspend "pack"
QED

Resume raw_call_prefix_sim[pack]:
  `safe_operand s3 len /\ safe_operand s4 ptr_op` by
    metis_tac[emit_op_safe_operand] >>
  `eval_operand len tm = SOME (n2w (LENGTH bs)) /\
   eval_operand ptr_op tm = SOME (n2w (b+32))` by
    simp[Abbr `tm`, eval_operand_def] >>
  `eval_operand len t'' = SOME (n2w (LENGTH bs)) /\
   eval_operand ptr_op t'' = SOME (n2w (b+32))` by
    (fs[safe_operand_def] >> metis_tac[]) >>
  `expr_val_rel cx (BaseT AddressT) av addr tm` by
    fs[Abbr `tm`, expr_val_rel_def, is_word_type_def, eval_operand_def] >>
  `expr_val_rel cx (BaseT AddressT) av addr t''` by
    (qpat_x_assum `expr_val_rel _ _ _ addr tm` mp_tac >>
     qpat_x_assum `!op w. (_ /\ _ /\ _) ==> _` mp_tac >>
     qpat_x_assum `!x. addr = Var x \/ len = Var x \/ ptr_op = Var x ==> _` mp_tac >>
     qpat_x_assum `!l. addr <> Label l` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[expr_val_rel_def, is_word_type_def] >> metis_tac[]) >>
  suspend "freshness"
QED

Resume raw_call_prefix_sim[freshness]:
  `!x. gas = Var x ==> not_fresh_at s6 x` by
    (qpat_x_assum `(case go of NONE => _ | SOME g => _) = _` mp_tac >>
     qpat_x_assum `go = ext_call_kwarg _ _ _` mp_tac >>
     qpat_x_assum `EVERY _ xs` mp_tac >>
     qpat_x_assum `ci_mono s5 s6` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     Cases_on `go` >> gvs[]
     >- metis_tac[emit_op_safe_operand, safe_operand_def] >>
     `MEM (Var x) xs` by metis_tac[raw_call_kwarg_mem] >>
     fs[EVERY_MEM] >> first_x_assum drule >> simp[]) >>
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
  suspend "safety"
QED

Resume raw_call_prefix_sim[safety]:
  `!l. gas <> Label l` by
    (qpat_x_assum `(case go of NONE => _ | SOME g => _) = _` mp_tac >>
     qpat_x_assum `go = ext_call_kwarg _ _ _` mp_tac >>
     qpat_x_assum `EVERY _ xs` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     Cases_on `go` >> gvs[]
     >- metis_tac[emit_op_safe_operand, safe_operand_def] >>
     `MEM (Label l) xs` by metis_tac[raw_call_kwarg_mem] >>
     fs[EVERY_MEM] >> first_x_assum drule >> simp[]) >>
  `safe_operand s6 addr /\ safe_operand s6 len /\ safe_operand s6 ptr_op /\
   safe_operand s6 gas` by
    (qpat_x_assum `!x. addr = Var x \/ len = Var x \/ ptr_op = Var x \/ gas = Var x \/ _ ==> _` mp_tac >>
     qpat_x_assum `!l. addr <> Label l` mp_tac >>
     qpat_x_assum `safe_operand s3 len` mp_tac >>
     qpat_x_assum `safe_operand s4 ptr_op` mp_tac >>
     qpat_x_assum `!l. gas <> Label l` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[safe_operand_def] >> metis_tac[]) >>
  `safe_operand s6 (case ext_call_kwarg EKValue flags.rcf_kws xs of
    NONE => Lit 0w | SOME v => v)` by
    (Cases_on `ext_call_kwarg EKValue flags.rcf_kws xs` >> simp[] >>
     `MEM x xs` by metis_tac[raw_call_kwarg_mem] >>
     fs[EVERY_MEM, safe_operand_def] >> metis_tac[]) >>
  suspend "continuation"
QED

Resume raw_call_prefix_sim[continuation]:
  qpat_x_assum `!gsA av esA tA gsD bs esD tD gsK kvs esK tm tk t xs b gw. _`
    irule >>
  simp[stmt_state_rel_inst_idx, eval_operand_def,
       expr_val_rel_def, is_word_type_def] >>
  conj_tac >- (qexists_tac `b` >> fs[]) >>
  conj_tac >- fs[expr_val_rel_def, is_word_type_def] >>
  conj_tac
  >- (qpat_x_assum `wb_frame cenv es sa s0 t''` mp_tac >>
      rpt (pop_assum kall_tac) >>
      simp[wb_frame_def, locals_kept_def, lookup_var_def] >> metis_tac[]) >>
  qexistsl_tac [`esA`,`esD`,`gsA`,`gsD`,`gs`,`tA`,`tD`,`t'`,`tm`,`xs`] >>
  simp[] >> first_x_assum ACCEPT_TAC
QED

Finalise raw_call_prefix_sim

(* Oracle tail, independent of the expression producing calldata. *)
Theorem raw_call_memory_oracle_exec[local]:
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
  VALID (drule_all_then
    (strip_assume_tac o Q.ISPECL [`gas:bytes32`, `ro:bytes32`, `rz:bytes32`])
    exec_ext_call_oracle_step) >>
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

(* Turn the parametric external-call equation into emitted code execution. *)
Theorem raw_call_emit_run:
  emit_op (if static_call then STATICCALL else CALL)
    (if static_call then [gas_op; to_op; ao_op; az_op; ro_op; rz_op]
     else [gas_op; to_op; val_op; ao_op; az_op; ro_op; rz_op]) sm = (ok_op,sb) /\
  eval_operand gas_op s = SOME gas /\ eval_operand to_op s = SOME aw /\
  eval_operand ao_op s = SOME ao /\ eval_operand az_op s = SOME az /\
  eval_operand ro_op s = SOME ro /\ eval_operand rz_op s = SOME rz /\
  (~static_call ==> eval_operand val_op s = SOME vw) /\
  (~static_call /\ s.vs_call_ctx.cc_static ==> vw = 0w) /\
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
  gvs[run_inst_seq_def, Once step_inst_base_def, mk_inst_def] >>
  Cases_on `s.vs_call_ctx.cc_static` >> gvs[]
QED

(* CALL and STATICCALL are straight-line counted instructions too. *)
Theorem raw_call_emit_path[local]:
  emit_op (if stat then STATICCALL else CALL) ops sa = (ok,sb) /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  frag_path ctx sa sb (\u. u = s)
    (\u. u = t with vs_inst_idx := LENGTH sb.cs_current_insts) (\r. F)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_same_blocks >> strip_tac >>
  irule frag_path_run_inst_seq >>
  Cases_on `stat` >>
  fs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND, mk_inst_def, is_terminator_def]
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

Theorem raw_call_oracle_stmt_frame[local]:
  take_call_outcome target calldata value_opt es = (INL (rq,outcome),es1) /\
  es' = SND (adopt_call_outcome rq outcome es1) /\
  stmt_state_rel ctx func cenv cx es s /\ state_rel func cenv cx es' t /\
  t.vs_vars = s.vs_vars /\ t.vs_allocas = s.vs_allocas /\
  t.vs_alloca_next = s.vs_alloca_next /\
  t.vs_fmp = s.vs_fmp /\ t.vs_labels = s.vs_labels ==>
  stmt_state_rel ctx func cenv cx es' t
Proof
  strip_tac >>
  `es'.scopes = es.scopes /\ es'.immutables = es.immutables` by
    (drule raw_call_take_adopt_fields >> simp[]) >>
  `immutable_base_zero cenv t` by
    (irule immutable_base_zero_frame >> qexists_tac `s` >>
     fs[stmt_state_rel_def, lookup_var_def]) >>
  irule stmt_state_rel_allocas_frame >> simp[] >>
  conj_tac
  >- (irule immutable_alloca_sep_fields >>
      qexistsl_tac [`s`,`es`] >> gvs[] >>
      reverse conj_tac >- fs[stmt_state_rel_def] >>
      simp[local_region_def, lookup_var_def] >> metis_tac[]) >>
  qexistsl_tac [`es`,`s`] >> simp[]
QED


(* The two new blocks are essential: the failure arm is not a linear prefix
   of the successful arm.  Leave the final length-store program packaged. *)


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
  drule_all (SRULE [] exprSimRawCallCalldataTheory.raw_call_cap_run) >>
  strip_tac >> qexists_tac `t` >>
  gvs[arithmeticTheory.MIN_COMM]
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
  `cap < dimword(:256) /\ LENGTH s.vs_returndata < dimword(:256)` by fs[] >>
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

Theorem raw_call_revert_inst_frag[local]:
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
    (irule (cj 1 exprSimRawCallCalldataTheory.raw_call_revert_copy) >>
     simp[Abbr `sizew`]) >>
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
    (irule raw_call_revert_inst_frag >> goal_assum (drule_at (Pat `emit_inst`)) >>
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
Theorem raw_call_finish_view_state_rel[local]:
  stmt_state_rel ctx func cenv cx es t /\
  raw_call_finish_view u = raw_call_finish_view t /\
  (!a w. eval_operand a t = SOME w ==> eval_operand a u = SOME w) ==>
  stmt_state_rel ctx func cenv cx es u
Proof
  strip_tac >>
  `!name entry p sz.
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    lookup_var p u = lookup_var p t` by
    (rpt strip_tac >>
     `?w. lookup_var p t = SOME w` by
       (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
        metis_tac[]) >>
     first_x_assum (qspecl_then [`Var p`, `w`] mp_tac) >>
     simp[eval_operand_def]) >>
  `!n b sz. local_region cenv es.scopes u n b sz =
              local_region cenv es.scopes t n b sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  qpat_x_assum `raw_call_finish_view _ = _` mp_tac >>
  simp[raw_call_finish_view_def, venom_state_component_equality] >> strip_tac >>
  `local_ptrs_rel func cenv es.scopes u` by
    (irule local_ptrs_rel_frame >> qexists_tac `t` >>
     simp[] >> fs[stmt_state_rel_def, state_rel_def] >>
     conj_tac >- first_assum ACCEPT_TAC >> rpt strip_tac >> gvs[]) >>
  `fmp_room ctx func u` by
    (irule fmp_room_fields >> qexists_tac `t` >> fs[stmt_state_rel_def]) >>
  `immutable_base_zero cenv u` by
    (fs[stmt_state_rel_def, immutable_base_zero_alt] >>
     rpt strip_tac >> first_x_assum drule >>
     rename1 `cenv.ce_imm_alloca = SOME operand` >>
     Cases_on `operand` >> simp[] >> strip_tac >>
     rename1 `FLOOKUP u.vs_vars x = SOME 0w` >>
     qpat_x_assum `!a w. eval_operand a t = SOME w ==> _`
       (qspec_then `Var x` mp_tac) >>
     simp[eval_operand_def, lookup_var_def]) >>
  `immutable_alloca_sep func cenv cx es u` by
    (irule immutable_alloca_sep_frame >> qexistsl_tac [`t`, `es`] >>
     fs[stmt_state_rel_def] >> metis_tac[]) >>
  fs[stmt_state_rel_def, state_rel_def, storage_rel_def, transient_rel_def,
    accounts_rel_def, logs_rel_def, immutables_rel_def, venomMemDefsTheory.alloca_inv_def,
    venomMemDefsTheory.allocas_non_overlapping_def,
    venomMemDefsTheory.alloca_next_valid_def, alloca_room_def,
    pending_alloca_size_def, immutable_alloca_sep_def,
    contract_storage_def, contract_transient_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem raw_call_finish_state_rel[local]:
  stmt_state_rel ctx func cenv cx es t /\
  (!a w. eval_operand a t = SOME w ==> eval_operand a u = SOME w) /\
  (if 0 < cap then
     raw_call_finish_view u = raw_call_finish_view (mstore (w2n addr) len t)
   else raw_call_finish_view u = raw_call_finish_view t) /\
  (0 < cap ==> ?inst b sz.
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) /\
    b <= w2n addr /\ w2n addr + 32 <= b + sz /\
    (!name lb lsz. local_region cenv es.scopes t name lb lsz ==>
       b + sz <= lb \/ lb + lsz <= b)) ==>
  stmt_state_rel ctx func cenv cx es u
Proof
  strip_tac >> Cases_on `0 < cap` >> fs[]
  >- (`stmt_state_rel ctx func cenv cx es (mstore (w2n addr) len t)` by
        (irule literal_mstore_state_rel >> simp[] >>
         qexistsl_tac [`b`, `inst`, `sz`] >> simp[] >> first_assum ACCEPT_TAC) >>
      irule raw_call_finish_view_state_rel >>
      qexists_tac `mstore (w2n addr) len t` >> simp[eval_operand_def, mstore_def]) >>
  irule raw_call_finish_view_state_rel >> qexists_tac `t` >> simp[]
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

(* Entry-age frames for arbitrary temporary-variable environments.  Operand
 * and state cleaning already use eval_operand_drop_fresh and
 * stmt_state_rel_drop_fresh; do not duplicate those exported boundaries. *)
Theorem raw_call_clean_operand_frame[local]:
  (!a w. (!x. a = Var x ==> not_fresh_at sa x) /\
    eval_operand a t = SOME w ==> eval_operand a u = SOME w) ==>
  !a w. eval_operand a (drop_fresh sa t) = SOME w ==>
    eval_operand a u = SOME w
Proof
  strip_tac >> Cases >> rpt strip_tac >>
  first_x_assum irule >>
  fs[eval_operand_def, lookup_var_def, drop_fresh_def,
    finite_mapTheory.FLOOKUP_DRESTRICT, IN_DEF]
QED

Theorem raw_call_clean_regions[local]:
  local_ptrs_reserved cenv sa ==>
  local_region cenv scopes (drop_fresh sa t) name b sz =
    local_region cenv scopes t name b sz
Proof
  strip_tac >> simp[local_region_def] >>
  eq_tac >> rpt strip_tac >> goal_assum (drule_at Any) >> simp[] >>
  `not_fresh_at sa p` by (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  fs[lookup_var_drop_fresh]
QED

Theorem raw_call_finish_state_rel_aged[local]:
  stmt_state_rel ctx func cenv cx es t /\ local_ptrs_reserved cenv sa /\
  (!a w. (!x. a = Var x ==> not_fresh_at sa x) /\
    eval_operand a t = SOME w ==> eval_operand a u = SOME w) /\
  (if 0 < cap then
     raw_call_finish_view u = raw_call_finish_view (mstore (w2n addr) len t)
   else raw_call_finish_view u = raw_call_finish_view t) /\
  (0 < cap ==> ?inst b sz.
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) /\
    b <= w2n addr /\ w2n addr + 32 <= b + sz /\
    (!name lb lsz. local_region cenv es.scopes t name lb lsz ==>
       b + sz <= lb \/ lb + lsz <= b)) ==>
  stmt_state_rel ctx func cenv cx es u
Proof
  strip_tac >>
  `!a w. eval_operand a (drop_fresh sa t) = SOME w ==>
    eval_operand a u = SOME w` by
    (qpat_x_assum `!a w. _ /\ eval_operand a t = SOME w ==> _`
       (mp_then Any mp_tac raw_call_clean_operand_frame) >> simp[]) >>
  irule raw_call_finish_state_rel >>
  qexistsl_tac [`addr`, `cap`, `len`, `drop_fresh sa t`] >>
  simp[stmt_state_rel_drop_fresh, raw_call_clean_regions] >>
  Cases_on `0 < cap` >> fs[raw_call_finish_view_def, drop_fresh_def, mstore_def] >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem raw_call_finish_frame_aged[local]:
  wb_frame cenv es st0 s0 t /\
  st0.cs_next_var <= sa.cs_next_var /\ local_ptrs_reserved cenv sa /\
  (!a w. (!x. a = Var x ==> not_fresh_at sa x) /\
    eval_operand a t = SOME w ==> eval_operand a u = SOME w) /\
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
  `wb_frame cenv es st0 s0 (drop_fresh sa t)` by
    (fs[wb_frame_def, locals_kept_def, drop_fresh_def] >>
     conj_tac
     >- (rpt strip_tac >>
         `not_fresh_at sa x` by
           (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `st0` >> simp[]) >>
         simp[lookup_var_def, finite_mapTheory.FLOOKUP_DRESTRICT, IN_DEF] >>
         metis_tac[lookup_var_def]) >>
     metis_tac[]) >>
  `!a w. eval_operand a (drop_fresh sa t) = SOME w ==>
    eval_operand a u = SOME w` by
    (qpat_x_assum `!a w. _ /\ eval_operand a t = SOME w ==> _`
       (mp_then Any mp_tac raw_call_clean_operand_frame) >> simp[]) >>
  irule raw_call_finish_frame >>
  qexistsl_tac [`addr`, `cap`, `len`, `drop_fresh sa t`] >> simp[] >>
  Cases_on `0 < cap` >> fs[raw_call_finish_view_def, drop_fresh_def, mstore_def] >>
  metis_tac[]
QED

Theorem raw_call_success_run_aged[local]:
  (do len <- emit_op RETURNDATASIZE [];
      cmp <- emit_op LT [len;Lit (n2w cap)];
      capped <- compile_select cmp len (Lit (n2w cap));
      emit_void MSTORE [ov;capped]; return ov od) sa = (result,sb) /\
  eval_operand ov s = SOME addr /\
  (!x. ov = Var x ==> not_fresh_at sa x) /\
  cap < dimword (:256) /\ LENGTH s.vs_returndata < dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    result = ov /\ eval_operand result t = SOME addr /\
    (!a w. (!x. a = Var x ==> not_fresh_at sa x) /\
      eval_operand a s = SOME w ==> eval_operand a t = SOME w) /\
    raw_call_finish_view t = raw_call_finish_view
      (mstore (w2n addr) (n2w (MIN (LENGTH s.vs_returndata) cap)) s)
Proof
  strip_tac >>
  `fresh_vars_wrt sa (drop_fresh sa s) /\
   eval_operand ov (drop_fresh sa s) = SOME addr /\
   LENGTH (drop_fresh sa s).vs_returndata < dimword (:256)` by
    (simp[fresh_vars_wrt_drop_fresh, eval_operand_drop_fresh, drop_fresh_def] >> fs[]) >>
  drule_all_then strip_assume_tac raw_call_success_run >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
     ~is_ext_call_op i.inst_opcode) (emitted_insts sa sb)` by
    suspend "code" >>
  `vars_ext_result (OK t) (run_inst_seq (emitted_insts sa sb) s)` by
    (qpat_x_assum `run_inst_seq _ _ = OK t` (fn th => rewrite_tac[GSYM th]) >>
     irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh]) >>
  fs[vars_ext_result_def] >>
  conj_tac >- suspend "value" >>
  conj_tac >- suspend "operands" >>
  suspend "view"
QED

Resume raw_call_success_run_aged[code]:
  qpat_x_assum `comp_bind _ _ _ = _` mp_tac >>
  simp[compile_select_def, comp_bind_def, emit_op_def, fresh_var_def,
       fresh_id_def, comp_ignore_bind_def, comp_return_def, emit_def,
       emit_void_def] >> strip_tac >> gvs[] >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  pure_rewrite_tac [rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[mk_inst_def, is_terminator_def, is_ext_call_op_def]
QED

Resume raw_call_success_run_aged[value]:
  rename1 `vars_ext clean actual` >>
  `eval_operand ov clean = SOME addr` by
    (gvs[] >> first_x_assum irule >> simp[]) >>
  qpat_x_assum `vars_ext clean actual` mp_tac >>
  pure_rewrite_tac[vars_ext_def] >> strip_tac >>
  qpat_x_assum `actual = _` (fn th => ONCE_REWRITE_TAC[th]) >>
  simp[eval_operand_vars_ext]
QED

Resume raw_call_success_run_aged[operands]:
  rpt strip_tac >> rename1 `vars_ext clean actual` >>
  `eval_operand a (drop_fresh sa s) = SOME w` by
    simp[eval_operand_drop_fresh] >>
  `eval_operand a clean = SOME w` by
    (gvs[] >> first_x_assum irule >> simp[]) >>
  qpat_x_assum `vars_ext clean actual` mp_tac >>
  pure_rewrite_tac[vars_ext_def] >> strip_tac >>
  qpat_x_assum `actual = _` (fn th => ONCE_REWRITE_TAC[th]) >>
  simp[eval_operand_vars_ext]
QED

Resume raw_call_success_run_aged[view]:
  gvs[vars_ext_def] >>
  qpat_x_assum `t' = _` (fn th => ONCE_REWRITE_TAC[th]) >>
  qpat_x_assum `u with vs_vars := FEMPTY = _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp[raw_call_finish_view_def, drop_fresh_def, mstore_def,
       venom_state_component_equality]
QED

Finalise raw_call_success_run_aged

(* Counted success suffix: no SETFMP is emitted by RawCallTarget. *)
Theorem raw_call_success_suffix_path[local]:
  (if 0 < n then
     do z <- emit_op RETURNDATASIZE [];
        cmp <- emit_op LT [z;Lit (n2w n)];
        cap <- compile_select cmp z (Lit (n2w n));
        emit_void MSTORE [ov;cap]; return ov od
   else return (Lit 0w)) sa = (result,sb) /\
  (0 < n ==> eval_operand ov s = SOME addr /\
    (!x. ov = Var x ==> not_fresh_at sa x)) /\
  n < dimword (:256) /\ LENGTH s.vs_returndata < dimword (:256) ==>
  frag_path ctx sa sb (\u. u = s)
    (\t. (!a w. (!x. a = Var x ==> not_fresh_at sa x) /\
          eval_operand a s = SOME w ==> eval_operand a t = SOME w) /\
      (if 0 < n then result = ov /\ eval_operand result t = SOME addr /\
         raw_call_finish_view t = raw_call_finish_view
           (mstore (w2n addr) (n2w (MIN (LENGTH s.vs_returndata) n)) s)
       else result = Lit 0w /\ eval_operand result t = SOME 0w /\
         raw_call_finish_view t = raw_call_finish_view s)) R
Proof
  strip_tac >> Cases_on `0 < n`
  >- (fs[] >> drule raw_call_success_code >> strip_tac >>
      `n < dimword (:256) /\ LENGTH s.vs_returndata < dimword (:256)` by fs[] >>
      drule_all raw_call_success_run_aged >> strip_tac >>
      irule frag_path_run_inst_seq >>
      fs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND] >>
      simp[raw_call_finish_view_control] >>
      gvs[eval_operand_def, lookup_var_def]) >>
  gvs[comp_return_def] >> irule frag_path_run_inst_seq >>
  simp[emitted_insts_def, run_inst_seq_def, raw_call_finish_view_control,
       instIdxIndepTheory.eval_op_inst_idx, eval_operand_def, lookup_var_def]
QED

Theorem raw_call_success_frag_aged[local]:
  (do len <- emit_op RETURNDATASIZE [];
      cmp <- emit_op LT [len;Lit (n2w cap)];
      capped <- compile_select cmp len (Lit (n2w cap));
      emit_void MSTORE [ov;capped]; return ov od) sa = (result,sb) /\
  eval_operand ov s = SOME addr /\
  (!x. ov = Var x ==> not_fresh_at sa x) /\
  cap < dimword (:256) /\ LENGTH s.vs_returndata < dimword (:256) ==>
  frag_exec ctx sa sb (\t. t = s)
    (\t. result = ov /\ eval_operand result t = SOME addr /\
      (!a w. (!x. a = Var x ==> not_fresh_at sa x) /\
        eval_operand a s = SOME w ==> eval_operand a t = SOME w) /\
      raw_call_finish_view t = raw_call_finish_view
        (mstore (w2n addr) (n2w (MIN (LENGTH s.vs_returndata) cap)) s)) R
Proof
  strip_tac >> drule raw_call_success_code >> strip_tac >>
  irule frag_exec_run_inst_seq >>
  fs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND] >>
  rpt strip_tac >> gvs[] >>
  `cap < dimword(:256) /\ LENGTH s.vs_returndata < dimword(:256)` by fs[] >>
  drule_all_then strip_assume_tac raw_call_success_run_aged >>
  disj1_tac >> goal_assum (drule_at Any) >>
  simp[raw_call_finish_view_control] >>
  gvs[eval_operand_def, lookup_var_def]
QED

Theorem raw_call_failure_prefix_frag_aged[local]:
  emit_op RETURNDATASIZE [] sa = (rds,sb) /\
  compile_alloc_buffer 0 sb = (buf,sc) /\ fn_has_code sa sc func /\
  stmt_state_rel ctx func cenv cx es s /\
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
  `fresh_vars_wrt sa (drop_fresh sa s) /\
   stmt_state_rel ctx func cenv cx es (drop_fresh sa s)` by
    simp[fresh_vars_wrt_drop_fresh, stmt_state_rel_drop_fresh] >>
  drule_all_then strip_assume_tac raw_call_failure_prefix >>
  `run_inst_seq (emitted_insts sa sc) (drop_fresh sa s) = OK u` by
    (irule run_emitted_compose2 >> qexistsl_tac [`t`,`sb`] >> simp[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
     ~is_ext_call_op i.inst_opcode) (emitted_insts sa sc)` by
    suspend "code" >>
  `vars_ext_result (OK u) (run_inst_seq (emitted_insts sa sc) s)` by
    (qpat_x_assum `run_inst_seq _ (drop_fresh sa s) = OK u`
       (fn th => rewrite_tac[GSYM th]) >>
     irule run_inst_seq_vars_ext >> simp[vars_ext_drop_fresh]) >>
  fs[vars_ext_result_def] >>
  irule frag_exec_run_inst_seq >>
  conj_tac >- suspend "post" >>
  suspend "shape"
QED

Resume raw_call_failure_prefix_frag_aged[code]:
  drule emitted_insts_emit_op >> strip_tac >>
  simp[emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[mk_inst_def, is_terminator_def, is_ext_call_op_def]
QED

Resume raw_call_failure_prefix_frag_aged[post]:
  rename1 `vars_ext clean actual` >>
  `eval_operand buf.buf_operand actual = SOME addr /\
   eval_operand rds actual = SOME (n2w (LENGTH s.vs_returndata)) /\
   actual.vs_returndata = s.vs_returndata` by
    (qpat_x_assum `vars_ext clean actual` mp_tac >>
     pure_rewrite_tac[vars_ext_def] >> strip_tac >>
     qpat_x_assum `actual = _` (fn th => ONCE_REWRITE_TAC[th]) >>
     simp[eval_operand_vars_ext] >> fs[drop_fresh_def]) >>
  rpt strip_tac >> gvs[] >> disj1_tac >>
  goal_assum (drule_at Any) >> qexists_tac `addr` >>
  gvs[eval_operand_def, lookup_var_def]
QED

Resume raw_call_failure_prefix_frag_aged[shape]:
  fs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND] >>
  fs[listTheory.EVERY_MEM] >> metis_tac[]
QED

Finalise raw_call_failure_prefix_frag_aged

Theorem raw_call_failure_frag_aged[local]:
  emit_op RETURNDATASIZE [] sa = (rds,sb) /\
  compile_alloc_buffer 0 sb = (buf,sc) /\
  emit_void RETURNDATACOPY [buf.buf_operand;Lit 0w;rds] sc = ((),sd) /\
  emit_inst REVERT [buf.buf_operand;rds] [] sd = ((),se) /\
  fn_has_code sa sc func /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  fn_inst_ids_distinct func /\ LENGTH s.vs_returndata < dimword (:256) /\
  (!t. t.vs_returndata = s.vs_returndata ==> R (Abort Revert_abort t)) ==>
  frag_exec ctx sa se (\t. t = s) Q R
Proof
  strip_tac >>
  drule_all_then (qspec_then `R` assume_tac) raw_call_failure_prefix_frag_aged >>
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

Theorem raw_call_oracle_emit_run_aged[local]:
  emit_op (if stat then STATICCALL else CALL)
    (if stat then [gas_op;to_op;dp;dl;op;Lit (n2w cap)]
     else [gas_op;to_op;val_op;dp;dl;op;Lit (n2w cap)]) sa = (ok,sb) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  eval_operand gas_op s = SOME gas /\ eval_operand to_op s = SOME aw /\
  eval_operand dp s = SOME ao /\ eval_operand dl s = SOME az /\
  eval_operand op s = SOME ro /\ eval_operand val_op s = SOME val_word /\
  w2w aw = target /\
  w2n (if stat then 0w else val_word) = (case value_opt of NONE => 0 | SOME n => n) /\
  stat = IS_NONE value_opt /\
  take_call_outcome target (read_memory (w2n ao) (w2n az) s) value_opt es =
    (INL (rq,outcome),es1) /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
    b + sz <= w2n ro \/ w2n ro + w2n (n2w cap : bytes32) <= b) /\
  (cenv.ce_is_ctor ==> !name tv v off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
    off + type_memory_size tv <= w2n ro \/
      w2n ro + w2n (n2w cap : bytes32) <= off) ==>
  ?t u. run_inst_seq (emitted_insts sa sb) s = OK u /\
    u = update_var (STRING #"%" (toString sa.cs_next_var))
      (bool_to_word outcome.co_success) t /\
    eval_operand ok u = SOME (bool_to_word outcome.co_success) /\
    stmt_state_rel ctx func cenv cx (SND (adopt_call_outcome rq outcome es1)) u /\
    t = s with <| vs_outcomes := t.vs_outcomes; vs_requests := t.vs_requests;
      vs_accounts := t.vs_accounts; vs_transient := t.vs_transient;
      vs_logs := t.vs_logs; vs_pending_deletions := t.vs_pending_deletions;
      vs_returndata := t.vs_returndata; vs_memory := t.vs_memory |> /\
    t.vs_memory = (write_memory_with_expansion (w2n ro)
      (TAKE (w2n (n2w cap : bytes32)) outcome.co_returnData) s).vs_memory /\
    t.vs_returndata = outcome.co_returnData /\
    mem_bytes_at (w2n ro)
      (LENGTH (TAKE (w2n (n2w cap : bytes32)) outcome.co_returnData)) t.vs_memory =
      TAKE (w2n (n2w cap : bytes32)) outcome.co_returnData
Proof
  strip_tac >>
  qmatch_asmsub_abbrev_tac `emit_op _ ops sa = (ok,sb)` >>
  qabbrev_tac `call_inst = mk_inst sa.cs_next_id (if stat then STATICCALL else CALL)
    ops [STRING #"%" (toString sa.cs_next_var)]` >>
  `call_inst.inst_outputs = [STRING #"%" (toString sa.cs_next_var)]` by
    simp[Abbr `call_inst`, mk_inst_def] >>
  drule_all_then (qspec_then `gas`
    (qx_choose_then `oracle_state` strip_assume_tac))
    (raw_call_memory_oracle_exec |> Q.INST
      [`inst` |-> `call_inst`, `vw` |-> `if stat then 0w else val_word`,
       `out` |-> `STRING #"%" (toString sa.cs_next_var)`,
       `rz` |-> `(n2w cap : bytes32)`]) >>
  `~s.vs_call_ctx.cc_static` by fs[stmt_state_rel_def, state_rel_def] >>
  `oracle_state.vs_vars = s.vs_vars /\ oracle_state.vs_allocas = s.vs_allocas /\
   oracle_state.vs_alloca_next = s.vs_alloca_next /\
   oracle_state.vs_fmp = s.vs_fmp /\ oracle_state.vs_labels = s.vs_labels` by
    (qpat_x_assum `oracle_state = _ with <| vs_outcomes := _; vs_requests := _;
       vs_accounts := _; vs_transient := _; vs_logs := _;
       vs_pending_deletions := _; vs_returndata := _; vs_memory := _ |>`
       (fn th => once_rewrite_tac[th]) >> simp[]) >>
  drule_all_then (qspec_then `bool_to_word outcome.co_success`
    (qx_choose_then `result_state` strip_assume_tac)) raw_call_result_frame >>
  suspend "result"
QED

Resume raw_call_oracle_emit_run_aged[result]:
  `run_inst_seq (emitted_insts sa sb) s = OK result_state` by
    (fs[Abbr `ops`] >> irule raw_call_emit_run >>
     goal_assum (drule_at (Pat `emit_op _ _ _ = _`)) >>
     simp[eval_operand_def] >> qexists_tac `val_word` >>
     gvs[Abbr `call_inst`, bool_to_word_def] >>
     Cases_on `outcome.co_success` >> simp[bool_to_word_def]) >>
  `stmt_state_rel ctx func cenv cx (SND (adopt_call_outcome rq outcome es1)) oracle_state` by
    (irule raw_call_oracle_stmt_frame >> simp[] >>
     goal_assum (drule_at (Pat `take_call_outcome _ _ _ _ = _`)) >>
     simp[] >> qexists_tac `s` >> simp[]) >>
  qexistsl_tac [`oracle_state`,`result_state`] >> simp[] >>
  qpat_assum `result_state = _` (fn th => once_rewrite_tac[th]) >>
  irule stmt_state_rel_update_var >> simp[] >>
  irule fresh_not_local_ptr >> qexists_tac `sa` >> simp[not_fresh_at_def]
QED

Finalise raw_call_oracle_emit_run_aged

Theorem raw_call_finish_frag_aged[local]:
  compile_raw_call_finish to_op dp dl gas_op val_op
    (if stat then StaticCall else RegularCall) cap T ov op sa = (result,sb) /\
  emit_op (if stat then STATICCALL else CALL)
    (if stat then [gas_op;to_op;dp;dl;op;Lit (n2w cap)]
     else [gas_op;to_op;val_op;dp;dl;op;Lit (n2w cap)]) sa = (ok,sc) /\
  run_inst_seq (emitted_insts sa sc) s = OK t /\
  eval_operand ok t = SOME (bool_to_word success) /\
  stmt_state_rel ctx func cenv cx es' t /\ local_ptrs_reserved cenv sa /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  cap < dimword (:256) /\ LENGTH t.vs_returndata < dimword (:256) /\
  (0 < cap ==> eval_operand ov t = SOME addr /\
    (!x. ov = Var x ==> not_fresh_at sa x)) ==>
  frag_exec ctx sa sb (\u. u = s)
    (\u. success /\
      (!a w. (!x. a = Var x ==> not_fresh_at sa x) /\
        eval_operand a t = SOME w ==> eval_operand a u = SOME w) /\
      (if 0 < cap then result = ov /\ eval_operand result u = SOME addr /\
         raw_call_finish_view u = raw_call_finish_view
           (mstore (w2n addr) (n2w (MIN (LENGTH t.vs_returndata) cap)) t)
       else result = Lit 0w /\ eval_operand result u = SOME 0w /\
         raw_call_finish_view u = raw_call_finish_view t))
    (\r. ?u. ~success /\ r = Abort Revert_abort u /\
      u.vs_returndata = t.vs_returndata)
Proof
  strip_tac >>
  drule exprSimRawCallCalldataTheory.raw_call_finish_revert_compile >>
  simp[arithmeticTheory.GREATER_DEF] >> strip_tac >>
  rename1 `compile_alloc_buffer 0 s6 = (buf,s7)` >>
  rename1 `fresh_label "call_ok" s2 = (kl,s3)` >>
  rename1 `fresh_label "call_failed" call_end = (fl,s2)` >>
  `call_end = sc /\ success' = ok` by (Cases_on `stat` >> gvs[]) >> gvs[] >>
  qpat_x_assum `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `(case _ of RegularCall => _ | DelegateCall => _ | StaticCall => _) = _` kall_tac >>
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

Resume raw_call_finish_frag_aged[extensions]:
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

Resume raw_call_finish_frag_aged[entry]:
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

Resume raw_call_finish_frag_aged[branches]:
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
  `sa.cs_next_var <= s5.cs_next_var /\ sa.cs_next_var <= s10.cs_next_var /\
   local_ptrs_reserved cenv s5` by suspend "ages" >>
  imp_res_tac new_block_props >>
  Cases_on `success` >> simp[instIdxIndepTheory.eval_op_inst_idx]
  >- suspend "success" >> suspend "failure"
QED

Resume raw_call_finish_frag_aged[ages]:
  imp_res_tac fresh_label_props >> imp_res_tac new_block_props >>
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
  `sa.cs_next_var <= s5.cs_next_var /\ sa.cs_next_var <= s10.cs_next_var` by decide_tac >>
  simp[] >> irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]
QED

Resume raw_call_finish_frag_aged[success]:
  Cases_on `0 < cap` >> fs[]
  >- suspend "positive" >> suspend "zero"
QED

Resume raw_call_finish_frag_aged[positive]:
  qmatch_goalsub_abbrev_tac `frag_exec ctx s10 sb (\u. u = entry) Q R` >>
  `eval_operand ov entry = SOME addr /\
   (!x. ov = Var x ==> not_fresh_at s10 x) /\
   LENGTH entry.vs_returndata < dimword (:256)` by
    (simp[Abbr `entry`, raw_call_control_operands, jump_to_def,
          instIdxIndepTheory.eval_op_inst_idx] >>
     rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `cap < dimword(:256)` by fs[] >>
  drule_all_then (qspecl_then [`ctx`,`R`] mp_tac) raw_call_success_frag_aged >>
  disch_then (mp_then Any irule frag_exec_weaken) >>
  simp[] >> rpt strip_tac >>
  `!a w. (!x. a = Var x ==> not_fresh_at sa x) /\
     eval_operand a t = SOME w ==> eval_operand a s'' = SOME w` by
    (rpt strip_tac >> first_x_assum irule >>
     simp[Abbr `entry`, raw_call_control_operands,
          instIdxIndepTheory.eval_op_inst_idx] >>
     rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  simp[Abbr `Q`] >>
  simp[raw_call_finish_view_def, mstore_def, Abbr `entry`, jump_to_def] >>
  simp[venom_state_component_equality]
QED

Resume raw_call_finish_frag_aged[zero]:
  fs[comp_return_def] >> gvs[] >>
  irule frag_exec_refl >>
  simp[Abbr `Q`, raw_call_control_operands,
       instIdxIndepTheory.eval_op_inst_idx,
       raw_call_finish_view_control, eval_operand_def]
QED

Resume raw_call_finish_frag_aged[failure]:
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
  `stmt_state_rel ctx func cenv cx es' entry /\
   LENGTH entry.vs_returndata < dimword (:256)` by
    simp[Abbr `entry`, raw_call_control_operands,
         stmt_state_rel_jump_to, stmt_state_rel_inst_idx, jump_to_def] >>
  irule frag_exec_exit_prefix >> qexists_tac `s9` >> simp[] >>
  irule raw_call_failure_frag_aged >>
  simp[Abbr `R`, Abbr `entry`, jump_to_def] >>
  qexistsl_tac [`cenv`,`cx`,`es'`,`func`] >>
  simp[stmt_state_rel_jump_to, stmt_state_rel_inst_idx] >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ (jump_to _ _)` mp_tac >>
  simp[jump_to_def]
QED

Finalise raw_call_finish_frag_aged

Theorem raw_call_revert_finish_path[local]:
  compile_raw_call_finish to_op dp dl gas_op val_op
    (if stat then StaticCall else RegularCall) n T ov op sa = (result,sb) /\
  emit_op (if stat then STATICCALL else CALL)
    (if stat then [gas_op;to_op;dp;dl;op;Lit (n2w n)]
     else [gas_op;to_op;val_op;dp;dl;op;Lit (n2w n)]) sa = (ok,sc) /\
  eval_operand ok s = SOME (if success then 1w else 0w) /\
  n < dimword (:256) /\ LENGTH s.vs_returndata < dimword (:256) /\
  (0 < n ==> eval_operand ov s = SOME addr /\
    (!x. ov = Var x ==> not_fresh_at sc x)) ==>
  frag_path ctx sc sb (\u. u = s)
    (\u. success /\
      (!a w. (!x. a = Var x ==> not_fresh_at sc x) /\
        eval_operand a s = SOME w ==> eval_operand a u = SOME w) /\
      (if 0 < n then result = ov /\ eval_operand result u = SOME addr /\
         raw_call_finish_view u = raw_call_finish_view
           (mstore (w2n addr) (n2w (MIN (LENGTH s.vs_returndata) n)) s)
       else result = Lit 0w /\ eval_operand result u = SOME 0w /\
         raw_call_finish_view u = raw_call_finish_view s))
    (\r. ?u. ~success /\ r = Abort Revert_abort u /\
       u.vs_returndata = s.vs_returndata)
Proof
  strip_tac >> drule raw_call_finish_revert_compile >>
  simp[arithmeticTheory.GREATER_DEF] >> strip_tac >>
  rename1 `fresh_label "call_failed" ce = (fl,s2)` >>
  rename1 `fresh_label "call_ok" s2 = (kl,s3)` >>
  `ce = sc /\ success' = ok` by (Cases_on `stat` >> gvs[]) >> gvs[] >>
  qpat_x_assum `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `(case _ of RegularCall => _ | DelegateCall => _ | StaticCall => _) = _` kall_tac >>
  qmatch_goalsub_abbrev_tac `frag_path ctx sc sb P Q R` >>
  `ci_mono sc s3 /\ ci_mono s3 s10 /\ cs_extends s5 s9 /\ cs_extends s10 sb` by
    suspend "metadata" >>
  `cs_extends sc s3 /\ cs_extends s3 sb` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  irule frag_path_seq >>
  qexistsl_tac [`\u. u = s with vs_inst_idx := LENGTH s3.cs_current_insts`,`s3`] >>
  simp[] >> conj_tac >- suspend "entry" >> suspend "branch"
QED

Resume raw_call_revert_finish_path[metadata]:
  `ci_mono sc s2 /\ ci_mono s2 s3 /\ ci_mono s3 s4 /\
   ci_mono s4 s5 /\ ci_mono s5 s6 /\ ci_mono s6 s7 /\
   ci_mono s7 s8 /\ ci_mono s8 s9 /\ ci_mono s9 s10` by
    (rpt conj_tac >> metis_tac[ci_mono_fresh_label, ci_mono_emit_inst,
      ci_mono_new_block, ci_mono_emit_op, ci_mono_compile_alloc_buffer,
      ci_mono_emit_void, pairTheory.SND]) >>
  `cs_extends s10 sb` by
    (Cases_on `0 < n` >> fs[comp_return_def]
     >- (drule raw_call_success_code >> strip_tac >>
         irule cs_extends_same_block >>
         fs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND]) >>
     gvs[] >> simp[cs_extends_refl]) >>
  fs[ci_mono_def] >> rpt conj_tac >> metis_tac[cs_extends_trans]
QED

Resume raw_call_revert_finish_path[entry]:
  imp_res_tac fresh_label_props >>
  irule frag_path_run_inst_seq >>
  simp[Abbr `P`, emitted_insts_def, run_inst_seq_def]
QED

Resume raw_call_revert_finish_path[branch]:
  irule raw_call_finish_branch_guarded_frag >>
  conj_tac >- simp[] >>
  goal_assum (drule_at (Pat `emit_inst JNZ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_inst REVERT _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_void RETURNDATACOPY _ _ = _`)) >>
  goal_assum (drule_at (Pat `compile_alloc_buffer _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_op RETURNDATASIZE _ _ = _`)) >>
  goal_assum (drule_at (Pat `new_block _ _ = _`)) >>
  goal_assum (drule_at (Pat `new_block _ _ = _`)) >>
  qexists_tac `success` >>
  simp[instIdxIndepTheory.eval_op_inst_idx, Abbr `R`] >>
  strip_tac >>
  qmatch_goalsub_abbrev_tac `frag_path ctx s10 sb (\u. u = entry) Q R` >>
  `sc.cs_next_var <= s10.cs_next_var` by fs[ci_mono_def] >>
  `n < dimword (:256) /\ LENGTH entry.vs_returndata < dimword (:256) /\
   (0 < n ==> eval_operand ov entry = SOME addr /\
     (!x. ov = Var x ==> not_fresh_at s10 x))` by
    (simp[Abbr `entry`, jump_to_def, instIdxIndepTheory.eval_op_inst_idx] >>
     rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sc` >> fs[]) >>
  drule_all raw_call_success_suffix_path >>
  disch_then (qspecl_then [`ctx`,`R`] assume_tac) >>
  irule frag_path_conseq >>
  goal_assum (drule_at (Pat `frag_path _ _ _ _ _ _`)) >>
  simp[] >> rpt strip_tac >>
  simp[Abbr `Q`] >> conj_tac
  >- (rpt strip_tac >> first_x_assum irule >>
      simp[Abbr `entry`, jump_to_def, instIdxIndepTheory.eval_op_inst_idx] >>
      rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
      qexists_tac `sc` >> simp[]) >>
  gvs[Abbr `entry`, raw_call_finish_view_def, jump_to_def, mstore_def]
QED

Finalise raw_call_revert_finish_path

Theorem raw_call_finish_related_frag_aged[local]:
  compile_raw_call_finish to_op dp dl gas_op val_op
    (if stat then StaticCall else RegularCall) cap T ov op sa = (result,sb) /\
  emit_op (if stat then STATICCALL else CALL)
    (if stat then [gas_op;to_op;dp;dl;op;Lit (n2w cap)]
     else [gas_op;to_op;val_op;dp;dl;op;Lit (n2w cap)]) sa = (ok,sc) /\
  run_inst_seq (emitted_insts sa sc) s = OK t /\
  eval_operand ok t = SOME (bool_to_word success) /\
  stmt_state_rel ctx func cenv cx es' t /\ local_ptrs_reserved cenv sa /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  cap < dimword (:256) /\ LENGTH t.vs_returndata < dimword (:256) /\
  wb_frame cenv es initial s0 t /\ initial.cs_next_var <= sa.cs_next_var /\
  (0 < cap ==> eval_operand ov t = SOME addr /\
    (!x. ov = Var x ==> not_fresh_at sa x) /\
    (?inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) /\
      b <= w2n addr /\ w2n addr + 32 <= b + sz /\
      (!name lb lsz. local_region cenv es'.scopes t name lb lsz ==>
        b + sz <= lb \/ lb + lsz <= b)) /\
    (!aid b sz. aid < initial.cs_next_id /\
      FLOOKUP t.vs_allocas aid = SOME (b,sz) ==>
      regions_disjoint (w2n addr) 32 b sz) /\
    (!name b sz. local_region cenv es.scopes s0 name b sz ==>
      regions_disjoint (w2n addr) 32 b sz)) ==>
  frag_exec ctx sa sb (\u. u = s)
    (\u. success /\ stmt_state_rel ctx func cenv cx es' u /\
      wb_frame cenv es initial s0 u /\
      (!a w. (!x. a = Var x ==> not_fresh_at sa x) /\
        eval_operand a t = SOME w ==> eval_operand a u = SOME w) /\
      (if 0 < cap then result = ov /\ eval_operand result u = SOME addr /\
         raw_call_finish_view u = raw_call_finish_view
           (mstore (w2n addr) (n2w (MIN (LENGTH t.vs_returndata) cap)) t)
       else result = Lit 0w /\ eval_operand result u = SOME 0w /\
         raw_call_finish_view u = raw_call_finish_view t))
    (\r. ?u. ~success /\ r = Abort Revert_abort u /\
      u.vs_returndata = t.vs_returndata)
Proof
  strip_tac >>
  `0 < cap ==> eval_operand ov t = SOME addr /\
     (!x. ov = Var x ==> not_fresh_at sa x)` by simp[] >>
  drule_all_then mp_tac raw_call_finish_frag_aged >>
  disch_then (mp_then Any irule frag_exec_weaken) >> simp[] >>
  rpt strip_tac >> rename1 `eval_operand result final = SOME _` >>
  `stmt_state_rel ctx func cenv cx es' final` by
    (irule (raw_call_finish_state_rel_aged |> INST_TYPE [alpha |-> ``:256``]) >>
     qexistsl_tac [`addr`, `cap`,
       `n2w (MIN (LENGTH t.vs_returndata) cap)`, `sa`, `t`] >>
     Cases_on `0 < cap` >> gvs[] >>
     rename1 `MEM alloc_inst (fn_insts func)` >>
     rename1 `FLOOKUP t.vs_allocas alloc_inst.inst_id = SOME (out_base,out_size)` >>
     qexistsl_tac [`alloc_inst`, `out_base`, `out_size`] >> simp[] >> first_assum ACCEPT_TAC) >>
  `wb_frame cenv es initial s0 final` by
    (irule (raw_call_finish_frame_aged |> INST_TYPE [alpha |-> ``:256``]) >>
     qexistsl_tac [`addr`, `cap`,
       `n2w (MIN (LENGTH t.vs_returndata) cap)`, `sa`, `t`] >>
     Cases_on `0 < cap` >> gvs[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp[] >> Cases_on `0 < cap` >> gvs[]
QED

Theorem raw_call_output_alloca_sep[local]:
  stmt_state_rel ctx func cenv cx es t /\
  FLOOKUP t.vs_allocas new_id = SOME (outbase:num,rounded + 32) /\
  cap <= rounded /\ initial.cs_next_id <= new_id ==>
  !aid b sz. aid < initial.cs_next_id /\
    FLOOKUP t.vs_allocas aid = SOME (b,sz) ==>
    loweringStateRelDefs$regions_disjoint outbase 32 b sz /\
    loweringStateRelDefs$regions_disjoint (outbase+32) cap b sz
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `aid <> new_id` by decide_tac >>
  `outbase + (rounded + 32) <= b \/ b + sz <= outbase` by
    (fs[stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def,
         venomMemDefsTheory.allocas_non_overlapping_def] >>
     metis_tac[]) >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem raw_call_output_local_sep[local]:
  (!name b sz. local_region cenv scopes t name b sz ==>
    loweringStateRelDefs$regions_disjoint outbase (rounded+32) b sz) /\ cap <= rounded ==>
  !name b sz. local_region cenv scopes t name b sz ==>
    loweringStateRelDefs$regions_disjoint outbase 32 b sz /\
    loweringStateRelDefs$regions_disjoint (outbase+32) cap b sz
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Theorem raw_call_oracle_frame[local]:
  wb_frame cenv es sa s0 s /\
  t.vs_vars = s.vs_vars /\ t.vs_allocas = s.vs_allocas /\
  t.vs_memory = (write_memory_with_expansion dst payload s).vs_memory /\
  (!aid b sz. aid < sa.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
    loweringStateRelDefs$regions_disjoint dst (LENGTH payload) b sz) /\
  (!name b sz. local_region cenv es.scopes s0 name b sz ==>
    loweringStateRelDefs$regions_disjoint dst (LENGTH payload) b sz) /\
  ~not_fresh_at sa out ==>
  wb_frame cenv es sa s0 (update_var out result t)
Proof
  strip_tac >>
  `!b sz. loweringStateRelDefs$regions_disjoint dst (LENGTH payload) b sz ==>
    mem_bytes_at b sz (update_var out result t).vs_memory =
    mem_bytes_at b sz s.vs_memory` by
    (rpt strip_tac >> simp[update_var_def] >>
     asm_rewrite_tac[] >> irule hash_write_memory_disjoint >>
     fs[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  fs[wb_frame_def] >> conj_tac
  >- (rpt strip_tac >> simp[lookup_var_def, update_var_def] >>
      `x <> out` by metis_tac[] >>
      simp[finite_mapTheory.FLOOKUP_UPDATE] >>
      fs[lookup_var_def]) >>
  conj_tac
  >- (rpt strip_tac >>
      `FLOOKUP s.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
      metis_tac[]) >>
  irule locals_kept_regions_tail >> qexists_tac `s` >> simp[] >>
  metis_tac[]
QED

Theorem raw_call_output_initial_locals[local]:
  wb_frame cenv es sa s0 t /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\ cap <= rounded /\
  (!name b sz. local_region cenv es'.scopes t name b sz ==>
    loweringStateRelDefs$regions_disjoint outbase (rounded+32) b sz) ==>
  !name b sz. local_region cenv es.scopes s0 name b sz ==>
    loweringStateRelDefs$regions_disjoint outbase 32 b sz /\
    loweringStateRelDefs$regions_disjoint (outbase+32) cap b sz
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `local_region cenv es'.scopes t name b sz` by
    (irule exprSimPropsTheory.local_region_frame_fwd >>
     qexistsl_tac [`s0`, `sa`, `es.scopes`] >> fs[wb_frame_def]) >>
  first_x_assum drule >> simp[loweringStateRelDefsTheory.regions_disjoint_def] >>
  decide_tac
QED

Theorem raw_call_oracle_zero_frame[local]:
  wb_frame cenv es sa s0 s /\ t.vs_vars = s.vs_vars /\
  t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
  ~not_fresh_at sa out ==>
  wb_frame cenv es sa s0 (update_var out result t)
Proof
  strip_tac >> irule wb_frame_readonly_tail >>
  qexistsl_tac [`sa`, `s`] >> simp[update_var_def] >>
  rpt strip_tac >> simp[lookup_var_def, update_var_def] >>
  `z <> out` by metis_tac[] >>
  simp[finite_mapTheory.FLOOKUP_UPDATE] >> fs[lookup_var_def]
QED

(* Policy-independent counted oracle instruction, preserving the incoming
   allocation metadata and the original expression's writeback frame. *)
Theorem raw_call_oracle_path[local]:
  emit_op (if stat then STATICCALL else CALL)
    (if stat then [gas_op;to_op;dp;dl;op;Lit (n2w cap)]
     else [gas_op;to_op;val_op;dp;dl;op;Lit (n2w cap)]) sa = (ok,sb) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  eval_operand gas_op s = SOME gas /\ eval_operand to_op s = SOME aw /\
  eval_operand dp s = SOME ao /\ eval_operand dl s = SOME az /\
  eval_operand op s = SOME ro /\ eval_operand val_op s = SOME val_word /\
  w2w aw = target /\
  w2n (if stat then 0w else val_word) = (case value_opt of NONE => 0 | SOME n => n) /\
  stat = IS_NONE value_opt /\
  take_call_outcome target (read_memory (w2n ao) (w2n az) s) value_opt es =
    (INL (rq,outcome),es1) /\ cap < dimword (:256) /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
    b + sz <= w2n ro \/ w2n ro + cap <= b) /\
  (cenv.ce_is_ctor ==> !name tv v off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
    off + type_memory_size tv <= w2n ro \/ w2n ro + cap <= off) /\
  wb_frame cenv initial_es initial s0 s /\ initial.cs_next_var <= sa.cs_next_var /\
  (!aid b sz. aid < initial.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
    loweringStateRelDefs$regions_disjoint (w2n ro) cap b sz) /\
  (!name b sz. local_region cenv initial_es.scopes s0 name b sz ==>
    loweringStateRelDefs$regions_disjoint (w2n ro) cap b sz) ==>
  frag_path ctx sa sb (\u. u = s)
    (\u. stmt_state_rel ctx func cenv cx (SND (adopt_call_outcome rq outcome es1)) u /\
      wb_frame cenv initial_es initial s0 u /\
      eval_operand ok u = SOME (bool_to_word outcome.co_success) /\
      u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp /\
      u.vs_returndata = outcome.co_returnData /\
      mem_bytes_at (w2n ro) (LENGTH (TAKE cap outcome.co_returnData)) u.vs_memory =
        TAKE cap outcome.co_returnData /\
      (!p. safe_operand sa p ==> eval_operand p u = eval_operand p s)) (\r. F)
Proof
  strip_tac >>
  drule_at (Pat `stmt_state_rel _ _ _ _ _ _`) raw_call_oracle_emit_run_aged >>
  disch_then (drule_at (Pat `emit_op _ _ _ = _`)) >>
  disch_then (drule_at (Pat `take_call_outcome _ _ _ _ = _`)) >>
  disch_then (qspecl_then [`val_word`, `ro`, `gas`, `aw`] mp_tac) >>
  impl_tac
  >- (fs[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `oracle` (qx_choose_then `u` strip_assume_tac)) >>
  suspend "frame"
QED

Resume raw_call_oracle_path[frame]:
  `oracle.vs_vars = s.vs_vars /\ oracle.vs_allocas = s.vs_allocas /\
   oracle.vs_fmp = s.vs_fmp` by
    (qpat_assum `oracle = _ with <| vs_outcomes := _; vs_requests := _;
       vs_accounts := _; vs_transient := _; vs_logs := _;
       vs_pending_deletions := _; vs_returndata := _; vs_memory := _ |>`
       (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `~not_fresh_at initial (STRING #"%" (toString sa.cs_next_var))` by
    simp[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
  `wb_frame cenv initial_es initial s0 u` by
    (qpat_assum `u = update_var _ _ oracle` (fn th => once_rewrite_tac[th]) >>
     irule raw_call_oracle_frame >> simp[] >>
     goal_assum (drule_at (Pat `wb_frame _ _ _ _ _`)) >>
     qexistsl_tac [`w2n ro`, `TAKE cap outcome.co_returnData`] >> simp[] >>
     conj_tac >> rpt gen_tac >> strip_tac >>
     first_x_assum (drule_all_then mp_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def, LENGTH_TAKE_EQ] >> decide_tac) >>
  suspend "post"
QED

Resume raw_call_oracle_path[post]:
  drule_all raw_call_emit_path >>
  disch_then (qspec_then `ctx` (mp_then Any irule frag_path_conseq)) >> simp[] >>
  simp[stmt_state_rel_inst_idx, raw_call_wb_frame_inst_idx,
       instIdxIndepTheory.eval_op_inst_idx] >>
  qpat_x_assum `u = update_var _ _ oracle` SUBST_ALL_TAC >>
  simp[update_var_def] >>
  gvs[] >> rpt strip_tac >>
  Cases_on `p` >> gvs[safe_operand_def, eval_operand_def, lookup_var_def,
    update_var_def, finite_mapTheory.FLOOKUP_UPDATE, not_fresh_at_def,
    ASCIInumbersTheory.toString_inj]
QED

Finalise raw_call_oracle_path

Theorem raw_call_allocated_tail_frag_aged[local]:
  compile_raw_call_finish to_op dp dl gas_op val_op
    (if stat then StaticCall else RegularCall) cap T ov op sa = (result,sb) /\
  emit_op (if stat then STATICCALL else CALL)
    (if stat then [gas_op;to_op;dp;dl;op;Lit (n2w cap)]
     else [gas_op;to_op;val_op;dp;dl;op;Lit (n2w cap)]) sa = (ok,sc) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  eval_operand gas_op s = SOME gas /\ eval_operand to_op s = SOME aw /\
  eval_operand dp s = SOME ao /\ eval_operand dl s = SOME az /\
  eval_operand op s = SOME ro /\ eval_operand val_op s = SOME val_word /\
  w2w aw = target /\
  w2n (if stat then 0w else val_word) = (case value_opt of NONE => 0 | SOME n => n) /\
  stat = IS_NONE value_opt /\
  take_call_outcome target (read_memory (w2n ao) (w2n az) s) value_opt es =
    (INL (rq,outcome),es1) /\
  cap < dimword (:256) /\ LENGTH outcome.co_returnData < dimword (:256) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  wb_frame cenv initial_es initial s0 s /\
  initial.cs_next_var <= sa.cs_next_var /\
  MAP FDOM es.scopes = MAP FDOM (SND (adopt_call_outcome rq outcome es1)).scopes /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
    b + sz <= w2n ro \/ w2n ro + cap <= b) /\
  (cenv.ce_is_ctor ==> !name tv v off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
    off + type_memory_size tv <= w2n ro \/ w2n ro + cap <= off) /\
  (!aid b sz. aid < initial.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
    loweringStateRelDefs$regions_disjoint (w2n ro) cap b sz) /\
  (!name b sz. local_region cenv initial_es.scopes s0 name b sz ==>
    loweringStateRelDefs$regions_disjoint (w2n ro) cap b sz) /\
  (0 < cap ==>
    eval_operand ov s = SOME addr /\
    (!x. ov = Var x ==> not_fresh_at sa x) /\
    (?inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
      b <= w2n addr /\ w2n addr + 32 <= b + sz /\
      (!name lb lsz. local_region cenv es.scopes s name lb lsz ==>
        b + sz <= lb \/ lb + lsz <= b)) /\
    (!aid b sz. aid < initial.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
      loweringStateRelDefs$regions_disjoint (w2n addr) 32 b sz) /\
    (!name b sz. local_region cenv initial_es.scopes s0 name b sz ==>
      loweringStateRelDefs$regions_disjoint (w2n addr) 32 b sz)) ==>
  frag_exec ctx sa sb (\u. u = s)
    (\u. outcome.co_success /\
      stmt_state_rel ctx func cenv cx (SND (adopt_call_outcome rq outcome es1)) u /\
      wb_frame cenv initial_es initial s0 u /\
      (?t. t.vs_allocas = s.vs_allocas /\
        mem_bytes_at (w2n ro) (LENGTH (TAKE cap outcome.co_returnData)) t.vs_memory =
          TAKE cap outcome.co_returnData /\
        (if 0 < cap then result = ov /\ eval_operand result u = SOME addr /\
           raw_call_finish_view u = raw_call_finish_view
             (mstore (w2n addr) (n2w (MIN (LENGTH outcome.co_returnData) cap)) t)
         else result = Lit 0w /\ eval_operand result u = SOME 0w /\
           raw_call_finish_view u = raw_call_finish_view t)))
    (\r. ?u. ~outcome.co_success /\ r = Abort Revert_abort u /\
      u.vs_returndata = outcome.co_returnData)
Proof
  strip_tac >>
  `?t u. run_inst_seq (emitted_insts sa sc) s = OK u /\
    u = update_var (STRING #"%" (toString sa.cs_next_var))
      (bool_to_word outcome.co_success) t /\
    eval_operand ok u = SOME (bool_to_word outcome.co_success) /\
    stmt_state_rel ctx func cenv cx (SND (adopt_call_outcome rq outcome es1)) u /\
    t = s with <| vs_outcomes := t.vs_outcomes; vs_requests := t.vs_requests;
      vs_accounts := t.vs_accounts; vs_transient := t.vs_transient;
      vs_logs := t.vs_logs; vs_pending_deletions := t.vs_pending_deletions;
      vs_returndata := t.vs_returndata; vs_memory := t.vs_memory |> /\
    t.vs_memory = (write_memory_with_expansion (w2n ro)
      (TAKE (w2n (n2w cap : bytes32)) outcome.co_returnData) s).vs_memory /\
    t.vs_returndata = outcome.co_returnData /\
    mem_bytes_at (w2n ro)
      (LENGTH (TAKE (w2n (n2w cap : bytes32)) outcome.co_returnData)) t.vs_memory =
      TAKE (w2n (n2w cap : bytes32)) outcome.co_returnData` by
    (irule raw_call_oracle_emit_run_aged >> gvs[] >>
     goal_assum (drule_at (Pat `emit_op _ _ _ = _`)) >> simp[] >>
     goal_assum (drule_at (Pat `take_call_outcome _ _ _ _ = _`)) >> simp[] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  suspend "frame"
QED

Resume raw_call_allocated_tail_frag_aged[frame]:
  map_every (fn p => qpat_x_assum p kall_tac)
    [`eval_operand gas_op s = _`, `eval_operand to_op s = _`,
     `eval_operand dp s = _`, `eval_operand dl s = _`,
     `eval_operand val_op s = _`, `w2w aw = target`,
     `w2n (if stat then _ else _) = _`, `stat = IS_NONE value_opt`,
     `take_call_outcome _ _ _ _ = _`, `cenv.ce_is_ctor ==> _`] >>
  `t.vs_vars = s.vs_vars /\ t.vs_allocas = s.vs_allocas /\
   t.vs_labels = s.vs_labels` by
    (qpat_assum `t = s with <| vs_outcomes := _; vs_requests := _;
       vs_accounts := _; vs_transient := _; vs_logs := _;
       vs_pending_deletions := _; vs_returndata := _; vs_memory := _ |>`
       (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `~not_fresh_at initial (STRING #"%" (toString sa.cs_next_var))` by
    simp[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
  `wb_frame cenv initial_es initial s0 u` by
    (qpat_assum `u = update_var _ _ t` (fn th => once_rewrite_tac[th]) >>
     irule raw_call_oracle_frame >> simp[] >>
     goal_assum (drule_at (Pat `wb_frame _ _ _ _ _`)) >>
     qexistsl_tac [`w2n ro`, `TAKE cap outcome.co_returnData`] >> simp[] >>
     conj_tac >> rpt gen_tac >> strip_tac >>
     first_x_assum (drule_all_then mp_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def, LENGTH_TAKE_EQ] >> decide_tac) >>
  suspend "finish"
QED

Resume raw_call_allocated_tail_frag_aged[finish]:
  `u.vs_allocas = s.vs_allocas /\ u.vs_returndata = outcome.co_returnData` by
    (qpat_assum `u = update_var _ _ t` (fn th => once_rewrite_tac[th]) >>
     simp[update_var_def]) >>
  `!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s` by
    (rpt strip_tac >>
     `x <> STRING #"%" (toString sa.cs_next_var)` by
       fs[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
     qpat_assum `u = update_var _ _ t` (fn th => once_rewrite_tac[th]) >>
     simp[lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE]) >>
  `!a w. (!x. a = Var x ==> not_fresh_at sa x) /\
    eval_operand a s = SOME w ==> eval_operand a u = SOME w` by
    (Cases >> simp[eval_operand_def] >> rpt strip_tac >>
     fs[eval_operand_def]) >>
  `!name b sz.
    local_region cenv (SND (adopt_call_outcome rq outcome es1)).scopes u name b sz ==>
    local_region cenv es.scopes s name b sz` by
    (rpt strip_tac >> irule exprSimPropsTheory.local_region_frame >>
     conj_tac >- (qexists_tac `func` >> fs[stmt_state_rel_def, state_rel_def]) >>
     goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
     qexists_tac `sa` >> simp[]) >>
  suspend "header"
QED

Resume raw_call_allocated_tail_frag_aged[header]:
  `u.vs_memory = t.vs_memory` by
    (qpat_assum `u = update_var _ _ t` (fn th => once_rewrite_tac[th]) >>
     simp[update_var_def]) >>
  qpat_x_assum `t = _ with <| vs_outcomes := _; vs_requests := _;
    vs_accounts := _; vs_transient := _; vs_logs := _;
    vs_pending_deletions := _; vs_returndata := _; vs_memory := _ |>` kall_tac >>
  qpat_assum `cap < dimword(:256)` (assume_tac o SRULE []) >>
  qpat_assum `LENGTH outcome.co_returnData < dimword(:256)` (assume_tac o SRULE []) >>
  `frag_exec ctx sa sb (\v. v = s)
    (\v. outcome.co_success /\
      stmt_state_rel ctx func cenv cx (SND (adopt_call_outcome rq outcome es1)) v /\
      wb_frame cenv initial_es initial s0 v /\
      (!a w. (!x. a = Var x ==> not_fresh_at sa x) /\
        eval_operand a u = SOME w ==> eval_operand a v = SOME w) /\
      (if 0 < cap then result = ov /\ eval_operand result v = SOME addr /\
        raw_call_finish_view v = raw_call_finish_view
          (mstore (w2n addr) (n2w (MIN (LENGTH u.vs_returndata) cap)) u)
       else result = Lit 0w /\ eval_operand result v = SOME 0w /\
         raw_call_finish_view v = raw_call_finish_view u))
    (\r. ?v. ~outcome.co_success /\ r = Abort Revert_abort v /\
      v.vs_returndata = u.vs_returndata)` by
    (irule raw_call_finish_related_frag_aged >> simp[] >>
     conj_tac
     >- (goal_assum (drule_at (Pat `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
         goal_assum (drule_at (Pat `emit_op _ _ _ = _`)) >> simp[] >>
         qpat_assum `u = update_var _ _ t` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
     suspend "header_regions") >>
  suspend "post"
QED

Resume raw_call_allocated_tail_frag_aged[header_regions]:
  strip_tac >>
  qpat_x_assum `0 < cap ==> _` mp_tac >> simp[] >> strip_tac >>
  simp[] >> conj_tac
  >- (goal_assum (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >> simp[] >>
      qpat_assum `u = update_var _ _ t` (fn th => rewrite_tac[GSYM th]) >>
      rpt strip_tac >>
      qpat_x_assum `!name b sz. local_region _ _ u _ _ _ ==> _` drule >>
      strip_tac >>
      qpat_x_assum `!name lb lsz. local_region _ _ _ name lb lsz ==> b + sz <= lb \/ _` drule >>
      simp[]) >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Resume raw_call_allocated_tail_frag_aged[post]:
  qpat_x_assum `frag_exec _ _ _ _ _ _` (mp_then Any irule frag_exec_weaken) >>
  rpt (qpat_x_assum `!x. _` kall_tac) >>
  qpat_x_assum `0 < cap ==> _` kall_tac >>
  qpat_x_assum `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `emit_op _ _ _ = _` kall_tac >>
  simp[] >> rpt strip_tac >> qexists_tac `u` >>
  simp[] >> Cases_on `0 < cap` >> gvs[]
QED

Finalise raw_call_allocated_tail_frag_aged

Theorem raw_call_none_post[local]:
  post_value_type cenv e = expr_type e /\
  expr_type e = NoneT /\ stmt_state_rel ctx func cenv cx es' s /\
  wb_frame cenv es sa s0 s ==>
  vv_post ctx func cenv cx e es sa sb s0 es' (Value NoneV)
    (StackValue ann (Lit 0w)) s
Proof
  strip_tac >> irule vv_post_frame_intro >>
  simp[vv_holds_def, vv_at_def, read_result_def, return_def,
    expr_val_rel_def, expr_val_at_def, eval_operand_def,
    vyperValueTheory.evaluate_type_def, is_word_type_def,
    val_in_memory_def, val_wf_def, val_footprint_def, type_memory_size_def] >>
  gvs[]
QED

Theorem raw_call_bool_post[local]:
  post_value_type cenv e = expr_type e /\
  expr_type e = BaseT BoolT /\
  stmt_state_rel ctx func cenv cx es' s /\
  expr_val_rel cx (expr_type e) (BoolV success) result s /\
  wb_frame cenv es sa s0 s ==>
  vv_post ctx func cenv cx e es sa sb s0 es' (Value (BoolV success))
    (StackValue ann result) s
Proof
  strip_tac >> irule vv_post_word_intro >>
  gvs[expr_val_rel_def, is_word_type_def]
QED

Theorem raw_call_tuple_post[local]:
  post_value_type cenv e = expr_type e /\
  expr_type e = TupleT [BaseT BoolT;BaseT (BytesT (Dynamic n))] /\
  evaluate_type (get_tenv cx) (expr_type e) =
    SOME (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))]) /\
  stmt_state_rel ctx func cenv cx es' s /\
  wb_frame cenv es sa s0 s /\
  eval_operand result s = SOME w /\
  FLOOKUP s.vs_allocas aid = SOME (w2n w,64 + ((n+31) DIV 32)*32) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  (!name lb lsz. local_region cenv es'.scopes s name lb lsz ==>
    w2n w + (64 + ((n+31) DIV 32)*32) <= lb \/ lb + lsz <= w2n w) /\
  val_in_memory (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))])
    (ArrayV (TupleV [BoolV success;BytesV (TAKE n bytes)])) (w2n w) s.vs_memory ==>
  vv_post ctx func cenv cx e es sa sb s0 es'
    (Value (ArrayV (TupleV [BoolV success;BytesV (TAKE n bytes)])))
    (LocatedValue (expr_type e) (mk_ptr result LocMemory)) s
Proof
  strip_tac >> irule vv_post_allocated_memory_intro >>
  qpat_assum `post_value_type _ _ = _`
    (fn th => simp[th, is_word_type_def, contextTheory.mk_ptr_def]) >>
  qexistsl_tac [`aid`,`w2n w`,`64 + ((n+31) DIV 32)*32`] >>
  simp[val_wf_def, LENGTH_TAKE_EQ, val_footprint_def, type_memory_size_def] >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum drule >> simp[arithmeticTheory.MULT_COMM]) >>
  simp[vfmConstantsTheory.word_size_def] >>
  qspec_then `n` mp_tac valueTypingMemoryPropsTheory.word_size_capacity >>
  simp[vfmConstantsTheory.word_size_def] >> decide_tac
QED

Theorem raw_call_nonrevert_vv_path[local]:
  post_value_type cenv e = expr_type e /\
  (if n > 0 then
       do z <- emit_op RETURNDATASIZE [];
          cmp <- emit_op LT [z;Lit (n2w n)];
          cap <- compile_select cmp z (Lit (n2w n));
          emit_void MSTORE [ov;cap];
          buf <- compile_alloc_buffer (64 + ((n + 31) DIV 32) * 32);
          emit_void MSTORE [buf.buf_operand;ok];
          dst <- emit_op ADD [buf.buf_operand;Lit 32w];
          emit_void MCOPY [dst;ov;Lit (n2w (32 + ((n + 31) DIV 32) * 32))];
          return buf.buf_operand od
     else return ok) sa = (result,sb) /\
  stmt_state_rel ctx func cenv cx es s /\ wb_frame cenv es0 sf s0 s /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  MEM alloc (fn_insts func) /\ alloc.inst_opcode = ALLOCA /\
  alloc.inst_outputs = [q] /\ not_local_ptr cenv es.scopes q /\
  FLOOKUP s.vs_allocas alloc.inst_id = SOME (w2n w,32 + ((n + 31) DIV 32) * 32) /\
  local_ptrs_reserved cenv sf /\ local_ptrs_reserved cenv sa /\
  sf.cs_next_var <= sa.cs_next_var /\ sf.cs_next_id <= alloc.inst_id /\
  alloc.inst_id < sa.cs_next_id /\ MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  safe_operand sa ov /\ safe_operand sa ok /\
  eval_operand ov s = SOME w /\ eval_operand ok s = SOME (if success then 1w else 0w) /\
  LENGTH s.vs_returndata < dimword (:256) /\
  (0 < n ==> mem_bytes_at (w2n w + 32) (LENGTH (TAKE n s.vs_returndata)) s.vs_memory =
    TAKE n s.vs_returndata) /\
  64 + ((n + 31) DIV 32) * 32 < dimword (:256) /\ n < dimword (:256) /\
  ~flags.rcf_revert_on_failure /\ flags.rcf_max_outsize = n /\
  expr_type e = raw_call_return_type flags /\
  (0 < n ==> evaluate_type (get_tenv cx) (expr_type e) =
    SOME (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))])) /\
  post_value_type cenv e = expr_type e ==>
  frag_path ctx sa sb (\u. u = s)
    (\t. vv_post ctx func cenv cx e es0 sf sb s0 es
      (Value (if n = 0 then BoolV success else
        ArrayV (TupleV [BoolV success;BytesV (TAKE n s.vs_returndata)])))
      (if n = 0 then StackValue ann result
       else LocatedValue (expr_type e) (mk_ptr result LocMemory)) t) (\r. F)
Proof
  strip_tac >> drule_all raw_call_nonrevert_no_restore_frag >>
  disch_then (mp_then Any irule frag_path_conseq) >> simp[] >>
  rpt strip_tac >> Cases_on `n = 0`
  >- (gvs[raw_call_return_type_def] >> irule raw_call_bool_post >> simp[]) >>
  `0 < n` by decide_tac >> fs[] >>
  qpat_assum `expr_type e = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  irule raw_call_tuple_post >>
  gvs[raw_call_return_type_def] >>
  qexists_tac `ti` >> simp[] >> first_assum ACCEPT_TAC
QED

Theorem raw_call_bytes_post[local]:
  post_value_type cenv e = expr_type e /\
  expr_type e = BaseT (BytesT (Dynamic cap)) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic cap))) /\
  cap <= rounded /\
  b < dimword (:256) /\
  raw_call_finish_view u =
    raw_call_finish_view (mstore b (n2w (MIN (LENGTH bytes) cap)) t) /\
  mem_bytes_at (b+32) (LENGTH (TAKE cap bytes)) t.vs_memory = TAKE cap bytes /\
  stmt_state_rel ctx func cenv cx es' u /\
  eval_operand result u = SOME (n2w b) /\
  FLOOKUP t.vs_allocas aid = SOME (b,rounded+32) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  (!n lb lsz. local_region cenv es'.scopes u n lb lsz ==>
     b + (rounded+32) <= lb \/ lb + lsz <= b) /\
  wb_frame cenv es sa s0 u ==>
  vv_post ctx func cenv cx e es sa sb s0 es' (Value (BytesV (TAKE cap bytes)))
    (LocatedValue (expr_type e) (mk_ptr result LocMemory)) u
Proof
  strip_tac >>
  `post_value_type cenv e = expr_type e` by
    (irule post_value_type_bytestring >> fs[is_bytestring_type_def]) >>
  `u.vs_memory = (mstore b (n2w (MIN (LENGTH bytes) cap)) t).vs_memory /\
   u.vs_allocas = t.vs_allocas` by
    (qpat_x_assum `raw_call_finish_view _ = _` mp_tac >>
     simp[raw_call_finish_view_def, venom_state_component_equality, mstore_def]) >>
  irule vv_post_allocated_memory_intro >>
  qpat_assum `post_value_type _ _ = _`
    (fn th => simp[th, is_word_type_def, contextTheory.mk_ptr_def]) >>
  qexistsl_tac [`aid`, `b`, `rounded+32`] >>
  simp[is_word_type_def, val_wf_def, LENGTH_TAKE_EQ, val_footprint_def,
    type_memory_size_def, contextTheory.mk_ptr_def, wordsTheory.w2n_n2w] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qspec_then `cap` mp_tac valueTypingMemoryPropsTheory.word_size_capacity >>
      simp[arithmeticTheory.MIN_DEF] >> decide_tac) >>
  drule exprSimRawCallCalldataTheory.raw_call_output_length_memory >>
  simp[mstore_def, write_memory_with_expansion_def, write_memory_def,
       expand_memory_def, arithmeticTheory.MIN_COMM]
QED

Theorem raw_call_outbuf_zero_tail_vv_path[local]:
  post_value_type cenv e = expr_type e /\
  cap = 0 /\ compile_raw_call_outbuf cap sa = ((ov,op),sm) /\
  compile_raw_call_finish to_op dp dl gas_op val_op
    (if stat then StaticCall else RegularCall) cap flags.rcf_revert_on_failure ov op sm = (result,sb) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ci_mono initial sa /\ wb_frame cenv initial_es initial s0 s /\
  stmt_state_rel ctx func cenv cx initial_es s0 /\ local_ptrs_reserved cenv initial /\
  MAP FDOM initial_es.scopes = MAP FDOM es.scopes /\
  eval_operand gas_op s = SOME gas /\ eval_operand to_op s = SOME aw /\
  eval_operand dp s = SOME ao /\ eval_operand dl s = SOME az /\ eval_operand val_op s = SOME val_word /\
  safe_operand sa to_op /\ safe_operand sa dp /\ safe_operand sa dl /\
  safe_operand sa gas_op /\ safe_operand sa val_op /\
  w2w aw = target /\
  w2n (if stat then 0w else val_word) = (case value_opt of NONE => 0 | SOME n => n) /\
  stat = IS_NONE value_opt /\
  take_call_outcome target (read_memory (w2n ao) (w2n az) s) value_opt es = (INL (rq,outcome),es1) /\
  MAP FDOM es.scopes = MAP FDOM (SND (adopt_call_outcome rq outcome es1)).scopes /\
  cap < dimword (:256) /\ LENGTH outcome.co_returnData < dimword (:256) /\
  (0 < cap ==> 64 + ((cap + 31) DIV 32) * 32 < dimword (:256)) /\
  flags.rcf_max_outsize = cap /\ expr_type e = raw_call_return_type flags /\
  (0 < cap ==> evaluate_type (get_tenv cx) (expr_type e) =
    SOME (if flags.rcf_revert_on_failure then BaseTV (BytesT (Dynamic cap))
      else TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic cap))])) /\
  post_value_type cenv e = expr_type e ==>
  frag_path ctx sa sb (\u. u = s)
    (\u. (flags.rcf_revert_on_failure ==> outcome.co_success) /\
      vv_post ctx func cenv cx e initial_es initial sb s0
        (SND (adopt_call_outcome rq outcome es1))
        (Value (if flags.rcf_revert_on_failure then
          if cap = 0 then NoneV else BytesV (TAKE cap outcome.co_returnData)
         else if cap = 0 then BoolV outcome.co_success
         else ArrayV (TupleV [BoolV outcome.co_success;BytesV (TAKE cap outcome.co_returnData)])))
        (if cap = 0 then StackValue ann result
         else LocatedValue (expr_type e) (mk_ptr result LocMemory)) u)
    (\r. ?u. flags.rcf_revert_on_failure /\ ~outcome.co_success /\
      r = Abort Revert_abort u /\ u.vs_returndata = outcome.co_returnData)
Proof
  strip_tac >>
  `ci_mono sa sm` by metis_tac[ci_mono_compile_raw_call_outbuf, pairTheory.SND] >>
  `ci_mono sm sb` by metis_tac[ci_mono_compile_raw_call_finish, pairTheory.SND] >>
  `cs_extends sa sm /\ cs_extends sm sb` by fs[ci_mono_def] >>
  drule_all fn_has_code_split >> strip_tac >>
  `0 < cap ==> ((cap+31) DIV 32)*32+32 < dimword (:256)` by
    (strip_tac >> qpat_x_assum `0 < cap ==> 64 + _ < _` drule >> decide_tac) >>
  qpat_assum `stmt_state_rel _ _ _ _ es s`
    (mp_then Any mp_tac raw_call_outbuf_alloc_path) >>
  disch_then drule_all >> strip_tac >>
  qmatch_asmsub_abbrev_tac `frag_path ctx sa sm _ Alloc _` >>
  irule frag_path_seq >> qexistsl_tac [`Alloc`,`sm`] >> simp[] >>
  conj_tac
  >- (irule frag_path_conseq >> goal_assum (drule_at (Pat `frag_path _ _ _ _ _ _`)) >> simp[]) >>
  irule frag_path_pointwise >> simp[Abbr `Alloc`] >> rpt strip_tac >>
  rename1 `stmt_state_rel ctx func cenv cx es t` >>
  qpat_x_assum `frag_path _ sa sm _ _ _` kall_tac >>
  qmatch_goalsub_abbrev_tac `frag_path ctx sm sb _ Post Exit` >>
  `wb_frame cenv initial_es initial s0 t` by
    (irule wb_frame_trans >> simp[] >> conj_tac
     >- (qexistsl_tac [`es`,`sa`,`s`] >> fs[ci_mono_def]) >>
     metis_tac[]) >>
  `eval_operand gas_op t = SOME gas /\ eval_operand to_op t = SOME aw /\
   eval_operand dp t = SOME ao /\ eval_operand dl t = SOME az /\
   eval_operand val_op t = SOME val_word` by metis_tac[] >>
  `take_call_outcome target (read_memory (w2n ao) (w2n az) t) value_opt es =
    (INL (rq,outcome),es1)` by fs[read_memory_def] >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> fs[ci_mono_def]) >>
  suspend "oracle"
QED

Resume raw_call_outbuf_zero_tail_vv_path[oracle]:
  Cases_on `emit_op (if stat then STATICCALL else CALL)
    (if stat then [gas_op;to_op;dp;dl;op;Lit (n2w cap)]
     else [gas_op;to_op;val_op;dp;dl;op;Lit (n2w cap)]) sm` >>
  rename1 `emit_op _ _ sm = (ok,sc)` >>
  `ci_mono sm sc` by metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  fs[] >>
  `initial.cs_next_id <= sa.cs_next_id /\ initial.cs_next_var <= sm.cs_next_var` by
    (fs[ci_mono_def] >> decide_tac) >>
  qpat_assum `stmt_state_rel _ _ _ _ es t`
    (mp_then Any mp_tac raw_call_zero_alloca_sep) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  disch_then (qspec_then `initial.cs_next_id` mp_tac) >> simp[] >> strip_tac >>
  `!name b sz. local_region cenv initial_es.scopes s0 name b sz ==>
    regions_disjoint (w2n w) 0 b sz` by
    (rpt strip_tac >>
     `local_region cenv es.scopes t name b sz` by
       (irule exprSimPropsTheory.local_region_frame_fwd >>
        qexistsl_tac [`s0`,`initial`,`initial_es.scopes`] >>
        fs[wb_frame_def]) >>
     metis_tac[]) >>
  suspend "call"
QED

Resume raw_call_outbuf_zero_tail_vv_path[call]:
  gvs[] >>
  qpat_assum `stmt_state_rel _ _ _ _ es t`
    (mp_then Any mp_tac raw_call_oracle_path) >>
  disch_then (drule_at (Pat `emit_op _ _ _ = _`)) >>
  disch_then (drule_at (Pat `take_call_outcome _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `wb_frame _ _ _ _ _`)) >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >>
  disch_then (qspecl_then [`val_word`,`gas`,`aw`] mp_tac) >>
  impl_tac >- (fs[loweringStateRelDefsTheory.regions_disjoint_def] >>
    rpt conj_tac >> metis_tac[]) >>
  strip_tac >>
  `cs_extends sm sc` by fs[ci_mono_def] >>
  qmatch_asmsub_abbrev_tac `frag_path ctx sm sc _ OraclePost _` >>
  match_mp_tac frag_path_seq >> qexistsl_tac [`sc`,`OraclePost`] >>
  conj_tac
  >- (irule frag_path_conseq >>
      goal_assum (drule_at (Pat `frag_path _ _ _ _ _ _`)) >> simp[]) >>
  conj_tac
  >- (irule frag_path_pointwise >> simp[Abbr `OraclePost`] >> rpt strip_tac >>
      rename1 `eval_operand ok u = SOME _` >> suspend "finish") >>
  simp[] >> suspend "call_metadata"
QED

Resume raw_call_outbuf_zero_tail_vv_path[call_metadata]:
  qpat_x_assum `emit_op _ _ sm = _` mp_tac >>
  qpat_x_assum `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  Cases_on `value_opt = NONE` >> fs[] >>
  Cases_on `flags.rcf_revert_on_failure` >>
  gvs[compile_raw_call_finish_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> simp[cs_extends_refl] >>
  rename1 `fresh_label "call_failed" sc = (fl,s2)` >>
  rename1 `fresh_label "call_ok" s2 = (kl,s3)` >>
  rename1 `emit_inst JNZ _ _ s3 = ((),s4)` >>
  rename1 `new_block fl s4 = (_,s5)` >>
  rename1 `emit_op RETURNDATASIZE [] s5 = (_,s6)` >>
  rename1 `compile_alloc_buffer 0 s6 = (_,s7)` >>
  rename1 `emit_void RETURNDATACOPY _ s7 = ((),s8)` >>
  rename1 `emit_inst REVERT _ _ s8 = ((),s9)` >>
  rename1 `new_block kl s9 = (_,s10)` >>
  `ci_mono sc s2 /\ ci_mono s2 s3 /\ ci_mono s3 s4 /\
   ci_mono s4 s5 /\ ci_mono s5 s6 /\ ci_mono s6 s7 /\
   ci_mono s7 s8 /\ ci_mono s8 s9 /\ ci_mono s9 s10` by
    (rpt conj_tac >> metis_tac[ci_mono_fresh_label, ci_mono_emit_inst,
      ci_mono_new_block, ci_mono_emit_op, ci_mono_compile_alloc_buffer,
      ci_mono_emit_void, pairTheory.SND]) >>
  fs[ci_mono_def] >> metis_tac[cs_extends_trans]
QED

Resume raw_call_outbuf_zero_tail_vv_path[finish]:
  `LENGTH u.vs_returndata < dimword (:256)` by fs[] >>
  `initial.cs_next_var <= sc.cs_next_var` by (fs[ci_mono_def] >> decide_tac) >>
  `local_ptrs_reserved cenv sc` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sm` >> fs[ci_mono_def]) >>
  simp[Abbr `Post`, Abbr `Exit`] >>
  qpat_x_assum `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  qpat_x_assum `emit_op _ _ sm = _` mp_tac >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ u` mp_tac >>
  qpat_x_assum `wb_frame _ _ _ _ u` mp_tac >>
  qpat_x_assum `eval_operand ok u = _` mp_tac >>
  qpat_x_assum `LENGTH u.vs_returndata < _` mp_tac >>
  qpat_x_assum `u.vs_returndata = _` mp_tac >>
  qpat_x_assum `post_value_type _ _ = _` mp_tac >>
  qpat_x_assum `expr_type e = _` mp_tac >>
  qpat_x_assum `flags.rcf_max_outsize = 0` mp_tac >>
  qpat_x_assum `local_ptrs_reserved cenv sc` mp_tac >>
  qpat_x_assum `initial.cs_next_var <= sc.cs_next_var` mp_tac >>
  qpat_x_assum `post_value_type _ _ = _` mp_tac >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >>
  Cases_on `flags.rcf_revert_on_failure`
  >- suspend "revert_zero" >>
  fs[] >> drule raw_call_nonrevert_finish_code >>
  simp[] >> strip_tac >>
  `sc' = sc /\ ok' = ok` by (Cases_on `value_opt = NONE` >> gvs[]) >>
  gvs[comp_return_def] >>
  irule frag_path_run_inst_seq >>
  simp[emitted_insts_def, run_inst_seq_def] >>
  irule raw_call_bool_post >>
  fs[raw_call_return_type_def, stmt_state_rel_inst_idx, raw_call_wb_frame_inst_idx] >>
  simp[expr_val_rel_def, expr_val_at_def, instIdxIndepTheory.eval_op_inst_idx,
       vyperValueTheory.evaluate_type_def, bool_to_word_def,
       is_word_type_def, typed_val_to_w256_def, val_to_w256_def] >>
  Cases_on `outcome.co_success` >> simp[bool_to_word_def]
QED

Resume raw_call_outbuf_zero_tail_vv_path[revert_zero]:
  fs[] >> drule raw_call_revert_finish_path >>
  disch_then (drule_at (Pat `emit_op _ _ _ = _`)) >>
  disch_then (qspecl_then [`outcome.co_success`,`u`,`ctx`,`0w`] mp_tac) >>
  simp[] >>
  impl_tac
  >- (Cases_on `outcome.co_success` >> gvs[bool_to_word_def]) >>
  disch_then (mp_then Any irule frag_path_conseq) >> simp[] >>
  rpt strip_tac >> gvs[] >>
  match_mp_tac raw_call_none_post >>
  conj_tac >- gvs[] >>
  conj_tac >- gvs[raw_call_return_type_def] >>
  conj_tac
  >- (irule raw_call_finish_state_rel_aged >>
      qexistsl_tac [`0w`,`0`,`0w`,`sc`,`u`] >> simp[] >>
      first_assum ACCEPT_TAC) >>
  irule raw_call_finish_frame_aged >>
  qexistsl_tac [`0w`,`0`,`0w`,`sc`,`u`] >> simp[] >>
  first_assum ACCEPT_TAC
QED

Finalise raw_call_outbuf_zero_tail_vv_path

Theorem raw_call_outbuf_allocation_site[local]:
  0 < cap /\ compile_raw_call_outbuf cap sa = ((ov,op),sm) /\
  fn_has_code sa sm func /\ local_ptrs_reserved cenv sa ==>
  ?alloc q. MEM alloc (fn_insts func) /\ alloc.inst_opcode = ALLOCA /\
    alloc.inst_outputs = [q] /\ alloc.inst_id = sa.cs_next_id /\
    not_local_ptr cenv scopes q /\ sa.cs_next_id < sm.cs_next_id
Proof
  strip_tac >> drule_all raw_call_outbuf_positive_code >> strip_tac >>
  drule_all raw_call_outbuf_positive_id_growth >> strip_tac >>
  qexistsl_tac [`mk_inst sa.cs_next_id ALLOCA
    [Lit (n2w (((cap+31) DIV 32)*32+32))]
    [STRING #"%" (toString sa.cs_next_var)]`,
    `STRING #"%" (toString sa.cs_next_var)`] >>
  simp[mk_inst_def] >> conj_tac
  >- (irule exprSimHashTheory.hash_emitted_inst_mem >>
      goal_assum (drule_at (Pat `fn_has_code _ _ _`)) >>
      fs[mk_inst_def, arithmeticTheory.MULT_COMM]) >>
  irule fresh_not_local_ptr >> qexists_tac `sa` >> simp[not_fresh_at_def]
QED

Theorem raw_call_outbuf_positive_tail_vv_path[local]:
  post_value_type cenv e = expr_type e /\
  0 < cap /\ compile_raw_call_outbuf cap sa = ((ov,op),sm) /\
  compile_raw_call_finish to_op dp dl gas_op val_op
    (if stat then StaticCall else RegularCall) cap flags.rcf_revert_on_failure ov op sm = (result,sb) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ci_mono initial sa /\ wb_frame cenv initial_es initial s0 s /\
  stmt_state_rel ctx func cenv cx initial_es s0 /\ local_ptrs_reserved cenv initial /\
  MAP FDOM initial_es.scopes = MAP FDOM es.scopes /\
  eval_operand gas_op s = SOME gas /\ eval_operand to_op s = SOME aw /\
  eval_operand dp s = SOME ao /\ eval_operand dl s = SOME az /\ eval_operand val_op s = SOME val_word /\
  safe_operand sa to_op /\ safe_operand sa dp /\ safe_operand sa dl /\
  safe_operand sa gas_op /\ safe_operand sa val_op /\
  w2w aw = target /\
  w2n (if stat then 0w else val_word) = (case value_opt of NONE => 0 | SOME n => n) /\
  stat = IS_NONE value_opt /\
  take_call_outcome target (read_memory (w2n ao) (w2n az) s) value_opt es = (INL (rq,outcome),es1) /\
  MAP FDOM es.scopes = MAP FDOM (SND (adopt_call_outcome rq outcome es1)).scopes /\
  cap < dimword (:256) /\ LENGTH outcome.co_returnData < dimword (:256) /\
  (0 < cap ==> 64 + ((cap + 31) DIV 32) * 32 < dimword (:256)) /\
  flags.rcf_max_outsize = cap /\ expr_type e = raw_call_return_type flags /\
  (0 < cap ==> evaluate_type (get_tenv cx) (expr_type e) =
    SOME (if flags.rcf_revert_on_failure then BaseTV (BytesT (Dynamic cap))
      else TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic cap))])) /\
  post_value_type cenv e = expr_type e ==>
  frag_path ctx sa sb (\u. u = s)
    (\u. (flags.rcf_revert_on_failure ==> outcome.co_success) /\
      vv_post ctx func cenv cx e initial_es initial sb s0
        (SND (adopt_call_outcome rq outcome es1))
        (Value (if flags.rcf_revert_on_failure then
          if cap = 0 then NoneV else BytesV (TAKE cap outcome.co_returnData)
         else if cap = 0 then BoolV outcome.co_success
         else ArrayV (TupleV [BoolV outcome.co_success;BytesV (TAKE cap outcome.co_returnData)])))
        (if cap = 0 then StackValue ann result
         else LocatedValue (expr_type e) (mk_ptr result LocMemory)) u)
    (\r. ?u. flags.rcf_revert_on_failure /\ ~outcome.co_success /\
      r = Abort Revert_abort u /\ u.vs_returndata = outcome.co_returnData)
Proof
  strip_tac >>
  `ci_mono sa sm` by metis_tac[ci_mono_compile_raw_call_outbuf, pairTheory.SND] >>
  `ci_mono sm sb` by metis_tac[ci_mono_compile_raw_call_finish, pairTheory.SND] >>
  `cs_extends sa sm /\ cs_extends sm sb` by fs[ci_mono_def] >>
  drule_all fn_has_code_split >> strip_tac >>
  `0 < cap ==> ((cap+31) DIV 32)*32+32 < dimword (:256)` by
    (strip_tac >> qpat_x_assum `0 < cap ==> 64 + _ < _` drule >> decide_tac) >>
  qpat_assum `stmt_state_rel _ _ _ _ es s`
    (mp_then Any mp_tac raw_call_outbuf_alloc_path) >>
  disch_then drule_all >> strip_tac >>
  qmatch_asmsub_abbrev_tac `frag_path ctx sa sm _ Alloc _` >>
  irule frag_path_seq >> qexistsl_tac [`Alloc`,`sm`] >> simp[] >>
  conj_tac
  >- (irule frag_path_conseq >> goal_assum (drule_at (Pat `frag_path _ _ _ _ _ _`)) >> simp[]) >>
  irule frag_path_pointwise >> simp[Abbr `Alloc`] >> rpt strip_tac >>
  rename1 `stmt_state_rel ctx func cenv cx es t` >>
  qpat_x_assum `frag_path _ sa sm _ _ _` kall_tac >>
  qmatch_goalsub_abbrev_tac `frag_path ctx sm sb _ Post Exit` >>
  `wb_frame cenv initial_es initial s0 t` by
    (irule wb_frame_trans >> simp[] >> conj_tac
     >- (qexistsl_tac [`es`,`sa`,`s`] >> fs[ci_mono_def]) >> metis_tac[]) >>
  `eval_operand gas_op t = SOME gas /\ eval_operand to_op t = SOME aw /\
   eval_operand dp t = SOME ao /\ eval_operand dl t = SOME az /\
   eval_operand val_op t = SOME val_word` by metis_tac[] >>
  `take_call_outcome target (read_memory (w2n ao) (w2n az) t) value_opt es =
    (INL (rq,outcome),es1)` by fs[read_memory_def] >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> fs[ci_mono_def]) >>
  suspend "oracle"
QED

Resume raw_call_outbuf_positive_tail_vv_path[oracle]:
  Cases_on `emit_op (if stat then STATICCALL else CALL)
    (if stat then [gas_op;to_op;dp;dl;op;Lit (n2w cap)]
     else [gas_op;to_op;val_op;dp;dl;op;Lit (n2w cap)]) sm` >>
  rename1 `emit_op _ _ sm = (ok,sc)` >>
  `ci_mono sm sc` by metis_tac[ci_mono_emit_op, pairTheory.SND] >>
  fs[] >>
  `cap <= ((cap+31) DIV 32)*32` by
    (qspec_then `cap` mp_tac valueTypingMemoryPropsTheory.word_size_capacity >>
     simp[vfmConstantsTheory.word_size_def]) >>
  `initial.cs_next_id <= sa.cs_next_id` by fs[ci_mono_def] >>
  qpat_assum `stmt_state_rel _ _ _ _ es t`
    (mp_then Any mp_tac raw_call_output_alloca_sep) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  disch_then (qspecl_then [`initial`,`cap`] mp_tac) >>
  simp[] >> strip_tac >>
  qpat_assum `!name b sz. local_region cenv es.scopes t name b sz ==> _`
    (mp_then Any mp_tac raw_call_output_local_sep) >>
  disch_then (qspec_then `cap` mp_tac) >> simp[] >> strip_tac >>
  `MAP FDOM initial_es.scopes = MAP FDOM es.scopes` by metis_tac[] >>
  `cap <= 32*((cap+31) DIV 32)` by fs[arithmeticTheory.MULT_COMM] >>
  qpat_assum `wb_frame cenv initial_es initial s0 t`
    (mp_then Any mp_tac raw_call_output_initial_locals) >>
  disch_then (qspecl_then [`32*((cap+31) DIV 32)`,`w2n w`,`es`,`cap`] mp_tac) >>
  simp[] >> strip_tac >>
  suspend "call"
QED

Resume raw_call_outbuf_positive_tail_vv_path[call]:
  `initial.cs_next_var <= sm.cs_next_var` by (fs[ci_mono_def] >> decide_tac) >>
  gvs[] >>
  qpat_assum `stmt_state_rel _ _ _ _ es t`
    (mp_then Any mp_tac raw_call_oracle_path) >>
  disch_then (drule_at (Pat `emit_op _ _ _ = _`)) >>
  disch_then (drule_at (Pat `take_call_outcome _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `wb_frame _ _ _ _ _`)) >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >>
  disch_then (qspecl_then [`val_word`,`gas`,`aw`] mp_tac) >>
  impl_tac >- (fs[loweringStateRelDefsTheory.regions_disjoint_def] >>
    conj_tac
    >- (rpt strip_tac >>
        qpat_x_assum `!name b sz. local_region cenv es.scopes t name b sz ==> _ /\ _`
          (drule_all_then strip_assume_tac) >> decide_tac) >>
    conj_tac
    >- (rpt strip_tac >>
        qpat_x_assum `cenv.ce_is_ctor ==> _` drule >>
        disch_then (drule_all_then strip_assume_tac) >> decide_tac) >>
    conj_tac
    >- (rpt strip_tac >>
        qpat_x_assum `!aid b sz. _ ==> _ /\ _`
          (drule_all_then strip_assume_tac) >> decide_tac) >>
    rpt strip_tac >>
    qpat_x_assum `!name b sz. _ /\ local_region cenv initial_es.scopes s0 name b sz ==> _`
      (drule_all_then strip_assume_tac) >> decide_tac) >>
  strip_tac >>
  `cs_extends sm sc` by fs[ci_mono_def] >>
  qmatch_asmsub_abbrev_tac `frag_path ctx sm sc _ OraclePost _` >>
  match_mp_tac frag_path_seq >> qexistsl_tac [`sc`,`OraclePost`] >>
  conj_tac
  >- (irule frag_path_conseq >>
      goal_assum (drule_at (Pat `frag_path _ _ _ _ _ _`)) >> simp[]) >>
  conj_tac
  >- (irule frag_path_pointwise >> simp[Abbr `OraclePost`] >> rpt strip_tac >>
      rename1 `eval_operand ok u = SOME _` >> suspend "finish") >>
  simp[] >> suspend "call_metadata"
QED

Resume raw_call_outbuf_positive_tail_vv_path[finish]:
  drule_all raw_call_outbuf_allocation_site >>
  disch_then (qspec_then `(SND (adopt_call_outcome rq outcome es1)).scopes` strip_assume_tac) >>
  `LENGTH u.vs_returndata < dimword (:256)` by fs[] >>
  `initial.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id < sc.cs_next_id` by
    (fs[ci_mono_def] >> decide_tac) >>
  `local_ptrs_reserved cenv sc` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sm` >> fs[ci_mono_def]) >>
  `safe_operand sc ov` by
    (irule safe_operand_mono >> qexists_tac `sm` >> fs[ci_mono_def]) >>
  `safe_operand sc ok` by metis_tac[emit_op_safe_operand] >>
  `eval_operand ov u = SOME w` by metis_tac[] >>
  simp[Abbr `Post`, Abbr `Exit`] >>
  Cases_on `flags.rcf_revert_on_failure`
  >- suspend "revert_positive" >>
  fs[] >> drule raw_call_nonrevert_finish_code >> simp[] >> strip_tac >>
  `sc' = sc /\ ok' = ok` by (Cases_on `value_opt = NONE` >> gvs[]) >>
  gvs[] >> suspend "tuple_positive"
QED

Resume raw_call_outbuf_positive_tail_vv_path[tuple_positive]:
  `post_value_type cenv e = expr_type e` by gvs[] >>
  qpat_assum `expr_type e = _`
    (mp_then (Pat `expr_type _ = _`) mp_tac raw_call_nonrevert_vv_path) >>
  simp[arithmeticTheory.GREATER_DEF] >>
  disch_then (drule_at (Pat `post_value_type _ _ = _`)) >>
  disch_then (drule_at (Pos hd)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ u`)) >>
  disch_then (drule_at (Pat `MEM _ (fn_insts _)`)) >>
  disch_then (drule_at (Pat `wb_frame _ _ _ _ u`)) >>
  disch_then (qspecl_then [`w`,`outcome.co_success`,`q`] mp_tac) >>
  `cs_extends sc sb` by
    (drule_at (Pat `0 < _`) raw_call_nonrevert_suffix_code >> simp[] >>
     disch_then drule >> strip_tac >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sc sb func` by metis_tac[fn_has_code_split] >>
  `bool_to_word outcome.co_success = (if outcome.co_success then 1w else 0w)` by
    (Cases_on `outcome.co_success` >> simp[bool_to_word_def]) >>
  impl_tac
  >- (gvs[] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp[]
QED

Resume raw_call_outbuf_positive_tail_vv_path[revert_positive]:
  fs[] >>
  `!name lb lsz. local_region cenv (SND (adopt_call_outcome rq outcome es1)).scopes u name lb lsz ==>
    w2n w + (32*((flags.rcf_max_outsize+31) DIV 32)+32) <= lb \/ lb+lsz <= w2n w` by
    (rpt strip_tac >>
     `regions_disjoint (w2n w) (32*((flags.rcf_max_outsize+31) DIV 32)+32) lb lsz`
       suffices_by simp[loweringStateRelDefsTheory.regions_disjoint_def] >>
     irule local_ptrs_rel_alloca_disjoint >>
     goal_assum (drule_at (Pat `MEM _ (fn_insts _)`)) >>
     goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
     fs[stmt_state_rel_def, state_rel_def]) >>
  `!x. ov = Var x ==> not_fresh_at sc x` by fs[safe_operand_def] >>
  drule raw_call_revert_finish_path >>
  disch_then (drule_at (Pat `emit_op _ _ _ = _`)) >>
  disch_then (qspecl_then [`outcome.co_success`,`u`,`ctx`,`w`] mp_tac) >>
  `bool_to_word outcome.co_success = (if outcome.co_success then 1w else 0w)` by
    (Cases_on `outcome.co_success` >> simp[bool_to_word_def]) >>
  simp[] >>
  disch_then (mp_then Any irule frag_path_conseq) >> simp[] >>
  rpt strip_tac >> gvs[] >>
  rename1 `raw_call_finish_view final = _` >>
  suspend "bytes_positive"
QED

Resume raw_call_outbuf_positive_tail_vv_path[bytes_positive]:
  `stmt_state_rel ctx func cenv cx (SND (adopt_call_outcome rq outcome es1)) final` by
    (irule (INST_TYPE [alpha |-> ``:256``] raw_call_finish_state_rel_aged) >>
     qexistsl_tac [`w`,`flags.rcf_max_outsize`,
       `n2w (MIN (LENGTH outcome.co_returnData) flags.rcf_max_outsize)`,`sc`,`u`] >>
     simp[] >> qexistsl_tac [`alloc`,`w2n w`,
       `32*((flags.rcf_max_outsize+31) DIV 32)+32`] >> simp[] >>
     first_assum ACCEPT_TAC) >>
  `wb_frame cenv initial_es initial s0 final` by
    (irule (INST_TYPE [alpha |-> ``:256``] raw_call_finish_frame_aged) >>
     qexistsl_tac [`w`,`flags.rcf_max_outsize`,
       `n2w (MIN (LENGTH outcome.co_returnData) flags.rcf_max_outsize)`,`sc`,`u`] >>
     simp[] >> conj_tac
     >- (rpt strip_tac >>
         qpat_assum `!aid b sz. _ /\ FLOOKUP t.vs_allocas aid = _ ==> _`
           (drule_all_then strip_assume_tac) >> simp[]) >>
     rpt strip_tac >>
     qpat_assum `!name b sz. _ /\ local_region cenv initial_es.scopes s0 name b sz ==> _`
       (drule_all_then strip_assume_tac) >> simp[]) >>
  suspend "bytes_post"
QED

Resume raw_call_outbuf_positive_tail_vv_path[bytes_post]:
  `expr_type e = BaseT (BytesT (Dynamic flags.rcf_max_outsize))` by
    fs[raw_call_return_type_def] >>
  `final.vs_allocas = u.vs_allocas` by
    (qpat_assum `raw_call_finish_view final = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[raw_call_finish_view_def, venom_state_component_equality, mstore_def]) >>
  `eval_operand ov final = SOME w` by metis_tac[] >>
  `!name lb lsz. local_region cenv (SND (adopt_call_outcome rq outcome es1)).scopes final name lb lsz ==>
    w2n w + (32*((flags.rcf_max_outsize+31) DIV 32)+32) <= lb \/ lb+lsz <= w2n w` by
    (rpt strip_tac >>
     `regions_disjoint (w2n w) (32*((flags.rcf_max_outsize+31) DIV 32)+32) lb lsz`
       suffices_by simp[loweringStateRelDefsTheory.regions_disjoint_def] >>
     irule local_ptrs_rel_alloca_disjoint >>
     goal_assum (drule_at (Pat `MEM _ (fn_insts _)`)) >>
     goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
     fs[stmt_state_rel_def, state_rel_def]) >>
  qpat_assum `expr_type e = raw_call_return_type flags` (fn th => rewrite_tac[GSYM th]) >>
  `evaluate_type (get_tenv cx) (expr_type e) =
    SOME (BaseTV (BytesT (Dynamic flags.rcf_max_outsize)))` by metis_tac[] >>
  `post_value_type cenv e = expr_type e` by gvs[] >>
  irule raw_call_bytes_post >>
  TRY (first_assum ACCEPT_TAC >> NO_TAC) >> simp[NoAsms] >>
  simp[] >>
  qexistsl_tac [`sa.cs_next_id`,`w2n w`,
    `32*((flags.rcf_max_outsize+31) DIV 32)`,`u`] >>
  simp[] >> conj_tac >- fs[ci_mono_def] >> first_assum ACCEPT_TAC
QED

Resume raw_call_outbuf_positive_tail_vv_path[call_metadata]:
  Cases_on `flags.rcf_revert_on_failure`
  >- (fs[] >> drule raw_call_finish_revert_compile >>
      simp[arithmeticTheory.GREATER_DEF] >> strip_tac >>
      rename1 `fresh_label "call_failed" ce = (fl,s2)` >>
      `ce = sc` by (Cases_on `value_opt = NONE` >> gvs[]) >> gvs[] >>
      rename1 `fresh_label "call_failed" sc = _` >>
      `ci_mono sc s2 /\ ci_mono s2 s3 /\ ci_mono s3 s4 /\
       ci_mono s4 s5 /\ ci_mono s5 s6 /\ ci_mono s6 s7 /\
       ci_mono s7 s8 /\ ci_mono s8 s9 /\ ci_mono s9 s10` by
        (rpt conj_tac >> metis_tac[ci_mono_fresh_label, ci_mono_emit_inst,
          ci_mono_new_block, ci_mono_emit_op, ci_mono_compile_alloc_buffer,
          ci_mono_emit_void, pairTheory.SND]) >>
      `cs_extends s10 sb` by
        (drule raw_call_success_code >> strip_tac >>
         irule cs_extends_same_block >>
         fs[same_blocks_def, rich_listTheory.IS_PREFIX_APPEND]) >>
      fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  fs[] >> drule raw_call_nonrevert_finish_code >> simp[] >> strip_tac >>
  `sc' = sc` by (Cases_on `value_opt = NONE` >> gvs[]) >> gvs[] >>
  drule_at (Pat `0 < _`) raw_call_nonrevert_suffix_code >> simp[] >>
  disch_then drule >> strip_tac >> metis_tac[cs_extends_trans]
QED

Finalise raw_call_outbuf_positive_tail_vv_path

Theorem raw_call_outbuf_tail_vv_path[local]:
  compile_raw_call_outbuf cap sa = ((ov,op),sm) /\
  compile_raw_call_finish to_op dp dl gas_op val_op
    (if stat then StaticCall else RegularCall) cap flags.rcf_revert_on_failure ov op sm = (result,sb) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ci_mono initial sa /\ wb_frame cenv initial_es initial s0 s /\
  stmt_state_rel ctx func cenv cx initial_es s0 /\ local_ptrs_reserved cenv initial /\
  MAP FDOM initial_es.scopes = MAP FDOM es.scopes /\
  eval_operand gas_op s = SOME gas /\ eval_operand to_op s = SOME aw /\
  eval_operand dp s = SOME ao /\ eval_operand dl s = SOME az /\ eval_operand val_op s = SOME val_word /\
  safe_operand sa to_op /\ safe_operand sa dp /\ safe_operand sa dl /\
  safe_operand sa gas_op /\ safe_operand sa val_op /\
  w2w aw = target /\
  w2n (if stat then 0w else val_word) = (case value_opt of NONE => 0 | SOME n => n) /\
  stat = IS_NONE value_opt /\
  take_call_outcome target (read_memory (w2n ao) (w2n az) s) value_opt es = (INL (rq,outcome),es1) /\
  MAP FDOM es.scopes = MAP FDOM (SND (adopt_call_outcome rq outcome es1)).scopes /\
  cap < dimword (:256) /\ LENGTH outcome.co_returnData < dimword (:256) /\
  (0 < cap ==> 64 + ((cap + 31) DIV 32) * 32 < dimword (:256)) /\
  flags.rcf_max_outsize = cap /\ expr_type e = raw_call_return_type flags /\
  (0 < cap ==> evaluate_type (get_tenv cx) (expr_type e) =
    SOME (if flags.rcf_revert_on_failure then BaseTV (BytesT (Dynamic cap))
      else TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic cap))])) /\
  post_value_type cenv e = expr_type e ==>
  frag_path ctx sa sb (\u. u = s)
    (\u. (flags.rcf_revert_on_failure ==> outcome.co_success) /\
      vv_post ctx func cenv cx e initial_es initial sb s0
        (SND (adopt_call_outcome rq outcome es1))
        (Value (if flags.rcf_revert_on_failure then
          if cap = 0 then NoneV else BytesV (TAKE cap outcome.co_returnData)
         else if cap = 0 then BoolV outcome.co_success
         else ArrayV (TupleV [BoolV outcome.co_success;BytesV (TAKE cap outcome.co_returnData)])))
        (if cap = 0 then StackValue ann result
         else LocatedValue (expr_type e) (mk_ptr result LocMemory)) u)
    (\r. ?u. flags.rcf_revert_on_failure /\ ~outcome.co_success /\
      r = Abort Revert_abort u /\ u.vs_returndata = outcome.co_returnData)
Proof
  strip_tac >> Cases_on `cap = 0`
  >- (drule_all raw_call_outbuf_zero_tail_vv_path >> simp[]) >>
  `0 < cap` by decide_tac >>
  drule_all raw_call_outbuf_positive_tail_vv_path >> simp[]
QED

Theorem raw_call_outbuf_tail_vv_frag[local]:
  post_value_type cenv e = expr_type e /\
  compile_raw_call_outbuf cap sa = ((ov,op),sm) /\
  compile_raw_call_finish to_op dp dl gas_op val_op
    (if stat then StaticCall else RegularCall) cap T ov op sm = (result,sb) /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ci_mono initial sa /\ wb_frame cenv initial_es initial s0 s /\
  stmt_state_rel ctx func cenv cx initial_es s0 /\
  local_ptrs_reserved cenv initial /\
  MAP FDOM initial_es.scopes = MAP FDOM es.scopes /\
  eval_operand gas_op s = SOME gas /\ eval_operand to_op s = SOME aw /\
  eval_operand dp s = SOME ao /\ eval_operand dl s = SOME az /\
  eval_operand val_op s = SOME val_word /\
  (!x. to_op = Var x \/ dp = Var x \/ dl = Var x \/ gas_op = Var x \/ val_op = Var x ==> not_fresh_at sa x) /\
  w2w aw = target /\
  w2n (if stat then 0w else val_word) = (case value_opt of NONE => 0 | SOME n => n) /\
  stat = IS_NONE value_opt /\
  take_call_outcome target (read_memory (w2n ao) (w2n az) s) value_opt es = (INL (rq,outcome),es1) /\
  MAP FDOM es.scopes = MAP FDOM (SND (adopt_call_outcome rq outcome es1)).scopes /\
  cap < dimword (:256) /\ LENGTH outcome.co_returnData < dimword (:256) /\
  (0 < cap ==> ((cap + 31) DIV 32) * 32 + 32 < dimword (:256)) /\
  expr_type e = (if cap = 0 then NoneT else BaseT (BytesT (Dynamic cap))) /\
  (0 < cap ==> evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV (BytesT (Dynamic cap)))) /\
  post_value_type cenv e = expr_type e ==>
  frag_exec ctx sa sb (\u. u = s)
    (\u. outcome.co_success /\
      vv_post ctx func cenv cx e initial_es initial sb s0
        (SND (adopt_call_outcome rq outcome es1))
        (Value (if cap = 0 then NoneV else BytesV (TAKE cap outcome.co_returnData)))
        (if cap = 0 then StackValue ann result
         else LocatedValue (expr_type e) (mk_ptr result LocMemory)) u)
    (\r. ?u. ~outcome.co_success /\ r = Abort Revert_abort u /\
      u.vs_returndata = outcome.co_returnData)
Proof
  strip_tac >>
  `ci_mono sa sm` by
    (metis_tac[ci_mono_compile_raw_call_outbuf, pairTheory.SND]) >>
  `ci_mono sm sb` by
    (metis_tac[ci_mono_compile_raw_call_finish, pairTheory.SND]) >>
  `cs_extends sa sm /\ cs_extends sm sb` by fs[ci_mono_def] >>
  drule_all fn_has_code_split >> strip_tac >>
  Cases_on `cap = 0`
  >- suspend "zero"
  >> suspend "positive"
QED

Resume raw_call_outbuf_tail_vv_frag[zero]:
  gvs[] >>
  qpat_x_assum `compile_raw_call_outbuf _ _ = _` mp_tac >>
  simp[compile_raw_call_outbuf_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  drule_all buffer_alloc_code >> strip_tac >>
  `0 < dimword (:256)` by simp[] >>
  qpat_x_assum `stmt_state_rel _ _ _ _ initial_es s0` mp_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >> strip_tac >>
  rename1 `compile_alloc_buffer 0 sa = (buf,sm)` >>
  `wb_frame cenv initial_es initial s0 t` by
    (irule wb_frame_readonly_tail >>
     qexistsl_tac [`sa`, `s`] >> fs[ci_mono_def]) >>
  `!n b sz. local_region cenv initial_es.scopes s0 n b sz ==>
      local_region cenv es.scopes t n b sz` by
    (rpt strip_tac >> irule exprSimPropsTheory.local_region_frame_fwd >>
     qexistsl_tac [`s0`, `initial`, `initial_es.scopes`] >>
     simp[] >> metis_tac[wb_frame_vars]) >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> fs[ci_mono_def]) >>
  `t.vs_labels = s.vs_labels` by metis_tac[hash_alloc_buffer_labels] >>
  `eval_operand gas_op t = SOME gas /\ eval_operand to_op t = SOME aw /\
   eval_operand dp t = SOME ao /\ eval_operand dl t = SOME az /\
   eval_operand val_op t = SOME val_word` by
    (`!a v. eval_operand a s = SOME v /\
         (!x. a = Var x ==> not_fresh_at sa x) ==>
         eval_operand a t = SOME v` by
       (Cases >> simp[eval_operand_def] >> metis_tac[]) >>
     metis_tac[]) >>
  suspend "zero_tail"
QED

Resume raw_call_outbuf_tail_vv_frag[zero_tail]:
  `!aid b sz. aid < initial.cs_next_id /\
      FLOOKUP t.vs_allocas aid = SOME (b,sz) ==>
      regions_disjoint (w2n w) 0 b sz` by
    (rpt gen_tac >> strip_tac >>
     `aid <> sa.cs_next_id` by (fs[ci_mono_def] >> decide_tac) >>
     qpat_assum `stmt_state_rel _ _ _ _ es t` mp_tac >>
     pure_rewrite_tac[stmt_state_rel_def, venomMemDefsTheory.alloca_inv_def,
          venomMemDefsTheory.allocas_non_overlapping_def] >>
     strip_tac >> first_x_assum drule_all >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `cenv.ce_is_ctor ==> !name tv v off.
      FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
      FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
        | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
      regions_disjoint off (type_memory_size tv) (w2n w) 0` by
    (rpt strip_tac >>
     qpat_assum `stmt_state_rel _ _ _ _ es t` mp_tac >>
     pure_rewrite_tac[stmt_state_rel_def, immutable_alloca_sep_def] >> strip_tac >>
     qpat_x_assum `cenv.ce_is_ctor ==> _` drule >>
     disch_then drule_all >> strip_tac >>
     first_x_assum (qspec_then
       `mk_inst sa.cs_next_id ALLOCA [Lit 0w]
         [STRING #"%" (toString sa.cs_next_var)]` mp_tac) >>
     simp[mk_inst_def]) >>
  `frag_exec ctx sa sm (\u. u = s)
      (\u. u = t with vs_inst_idx := LENGTH sm.cs_current_insts)
      (\r. ?u. ~outcome.co_success /\ r = Abort Revert_abort u /\
        u.vs_returndata = outcome.co_returnData)` by
    (irule frag_exec_run_inst_seq >>
     qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[contextTheory.compile_alloc_buffer_def, emit_op_def,
       comp_bind_def, comp_return_def] >> pairarg_tac >> strip_tac >> gvs[] >>
     gvs[fresh_id_def, fresh_var_def, emit_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def, emitted_insts_def,
       rich_listTheory.DROP_LENGTH_APPEND, rich_listTheory.IS_PREFIX_APPEND,
       mk_inst_def, is_terminator_def]) >>
  drule frag_exec_then >> disch_then irule >> simp[] >>
  suspend "zero_finish"
QED

Resume raw_call_outbuf_tail_vv_frag[zero_finish]:
  qmatch_goalsub_abbrev_tac `t with vs_inst_idx := k` >>
  qabbrev_tac `entry = t with vs_inst_idx := k` >>
  `stmt_state_rel ctx func cenv cx es entry /\
   wb_frame cenv initial_es initial s0 entry /\
   eval_operand gas_op entry = SOME gas /\
   eval_operand to_op entry = SOME aw /\ eval_operand dp entry = SOME ao /\
   eval_operand dl entry = SOME az /\ eval_operand val_op entry = SOME val_word /\
   eval_operand buf.buf_operand entry = SOME w` by
    simp[Abbr `entry`, stmt_state_rel_inst_idx, raw_call_control_frame,
         instIdxIndepTheory.eval_op_inst_idx] >>
  `take_call_outcome (w2w aw) (read_memory (w2n ao) (w2n az) entry) value_opt es =
     (INL (rq,outcome),es1)` by
    ( `read_memory (w2n ao) (w2n az) entry = read_memory (w2n ao) (w2n az) s`
        by simp[Abbr `entry`, read_memory_def] >> asm_rewrite_tac[]) >>
  `initial.cs_next_var <= sm.cs_next_var` by (fs[ci_mono_def] >> decide_tac) >>
  `!name b sz. local_region cenv es.scopes entry name b sz ==>
      b + sz <= w2n w \/ w2n w + 0 <= b` by
    (rpt gen_tac >>
     `local_region cenv es.scopes entry name b sz =
      local_region cenv es.scopes t name b sz` by simp[Abbr `entry`, local_region_def, lookup_var_def] >>
     asm_rewrite_tac[] >> strip_tac >>
     first_assum (drule_then mp_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  `!name b sz. local_region cenv initial_es.scopes s0 name b sz ==>
      regions_disjoint (w2n w) 0 b sz` by metis_tac[] >>
  `!aid b sz. aid < initial.cs_next_id /\ FLOOKUP entry.vs_allocas aid = SOME (b,sz) ==>
      regions_disjoint (w2n w) 0 b sz` by
      (simp[Abbr `entry`] >> metis_tac[]) >>
  Cases_on `emit_op (if value_opt = NONE then STATICCALL else CALL)
    (if value_opt = NONE then [gas_op;to_op;dp;dl;buf.buf_operand;Lit 0w]
     else [gas_op;to_op;val_op;dp;dl;buf.buf_operand;Lit 0w]) sm` >>
  rename1 `emit_op _ _ sm = (ok,sc)` >>
  drule raw_call_allocated_tail_frag_aged >>
  disch_then (drule_at (Pat `take_call_outcome _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `wb_frame _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  simp[] >> impl_tac
  >- (fs[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
  disch_then (mp_then Any irule frag_exec_weaken) >>
  simp[] >> rpt strip_tac >> gvs[] >>
  irule raw_call_none_post >> simp[] >> gvs[]
QED

Resume raw_call_outbuf_tail_vv_frag[positive]:
  `0 < cap` by decide_tac >>
  `((cap + 31) DIV 32) * 32 + 32 < dimword (:256)` by metis_tac[] >>
  qpat_x_assum `stmt_state_rel _ _ _ _ initial_es s0` mp_tac >>
  drule_all raw_call_outbuf_positive_run >> strip_tac >> strip_tac >>
  `wb_frame cenv initial_es initial s0 t` by
    (irule wb_frame_trans >> simp[] >> conj_tac
     >- (qexistsl_tac [`es`, `sa`, `s`] >> fs[ci_mono_def]) >>
     metis_tac[]) >>
  suspend "positive_operands"
QED

Resume raw_call_outbuf_tail_vv_frag[positive_operands]:
  drule_all raw_call_outbuf_positive_code >> strip_tac >>
  `t.vs_labels = s.vs_labels` by
    (drule_all raw_call_outbuf_positive_labels >> simp[]) >>
  `eval_operand gas_op t = SOME gas /\ eval_operand to_op t = SOME aw /\
   eval_operand dp t = SOME ao /\ eval_operand dl t = SOME az /\
   eval_operand val_op t = SOME val_word` by
    (`!a v. eval_operand a s = SOME v /\
         (!x. a = Var x ==> not_fresh_at sa x) ==>
         eval_operand a t = SOME v` by
       (Cases >> simp[eval_operand_def] >> metis_tac[wb_frame_vars]) >>
     metis_tac[]) >>
  suspend "positive_geometry"
QED

Resume raw_call_outbuf_tail_vv_frag[positive_geometry]:
  `cap <= ((cap+31) DIV 32)*32` by
    (mp_tac (Q.SPEC `cap` valueTypingMemoryPropsTheory.word_size_capacity) >>
     simp[vfmConstantsTheory.word_size_def]) >>
  `initial.cs_next_id <= sa.cs_next_id` by fs[ci_mono_def] >>
  qpat_assum `stmt_state_rel _ _ _ _ es t`
    (mp_then Any mp_tac raw_call_output_alloca_sep) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >>
  disch_then (qspecl_then [`initial`, `cap`] mp_tac) >>
  simp[] >> strip_tac >>
  qpat_assum `!name b len. local_region cenv es.scopes t name b len ==> _`
    (mp_then Any mp_tac raw_call_output_local_sep) >>
  disch_then (qspec_then `cap` mp_tac) >> simp[] >> strip_tac >>
  `!name b sz. local_region cenv es.scopes t name b sz ==>
      regions_disjoint (w2n w) (32*((cap+31) DIV 32)+32) b sz` by
    (rpt strip_tac >>
     qpat_assum `!name b len. local_region cenv es.scopes t name b len ==> regions_disjoint _ (_ + 32) _ _`
       drule >> simp[arithmeticTheory.MULT_COMM]) >>
  qpat_assum `wb_frame cenv initial_es initial s0 t`
    (mp_then Any mp_tac raw_call_output_initial_locals) >>
  disch_then (qspecl_then [`32*((cap+31) DIV 32)`, `w2n w`, `es`, `cap`] mp_tac) >>
  simp[] >> disch_tac >>
  `!name b sz. local_region cenv initial_es.scopes s0 name b sz ==>
      regions_disjoint (w2n w) 32 b sz /\
      regions_disjoint (w2n w + 32) cap b sz` by metis_tac[] >>
  suspend "positive_lift"
QED

Resume raw_call_outbuf_tail_vv_frag[positive_lift]:
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> fs[ci_mono_def]) >>
  `frag_exec ctx sa sm (\u. u = s)
      (\u. u = t with vs_inst_idx := LENGTH sm.cs_current_insts)
      (\r. ?u. ~outcome.co_success /\ r = Abort Revert_abort u /\
        u.vs_returndata = outcome.co_returnData)` by
    (drule_all raw_call_outbuf_positive_straight >> strip_tac >>
     irule frag_exec_run_inst_seq >> fs[EVERY_MEM] >> metis_tac[]) >>
  drule_at (Pat `frag_exec _ _ _ _ _ _`) frag_exec_then >>
  disch_then irule >>
  simp[] >> suspend "positive_finish"
QED

Resume raw_call_outbuf_tail_vv_frag[positive_finish]:
  qmatch_goalsub_abbrev_tac `t with vs_inst_idx := k` >>
  qabbrev_tac `entry = t with vs_inst_idx := k` >>
  `stmt_state_rel ctx func cenv cx es entry /\
   wb_frame cenv initial_es initial s0 entry /\
   eval_operand gas_op entry = SOME gas /\
   eval_operand to_op entry = SOME aw /\ eval_operand dp entry = SOME ao /\
   eval_operand dl entry = SOME az /\ eval_operand val_op entry = SOME val_word /\
   eval_operand ov entry = SOME w /\
   eval_operand op entry = SOME (w + 32w)` by
    simp[Abbr `entry`, stmt_state_rel_inst_idx, raw_call_control_frame,
         instIdxIndepTheory.eval_op_inst_idx] >>
  `take_call_outcome (w2w aw) (read_memory (w2n ao) (w2n az) entry) value_opt es =
     (INL (rq,outcome),es1)` by
    (`read_memory (w2n ao) (w2n az) entry = read_memory (w2n ao) (w2n az) s`
       by simp[Abbr `entry`, read_memory_def] >> asm_rewrite_tac[]) >>
  `initial.cs_next_var <= sm.cs_next_var` by (fs[ci_mono_def] >> decide_tac) >>
  Cases_on `emit_op (if value_opt = NONE then STATICCALL else CALL)
    (if value_opt = NONE then [gas_op;to_op;dp;dl;op;Lit (n2w cap)]
     else [gas_op;to_op;val_op;dp;dl;op;Lit (n2w cap)]) sm` >>
  rename1 `emit_op _ _ sm = (ok,sc)` >>
  drule raw_call_allocated_tail_frag_aged >>
  disch_then (drule_at (Pat `take_call_outcome _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `wb_frame _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  simp[] >> impl_tac
  >- (`!sc name b sz. local_region cenv sc entry name b sz =
           local_region cenv sc t name b sz` by
          simp[Abbr `entry`, local_region_def, lookup_var_def] >>
      simp[Abbr `entry`] >>
      rpt conj_tac
      >- (Cases_on `value_opt` >> gvs[])
      >- (rpt strip_tac >>
          qpat_x_assum `!name b sz. local_region cenv es.scopes t name b sz ==> _ /\ _`
            drule >> simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac)
      >- (rpt strip_tac >>
          qpat_x_assum `cenv.ce_is_ctor ==> _` drule >>
          disch_then drule_all >> simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac)
      >- metis_tac[]
      >- metis_tac[]
      >- suspend "positive_header_witness"
      >- metis_tac[] >> metis_tac[]) >>
  suspend "positive_post"
QED

Resume raw_call_outbuf_tail_vv_frag[positive_header_witness]:
  qexistsl_tac [`mk_inst sa.cs_next_id ALLOCA
      [Lit (n2w (((cap+31) DIV 32)*32+32))]
      [STRING #"%" (toString sa.cs_next_var)]`,
    `w2n w`, `((cap+31) DIV 32)*32+32`] >>
  simp[mk_inst_def] >> conj_tac
  >- (qpat_x_assum `fn_has_code sa sm func` mp_tac >>
      pure_rewrite_tac[fn_has_code_def, rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
      irule lookup_block_fn_insts >> goal_assum (drule_at Any) >>
      fs[MEM_APPEND, mk_inst_def] >> metis_tac[]) >>
  rpt strip_tac >>
  qpat_x_assum `!name b len. local_region cenv es.scopes t name b len ==> _`
    drule >> simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Resume raw_call_outbuf_tail_vv_frag[positive_post]:
  disch_then (mp_then Any irule frag_exec_weaken) >>
  simp[] >> rpt strip_tac >> gvs[] >>
  rename1 `raw_call_finish_view u = raw_call_finish_view (mstore _ _ after)` >>
  `!name b sz. local_region cenv (SND (adopt_call_outcome rq outcome es1)).scopes u name b sz ==>
      local_region cenv es.scopes t name b sz` by
    (rpt strip_tac >>
     `local_region cenv initial_es.scopes s0 name b sz` by
       (irule exprSimPropsTheory.local_region_frame >>
        conj_tac >- (qexists_tac `func` >> fs[stmt_state_rel_def, state_rel_def]) >>
        goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
        qexists_tac `initial` >> simp[] >> rpt strip_tac >>
        irule wb_frame_vars >> goal_assum (drule_at (Pat `wb_frame _ _ _ _ u`)) >> simp[]) >>
     irule exprSimPropsTheory.local_region_frame_fwd >>
     qexistsl_tac [`s0`, `initial`, `initial_es.scopes`] >>
     simp[] >> metis_tac[wb_frame_vars]) >>
  qpat_assum `expr_type e = _` (fn th => once_rewrite_tac[GSYM th]) >>
  irule raw_call_bytes_post >> simp[] >>
  qexistsl_tac [`sa.cs_next_id`, `w2n w`, `32*((cap+31) DIV 32)`, `after`] >>
  simp[Abbr `entry`] >> conj_tac
  >- (drule_all raw_call_outbuf_positive_id_growth >> fs[ci_mono_def] >> decide_tac) >>
  rpt strip_tac >>
  `local_region cenv es.scopes t n lb lsz` by metis_tac[] >>
  qpat_x_assum `!name b len. local_region cenv es.scopes t name b len ==> _` drule >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def]
QED

Finalise raw_call_outbuf_tail_vv_frag

Theorem eval_expr_raw_call_values[local]:
  eval_exprs cx args es = (INL (AddressV target::BytesV bytes::vs),es1) /\
  LENGTH vs = LENGTH flags.rcf_kws /\
  raw_call_value flags.rcf_kws vs = SOME amount ==>
  eval_expr cx (Call ann (RawCallTarget flags) args dflt) es =
    eval_raw_call cx flags target bytes amount
      (forwarded_gas default_evm_gas_limit
        (ext_call_kwarg EKGas flags.rcf_kws vs)) es1
Proof
  strip_tac >> simp[Once evaluate_def, bind_def, ignore_bind_def,
    type_check_def, assert_def, return_def, raise_def,
    lift_option_type_def, lift_option_def, check_def,
    dest_AddressV_def, dest_BytesV_def, byteTheory.word_of_bytes_be_def,
    byteTheory.word_of_bytes_word_to_bytes, dividesTheory.divides_def,
    fcpLib.INDEX_CONV ``dimindex(:160)``]
QED

Theorem raw_call_keyword_values[local]:
  !ks es vs es'.
    EVERY (\e. expr_type e = BaseT (UintT 256) /\
      !st. expr_sim_inv cenv cx env st ==> expr_body_pre cenv cx env e st) ks /\
    expr_sim_inv cenv cx env es /\ eval_exprs cx ks es = (INL vs,es') ==>
    EVERY (value_has_type (BaseTV (UintT 256))) vs /\
    LENGTH vs = LENGTH ks /\ expr_sim_inv cenv cx env es'
Proof
  Induct >- simp[eval_exprs_nil] >>
  rpt gen_tac >> simp[] >> strip_tac >>
  drule eval_exprs_cons_cases >> strip_tac >> gvs[] >>
  Cases_on `rr` >> gvs[] >>
  `expr_body_pre cenv cx env h es` by metis_tac[] >>
  drule_all expr_body_pre_base_result >> strip_tac >>
  qpat_x_assum `!es vs es'. _` drule_all >> simp[]
QED

Theorem raw_call_keywords_post[local]:
  !ks xs vs.
    typed_args_post ctx func cenv cx es sa s0 es' ks xs vs s /\
    EVERY (\e. expr_type e = BaseT (UintT 256)) ks ==>
    LIST_REL (\x v. eval_operand x s = SOME
      (typed_val_to_w256 (BaseTV (UintT 256)) v)) xs vs
Proof
  Induct >> rpt gen_tac >>
  Cases_on `xs` >> Cases_on `vs` >>
  simp[typed_args_post_def, vyperValueTheory.evaluate_type_def] >>
  strip_tac >> gvs[vyperValueTheory.evaluate_type_def] >>
  first_x_assum irule >> simp[typed_args_post_def] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem raw_call_value_operand[local]:
  !ks xs vs.
    LIST_REL (\x v. eval_operand x s = SOME
      (typed_val_to_w256 (BaseTV (UintT 256)) v)) xs vs /\
    EVERY (value_has_type (BaseTV (UintT 256))) vs ==>
    ?amount. raw_call_value ks vs = SOME amount /\
      eval_operand (case ext_call_kwarg EKValue ks xs of
        NONE => Lit 0w | SOME x => x) s = SOME (n2w amount) /\
      amount < dimword (:256)
Proof
  Induct >- simp[raw_call_value_def, ext_call_kwarg_def, eval_operand_def] >>
  rpt gen_tac >> Cases_on `xs` >> Cases_on `vs` >>
  simp[raw_call_value_def, ext_call_kwarg_def, eval_operand_def] >>
  strip_tac >> gvs[] >> Cases_on `h = EKValue` >> gvs[]
  >- (drule uint256_typed_dest >> simp[wordsTheory.w2n_lt] >>
      qspec_then `(typed_val_to_w256 (BaseTV (UintT 256)) h''):bytes32`
        mp_tac wordsTheory.w2n_lt >> simp[]) >>
  first_x_assum drule_all >> simp[raw_call_value_def]
QED

Theorem raw_call_keywords_decode[local]:
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) dflt) es /\
  expr_sim_inv cenv cx env es2 /\
  eval_exprs cx kws es2 = (INL kvs,es') /\
  typed_args_post ctx func cenv cx es0 sa s0 es' kws xs kvs s ==>
  ?amount. raw_call_value flags.rcf_kws kvs = SOME amount /\
    eval_operand (case ext_call_kwarg EKValue flags.rcf_kws xs of
      NONE => Lit 0w | SOME x => x) s = SOME (n2w amount) /\
    amount < dimword (:256) /\
    (flags.rcf_is_static ==> amount = 0) /\
    LENGTH kvs = LENGTH flags.rcf_kws /\ expr_sim_inv cenv cx env es'
Proof
  strip_tac >> drule raw_call_pre_flags >> simp[] >> strip_tac >>
  drule raw_call_kwargs_types >> strip_tac >>
  `EVERY (\e. expr_type e = BaseT (UintT 256) /\
    !st. expr_sim_inv cenv cx env st ==> expr_body_pre cenv cx env e st) kws` by
    (simp[EVERY_MEM] >> rpt gen_tac >> strip_tac >> conj_tac
     >- fs[EVERY_MEM] >> rpt strip_tac >>
     irule expr_body_pre_raw_call_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
  drule_all raw_call_keyword_values >> strip_tac >>
  drule_all raw_call_keywords_post >> strip_tac >>
  drule_all raw_call_value_operand >>
  disch_then (qspec_then `flags.rcf_kws` strip_assume_tac) >>
  `LENGTH kvs = LENGTH flags.rcf_kws` by decide_tac >>
  qexists_tac `amount` >> fs[] >> strip_tac >>
  `~MEM EKValue flags.rcf_kws` by fs[raw_call_kws_ok_def] >>
  gvs[raw_call_value_def, ext_call_kwarg_not_mem]
QED

Theorem raw_call_prefix_source_ready[local]:
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) dflt) es /\
  bind (eval_expr cx a) (read_result cx) (es with gas_obs := gsA) = (INL av,esA) /\
  bind (eval_expr cx d) (read_result cx) (esA with gas_obs := gsD) =
    (INL (BytesV bs),esD) /\
  eval_exprs cx kws (esD with gas_obs := gsK) = (INL kvs,esK) /\
  expr_val_rel cx (BaseT AddressT) av addr t /\
  typed_args_post ctx func cenv cx esD s4 tm esK kws xs kvs tk /\
  (!x w. MEM x xs /\ eval_operand x tk = SOME w ==> eval_operand x t = SOME w) ==>
  ?target amount.
    av = AddressV target /\ dest_AddressV av = SOME target /\
    eval_operand addr t = SOME (w2w target) /\
    raw_call_value flags.rcf_kws kvs = SOME amount /\
    eval_operand (case ext_call_kwarg EKValue flags.rcf_kws xs of
      NONE => Lit 0w | SOME x => x) t = SOME (n2w amount) /\
    amount < dimword(:256) /\ (flags.rcf_is_static ==> amount = 0) /\
    LENGTH kvs = LENGTH flags.rcf_kws /\ expr_sim_inv cenv cx env esK
Proof
  strip_tac >> drule raw_call_pre_operands >> simp[] >> strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  `expr_body_pre cenv cx env a (es with gas_obs := gsA)` by
    (irule expr_body_pre_raw_call_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
  `expr_sim_inv cenv cx env esA` by
    (irule (cj 1 expr_body_pre_base_result) >>
     goal_assum (drule_at Any) >> simp[ETA_THM] >>
     qexists_tac `INL av` >> fs[bind_def]) >>
  `value_has_type (BaseTV AddressT) av` by
    (irule (cj 3 expr_body_pre_base_result) >>
     goal_assum (drule_at Any) >> simp[] >>
     qexists_tac `esA` >> fs[bind_def]) >>
  `expr_body_pre cenv cx env d (esA with gas_obs := gsD)` by
    (irule expr_body_pre_raw_call_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >> simp[]) >>
  `expr_sim_inv cenv cx env esD` by
    (irule (cj 1 expr_body_pre_base_result) >>
     goal_assum (drule_at Any) >> simp[ETA_THM] >>
     qexists_tac `INL (BytesV bs)` >> fs[bind_def]) >>
  `expr_sim_inv cenv cx env (esD with gas_obs := gsK)` by simp[] >>
  drule_all raw_call_keywords_decode >> strip_tac >>
  Cases_on `av` >> gvs[value_has_type_def] >>
  gvs[expr_val_rel_def, is_word_type_def,
    vyperValueTheory.evaluate_type_def, typed_val_to_w256_def] >>
  qexists_tac `word_of_bytes_be l` >> simp[dest_AddressV_def] >>
  `word_to_bytes (word_of_bytes_be l : address) T = l` by
    (simp[byteTheory.word_of_bytes_be_def] >>
     irule venomMemPropsTheory.word_bytes_roundtrip >>
     simp[byteTheory.word_of_bytes_be_def, dividesTheory.divides_def,
       fcpLib.INDEX_CONV ``dimindex(:160)``]) >>
  simp[] >> conj_tac
  >- (qspec_then `l` mp_tac
       (venomMemPropsTheory.w2w_word_of_bytes_be_pad_left
         |> INST_TYPE [alpha |-> ``:160``, beta |-> ``:256``]) >>
      simp[dividesTheory.compute_divides,
        fcpLib.INDEX_CONV ``dimindex(:160)``, EQ_SYM_EQ]) >>
  Cases_on `ext_call_kwarg EKValue flags.rcf_kws xs` >>
  gvs[eval_operand_def] >>
  `MEM x xs` by metis_tac[raw_call_kwarg_mem] >> metis_tac[]
QED

Theorem raw_call_source_continuation[local]:
  dest_AddressV av = SOME target /\ LENGTH kvs = LENGTH flags.rcf_kws /\
  raw_call_value flags.rcf_kws kvs = SOME amount ==>
  (do
    type_check (LENGTH (av::BytesV bs::kvs) = 2 + LENGTH flags.rcf_kws) "raw_call args";
    target <- lift_option_type (dest_AddressV av) "raw_call target";
    data <- lift_option_type (dest_BytesV (BytesV bs)) "raw_call data";
    amount <- lift_option_type (raw_call_value flags.rcf_kws kvs) "raw_call value";
    eval_raw_call cx flags target data amount
      (forwarded_gas default_evm_gas_limit (ext_call_kwarg EKGas flags.rcf_kws kvs))
  od) = eval_raw_call cx flags target bs amount
    (forwarded_gas default_evm_gas_limit (ext_call_kwarg EKGas flags.rcf_kws kvs))
Proof
  strip_tac >> simp[FUN_EQ_THM, bind_def, ignore_bind_def, type_check_def,
    assert_def, lift_option_type_def, dest_BytesV_def, return_def]
QED

Theorem raw_call_source_tail[local]:
  ~cx.txn.is_static /\ ~flags.rcf_is_delegate /\
  (flags.rcf_is_static ==> amount = 0) /\ IS_SOME es.outcomes /\
  outcomes_accounts_typed es.outcomes /\
  accounts_runtime_well_typed es.accounts ==>
  ?rq outcome es1 es2.
    take_call_outcome target bytes
      (if flags.rcf_is_static then NONE else SOME amount) es =
        (INL (rq,outcome),es1) /\
    adopt_call_outcome rq outcome es1 = (INL (),es2) /\
    eval_raw_call cx flags target bytes amount gas es =
      (if flags.rcf_revert_on_failure /\ ~outcome.co_success then
         INR (Error (RevertData outcome.co_returnData))
       else INL (Value
         (if flags.rcf_revert_on_failure then
            if flags.rcf_max_outsize = 0 then NoneV
            else BytesV (TAKE flags.rcf_max_outsize outcome.co_returnData)
          else if flags.rcf_max_outsize = 0 then BoolV outcome.co_success
          else ArrayV (TupleV [BoolV outcome.co_success;
            BytesV (TAKE flags.rcf_max_outsize outcome.co_returnData)]))),es2) /\
    es2.gas_obs = es.gas_obs /\
    (!gs. eval_raw_call cx flags target bytes amount gas (es with gas_obs := gs) =
      (FST (eval_raw_call cx flags target bytes amount gas es),es2 with gas_obs := gs))
Proof
  strip_tac >>
  drule_all raw_call_typed_outcome >>
  disch_then (qspecl_then [`target`, `bytes`,
    `if flags.rcf_is_static then NONE else SOME amount`] strip_assume_tac) >>
  Cases_on `adopt_call_outcome rq outcome es1` >>
  drule adopt_call_outcome_frame >> strip_tac >> gvs[] >>
  drule_all raw_call_oracle_result >> strip_tac >>
  conj_tac
  >- (Cases_on `flags.rcf_revert_on_failure /\ ~outcome.co_success` >> simp[]) >>
  Cases_on `flags.rcf_revert_on_failure /\ ~outcome.co_success` >>
  qspecl_then [`cx`,`flags`,`target`,`bytes`,`amount`,`gas`,`es`] mp_tac
    calldata_raw_call_gas_obs >> simp[]
QED

(* Lift a target-only suffix: every observed target GAS is implicit. *)
Theorem raw_call_tail_path_outcome[local]:
  (!gs. source (es with gas_obs := gs) = (res,ee with gas_obs := gs)) /\
  frag_path ctx sa sb (\u. u = s)
    (\u. Q res (ee with gas_obs := []) u)
    (\r. R res (ee with gas_obs := []) r) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F tops (ctx,func) source (es,s)
    (\res ee u. Q res ee u /\ u.vs_current_bb = sb.cs_current_bb /\
       u.vs_inst_idx = LENGTH sb.cs_current_insts) R
Proof
  strip_tac >>
  qpat_x_assum `frag_path _ _ _ _ _ _` mp_tac >>
  simp[frag_path_def] >>
  disch_then (qspec_then `func` mp_tac) >> simp[] >> strip_tac >>
  simp[gas_outcome_def] >> qexists_tac `REPLICATE n F` >> disj1_tac >>
  simp[gas_summary_at_def, gas_marked_exec_def,
    fragGasModeTheory.gas_marked_path_def] >>
  qexistsl_tac [`res`,`ee`,`r`] >> simp[]
QED

Theorem raw_call_tail_outcome[local]:
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) dflt) es /\
  bind (eval_expr cx a) (read_result cx) (es with gas_obs := gsA) = (INL av,esA) /\
  bind (eval_expr cx d) (read_result cx) (esA with gas_obs := gsD) =
    (INL (BytesV bs),esD) /\
  eval_exprs cx kws (esD with gas_obs := gsK) = (INL kvs,esK) /\
  esK.gas_obs = [] /\ expr_sim_inv cenv cx env esK /\
  typed_args_post ctx func cenv cx esD s4 tm esK kws xs kvs tk /\
  expr_val_rel cx (BaseT AddressT) av addr t /\
  (!x w. MEM x xs /\ eval_operand x tk = SOME w ==> eval_operand x t = SOME w) /\
  eval_operand len t = SOME (n2w (LENGTH bs)) /\
  eval_operand dp t = SOME (n2w (b+32)) /\ eval_operand gas t = SOME gw /\
  mem_bytes_at (b+32) (LENGTH bs) t.vs_memory = bs /\
  b+32 < dimword (:256) /\ LENGTH bs < dimword (:256) /\
  stmt_state_rel ctx func cenv cx esK t /\ wb_frame cenv es sa s0 t /\
  stmt_state_rel ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  ci_mono sa s6 /\ fn_has_code s6 sb func /\ fn_inst_ids_distinct func /\
  ~t.vs_halted /\ t.vs_current_bb = s6.cs_current_bb /\
  t.vs_inst_idx = LENGTH s6.cs_current_insts /\
  safe_operand s6 addr /\ safe_operand s6 len /\ safe_operand s6 dp /\
  safe_operand s6 gas /\ safe_operand s6
    (case ext_call_kwarg EKValue flags.rcf_kws xs of NONE => Lit 0w | SOME v => v) /\
  compile_raw_call_outbuf flags.rcf_max_outsize s6 = ((ov,op),s7) /\
  compile_raw_call_finish addr dp len gas
    (case ext_call_kwarg EKValue flags.rcf_kws xs of NONE => Lit 0w | SOME v => v)
    (if flags.rcf_is_static then StaticCall else RegularCall)
    flags.rcf_max_outsize flags.rcf_revert_on_failure ov op s7 = (result,sb) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (do
      type_check (LENGTH (av::BytesV bs::kvs) = 2 + LENGTH flags.rcf_kws) "raw_call args";
      target <- lift_option_type (dest_AddressV av) "raw_call target";
      data <- lift_option_type (dest_BytesV (BytesV bs)) "raw_call data";
      amount <- lift_option_type (raw_call_value flags.rcf_kws kvs) "raw_call value";
      eval_raw_call cx flags target data amount
        (forwarded_gas default_evm_gas_limit (ext_call_kwarg EKGas flags.rcf_kws kvs))
    od) (esK,t)
    (\res ee u. (\res ee u. ?tv. res = INL tv /\
      vv_post ctx func cenv cx
        (Call (raw_call_return_type flags) (RawCallTarget flags) (a::d::kws) NONE)
        es sa sb s0 ee tv
        (if flags.rcf_max_outsize = 0 then StackValue ann result
         else LocatedValue (raw_call_return_type flags) (mk_ptr result LocMemory)) u) res ee u /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >> drule_all raw_call_prefix_source_ready >> strip_tac >>
  drule raw_call_pre_flags >> strip_tac >>
  `~cx.txn.is_static` by fs[stmt_state_rel_def, state_rel_def] >>
  `IS_SOME esK.outcomes /\ outcomes_accounts_typed esK.outcomes /\
   accounts_runtime_well_typed esK.accounts` by
    fs[expr_sim_inv_def,
      vyperTypeExtCallCoreTheory.accounts_runtime_well_typed_accounts_well_typed] >>
  drule_all raw_call_source_tail >>
  disch_then (qspecl_then [`target`,
    `forwarded_gas default_evm_gas_limit (ext_call_kwarg EKGas flags.rcf_kws kvs)`,`bs`]
    strip_assume_tac) >>
  suspend "ready"
QED

Resume raw_call_tail_outcome[ready]:
  `MAP FDOM es.scopes = MAP FDOM esA.scopes` by
    (qpat_assum `bind (eval_expr cx a) _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[bind_def, AllCaseEqs()] >> strip_tac >>
     imp_res_tac read_result_state >> gvs[] >>
     drule eval_expr_preserves_scopes_dom >> simp[]) >>
  `MAP FDOM esA.scopes = MAP FDOM esD.scopes` by
    (qpat_assum `bind (eval_expr cx d) _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[bind_def, AllCaseEqs()] >> strip_tac >>
     imp_res_tac read_result_state >> gvs[] >>
     drule eval_expr_preserves_scopes_dom >> simp[]) >>
  `MAP FDOM esD.scopes = MAP FDOM esK.scopes` by
    (drule eval_exprs_preserves_scopes_dom >> simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM esK.scopes` by metis_tac[] >>
  `MAP FDOM esK.scopes = MAP FDOM es2.scopes` by
    (`es1.scopes = esK.scopes` by
       (drule take_call_outcome_frame >>
        disch_then (mp_tac o Q.AP_TERM `\s. s.scopes`) >> simp[]) >>
     drule adopt_call_outcome_frame >> simp[] >> strip_tac >>
     pop_assum (mp_tac o Q.AP_TERM `\s. s.scopes`) >> simp[]) >>
  drule_all raw_call_source_continuation >>
  disch_then (qspecl_then [`cx`,`bs`] SUBST1_TAC) >>
  map_every (fn q => qpat_x_assum q kall_tac)
    [`bind (eval_expr cx a) _ _ = _`, `bind (eval_expr cx d) _ _ = _`,
     `eval_exprs cx kws _ = _`, `typed_args_post _ _ _ _ _ _ _ _ _ _ _ _`,
     `expr_val_rel _ _ _ _ _`, `!x w. MEM x xs /\ _ ==> _`,
     `MAP FDOM es.scopes = MAP FDOM esA.scopes`,
     `MAP FDOM esA.scopes = MAP FDOM esD.scopes`,
     `MAP FDOM esD.scopes = MAP FDOM esK.scopes`] >>
  suspend "capacity"
QED

Resume raw_call_tail_outcome[capacity]:
  `0 < flags.rcf_max_outsize ==>
    64 + ((flags.rcf_max_outsize + 31) DIV 32)*32 < dimword (:256)` by
    (strip_tac >>
     `type_alloc_ok cenv ann` by fs[expr_body_pre_def, alloc_limits_expr_def] >>
     Cases_on `flags.rcf_revert_on_failure` >>
     gvs[raw_call_return_type_def, type_alloc_ok_def, is_word_type_def,
       type_memory_bytes_def] >>
     `2 ** 64 + 64 < dimword (:256)` by simp[wordsTheory.dimword_def] >>
     fs[] >> decide_tac) >>
  `local_ptrs_reserved cenv s6` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> fs[ci_mono_def]) >>
  `LENGTH outcome.co_returnData < dimword (:256)` by
    (drule_all exprSimRawCallCalldataTheory.calldata_take_call_outcome_bound >> simp[]) >>
  `read_memory (w2n (n2w (b+32):bytes32)) (w2n (n2w (LENGTH bs):bytes32)) t = bs` by
    simp[read_memory_def, GSYM mem_bytes_at_def] >>
  suspend "path"
QED

Resume raw_call_tail_outcome[path]:
  `w2w (w2w target : bytes32) = target` by wordsLib.WORD_DECIDE_TAC >>
  `w2n (if flags.rcf_is_static then 0w else (n2w amount : bytes32)) =
    (case (if flags.rcf_is_static then NONE else SOME amount) of NONE => 0 | SOME n => n)` by
    (Cases_on `flags.rcf_is_static` >> simp[]) >>
  `flags.rcf_is_static = IS_NONE (if flags.rcf_is_static then NONE else SOME amount)` by
    (Cases_on `flags.rcf_is_static` >> simp[]) >>
  `take_call_outcome target
    (read_memory (w2n (n2w (b+32):bytes32)) (w2n (n2w (LENGTH bs):bytes32)) t)
    (if flags.rcf_is_static then NONE else SOME amount) esK = (INL (rq,outcome),es1)` by simp[] >>
  `MAP FDOM esK.scopes = MAP FDOM (SND (adopt_call_outcome rq outcome es1)).scopes` by simp[] >>
  `0 < flags.rcf_max_outsize ==> evaluate_type (get_tenv cx)
    (expr_type (Call (raw_call_return_type flags) (RawCallTarget flags) (a::d::kws) NONE)) =
    SOME (if flags.rcf_revert_on_failure then BaseTV (BytesT (Dynamic flags.rcf_max_outsize))
      else TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic flags.rcf_max_outsize))])` by
    (qpat_assum `flags.rcf_max_outsize < dimword (:256)`
       (mp_then Any strip_assume_tac raw_call_bytes_slot_size_bound) >>
     Cases_on `flags.rcf_revert_on_failure` >>
     fs[expr_type_def, raw_call_return_type_def, evaluate_type_def]) >>
  `expr_type (Call (raw_call_return_type flags) (RawCallTarget flags) (a::d::kws) NONE) =
    raw_call_return_type flags` by simp[expr_type_def] >>
  irule raw_call_tail_path_outcome >>
  suspend "lift"
QED

Resume raw_call_tail_outcome[lift]:
  conj_tac >- simp[] >>
  qexistsl_tac [`es2`,
    `FST (eval_raw_call cx flags target bs amount
      (forwarded_gas default_evm_gas_limit (ext_call_kwarg EKGas flags.rcf_kws kvs)) esK)`, `s6`] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  conj_tac >- simp[] >>
  irule frag_path_conseq >>
  irule_at (Pos last) raw_call_outbuf_tail_vv_path >>
  goal_assum (drule_at (Pos hd)) >>
  goal_assum (drule_at (Pos hd)) >>
  qpat_assum `stmt_state_rel _ _ _ _ esK t` assume_tac >>
  rpt (goal_assum (drule_at (Pos hd))) >>
  qexistsl_tac [`Call (raw_call_return_type flags) (RawCallTarget flags) (a::d::kws) NONE`, `ann`] >>
  simp[] >>
  `es2 with gas_obs := [] = es2` by
    (Cases_on `es2` >> gvs[evaluation_state_fn_updates]) >>
  conj_tac >- (rpt strip_tac >> gvs[expr_exit_def]) >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Finalise raw_call_tail_outcome

Theorem compile_expr_raw_call[local]:
  compile_expr cenv ty (Call ann (RawCallTarget flags) (a::d::kws) dflt) sa =
    (vv,sb) ==>
  ?addr data len dp vo go ignored gas ov op result s1 s2 s3 s4 s5 s6 s7.
    lower_value compile_expr cenv (BaseT AddressT) a sa = (addr,s1) /\
    lower_value compile_expr cenv (expr_type d) d s1 = (data,s2) /\
    emit_op MLOAD [data] s2 = (len,s3) /\
    emit_op ADD [data;Lit 32w] s3 = (dp,s4) /\
    compile_ext_call_kwargs compile_expr cenv NoneT flags.rcf_kws kws s4 =
      ((vo,go,ignored),s5) /\
    (case go of SOME g => (g,s5) | NONE => emit_op GAS [] s5) = (gas,s6) /\
    compile_raw_call_outbuf flags.rcf_max_outsize s6 = ((ov,op),s7) /\
    compile_raw_call_finish addr dp len gas
      (case vo of SOME v => v | NONE => Lit 0w)
      (if flags.rcf_is_delegate then DelegateCall
       else if flags.rcf_is_static then StaticCall else RegularCall)
      flags.rcf_max_outsize flags.rcf_revert_on_failure ov op s7 = (result,sb) /\
    vv = (if flags.rcf_max_outsize = 0 then StackValue ann result
          else LocatedValue ann (mk_ptr result LocMemory))
Proof
  simp[compile_expr_call, compile_call_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rpt (goal_assum (drule_at Any) >> simp[]) >>
  Cases_on `flags.rcf_max_outsize = 0` >> gvs[]
QED


(* TOP-LEVEL *)
Theorem raw_call_exists_align[local]:
  ((?tv. P tv) /\ A /\ B) = (?tv. P tv /\ A /\ B)
Proof
  eq_tac
  >- (rpt strip_tac >> qexists_tac `tv` >> simp[]) >>
  strip_tac >> simp[] >> qexists_tac `tv` >> simp[]
QED

Theorem compile_raw_call_case:
  !nocalls ctx func cenv cx ann flags args dflt.
    exprs_case nocalls ctx func cenv cx args ==>
    expr_sim_case nocalls ctx func cenv cx (Call ann (RawCallTarget flags) args dflt) /\
    expr_vv_case nocalls ctx func cenv cx (Call ann (RawCallTarget flags) args dflt)
Proof
  rpt gen_tac >> strip_tac >>
  `expr_vv_case nocalls ctx func cenv cx
     (Call ann (RawCallTarget flags) args dflt)`
    suffices_by simp[expr_sim_case_of_vv] >>
  rewrite_tac[expr_vv_case_def] >> rpt strip_tac >>
  drule raw_call_pre_operands >> strip_tac >> gvs[] >>
  rewrite_tac[expr_vv_sim_def] >> rpt gen_tac >> strip_tac >>
  drule compile_expr_raw_call >> strip_tac >>
  drule raw_call_pre_flags >> strip_tac >>
  `ci_mono s6 s7 /\ ci_mono s7 sb` by
    metis_tac[ci_mono_compile_raw_call_outbuf,
              ci_mono_compile_raw_call_finish, pairTheory.SND] >>
  `cs_extends s6 sb` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  suspend "placement"
QED

Resume compile_raw_call_case[placement]:
  drule raw_call_kwargs_types >> simp[] >> strip_tac >>
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
  `ci_mono s5 s6` by
    (Cases_on `go` >> gvs[]
     >- metis_tac[ci_mono_emit_op, pairTheory.SND] >> simp[ci_mono_refl]) >>
  `ci_mono sa s6` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS]) >>
  `fn_has_code sa s6 func /\ fn_has_code s6 sb func` by
    (irule fn_has_code_split >> fs[ci_mono_def]) >>
  gvs[] >>
  rewrite_tac[raw_call_eval_action] >>
  irule (BETA_RULE (Q.ISPEC `\av dv kvs.
    do
      type_check (LENGTH (av::dv::kvs) = 2 + LENGTH flags.rcf_kws) "raw_call args";
      target <- lift_option_type (dest_AddressV av) "raw_call target";
      data <- lift_option_type (dest_BytesV dv) "raw_call data";
      amount <- lift_option_type (raw_call_value flags.rcf_kws kvs) "raw_call value";
      eval_raw_call cx flags target data amount
        (forwarded_gas default_evm_gas_limit (ext_call_kwarg EKGas flags.rcf_kws kvs))
    od` (Q.GEN `k` (SPEC_ALL raw_call_prefix_sim)))) >>
  first_assum (irule_at (Pat `expr_body_pre _ _ _ _ _`)) >>
  first_assum (irule_at (Pat `exprs_case _ _ _ _ _ _`)) >>
  first_assum (irule_at (Pat `lower_value _ _ _ a _ = _`)) >>
  simp[] >> conj_tac >-
    (rpt gen_tac >> Cases_on `r` >> Cases_on `exc` >>
     simp[expr_exit_def] >> rename1 `Error err` >>
     Cases_on `err` >> simp[expr_exit_def]) >>
  rpt strip_tac >>
  qpat_x_assum `ext_call_kwarg EKValue _ xs = _`
    (fn th => rule_assum_tac (REWRITE_RULE [th])) >>
  simp[CONJ_ASSOC, arithmeticTheory.ADD_COMM] >>
  irule (SRULE [raw_call_exists_align, CONJ_ASSOC, arithmeticTheory.ADD_COMM]
    (BETA_RULE raw_call_tail_outcome)) >>
  first_assum (irule_at (Pat `typed_args_post _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[] >>
  first_assum (irule_at (Pat `compile_raw_call_finish _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  first_assum (irule_at (Pat `compile_raw_call_outbuf _ _ = _`)) >>
  simp[] >> rpt (goal_assum (drule_at Any)) >> simp[]
QED

Finalise compile_raw_call_case
