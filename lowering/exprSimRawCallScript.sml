(*
 * Expression simulation: raw_call (#636, Calls row 3)
 *
 * raw_call(to, data, [value=], [gas=], [max_outsize=], [is_static_call=],
 * [revert_on_failure=]) lowers (compile_call's RawCallTarget clause) to
 * the address with lower_value, the data unwrapped to memory, the value=
 * and gas= keyword operands in source order, GAS without gas=, the output
 * buffer (compile_raw_call_outbuf) and the call (compile_raw_call_finish).
 * In oracle mode the source raw_call consumes and adopts the same outcome
 * as the lowered CALL, STATICCALL or DELEGATECALL.
 * Without revert_on_failure
 * the result is the success flag, or for max_outsize > 0 a fresh
 * (bool, Bytes[max_outsize]) tuple buffer: the flag word, then the bytes
 * value (length and data) inline, as val_in_memory lays out a tuple.
 *)

Theory exprSimRawCall
Ancestors
  ptrDiscipline exprSimSource exprSimHypsDefs exprSimDefs exprSimStack loweringPosts
  exprSimProps exprSimVVFrame exprSimAttributeFields
  gasOutcome gasSummary gasSummaryCompose gasExemptCert
  allocLimits freshWrites varsExt builtinSimple builtinProps
  list pair vyperMisc fragExec loweringSlice exprSimHyps exprSimWordArgs
  exprSimPrecompiles exprSimOperators exprSimOperands exprSimAccounts
  gasStorage vyperStorageTrace vyperStorageFootprint vyperFiniteStoragePreservation
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
  stmt_state_rel H ctx func cenv cx es s /\
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
  ?t. run_inst_seq (emitted_insts sa sc) s = OK t /\
    stmt_state_rel H ctx func cenv cx es t /\ wb_frame cenv es0 es sf s0 t /\
    t.vs_fmp = s.vs_fmp /\ eval_operand pop t = SOME w /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (w2n w,32 + sz) /\
    val_in_memory (TupleTV [BaseTV BoolT; BaseTV (BytesT (Dynamic n))])
      (ArrayV (TupleV [BoolV success; BytesV bs])) (w2n w) t.vs_memory /\
    (!p. safe_operand sa p ==> eval_operand p t = eval_operand p s)
Proof
  strip_tac >> drule_all raw_call_tuple_copy_seq_run >> strip_tac >>
  `w2n (w + 32w) = w2n w + 32` by
    (irule buffer_offset_no_wrap >> qexists_tac `32 + sz` >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx es u` by
    (qpat_assum `u = _` SUBST1_TAC >>
     irule raw_call_reserved_vars_frame >> simp[] >>
     qexists_tac `sa` >> simp[] >> rpt strip_tac >>
     `eval_operand p u = eval_operand p s` by simp[] >> gvs[]) >>
  `wb_frame cenv es0 es sf s0 u` by
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
  stmt_state_rel H ctx func cenv cx es s /\
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
  safe_operand sa ok /\ safe_operand sa src /\
  eval_operand ok s = SOME (if success then 1w else 0w) /\
  eval_operand src s = SOME a ==>
  ?t w. run_inst_seq (emitted_insts sa sc) s = OK t /\
    stmt_state_rel H ctx func cenv cx es t /\ wb_frame cenv es0 es sf s0 t /\
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
  `stmt_state_rel H ctx func cenv cx es (s with vs_fmp := s.vs_fmp)` by simp[] >>
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
  `sz < dimword (:256)` by
    (qpat_assum `sz + (w2n w + 32) < dimword (:256)` mp_tac >> decide_tac) >>
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

Theorem raw_call_nonrevert_finish_code:
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

Theorem raw_call_nonrevert_suffix_code:
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

Theorem raw_call_nonrevert_positive_run:
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
  stmt_state_rel H ctx func cenv cx es s /\ wb_frame cenv es0 es sf s0 s /\
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
    stmt_state_rel H ctx func cenv cx es t /\ wb_frame cenv es0 es sf s0 t /\
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
  `stmt_state_rel H ctx func cenv cx es (s with vs_fmp := s.vs_fmp)` by simp[] >>
  drule_at (Pat `MEM _ (fn_insts _)`) raw_call_output_prefix_ready >>
  simp[] >> disch_then drule >> simp[] >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME _`)) >> simp[] >>
  fs[wordsTheory.dimword_def] >>
  `stmt_state_rel H ctx func cenv cx es (s with vs_fmp := s.vs_fmp)` by simp[] >>
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




Theorem raw_call_eval_args_action[local]:
  eval_exprs cx (a::d::kws) =
    bind (bind (eval_expr cx a) (read_result cx)) (\av.
    bind (bind (eval_expr cx d) (read_result cx)) (\dv.
    bind (eval_exprs cx kws) (\kvs. return (av::dv::kvs))))
Proof
  simp[Once evaluate_def] >> simp[Once evaluate_def] >>
  simp[bind_assoc, bind_return]
QED

Theorem raw_call_eval_action:
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
          (ext_call_kwarg EKGas flags.rcf_kws kvs)
      od)))
Proof
  simp[Once evaluate_def, raw_call_eval_args_action, bind_assoc, bind_return]
QED

(* Counted prefix consumer contract (source replacements are sequential):
   quantify gsA av esA tA gsD bs esD tD.  The address continuation receives
     bind (eval_expr cx a) (read_result cx) (es with gas_obs := gsA) =
       (INL av,esA), esA.gas_obs = [],
     expr_post H ctx func cenv cx a es sa s1 s0 esA av addr tA;
   the data continuation receives
     bind (eval_expr cx d) (read_result cx) (esA with gas_obs := gsD) =
       (INL (BytesV bs),esD), esD.gas_obs = [],
     expr_post H ctx func cenv cx d esA s1 s2 tA esD (BytesV bs) data tD.
   Each operand endpoint has current_bb/inst_idx aligned with s1 or s2;
   the live address fact is expr_val_rel cx (BaseT AddressT) av addr tD.
   The final premise is gas_outcome F (cx_tops cx) (ctx,func)
     (k av (BytesV bs)) (esD,tD) Q R, not gas_summary_at.

   Consumer mapping: raw_call_eval_action exposes the two forced-value
   binds. Project data expr_post only
   after retaining the post and esA/tA/esD/tD witnesses.  At MLOAD/ADD,
   the data-prefix run supplies the data pointer b, length,
   payload, bounds and frame. Transport
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

Theorem raw_call_kwargs_types:
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
Theorem raw_call_kwargs_word_args:
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

Theorem raw_call_pre_operands:
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

Theorem raw_call_pre_flags:
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) args dflt) es ==>
  flags.rcf_max_outsize < dimword (:256) /\
  LENGTH args = 2 + LENGTH flags.rcf_kws /\
  raw_call_kws_ok flags (DROP 2 args) /\
  ann = raw_call_return_type flags /\ dflt = NONE
Proof
  simp[expr_body_pre_def, well_typed_expr_def]
QED

Theorem expr_body_pre_raw_call_target_arg:
  !cenv cx env ann flags target args dflt e es es'.
    (target = RawCallTarget flags \/ target = RawCallCalldataTarget flags) /\
    expr_body_pre cenv cx env (Call ann target args dflt) es /\
    MEM e args /\ expr_sim_inv cenv cx env es' ==>
    expr_body_pre cenv cx env e es'
Proof
  rpt gen_tac >> strip_tac >> gvs[] >>
  gvs[expr_body_pre_def, well_typed_expr_def, int_calls_expr_def,
     byte_widths_expr_def, alloc_limits_expr_def,
     supportedExprTraverseTheory.supported_expr_exists_def,
     supportedExprTraverseTheory.supported_exprs_exists_every, EXISTS_MEM] >>
  imp_res_tac int_calls_exprs_every_mem >>
  gvs[supportedExprTraverseTheory.expr_has_evm_run_thm, listTheory.EXISTS_MEM] >>
  metis_tac[well_typed_exprs_member, byte_widths_exprs_mem,
            alloc_limits_exprs_mem, call_evaluation_safe_exprs_mem]
QED

Theorem expr_body_pre_raw_call_arg:
  !cenv cx env ann flags args dflt e es es'.
    expr_body_pre cenv cx env (Call ann (RawCallTarget flags) args dflt) es /\
    MEM e args /\ expr_sim_inv cenv cx env es' ==>
    expr_body_pre cenv cx env e es'
Proof
  rpt strip_tac >> irule expr_body_pre_raw_call_target_arg >> simp[] >>
  qexistsl_tac [`ann`,`args`,`dflt`,`es`,`flags`,`RawCallTarget flags`] >>
  simp[]
QED


(* MLOAD/ADD only extend the variable map. Keep their memory and source
   relation interface explicit before running the keyword expressions. *)

Theorem raw_call_outbuf_zero_run:
  compile_raw_call_outbuf 0 sa = ((ov,op),sb) /\
  stmt_state_rel H ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ fn_has_code sa sb func ==>
  ?t w. run_inst_seq (emitted_insts sa sb) s = OK t /\
    stmt_state_rel H ctx func cenv cx es t /\ ov = op /\
    eval_operand ov t = SOME w /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,0) /\
    w2n w < dimword (:256) /\ t.vs_memory = s.vs_memory /\
    wb_frame cenv es es sa s t /\
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
  qexistsl_tac [`t`, `w`] >> simp[wb_frame_def, locals_kept_mem] >>
  fs[] >> conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >>
  qpat_assum `stmt_state_rel H ctx func cenv cx es t` mp_tac >>
  pure_rewrite_tac[stmt_state_rel_def, immutable_alloca_sep_def] >> strip_tac >>
  qpat_x_assum `cenv.ce_is_ctor ==> _` drule >>
  disch_then drule_all >> strip_tac >>
  qpat_x_assum `!inst b sz. MEM inst _ /\ _ ==> _`
    (qspec_then `mk_inst sa.cs_next_id ALLOCA [Lit 0w]
      [STRING #"%" (toString sa.cs_next_var)]` mp_tac) >>
  fs[mk_inst_def]
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

Theorem raw_call_outbuf_positive_id_growth:
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

(* Count the actual allocation instructions; retain the run endpoint so that
   allocation witnesses from either allocation theorem survive unchanged. *)
Theorem raw_call_outbuf_add_frame[local]:
  emit_op ADD [ov; Lit 32w] sa = (op,sb) /\
  eval_operand ov s = SOME w /\
  (!x. ov = Var x ==> not_fresh_at sa x) /\
  stmt_state_rel H ctx func cenv cx es s /\ local_ptrs_reserved cenv sa ==>
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand ov t = SOME w /\ eval_operand op t = SOME (w + 32w) /\
    stmt_state_rel H ctx func cenv cx es t /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    wb_frame cenv es es sa s t /\
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
  `stmt_state_rel H ctx func cenv cx es t` by
    (irule hash_readonly_state_rel >> goal_assum drule >> simp[]) >>
  qexists_tac `t` >>
  simp[Abbr `t`, update_var_def, wb_frame_def, locals_kept_mem,
       eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  conj_tac
  >- (Cases_on `ov` >> gvs[eval_operand_def, lookup_var_def,
                          emitHelperPropsTheory.lookup_var_update_var, not_fresh_at_def] >>
      first_x_assum (qspec_then `sa.cs_next_var` assume_tac) >>
      gvs[finite_mapTheory.FLOOKUP_UPDATE]) >>
  rpt strip_tac >> gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj]
QED

Theorem raw_call_outbuf_positive_run:
  0 < cap /\ compile_raw_call_outbuf cap sa = ((ov,op),sb) /\
  ((cap + 31) DIV 32) * 32 + 32 < dimword (:256) /\
  stmt_state_rel H ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ fn_has_code sa sb func ==>
  ?t w. run_inst_seq (emitted_insts sa sb) s = OK t /\
    eval_operand ov t = SOME w /\ eval_operand op t = SOME (w + 32w) /\
    w2n (w + 32w) = w2n w + 32 /\
    FLOOKUP t.vs_allocas sa.cs_next_id =
      SOME (w2n w, ((cap + 31) DIV 32) * 32 + 32) /\
    w2n w + (((cap + 31) DIV 32) * 32 + 32) < dimword (:256) /\
    stmt_state_rel H ctx func cenv cx es t /\ t.vs_memory = s.vs_memory /\
    wb_frame cenv es es sa s t /\
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
  >- (simp[wb_frame_def, locals_kept_mem] >> rpt strip_tac >> simp[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- suspend "immutable" >>
  qpat_x_assum `!x. buf.buf_operand = Var x \/ op = Var x ==> _` mp_tac >>
  asm_rewrite_tac[] >> simp[]
QED

Resume raw_call_outbuf_positive_run[immutable]:
  rpt strip_tac >>
  qpat_assum `stmt_state_rel H ctx func cenv cx es final` mp_tac >>
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
Theorem raw_call_frame_footprint[local]:
  expr_sim_inv cenv cx env es /\
  expr_val_at cenv cx (BaseT (BytesT (Dynamic cap))) sa sb es (BytesV bs) op s /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic cap))) =
    SOME (BaseTV (BytesT (Dynamic cap))) /\
  eval_operand op s = SOME w /\ sb.cs_next_id <= sk.cs_next_id /\
  wb_frame cenv es es' sk s t ==>
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
      drule exprSimPropsTheory.dynarray_len_untupled_imp_at >> strip_tac >>
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
  sb.cs_next_id <= sk.cs_next_id /\ wb_frame cenv es es' sk s t /\
  mem_bytes_at (b+32) (LENGTH bs) s.vs_memory = bs ==>
  mem_bytes_at (b+32) (LENGTH bs) t.vs_memory = bs
Proof
  strip_tac >>
  drule_all raw_call_frame_footprint >>
  simp[val_footprint_def, wordsTheory.w2n_n2w] >> strip_tac >>
  drule (cj 1 valueEncodingProofsTheory.mem_bytes_at_agree_window) >>
  disch_then (qspecl_then [`b+32`, `LENGTH bs`] mp_tac) >> simp[]
QED

Theorem raw_call_kwargs_payload:
  expr_sim_inv cenv cx env es /\
  expr_val_at cenv cx (BaseT (BytesT (Dynamic cap))) sa sd es (BytesV bs) data s /\
  evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic cap))) =
    SOME (BaseTV (BytesT (Dynamic cap))) /\
  eval_operand data s = SOME (n2w b) /\ b < dimword (:256) /\
  mem_bytes_at (b+32) (LENGTH bs) s.vs_memory = bs /\
  sd.cs_next_id <= sk.cs_next_id /\
  typed_args_post H ctx func cenv cx es sk s es' kws xs vs t ==>
  mem_bytes_at (b+32) (LENGTH bs) t.vs_memory = bs
Proof
  strip_tac >>
  `wb_frame cenv es es' sk s t` by fs[typed_args_post_def] >>
  drule_all raw_call_frame_bytes >> simp[]
QED

(* Oracle tail, independent of the expression producing calldata. *)
Theorem raw_call_kind_memory_oracle_exec[local]:
  stmt_state_rel H ctx func cenv cx es s /\ inst.inst_outputs = [out] /\
  w2w aw = target /\
  w2n (if call_ty = RegularCall then vw else 0w) =
    (case value_opt of NONE => 0 | SOME n => n) /\
  (call_ty = StaticCall \/ cx.txn.is_static) = IS_NONE value_opt /\
  (!g. gas_cap = SOME g ==> g = w2n gas) /\
  (if call_ty = DelegateCall then take_delegate_outcome else take_call_outcome)
    gas_cap target (read_memory (w2n ao) (w2n az) s) value_opt es =
    (INL (rq,outcome),es1) /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
     b + sz <= w2n ro \/ w2n ro + w2n rz <= b) /\
  (cenv.ce_is_ctor ==> !src name tv v off.
    (src = cenv.ce_module \/ IS_SOME (ALOOKUP cenv.ce_modules src)) /\
    FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables src imms) name = SOME (tv,v) ==>
    off + type_memory_size tv <= w2n ro \/ w2n ro + w2n rz <= off) ==>
  ?t. (if call_ty = DelegateCall then
         exec_delegatecall inst s gas aw ao az ro rz
       else exec_ext_call inst s gas aw
         (if call_ty = RegularCall then vw else 0w) ao az ro rz
         (call_ty = StaticCall \/ s.vs_call_ctx.cc_static)) =
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
    state_rel H func cenv cx (SND (adopt_call_outcome rq outcome es1)) t
Proof
  strip_tac >>
  `state_rel H func cenv cx es s` by fs[stmt_state_rel_def] >>
  `s.vs_call_ctx.cc_static = cx.txn.is_static` by
    fs[state_rel_def, call_ctx_rel_def] >>
  `call_ty = DelegateCall ==>
    value_opt = (if s.vs_call_ctx.cc_static then NONE else SOME 0)` by
    (Cases_on `value_opt` >> Cases_on `s.vs_call_ctx.cc_static` >> gvs[]) >>
  `?t. (if call_ty = DelegateCall then
         exec_delegatecall inst s gas aw ao az ro rz
       else exec_ext_call inst s gas aw
         (if call_ty = RegularCall then vw else 0w) ao az ro rz
         (call_ty = StaticCall \/ s.vs_call_ctx.cc_static)) =
        OK (update_var out (if outcome.co_success then 1w else 0w) t) /\
    t = s with <| vs_outcomes := t.vs_outcomes; vs_requests := t.vs_requests;
      vs_accounts := t.vs_accounts; vs_transient := t.vs_transient;
      vs_logs := t.vs_logs; vs_pending_deletions := t.vs_pending_deletions;
      vs_returndata := t.vs_returndata; vs_memory := t.vs_memory |> /\
    t.vs_memory = (write_memory_with_expansion (w2n ro)
      (TAKE (w2n rz) outcome.co_returnData) s).vs_memory /\
    t.vs_returndata = outcome.co_returnData /\
    (local_ptrs_rel func cenv es.scopes t /\
     (!src. src = cenv.ce_module \/ IS_SOME (ALOOKUP cenv.ce_modules src) ==>
        immutables_rel cenv cx.txn.target src cenv.ce_is_ctor es t) ==>
     state_rel H func cenv cx (SND (adopt_call_outcome rq outcome es1)) t)` by
    (Cases_on `call_ty` >> fs[] >>
     FIRST [irule (SIMP_RULE (srw_ss()) [] exec_delegate_call_oracle_step),
            irule (SIMP_RULE (srw_ss()) [] exec_ext_call_oracle_step)] >>
     rpt (goal_assum (drule_at Any)) >> gvs[]) >>
  rename1 `s'.vs_returndata = outcome.co_returnData` >>
  qabbrev_tac `payload = TAKE (w2n rz) outcome.co_returnData` >>
  qabbrev_tac `dst = w2n ro` >>
  `LENGTH payload <= w2n rz` by simp[Abbr `payload`, LENGTH_TAKE_EQ, arithmeticTheory.MIN_DEF] >>
  `!src. src = cenv.ce_module \/ IS_SOME (ALOOKUP cenv.ce_modules src) ==>
    immutables_rel cenv cx.txn.target src cenv.ce_is_ctor es
      (write_memory_with_expansion dst payload s)` by
    (gen_tac >> disch_tac >>
     irule immutables_rel_mem_agree >> qexists_tac `s` >>
     conj_tac >- simp[immutableMemoryFrameTheory.immutable_write_memory_capacity] >>
     conj_tac >- simp[write_memory_with_expansion_def, LET_THM] >>
     reverse conj_tac
     >- (fs[state_rel_def, optionTheory.IS_SOME_EXISTS] >> metis_tac[]) >>
     rpt strip_tac >> irule hash_write_memory_disjoint >>
     qpat_x_assum `cenv.ce_is_ctor ==> !src name tv v off. _` drule >>
     disch_then (qspecl_then [`src`, `name`, `tv`, `v`, `off`] mp_tac) >>
     simp[Abbr `dst`] >> decide_tac) >>
  `stmt_state_rel H ctx func cenv cx es (write_memory_with_expansion dst payload s)` by
    (irule write_memory_stmt_state_rel >> simp[] >>
     conj_tac >- (rpt strip_tac >> first_x_assum drule >> simp[Abbr `dst`] >> decide_tac) >>
     first_assum ACCEPT_TAC) >>
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
   (!src. src = cenv.ce_module \/ IS_SOME (ALOOKUP cenv.ce_modules src) ==>
     immutables_rel cenv cx.txn.target src cenv.ce_is_ctor es s')` by
    (qpat_x_assum `stmt_state_rel H _ _ _ _ _ (write_memory_with_expansion _ _ _)` mp_tac >>
     qpat_x_assum `_ = _ with <| vs_outcomes := _; vs_requests := _;
       vs_accounts := _; vs_transient := _; vs_logs := _;
       vs_pending_deletions := _; vs_returndata := _ |>` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >> once_asm_rewrite_tac[] >>
     simp[local_ptrs_rel_oracle_fields, stmt_state_rel_def, state_rel_def,
          immutables_rel_def] >> strip_tac >> simp[] >>
     metis_tac[optionTheory.IS_SOME_EXISTS]) >>
  qexists_tac `s'` >> simp[hash_write_memory_read_self] >>
  metis_tac[]
QED

(* A fresh result variable is disjoint from source locals even after adoption. *)
Theorem raw_call_result_frame:
  emit_op opc ops sm = (ok_op,sb) /\ local_ptrs_reserved cenv sm /\
  state_rel H func cenv cx es t ==>
  ?u. u = update_var (STRING #"%" (toString sm.cs_next_var)) w t /\
    eval_operand ok_op u = SOME w /\ state_rel H func cenv cx es u /\
    u.vs_memory = t.vs_memory /\ u.vs_returndata = t.vs_returndata
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  qexists_tac `update_var (STRING #"%" (toString sm.cs_next_var)) w t` >>
  simp[eval_operand_def, lookup_var_update_var] >>
  irule state_rel_update_var >> simp[] >>
  irule fresh_not_local_ptr >> qexists_tac `sm` >>
  simp[not_fresh_at_def]
QED

Theorem raw_call_kind_take_adopt_fields:
  (if delegate then take_delegate_outcome else take_call_outcome)
    gas_cap addr data value es = (INL (rq,outcome),es1) ==>
  (SND (adopt_call_outcome rq outcome es1)).scopes = es.scopes /\
  (SND (adopt_call_outcome rq outcome es1)).immutables = es.immutables
Proof
  Cases_on `delegate` >> simp[] >> strip_tac
  >- (drule take_delegate_outcome_frame >>
      disch_then (fn th => ONCE_REWRITE_TAC [th]) >>
      Cases_on `rq.cr_static` >> Cases_on `outcome.co_success` >>
      Cases_on `rq.cr_kind` >> simp[adopt_call_outcome_equation]) >>
  drule raw_call_take_adopt_fields >> simp[]
QED

Theorem raw_call_oracle_stmt_frame[local]:
  (if delegate then take_delegate_outcome else take_call_outcome)
    gas_cap target calldata value_opt es = (INL (rq,outcome),es1) /\
  es' = SND (adopt_call_outcome rq outcome es1) /\
  stmt_state_rel H ctx func cenv cx es s /\ state_rel H func cenv cx es' t /\
  t.vs_vars = s.vs_vars /\ t.vs_allocas = s.vs_allocas /\
  t.vs_alloca_next = s.vs_alloca_next /\
  t.vs_fmp = s.vs_fmp /\ t.vs_labels = s.vs_labels /\
  ((ptrDiscipline$ctx_has_dalloca ctx \/
    EXISTS (\inst. inst.inst_opcode = DALLOCA) (fn_insts func)) ==>
    t.vs_initial_fmp = s.vs_initial_fmp /\
    LENGTH s.vs_memory <= LENGTH t.vs_memory) ==>
  stmt_state_rel H ctx func cenv cx es' t
Proof
  strip_tac >>
  `es'.scopes = es.scopes /\ es'.immutables = es.immutables` by
    (drule raw_call_kind_take_adopt_fields >> simp[]) >>
  `immutable_base_zero cenv t` by
    (irule immutable_base_zero_frame >> qexists_tac `s` >>
     fs[stmt_state_rel_def, lookup_var_def]) >>
  qpat_x_assum `es' = SND _` (SUBST_ALL_TAC o SYM) >>
  irule stmt_state_rel_allocas_frame >>
  qpat_assum `stmt_state_rel H ctx func cenv cx es s` (irule_at Any) >>
  qpat_assum `state_rel H func cenv cx es' t` (irule_at Any) >>
  simp[] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  rpt gen_tac >> TRY disch_tac >>
  irule immutable_alloca_sep_fields >> qexistsl_tac [`s`,`es`] >>
  simp[local_region_def, lookup_var_def] >>
  qpat_assum `stmt_state_rel H ctx func cenv cx es s`
    (mp_tac o REWRITE_RULE [stmt_state_rel_def]) >>
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

Theorem raw_call_success_code:
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

(* Forget temporary variables and control positions only in finish posts. *)
Definition raw_call_finish_view_def[local]:
  raw_call_finish_view (s:venom_state) =
    s with <|vs_vars := FEMPTY; vs_prev_bb := NONE;
             vs_current_bb := ""; vs_inst_idx := 0|>
End

Theorem raw_call_finish_view_control:
  raw_call_finish_view (jump_to l s) = raw_call_finish_view s /\
  raw_call_finish_view (s with vs_inst_idx := k) = raw_call_finish_view s
Proof
  simp[raw_call_finish_view_def, jump_to_def]
QED

(* raw_call_success_run without fresh_vars_wrt: s may hold temporaries of
   any age, and operands not fresh at sa keep their values. *)
Theorem raw_call_success_run_aged:
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
  simp[drop_fresh_def] >>
  disch_then (mp_tac o AP_TERM
    ``\v. raw_call_finish_view
      (mstore (w2n (addr:256 word))
        (n2w (MIN (LENGTH s.vs_returndata) cap)) v)``) >>
  simp[raw_call_finish_view_def, mstore_def]
QED

Finalise raw_call_success_run_aged

Theorem raw_call_kind_oracle_emit_run_aged:
  emit_op (case call_ty of RegularCall => CALL | StaticCall => STATICCALL | DelegateCall => DELEGATECALL)
    (if call_ty = RegularCall then [gas_op;to_op;val_op;dp;dl;op;Lit (n2w cap)]
     else [gas_op;to_op;dp;dl;op;Lit (n2w cap)]) sa = (ok,sb) /\
  stmt_state_rel H ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  eval_operand gas_op s = SOME gas /\ eval_operand to_op s = SOME aw /\
  eval_operand dp s = SOME ao /\ eval_operand dl s = SOME az /\
  eval_operand op s = SOME ro /\ eval_operand val_op s = SOME val_word /\
  w2w aw = target /\
  w2n (if call_ty = RegularCall then val_word else 0w) = (case value_opt of NONE => 0 | SOME n => n) /\
  (call_ty = StaticCall \/ cx.txn.is_static) = IS_NONE value_opt /\
  (!g. gas_cap = SOME g ==> g = w2n gas) /\
  (if call_ty = DelegateCall then take_delegate_outcome else take_call_outcome)
    gas_cap target (read_memory (w2n ao) (w2n az) s) value_opt es =
    (INL (rq,outcome),es1) /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
    b + sz <= w2n ro \/ w2n ro + w2n (n2w cap : bytes32) <= b) /\
  (cenv.ce_is_ctor ==> !src name tv v off.
    (src = cenv.ce_module \/ IS_SOME (ALOOKUP cenv.ce_modules src)) /\
    FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables src imms) name = SOME (tv,v) ==>
    off + type_memory_size tv <= w2n ro \/
      w2n ro + w2n (n2w cap : bytes32) <= off) ==>
  ?t u. run_inst_seq (emitted_insts sa sb) s = OK u /\
    u = update_var (STRING #"%" (toString sa.cs_next_var))
      (bool_to_word outcome.co_success) t /\
    eval_operand ok u = SOME (bool_to_word outcome.co_success) /\
    stmt_state_rel H ctx func cenv cx (SND (adopt_call_outcome rq outcome es1)) u /\
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
  qabbrev_tac `call_inst = mk_inst sa.cs_next_id (case call_ty of RegularCall => CALL | StaticCall => STATICCALL | DelegateCall => DELEGATECALL)
    ops [STRING #"%" (toString sa.cs_next_var)]` >>
  `call_inst.inst_outputs = [STRING #"%" (toString sa.cs_next_var)]` by
    simp[Abbr `call_inst`, mk_inst_def] >>
  drule_all_then (qx_choose_then `oracle_state` strip_assume_tac)
    raw_call_kind_memory_oracle_exec >>
  `s.vs_call_ctx.cc_static = cx.txn.is_static` by
    fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  `call_ty = RegularCall /\ s.vs_call_ctx.cc_static ==> val_word = 0w` by
    (strip_tac >> Cases_on `value_opt` >> gvs[wordsTheory.w2n_eq_0]) >>
  `oracle_state.vs_vars = s.vs_vars /\ oracle_state.vs_allocas = s.vs_allocas /\
   oracle_state.vs_alloca_next = s.vs_alloca_next /\
   oracle_state.vs_fmp = s.vs_fmp /\ oracle_state.vs_labels = s.vs_labels /\
   oracle_state.vs_initial_fmp = s.vs_initial_fmp` by
    (qpat_x_assum `oracle_state = _ with <| vs_outcomes := _; vs_requests := _;
       vs_accounts := _; vs_transient := _; vs_logs := _;
       vs_pending_deletions := _; vs_returndata := _; vs_memory := _ |>`
       (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `LENGTH s.vs_memory <= LENGTH oracle_state.vs_memory` by
    (qpat_x_assum `oracle_state.vs_memory = _` (fn th => rewrite_tac[th]) >>
     simp[NoAsms, venomMemPropsTheory.write_memory_with_expansion_nondecreasing]) >>
  drule_all_then (qspec_then `bool_to_word outcome.co_success`
    (qx_choose_then `result_state` strip_assume_tac)) raw_call_result_frame >>
  suspend "result"
QED

val raw_call_step_eqs =
  let
    fun is_call_clause th =
      let val opc = rhs (fst (dest_imp (snd (strip_forall (concl th)))))
      in List.exists (aconv opc) [``CALL``, ``STATICCALL``, ``DELEGATECALL``] end
  in
    List.filter is_call_clause (CONJUNCTS step_inst_base_opcode_eqs)
  end;

Resume raw_call_kind_oracle_emit_run_aged[result]:
  `step_inst_base call_inst s = OK result_state` by
    (qpat_assum `Abbrev (call_inst = _)` mp_tac >>
     qpat_assum `Abbrev (ops = _)` mp_tac >>
     qpat_assum `eval_operand gas_op s = SOME gas` mp_tac >>
     qpat_assum `eval_operand to_op s = SOME aw` mp_tac >>
     qpat_assum `eval_operand dp s = SOME ao` mp_tac >>
     qpat_assum `eval_operand dl s = SOME az` mp_tac >>
     qpat_assum `eval_operand op s = SOME ro` mp_tac >>
     qpat_assum `eval_operand val_op s = SOME val_word` mp_tac >>
     qpat_assum `_ /\ s.vs_call_ctx.cc_static ==> val_word = 0w` mp_tac >>
     qpat_assum `(if _ then exec_delegatecall _ _ _ _ _ _ _ _ else _) = _`
       mp_tac >>
     qpat_assum `result_state = update_var _ _ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     Cases_on `call_ty` >>
     Cases_on `s.vs_call_ctx.cc_static` >>
     Cases_on `outcome.co_success` >>
     gvs([Abbr `call_inst`, Abbr `ops`, mk_inst_def,
          eval_operand_def, bool_to_word_def] @ raw_call_step_eqs)) >>
  `run_inst_seq (emitted_insts sa sb) s = OK result_state` by
    (drule emitted_insts_emit_op >> strip_tac >>
     `emitted_insts sa sb = [call_inst]` by simp[Abbr `call_inst`, Abbr `ops`] >>
     qpat_assum `emitted_insts sa sb = [call_inst]` (fn th => once_rewrite_tac[th]) >>
     rewrite_tac[run_inst_seq_def] >>
     qpat_assum `step_inst_base call_inst s = OK result_state`
       (fn th => simp[NoAsms, th])) >>
  `stmt_state_rel H ctx func cenv cx (SND (adopt_call_outcome rq outcome es1)) oracle_state` by
    (irule raw_call_oracle_stmt_frame >> metis_tac[]) >>
  qexistsl_tac [`oracle_state`,`result_state`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qpat_x_assum `oracle_state = _` kall_tac >>
  qpat_assum `result_state = _` (fn th => once_rewrite_tac[th]) >>
  irule stmt_state_rel_update_var >> simp[] >>
  irule fresh_not_local_ptr >> qexists_tac `sa` >> simp[not_fresh_at_def]
QED

Finalise raw_call_kind_oracle_emit_run_aged

Theorem raw_call_oracle_emit_run_aged:
  emit_op (if stat then STATICCALL else CALL)
    (if stat then [gas_op;to_op;dp;dl;op;Lit (n2w cap)]
     else [gas_op;to_op;val_op;dp;dl;op;Lit (n2w cap)]) sa = (ok,sb) /\
  stmt_state_rel H ctx func cenv cx es s /\ local_ptrs_reserved cenv sa /\
  eval_operand gas_op s = SOME gas /\ eval_operand to_op s = SOME aw /\
  eval_operand dp s = SOME ao /\ eval_operand dl s = SOME az /\
  eval_operand op s = SOME ro /\ eval_operand val_op s = SOME val_word /\
  w2w aw = target /\
  w2n (if stat then 0w else val_word) = (case value_opt of NONE => 0 | SOME n => n) /\
  (stat \/ cx.txn.is_static) = IS_NONE value_opt /\
  (!g. gas_cap = SOME g ==> g = w2n gas) /\
  take_call_outcome gas_cap target (read_memory (w2n ao) (w2n az) s) value_opt es =
    (INL (rq,outcome),es1) /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
    b + sz <= w2n ro \/ w2n ro + w2n (n2w cap : bytes32) <= b) /\
  (cenv.ce_is_ctor ==> !src name tv v off.
    (src = cenv.ce_module \/ IS_SOME (ALOOKUP cenv.ce_modules src)) /\
    FLOOKUP cenv.ce_module_vars (src,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables src imms) name = SOME (tv,v) ==>
    off + type_memory_size tv <= w2n ro \/
      w2n ro + w2n (n2w cap : bytes32) <= off) ==>
  ?t u. run_inst_seq (emitted_insts sa sb) s = OK u /\
    u = update_var (STRING #"%" (toString sa.cs_next_var))
      (bool_to_word outcome.co_success) t /\
    eval_operand ok u = SOME (bool_to_word outcome.co_success) /\
    stmt_state_rel H ctx func cenv cx (SND (adopt_call_outcome rq outcome es1)) u /\
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
  Cases_on `stat` >> simp[]
  >- MATCH_ACCEPT_TAC (raw_call_kind_oracle_emit_run_aged |>
      Q.INST [`call_ty` |-> `StaticCall`] |> SIMP_RULE (srw_ss()) [])
  >> MATCH_ACCEPT_TAC (raw_call_kind_oracle_emit_run_aged |>
      Q.INST [`call_ty` |-> `RegularCall`] |> SIMP_RULE (srw_ss()) [])
QED


Theorem raw_call_oracle_frame:
  wb_frame cenv es es' sa s0 s /\
  t.vs_vars = s.vs_vars /\ t.vs_allocas = s.vs_allocas /\
  t.vs_memory = (write_memory_with_expansion dst payload s).vs_memory /\
  (!aid b sz. aid < sa.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
    loweringStateRelDefs$regions_disjoint dst (LENGTH payload) b sz) /\
  (!name b sz. local_region cenv es.scopes s0 name b sz ==>
    loweringStateRelDefs$regions_disjoint dst (LENGTH payload) b sz) /\
  ~not_fresh_at sa out ==>
  wb_frame cenv es es' sa s0 (update_var out result t)
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

(* A raw call's outcome leaves the source scopes alone, so a frame at the
   pre-call state holds at the post-call one. *)
Theorem raw_call_none_post:
  storage_well_formed_on cx es' (FST H) /\
  expr_has_effect e /\
  expr_type e = NoneT /\ post_value_type cenv e = expr_type e /\
  stmt_state_rel H ctx func cenv cx es' s /\
  wb_frame cenv es es' sa s0 s ==>
  vv_post H ctx func cenv cx e es sa sb s0 es' (Value NoneV)
    (StackValue ann (Lit 0w)) s
Proof
  strip_tac >> irule vv_post_frame_intro >>
  simp[vv_holds_def, vv_at_def, read_result_def, return_def,
    expr_val_rel_def, expr_val_at_def, eval_operand_def,
    vyperValueTheory.evaluate_type_def, is_word_type_def,
    val_in_memory_def, val_wf_def, val_footprint_def, type_memory_size_def]
QED

Theorem raw_call_bool_post:
  storage_well_formed_on cx es' (FST H) /\
  expr_has_effect e /\
  post_value_type cenv e = expr_type e /\
  expr_type e = BaseT BoolT /\
  stmt_state_rel H ctx func cenv cx es' s /\
  expr_val_rel cx (expr_type e) (BoolV success) result s /\
  wb_frame cenv es es' sa s0 s ==>
  vv_post H ctx func cenv cx e es sa sb s0 es' (Value (BoolV success))
    (StackValue ann result) s
Proof
  strip_tac >> irule vv_post_word_intro >>
  gvs[expr_val_rel_def, is_word_type_def]
QED

Theorem raw_call_tuple_post:
  storage_well_formed_on cx es' (FST H) /\
  expr_has_effect e /\
  post_value_type cenv e = expr_type e /\
  expr_type e = TupleT [BaseT BoolT;BaseT (BytesT (Dynamic n))] /\
  evaluate_type (get_tenv cx) (expr_type e) =
    SOME (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))]) /\
  stmt_state_rel H ctx func cenv cx es' s /\
  wb_frame cenv es es' sa s0 s /\
  eval_operand result s = SOME w /\
  FLOOKUP s.vs_allocas aid = SOME (w2n w,64 + ((n+31) DIV 32)*32) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  (!name lb lsz. local_region cenv es'.scopes s name lb lsz ==>
    w2n w + (64 + ((n+31) DIV 32)*32) <= lb \/ lb + lsz <= w2n w) /\
  val_in_memory (TupleTV [BaseTV BoolT;BaseTV (BytesT (Dynamic n))])
    (ArrayV (TupleV [BoolV success;BytesV (TAKE n bytes)])) (w2n w) s.vs_memory ==>
  vv_post H ctx func cenv cx e es sa sb s0 es'
    (Value (ArrayV (TupleV [BoolV success;BytesV (TAKE n bytes)])))
    (LocatedValue (expr_type e) (mk_ptr result LocMemory)) s
Proof
  strip_tac >> irule vv_post_allocated_memory_intro >>
  simp[is_word_type_def, contextTheory.mk_ptr_def] >>
  qexistsl_tac [`aid`,`w2n w`,`64 + ((n+31) DIV 32)*32`] >>
  simp[val_wf_def, LENGTH_TAKE_EQ, val_footprint_def, type_memory_size_def] >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum drule >> simp[arithmeticTheory.MULT_COMM]) >>
  simp[vfmConstantsTheory.word_size_def] >>
  qspec_then `n` mp_tac valueTypingMemoryPropsTheory.word_size_capacity >>
  simp[vfmConstantsTheory.word_size_def] >> decide_tac
QED


Theorem raw_call_outbuf_alloca_inst:
  compile_raw_call_outbuf cap sa = ((ov,op),sm) /\ fn_has_code sa sm func ==>
  ?alloc. MEM alloc (fn_insts func) /\ alloc.inst_opcode = ALLOCA /\
    alloc.inst_id = sa.cs_next_id
Proof
  strip_tac >>
  `?alloc. MEM alloc (emitted_insts sa sm) /\ alloc.inst_opcode = ALLOCA /\
    alloc.inst_id = sa.cs_next_id` by
    (Cases_on `cap = 0`
     >- (gvs[compile_raw_call_outbuf_def, contextTheory.compile_alloc_buffer_def,
              emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
              fresh_id_def, fresh_var_def, emit_def, emitted_insts_def,
              rich_listTheory.DROP_LENGTH_APPEND, mk_inst_def]) >>
     `0 < cap` by decide_tac >>
     drule_all raw_call_outbuf_positive_code >> strip_tac >>
     qexists_tac `mk_inst sa.cs_next_id ALLOCA
       [Lit (n2w (((cap+31) DIV 32)*32+32))]
       [STRING #"%" (toString sa.cs_next_var)]` >>
     asm_rewrite_tac[] >> simp[mk_inst_def]) >>
  metis_tac[exprSimHashTheory.hash_emitted_inst_mem]
QED

Theorem raw_call_outbuf_allocation_site:
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

(* The keyword operands of either raw call are uint256 expressions that satisfy
   the body precondition from any invariant state. *)
Theorem raw_call_keywords_pre_for_target:
  expr_body_pre cenv cx env (Call ann target args dflt) es /\
  ((target = RawCallTarget flags /\ args = a::d::kws) \/
   (target = RawCallCalldataTarget flags /\ args = a::kws)) ==>
  raw_call_kws_ok flags kws /\ LENGTH kws = LENGTH flags.rcf_kws /\
  EVERY (\e. expr_type e = BaseT (UintT 256) /\
    !st. expr_sim_inv cenv cx env st ==> expr_body_pre cenv cx env e st) kws
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `raw_call_kws_ok flags kws /\ LENGTH kws = LENGTH flags.rcf_kws` by
    (qpat_assum `expr_body_pre cenv cx env (Call ann target args dflt) es` mp_tac >>
     qpat_assum `_ \/ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >>
     gvs[expr_body_pre_def,well_typed_expr_def]) >>
  drule raw_call_kwargs_types >> strip_tac >>
  simp[EVERY_MEM] >> qx_gen_tac `e` >> disch_tac >> conj_tac
  >- fs[EVERY_MEM] >>
  qx_gen_tac `st` >> disch_tac >>
  irule expr_body_pre_raw_call_target_arg >> simp[] >>
  qexistsl [`ann`,`args`,`dflt`,`es`,`flags`,`target`] >> simp[] >>
  qpat_assum `_ \/ _` strip_assume_tac >> gvs[]
QED

Theorem raw_call_keywords_pre:
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) dflt) es ==>
  raw_call_kws_ok flags kws /\ LENGTH kws = LENGTH flags.rcf_kws /\
  EVERY (\e. expr_type e = BaseT (UintT 256) /\
    !st. expr_sim_inv cenv cx env st ==> expr_body_pre cenv cx env e st) kws
Proof
  strip_tac >>
  irule raw_call_keywords_pre_for_target >>
  qexistsl [`a`,`ann`,`a::d::kws`,`d`,`dflt`,`es`,`RawCallTarget flags`] >> simp[]
QED

Theorem raw_call_keyword_values:
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
    typed_args_post H ctx func cenv cx es sa s0 es' ks xs vs s /\
    EVERY (\e. expr_type e = BaseT (UintT 256)) ks ==>
    LIST_REL (\x v. eval_operand x s = SOME
      (typed_val_to_w256 (BaseTV (UintT 256)) v)) xs vs
Proof
  simp[typed_args_post_def] >> rpt strip_tac >>
  qpat_x_assum `LIST_REL _ _ _` mp_tac >>
  qpat_x_assum `LENGTH ks = LENGTH vs` mp_tac >>
  qpat_x_assum `EVERY _ ks` mp_tac >>
  rpt (pop_assum kall_tac) >>
  map_every qid_spec_tac [`xs`, `vs`, `ks`] >>
  Induct >> rpt gen_tac >> Cases_on `xs` >> Cases_on `vs` >>
  simp[vyperValueTheory.evaluate_type_def] >>
  rpt strip_tac >> gvs[vyperValueTheory.evaluate_type_def] >>
  first_x_assum irule >> simp[]
QED

Theorem raw_call_value_operand:
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

Theorem raw_call_kwarg_mem:
  !ks (ops : operand list) g.
    ext_call_kwarg key ks ops = SOME g ==> MEM g ops
Proof
  Induct_on `ks` >> Cases_on `ops` >>
  simp[ext_call_kwarg_def] >> rpt strip_tac >>
  rename1 `(if k = key then SOME op else _) = SOME g` >>
  Cases_on `k = key` >> gvs[] >> metis_tac[]
QED

Theorem raw_call_keywords_decode[local]:
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) dflt) es /\
  expr_sim_inv cenv cx env es2 /\
  eval_exprs cx kws es2 = (INL kvs,es') /\
  typed_args_post H ctx func cenv cx es0 sa s0 es' kws xs kvs s ==>
  ?amount. raw_call_value flags.rcf_kws kvs = SOME amount /\
    eval_operand (case ext_call_kwarg EKValue flags.rcf_kws xs of
      NONE => Lit 0w | SOME x => x) s = SOME (n2w amount) /\
    amount < dimword (:256) /\
    (flags.rcf_is_static ==> amount = 0) /\
    LENGTH kvs = LENGTH flags.rcf_kws /\ expr_sim_inv cenv cx env es'
Proof
  strip_tac >> drule raw_call_keywords_pre >> strip_tac >>
  `EVERY (\e. expr_type e = BaseT (UintT 256)) kws` by fs[EVERY_MEM] >>
  drule_all raw_call_keyword_values >> strip_tac >>
  drule_all raw_call_keywords_post >> strip_tac >>
  drule_all raw_call_value_operand >>
  disch_then (qspec_then `flags.rcf_kws` strip_assume_tac) >>
  `LENGTH kvs = LENGTH flags.rcf_kws` by decide_tac >>
  qexists_tac `amount` >> fs[] >> strip_tac >>
  `~MEM EKValue flags.rcf_kws` by fs[raw_call_kws_ok_def] >>
  gvs[raw_call_value_def, ext_call_kwarg_not_mem]
QED

Theorem raw_call_prefix_source_ready:
  expr_body_pre cenv cx env (Call ann (RawCallTarget flags) (a::d::kws) dflt) es /\
  bind (eval_expr cx a) (read_result cx) (es with gas_obs := gsA) = (INL av,esA) /\
  bind (eval_expr cx d) (read_result cx) (esA with gas_obs := gsD) =
    (INL (BytesV bs),esD) /\
  eval_exprs cx kws (esD with gas_obs := gsK) = (INL kvs,esK) /\
  expr_val_rel cx (BaseT AddressT) av addr t /\
  typed_args_post H ctx func cenv cx esD s4 tm esK kws xs kvs tk /\
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


Theorem raw_call_source_tail:
  (cx.txn.is_static ==> amount = 0) /\ ~flags.rcf_is_delegate /\
  (flags.rcf_is_static ==> amount = 0) /\ IS_SOME es.outcomes /\
  outcomes_accounts_typed es.outcomes /\
  accounts_runtime_well_typed es.accounts ==>
  (es.outcomes = SOME [] /\
   eval_raw_call cx flags target bytes amount gas es =
     (INR (Error (RuntimeError "take_call_outcome")),es)) \/
  ?rq outcome es1 es2.
    take_call_outcome (OPTION_BIND gas dest_NumV) target bytes
      (if flags.rcf_is_static \/ cx.txn.is_static then NONE else SOME amount) es =
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
  Cases_on `es.outcomes = SOME []`
  >- (disj1_tac >> simp[] >> irule raw_call_exhausted >> simp[]) >>
  disj2_tac >>
  drule_all raw_call_typed_outcome >>
  disch_then (qspecl_then [`target`, `bytes`,
    `if flags.rcf_is_static \/ cx.txn.is_static then NONE else SOME amount`,
    `OPTION_BIND gas dest_NumV`] strip_assume_tac) >>
  gvs[] >>
  Cases_on `adopt_call_outcome rq outcome es1` >>
  drule adopt_call_outcome_frame >> strip_tac >> gvs[] >>
  drule_all raw_call_oracle_result >> strip_tac >>
  conj_tac
  >- (Cases_on `flags.rcf_revert_on_failure /\ ~outcome.co_success` >> simp[]) >>
  Cases_on `flags.rcf_revert_on_failure /\ ~outcome.co_success` >>
  qspecl_then [`cx`,`flags`,`target`,`bytes`,`amount`,`gas`,`es`] mp_tac
    calldata_raw_call_gas_obs >> simp[]
QED

Theorem raw_call_oracle_empty:
  ~(flags.rcf_is_delegate /\ flags.rcf_is_static) /\
  ((flags.rcf_is_delegate \/ flags.rcf_is_static \/ cx.txn.is_static) ==>
     amount = 0) /\
  es.outcomes = SOME [] ==>
  eval_raw_call cx flags target bytes amount gas es =
    (INR (Error (RuntimeError "take_call_outcome")),es)
Proof
  Cases_on `flags.rcf_is_delegate` >>
  Cases_on `flags.rcf_is_static` >> Cases_on `cx.txn.is_static` >>
  simp[eval_raw_call_def, frame_call_value_def, take_call_outcome_def,
       take_delegate_outcome_def, take_request_outcome_def, type_check_def,
       check_def, assert_def, bind_def, ignore_bind_def, return_def, raise_def]
QED

Theorem raw_call_kind_source_tail:
  (cx.txn.is_static ==> amount = 0) /\
  ((flags.rcf_is_delegate \/ flags.rcf_is_static) ==> amount = 0) /\
  ~(flags.rcf_is_delegate /\ flags.rcf_is_static) /\
  IS_SOME es.outcomes /\ outcomes_accounts_typed es.outcomes /\
  accounts_runtime_well_typed es.accounts ==>
  (es.outcomes = SOME [] /\
   eval_raw_call cx flags target bytes amount gas es =
     (INR (Error (RuntimeError "take_call_outcome")),es)) \/
  ?rq outcome es1 es2.
    (if flags.rcf_is_delegate then take_delegate_outcome else take_call_outcome)
      (OPTION_BIND gas dest_NumV) target bytes
      (if flags.rcf_is_static \/ cx.txn.is_static then NONE else SOME amount) es =
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
    es2.gas_obs = es.gas_obs /\ LENGTH outcome.co_returnData < dimword (:256) /\
    (!gs. eval_raw_call cx flags target bytes amount gas (es with gas_obs := gs) =
      (FST (eval_raw_call cx flags target bytes amount gas es),es2 with gas_obs := gs))
Proof
  Cases_on `flags.rcf_is_delegate` >>
  disch_then (map_every assume_tac o CONJUNCTS)
  >- (gvs[] >> drule_all raw_delegate_call_source_tail >> simp[]) >>
  gvs[] >> drule_all raw_call_source_tail >>
  disch_then (qspecl_then [`target`, `gas`, `bytes`] strip_assume_tac) >>
  simp[] >> drule_all calldata_take_call_outcome_bound >> simp[]
QED

Theorem compile_expr_raw_call:
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
