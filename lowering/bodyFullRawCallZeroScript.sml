(* The zero-cap normal suffix uses the given call endpoint, with no ghost update. *)
Theory bodyFullRawCallZero
Ancestors
  exprSimRawCall exprSimRawCallCalldata fragGasEmitCtrl callStepPtr
  context fragGasOriginPtr bodyPtrDefs vyperInterpreter vyperState compileEnv
  exprLoweringProps fragExec emitHelperProps ptrDiscipline venomState

Theorem raw_call_zero_normal_suffix_joint:
  compile_raw_call_finish to_op dp dl gas_op val_op
    (if stat then StaticCall else RegularCall) 0 rev ov op sa = (result,sb) /\
  emit_op (if stat then STATICCALL else CALL)
    (if stat then [gas_op;to_op;dp;dl;op;Lit 0w]
     else [gas_op;to_op;val_op;dp;dl;op;Lit 0w]) sa = (ok,sc) /\
  (rev ==> success) /\
  eval_operand ok s = SOME (if success then 1w else 0w) /\
  op_taint tn ok = {} /\ op_prov G ok = NONE /\
  fn_has_code sc sb func /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  ~s.vs_halted /\ s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\
  t = (if rev then jump_to sb.cs_current_bb s else s) ==>
  result = (if rev then Lit 0w else ok) /\
  sb.cs_current_insts = (if rev then [] else sc.cs_current_insts) /\
  ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  eval_operand result t = SOME (if rev then 0w else if success then 1w else 0w) /\
  op_taint tn result = {} /\ op_prov G result = NONE /\
  (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK t,G,tn)) /\
  (!cx ann ee. ptr_vv_ok cx (if rev then NoneT else BaseT BoolT)
    (Value (if rev then NoneV else BoolV success))
    (StackValue ann result) ee G tn t)
Proof
  strip_tac >> Cases_on `rev`
  >- (gvs[] >> drule raw_call_finish_revert_compile >>
      simp[comp_return_def] >> strip_tac >>
      rename1 `fresh_label "call_failed" call_end = (fl,sl)` >>
      rename1 `emit_inst JNZ [status;Label good;Label bad] [] sj = ((),sn)` >>
      `call_end = sc /\ status = ok` by (Cases_on `stat` >> gvs[]) >>
      gvs[] >>
      `sb.cs_current_bb = good /\ sb.cs_current_insts = []` by
        metis_tac[emitHelperPropsTheory.new_block_props] >>
      `fn_has_code sj sn func /\ sj.cs_current_bb = call_end.cs_current_bb /\
       sj.cs_current_insts = call_end.cs_current_insts` by suspend "metadata" >>
      `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
        (s,G,tn) [] (OK (jump_to good s),G,tn)` by
        (rpt gen_tac >> metis_tac[emit_jnz_origin_ptr]) >>
      simp[venomStateTheory.jump_to_def, venomStateTheory.eval_operand_def,
           op_taint_def, ptr_vv_ok_def, read_result_def, return_def, ptr_val_ok_none]) >>
  gvs[] >> drule raw_call_nonrevert_finish_code >> simp[comp_return_def] >>
  strip_tac >> Cases_on `stat` >> gvs[] >>
  (conj_tac >- simp[gas_origin_ptr_path_rules] >>
   simp[ptr_vv_ok_def, read_result_def, return_def, ptr_val_ok_def, is_word_type_def])
QED

Resume raw_call_zero_normal_suffix_joint[metadata]:
  `ci_mono call_end sl /\ ci_mono sl sj /\ ci_mono sj sn /\
   ci_mono sn s5 /\ ci_mono s5 s6 /\ ci_mono s6 s7 /\
   ci_mono s7 s8 /\ ci_mono s8 s9 /\ ci_mono s9 sb` by
    (rpt conj_tac >> metis_tac[ci_mono_fresh_label, ci_mono_emit_inst,
      ci_mono_new_block, ci_mono_emit_op, ci_mono_compile_alloc_buffer,
      ci_mono_emit_void, pairTheory.SND]) >>
  `cs_extends call_end sj /\ cs_extends sj sn /\ cs_extends sn sb` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  conj_tac >- metis_tac[fn_has_code_mid] >>
  imp_res_tac fresh_label_props >> simp[]
QED

Finalise raw_call_zero_normal_suffix_joint
