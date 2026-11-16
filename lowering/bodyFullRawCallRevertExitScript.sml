(* Failed CALL follows the same JNZ and uncapped forwarding execution. *)
Theory bodyFullRawCallRevertExit
Ancestors
  bodyFullRawCallFailure fragGasEmitCtrl exprSimDefs exprSimRawCallCalldata
  fragGasOriginPtr exprLoweringProps emitHelperProps emitHelper compileEnv context
  venomState venomInst fragExec ptrDiscipline list

Theorem raw_call_revert_suffix_full_exit:
  compile_raw_call_finish to_op dp dl gas_op val_op
    (if stat then StaticCall else RegularCall) n T ov op sa = (result,sb) /\
  emit_op (if stat then STATICCALL else CALL)
    (if stat then [gas_op;to_op;dp;dl;op;Lit (n2w n)]
     else [gas_op;to_op;val_op;dp;dl;op;Lit (n2w n)]) sa = (ok,sc) /\
  eval_operand ok s = SOME 0w /\ op_taint tn ok = {} /\ op_prov G ok = NONE /\
  fn_has_code sc sb func /\ ~ctx_has_dalloca ctx /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~s.vs_halted /\
  s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\
  LENGTH s.vs_returndata < dimword (:256) ==>
  ?u Gf tnf.
    u.vs_returndata = s.vs_returndata /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (Abort Revert_abort u,Gf,tnf)) /\
    (!H cx ee.
      expr_exit (INR (Error (RevertData s.vs_returndata))) (Abort Revert_abort u) /\
      halt_exit H cx ee (INR (Error (RevertData s.vs_returndata)))
        (Abort Revert_abort u) /\
      (ctx_has_dalloca ctx ==> !t. Abort Revert_abort u = Halt t ==> allocas_below_fmp t))
Proof
  strip_tac >> drule raw_call_finish_revert_compile >> strip_tac >>
  rename1 `fresh_label "call_failed" call_end = (fl,sl)` >>
  rename1 `emit_inst JNZ [status;Label good;Label bad] [] sj = ((),sn)` >>
  `call_end = sc /\ status = ok` by (Cases_on `stat` >> gvs[]) >>
  gvs[] >>
  `fn_has_code sj sn func /\ fn_has_code s5 s9 func /\
   sj.cs_current_bb = call_end.cs_current_bb /\
   sj.cs_current_insts = call_end.cs_current_insts /\
   s5.cs_current_bb = bad /\ s5.cs_current_insts = []` by suspend "metadata" >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s,G,tn) [] (OK (jump_to bad s),G,tn)` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`emit_inst JNZ _ _ _ = _`, `fn_has_code sj sn func`,
        `~ctx_has_dalloca ctx`, `allocas_from lo s`,
        `eval_operand ok s = SOME 0w`, `op_taint tn ok = {}`,
        `s.vs_current_bb = call_end.cs_current_bb`,
        `s.vs_inst_idx = LENGTH call_end.cs_current_insts`, `~s.vs_halted`,
        `sj.cs_current_bb = call_end.cs_current_bb`,
        `sj.cs_current_insts = call_end.cs_current_insts`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     metis_tac[emit_jnz_origin_ptr]) >>
  `?t. run_inst_seq (emitted_insts s5 s9) (jump_to bad s) = Abort Revert_abort t /\
       t.vs_returndata = s.vs_returndata` by suspend "run" >>
  `?Gf tnf. !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (jump_to bad s,G,tn) []
    (Abort Revert_abort (t with vs_inst_idx := 3),Gf,tnf)` by
    (map_every (fn q => qpat_assum q mp_tac)
       [`emit_op RETURNDATASIZE [] _ = _`, `compile_alloc_buffer 0 _ = _`,
        `emit_void RETURNDATACOPY _ _ = _`, `emit_inst REVERT _ _ _ = _`,
        `fn_has_code s5 s9 func`, `~s.vs_halted`, `~ctx_has_dalloca ctx`,
        `allocas_from lo s`, `lo <= s.vs_alloca_next`,
        `s5.cs_current_bb = bad`, `s5.cs_current_insts = []`,
        `LENGTH s.vs_returndata < dimword (:256)`,
        `run_inst_seq _ _ = Abort Revert_abort t`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     drule_at (Pat `run_inst_seq _ _ = _`) raw_call_failure_block_origin_ptr >>
     simp[jump_to_def,allocas_from_def] >>
     gvs[allocas_from_def] >> metis_tac[]) >>
  qexistsl_tac [`t with vs_inst_idx := 3`,`Gf`,`tnf`] >>
  simp[expr_exit_def,halt_exit_def] >> gen_tac >>
  qpat_x_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _`
    (qspec_then `D` assume_tac) >>
  drule gas_origin_ptr_path_append >> simp[] >>
  disch_then irule >> simp[]
QED

Resume raw_call_revert_suffix_full_exit[metadata]:
  `ci_mono s10 sb` by
    (qpat_x_assum `(if _ then _ else _) s10 = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> IF_CASES_TAC >>
     simp[comp_return_def] >> strip_tac >>
     TRY (gvs[ci_mono_refl] >> NO_TAC) >>
     `ci_mono s10 (SND ((do
       rds2 <- emit_op RETURNDATASIZE [];
       cmp <- emit_op LT [rds2;Lit (n2w n)];
       capped <- compile_select cmp rds2 (Lit (n2w n));
       emit_void MSTORE [ov;capped]; comp_return ov od) s10))`
       suffices_by gvs[] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     rpt (FIRST [
       CHANGED_TAC (simp[LET_THM,pairTheory.FORALL_PROD,pairTheory.UNCURRY_DEF,
         ci_mono_emit_op,ci_mono_emit_void,ci_mono_emit_inst,
         ci_mono_compile_select,ci_mono_comp_return]),
       gen_tac, ho_match_mp_tac ci_mono_bind >> conj_tac,
       ho_match_mp_tac ci_mono_ignore_bind >> conj_tac])) >>
  `ci_mono call_end sl /\ ci_mono sl sj /\ ci_mono sj sn /\
   ci_mono sn s5 /\ ci_mono s5 s6 /\ ci_mono s6 s7 /\
   ci_mono s7 s8 /\ ci_mono s8 s9 /\ ci_mono s9 s10` by
    (rpt conj_tac >> metis_tac[ci_mono_fresh_label,ci_mono_emit_inst,
      ci_mono_new_block,ci_mono_emit_op,ci_mono_compile_alloc_buffer,
      ci_mono_emit_void,pairTheory.SND]) >>
  `cs_extends call_end sj /\ cs_extends sj sn /\ cs_extends sn sb /\
   cs_extends call_end s5 /\ cs_extends s5 s9 /\ cs_extends s9 sb` by
    (fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  rpt conj_tac
  >- metis_tac[fn_has_code_mid]
  >- metis_tac[fn_has_code_mid]
  >- (imp_res_tac fresh_label_props >> simp[])
  >- (imp_res_tac fresh_label_props >> simp[]) >>
  metis_tac[new_block_props]
QED

Resume raw_call_revert_suffix_full_exit[run]:
  map_every (fn q => qpat_x_assum q mp_tac)
    [`emit_op RETURNDATASIZE [] _ = _`,
     `compile_alloc_buffer 0 _ = _`,
     `emit_void RETURNDATACOPY _ _ = _`,
     `emit_inst REVERT _ _ _ = _`,
     `LENGTH s.vs_returndata < dimword (:256)`] >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  simp[compile_alloc_buffer_def, emit_op_def, emit_void_def, emit_inst_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def,
       fresh_var_def, fresh_id_def, emit_def] >>
  rpt strip_tac >> gvs[] >>
  simp[emitted_insts_def,GSYM APPEND_ASSOC,rich_listTheory.DROP_LENGTH_APPEND] >>
  irule raw_call_revert_run >>
  simp[ASCIInumbersTheory.toString_11,jump_to_def]
QED

Finalise raw_call_revert_suffix_full_exit
