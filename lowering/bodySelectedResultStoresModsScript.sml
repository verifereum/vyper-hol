(* Execute the caller's result stores at the reached INVOKE successor. *)
Theory bodySelectedResultStoresMods
Ancestors
  intCallResultFull intCallStep intCallFrame venomExecSemantics
  bodyPtrDefs ptrDiscipline venomState exprLoweringProps
  fragGasOriginPtrLoop fragExecMem emitHelperProps finite_map words list pred_set

Theorem bound_result_operands[local]:
  bind_outputs outs ws before_bind = SOME u /\ ALL_DISTINCT outs ==>
  LENGTH outs = LENGTH ws /\
  MAP (\op. eval_operand op (u with vs_inst_idx := k)) (MAP Var outs) =
    MAP SOME ws
Proof
  strip_tac >> drule_all intCallStepTheory.bind_outputs_lookup >> strip_tac >>
  simp[listTheory.LIST_EQ_REWRITE, listTheory.EL_MAP,
       venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def] >>
  fs[venomStateTheory.lookup_var_def]
QED

Theorem result_store_entry[local]:
  bind_outputs outs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state t cs)) = SOME u /\
  ir.iret_adopt_fmp = NONE /\ ALL_DISTINCT outs /\ ~MEM root outs /\
  lookup_var root t = SOME (n2w off) /\ FLOOKUP G root = SOME (off,cap) /\
  op_taint tn (Var root) = {} /\ off + cap < dimword (:256) /\
  off + cap <= t.vs_alloca_next /\ allocas_from lo t /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ ~t.vs_halted ==>
  let a = u with vs_inst_idx := SUC t.vs_inst_idx in
  let J = DRESTRICT G (COMPL (set outs)) in
  let N = tc with t_var := DRESTRICT tn.t_var (COMPL (set outs)) in
    lookup_var root a = SOME (n2w off) /\ ptr_covers J N root a cap /\
    EVERY (\op. op_taint N op = {}) (MAP Var outs) /\
    off + cap <= a.vs_alloca_next /\ allocas_from lo a /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp a) /\
    ~a.vs_halted /\ a.vs_current_bb = t.vs_current_bb
Proof
  strip_tac >> simp[] >>
  drule intCallFrameTheory.invoke_return_frame >> strip_tac >>
  `lookup_var root u = SOME (n2w off)` by simp[] >>
  `off < dimword (:256)` by decide_tac >>
  `lookup_var root (u with vs_inst_idx := SUC t.vs_inst_idx) = SOME (n2w off)` by
    fs[venomStateTheory.lookup_var_def] >>
  conj_tac >- simp[] >>
  conj_tac
  >- (simp[bodyPtrDefsTheory.ptr_covers_def, ptrDisciplineTheory.op_taint_def,
           finite_mapTheory.FLOOKUP_DRESTRICT, wordsTheory.w2n_n2w] >>
      fs[ptrDisciplineTheory.op_taint_def]) >>
  conj_tac
  >- simp[EVERY_MAP, EVERY_MEM, ptrDisciplineTheory.op_taint_def,
          finite_mapTheory.FLOOKUP_DRESTRICT] >>
  drule_all intCallStepTheory.bind_outputs_lookup >> strip_tac >>
  qpat_x_assum `u = _` SUBST1_TAC >>
  fs[venomExecSemanticsTheory.adopt_return_fmp_def,
     venomExecSemanticsTheory.merge_callee_state_def,
     ptrDisciplineTheory.allocas_from_def, ptrDisciplineTheory.allocas_below_fmp_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  strip_tac >> qpat_x_assum `ctx_has_dalloca _ ==> _` drule >>
  strip_tac >> first_assum ACCEPT_TAC
QED

Theorem selected_result_stores_mods:
  0 < (nret:num) /\ LENGTH outs = nret /\ ALL_DISTINCT outs /\
  bind_outputs outs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state t cs)) = SOME u /\
  ir.iret_adopt_fmp = NONE /\
  store_multi_results (Var root) (MAP Var outs) 0 st4 = ((),sm) /\
  fn_has_code st4 sm func /\ LENGTH st4.cs_current_insts = SUC t.vs_inst_idx /\
  st4.cs_current_bb = t.vs_current_bb /\ ~t.vs_halted /\
  not_fresh_at st4 root /\ ~MEM root outs /\
  (!x. MEM x outs ==> not_fresh_at st4 x) /\
  lookup_var root t = SOME (n2w off) /\
  FLOOKUP t.vs_allocas aid = SOME (off,32 * nret) /\
  FLOOKUP G root = SOME (off,32 * nret) /\ op_taint tn (Var root) = {} /\
  off + 32 * nret < dimword (:256) /\ off + 32 * nret <= t.vs_alloca_next /\
  allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) ==>
  let a = u with vs_inst_idx := SUC t.vs_inst_idx in
  let J = DRESTRICT G (COMPL (set outs)) in
  let N = tc with t_var := DRESTRICT tn.t_var (COMPL (set outs)) in
  ?stored Gs ts.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (a,J,N) []
      (OK (stored with vs_inst_idx := LENGTH sm.cs_current_insts),Gs,ts)) /\
    run_inst_seq (emitted_insts st4 sm) a = OK stored /\
    sm.cs_current_insts = st4.cs_current_insts ++ emitted_insts st4 sm /\
    same_blocks st4 sm /\ st4.cs_next_var <= sm.cs_next_var /\
    st4.cs_next_id <= sm.cs_next_id /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts st4 sm) /\
    (stored with <|vs_vars := a.vs_vars; vs_memory := a.vs_memory|>) = a /\
    FLOOKUP stored.vs_allocas aid = SOME (off,32 * nret) /\
    (!x. not_fresh_at st4 x ==>
      lookup_var x stored = lookup_var x u /\ FLOOKUP Gs x = FLOOKUP J x /\
      op_taint ts (Var x) = op_taint N (Var x)) /\
    ts.t_mem = tc.t_mem DIFF {i | off <= i /\ i < off + 32 * nret} /\
    ts.t_stor = tc.t_stor /\ ts.t_trans = tc.t_trans /\ ts.t_imm = tc.t_imm /\
    (!mem i. mem_agree_outside ts.t_mem stored.vs_memory mem /\ i < LENGTH ir.iret_values ==>
      mem_word_at (off + 32 * i) mem = EL i ir.iret_values) /\
    (!b len. b + len <= off \/ off + 32 * nret <= b ==>
      mem_bytes_at b len stored.vs_memory = mem_bytes_at b len u.vs_memory)
Proof
  strip_tac >>
  drule_all result_store_entry >> disch_then (qspec_then `tc` mp_tac) >>
  pure_rewrite_tac[LET_THM] >> CONV_TAC (DEPTH_CONV BETA_CONV) >> strip_tac >>
  drule_all bound_result_operands >>
  disch_then (qspec_then `SUC t.vs_inst_idx` strip_assume_tac) >>
  drule intCallResultTheory.store_multi_results_shape >> strip_tac >>
  drule_at (Pat `ptr_covers _ _ _ _ _`) intCallResultFullTheory.store_multi_results_origin_ptr >>
  disch_then drule >>
  disch_then (drule_at (Pat `MAP _ _ = _`)) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `ctx_has_dalloca _ ==> allocas_below_fmp _`)) >>
  disch_then (qspecl_then [`lo`,`explicit`,`n2w off`,`PG`] mp_tac) >>
  `off < dimword (:256)` by decide_tac >>
  `LENGTH ir.iret_values = nret` by
    (qpat_assum `LENGTH outs = LENGTH ir.iret_values` mp_tac >> simp[]) >>
  simp[wordsTheory.w2n_n2w, listTheory.MEM_MAP, venomStateTheory.lookup_var_def] >>
  impl_tac
  >- (once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
      qpat_assum `off + _ <= (u with vs_inst_idx := _).vs_alloca_next`
        (mp_tac o SIMP_RULE (srw_ss()) []) >> simp[]) >>
  disch_then (qx_choose_then `stored` (qx_choose_then `Gs`
    (qx_choose_then `ts` strip_assume_tac))) >>
  drule intCallFrameTheory.invoke_return_frame >> strip_tac >>
  `stored.vs_allocas = u.vs_allocas` by
    (qpat_assum `stored with <|vs_memory := _; vs_vars := _|> = _`
      (mp_tac o Q.AP_TERM `\s. s.vs_allocas`) >> simp[]) >>
  qpat_x_assum `u.vs_memory = _` kall_tac >>
  qexistsl [`stored`,`Gs`,`ts`] >> simp[] >> first_assum ACCEPT_TAC
QED
