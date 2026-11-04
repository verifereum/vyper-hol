(* Local mixed crossing boundaries; no whole-run safety hypotheses. *)
Theory dftMixedCrossing
Ancestors
  dftPendingSuspension dftMixedResidualProbe dftOccurrenceFrame
  dftOccurrenceOrdinaryEdit dftOccurrenceOrdinaryStop dftOccurrenceOrdinaryObserve
  dftOccurrenceReturn dftOrdinarySwap venomInstProofs1
  dftProtectedRuntime dftOrdinaryStop venomWf dftScheduleOrder
  dftWf dftAvailability dftSsaPreserve dftCorrectness dftScheduleEdits
  dftOccurrenceSuspended dftOccurrenceResidual dftOccurrenceMachine
  dftOccurrenceReplay dftOpenErase dftOpenMachine dftCommutation
  unitMemInv contextCodegenRel codegenRel venomEffects venomExecSemantics
  venomInst venomState list

Theorem dft_pending_call_enabled:
  dft_cut_pair us [] sL sR /\
  (!nm ops. decode_invoke call = SOME (nm,ops) ==>
     EVERY (\p. ~MEM (Var (FST p)) ops) us) ==>
  ((?nm ops callee args cs.
     decode_invoke call = SOME (nm,ops) /\
     lookup_function nm C.ctx_functions = SOME callee /\
     eval_operands ops sL = SOME args /\
     setup_callee callee args sL = SOME cs) <=>
   (?nm ops callee args cs.
     decode_invoke call = SOME (nm,ops) /\
     lookup_function nm C.ctx_functions = SOME callee /\
     eval_operands ops sR = SOME args /\
     setup_callee callee args sR = SOME cs))
Proof
  strip_tac >>
  `!nm ops. decode_invoke call = SOME (nm,ops) ==>
     eval_operands ops sL = eval_operands ops sR` by
    (rpt strip_tac >> irule dft_cut_pair_eval_operands >>
     qexistsl_tac [`us`, `[]`] >> simp[]) >>
  metis_tac[dft_cut_pair_setup_callee]
QED

Theorem dft_pending_call_failure:
  dft_cut_pair us [] sL sR /\
  l.dft_occ_core = DftOpen (DftAt fnL 0 bbL sL) tailL nL /\
  r.dft_occ_core = DftOpen (DftAt fnR 0 bbR sR) tailR nR /\
  get_instruction bbL sL.vs_inst_idx = SOME call /\
  get_instruction bbR sR.vs_inst_idx = SOME call /\
  call.inst_opcode = INVOKE /\
  (!nm ops. decode_invoke call = SOME (nm,ops) ==>
     EVERY (\p. ~MEM (Var (FST p)) ops) us) /\
  ~(?nm ops callee args cs.
     decode_invoke call = SOME (nm,ops) /\
     lookup_function nm C.ctx_functions = SOME callee /\
     eval_operands ops sR = SOME args /\ setup_callee callee args sR = SOME cs) ==>
  dft_suspend_cleared (dft_occ_oracle_next w C l) (dft_occ_oracle_next w C r)
Proof
  strip_tac >>
  `!nm ops. decode_invoke call = SOME (nm,ops) ==>
     eval_operands ops sL = eval_operands ops sR` by
    (rpt strip_tac >> irule dft_cut_pair_eval_operands >>
     qexistsl_tac [`us`, `[]`] >> simp[]) >>
  `!fn args. setup_callee fn args sL = setup_callee fn args sR` by
    metis_tac[dft_cut_pair_setup_callee] >>
  simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
       dft_open_next_def, dft_open_invoke_def, dft_erase_def,
       dft_fill_def, dft_fill_control_def] >>
  Cases_on `decode_invoke call`
  >- simp[dft_fill_def, dft_fill_control_def, dft_occ_update_def,
           dft_suspend_cleared_def] >>
  PairCases_on `x` >>
  `eval_operands x1 sL = eval_operands x1 sR` by metis_tac[] >>
  Cases_on `lookup_function x0 C.ctx_functions`
  >- simp[dft_fill_def, dft_fill_control_def, dft_occ_update_def,
           dft_suspend_cleared_def] >>
  rename1 `lookup_function _ _ = SOME callee` >>
  Cases_on `eval_operands x1 sR`
  >- simp[dft_fill_def, dft_fill_control_def, dft_occ_update_def,
           dft_suspend_cleared_def] >>
  rename1 `eval_operands _ _ = SOME args` >>
  `setup_callee callee args sR = NONE` by
    (Cases_on `setup_callee callee args sR` >> gvs[]) >>
  simp[dft_fill_def, dft_fill_control_def, dft_occ_update_def,
       dft_suspend_cleared_def]
QED

Theorem dft_empty_effect_ranges:
  read_effects inst.inst_opcode = empty_effects /\
  write_effects inst.inst_opcode = empty_effects ==>
  inst_mem_ranges inst s = []
Proof
  strip_tac >> irule dft_ordinary_no_memory_ranges >>
  simp[empty_effects_def]
QED

Theorem dft_invoke_partner_ranges:
  ~dft_must_order inst call /\ call.inst_opcode = INVOKE ==>
  inst_mem_ranges inst s = []
Proof
  strip_tac >> drule_all dft_invoke_inversion_disjoint >> strip_tac >>
  irule dft_empty_effect_ranges >> simp[]
QED

Theorem dft_gas_ordinary_stack_square:
  l.dft_occ_core = DftOpen (DftAt fnL 0 bbL s) stackL n /\
  r.dft_occ_core = DftOpen (DftAt fnR 0 bbR s) stackR n /\
  MAP (dft_fill_frame 0) stackL = stackL /\
  MAP (dft_fill_frame 0) stackR = stackR /\
  (stackL = [] ==> l.dft_occ_saved = []) /\
  (stackR = [] ==> r.dft_occ_saved = []) /\
  l.dft_occ_path = path /\ r.dft_occ_path = path /\
  l.dft_occ_visit = visit /\ r.dft_occ_visit = visit /\
  get_instruction bbL s.vs_inst_idx = SOME gas /\
  get_instruction bbL (SUC s.vs_inst_idx) = SOME inst /\
  get_instruction bbR s.vs_inst_idx = SOME inst /\
  get_instruction bbR (SUC s.vs_inst_idx) = SOME gas /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
  ~is_terminator inst.inst_opcode /\
  ~MEM (Var v) inst.inst_operands /\ ~MEM v inst.inst_outputs /\
  step_inst_base inst s = OK t ==>
  let after = (update_var v (w (path ++ [(visit,gas.inst_id)])) t)
                with vs_inst_idx := SUC (SUC s.vs_inst_idx)
  in
    (dft_occ_oracle_next w C (dft_occ_oracle_next w C l)).dft_occ_core =
      DftOpen (DftAt fnL 0 bbL after) stackL (SUC n) /\
    (dft_occ_oracle_next w C (dft_occ_oracle_next w C r)).dft_occ_core =
      DftOpen (DftAt fnR 0 bbR after) stackR (SUC n)
Proof
  strip_tac >> simp_tac bool_ss [LET_THM] >>
  `step_inst_base inst (update_var v (w (path ++ [(visit,gas.inst_id)])) s) =
     OK (update_var v (w (path ++ [(visit,gas.inst_id)])) t)` by
    metis_tac[dft_gas_value_ordinary_frame] >>
  `step_inst_base inst ((update_var v (w (path ++ [(visit,gas.inst_id)])) s)
      with vs_inst_idx := SUC s.vs_inst_idx) =
     OK ((update_var v (w (path ++ [(visit,gas.inst_id)])) t)
      with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[instIdxIndepTheory.step_inst_inst_idx_indep,
         instIdxIndepTheory.exec_result_map_def] >>
  qpat_assum `l.dft_occ_core = _` (mp_then Any mp_tac dft_suspend_gas_step) >>
  simp[] >> disch_then (qspecl_then [`w`, `C`] assume_tac) >>
  drule_all dft_occ_ordinary_next >>
  disch_then (qspecl_then [`w`, `C`] assume_tac) >>
  conj_tac
  >- (asm_rewrite_tac[] >>
      qmatch_goalsub_abbrev_tac `dft_occ_oracle_next w C mid` >>
      `mid.dft_occ_core = DftOpen (DftAt fnL 0 bbL
        ((update_var v (w (path ++ [(visit,gas.inst_id)])) s)
          with vs_inst_idx := SUC s.vs_inst_idx)) stackL (SUC n)` by
        simp[Abbr `mid`] >>
      drule dft_occ_ordinary_next >>
      simp[update_var_inst_idx] >>
      disch_then (qspecl_then [`w`, `(update_var v (w (path ++ [(visit,gas.inst_id)])) t) with vs_inst_idx := SUC s.vs_inst_idx`, `C`] mp_tac) >>
      simp[]) >>
  asm_rewrite_tac[] >>
  qmatch_goalsub_abbrev_tac `dft_occ_oracle_next w C mid` >>
  `mid.dft_occ_core = DftOpen (DftAt fnR 0 bbR
    (t with vs_inst_idx := SUC s.vs_inst_idx)) stackR n` by simp[Abbr `mid`] >>
  drule dft_suspend_gas_step >>
  simp[Abbr `mid`] >>
  disch_then (qspecl_then [`w`, `C`] mp_tac) >>
  simp[update_var_def] >> Cases_on `stackR` >> gvs[]
QED

Theorem dft_gas_ordinary_stack_abort:
  l.dft_occ_core = DftOpen (DftAt fnL 0 bbL s) stackL n /\
  r.dft_occ_core = DftOpen (DftAt fnR 0 bbR s) stackR n /\
  MAP (dft_fill_frame 0) stackL = stackL /\
  MAP (dft_fill_frame 0) stackR = stackR /\
  (stackL = [] ==> l.dft_occ_saved = []) /\
  l.dft_occ_path = path /\ l.dft_occ_visit = visit /\
  get_instruction bbL s.vs_inst_idx = SOME gas /\
  get_instruction bbL (SUC s.vs_inst_idx) = SOME inst /\
  get_instruction bbR s.vs_inst_idx = SOME inst /\
  gas.inst_opcode = GAS /\ gas.inst_outputs = [v] /\
  inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
  ~is_terminator inst.inst_opcode /\
  ~MEM (Var v) inst.inst_operands /\ ~MEM v inst.inst_outputs /\
  step_inst_base inst s = Abort a t ==>
  (dft_occ_oracle_next w C (dft_occ_oracle_next w C l)).dft_occ_core =
    DftOpen (DftDone (Abort a
      ((update_var v (w (path ++ [(visit,gas.inst_id)])) t)
        with vs_inst_idx := SUC s.vs_inst_idx))) stackL (SUC n) /\
  (dft_occ_oracle_next w C r).dft_occ_core =
    DftOpen (DftDone (Abort a t)) stackR n
Proof
  strip_tac >>
  `!y. MEM (Var y) inst.inst_operands ==> v <> y` by metis_tac[] >>
  drule_all step_inst_base_frame >>
  disch_then (qspecl_then [`s`, `w (path ++ [(visit,gas.inst_id)])`] mp_tac) >>
  simp[map_result_state_def] >> strip_tac >>
  `step_inst_base inst ((update_var v (w (path ++ [(visit,gas.inst_id)])) s)
      with vs_inst_idx := SUC s.vs_inst_idx) =
    Abort a ((update_var v (w (path ++ [(visit,gas.inst_id)])) t)
      with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[instIdxIndepTheory.step_inst_inst_idx_indep,
         instIdxIndepTheory.exec_result_map_def] >>
  reverse conj_tac
  >- (drule_all dft_occ_ordinary_abort >>
      disch_then (qspecl_then [`w`, `C`] mp_tac) >> simp[]) >>
  drule_all dft_suspend_gas_step >>
  disch_then (qspecl_then [`w`, `C`] SUBST1_TAC) >>
  qmatch_goalsub_abbrev_tac `(dft_occ_oracle_next w C mid).dft_occ_core` >>
  `mid.dft_occ_core = DftOpen (DftAt fnL 0 bbL
    ((update_var v (w (path ++ [(visit,gas.inst_id)])) s)
      with vs_inst_idx := SUC s.vs_inst_idx)) stackL (SUC n)` by
    simp[Abbr `mid`] >>
  drule dft_occ_ordinary_abort >> simp[update_var_inst_idx] >>
  disch_then (qspecl_then [`w`, `C`] mp_tac) >> simp[]
QED

Theorem dft_gas_ordinary_observation:
  ~is_terminator inst.inst_opcode /\ ~MEM (Var v) inst.inst_operands ==>
  let u = (update_var v value s) with vs_inst_idx := idx in
    u.vs_memory = s.vs_memory /\
    (!op. MEM op inst.inst_operands ==> eval_operand op u = eval_operand op s) /\
    inst_mem_ranges inst u = inst_mem_ranges inst s
Proof
  strip_tac >> simp_tac bool_ss [LET_THM] >>
  `!op. MEM op inst.inst_operands ==>
     eval_operand op ((update_var v value s) with vs_inst_idx := idx) =
     eval_operand op s` by
    (rpt strip_tac >> Cases_on `op` >>
     gvs[eval_operand_def, update_var_def, lookup_var_def,
         finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]) >>
  `inst.inst_opcode <> DRET` by metis_tac[is_terminator_def] >>
  conj_tac >- simp[update_var_def] >>
  conj_tac >- simp[] >>
  irule dft_ordinary_ranges_cong >> simp[]
QED

Theorem dft_restore_contexts:
  dft_restore outs ret cs s = SOME t ==>
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_tx_ctx = s.vs_tx_ctx /\
  t.vs_block_ctx = s.vs_block_ctx /\ t.vs_code = s.vs_code
Proof
  simp[dft_restore_def] >> strip_tac >>
  qspec_then `\s. (s.vs_call_ctx,s.vs_tx_ctx,s.vs_block_ctx,s.vs_code)` mp_tac
    bind_outputs_preserves >>
  simp[update_var_def] >> disch_then drule >>
  Cases_on `ret.iret_adopt_fmp` >>
  simp[adopt_return_fmp_def, merge_callee_state_def]
QED

Theorem dft_pending_lookup_outside[local]:
  !us s. EVERY (\p. FST p <> v) us ==>
    lookup_var v (dft_pending_apply us s) = lookup_var v s
Proof
  rewrite_tac[dft_pending_apply_def] >> Induct >> simp[] >> rpt strip_tac >>
  first_x_assum (qspec_then `update_var (FST h) (SND h) s` mp_tac) >>
  PairCases_on `h` >>
  gvs[update_var_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem dft_restore_lookup:
  dft_restore outs ret cs s = SOME t /\ ~MEM v outs ==>
  lookup_var v t = lookup_var v s
Proof
  simp[dft_restore_def, bind_outputs_def] >>
  strip_tac >>
  `!s. FOLDL (\u (v,x). update_var v x u) s (ZIP (outs,ret.iret_values)) =
        dft_pending_apply (ZIP (outs,ret.iret_values)) s` by
    simp[dft_pending_apply_def, pairTheory.LAMBDA_PROD] >>
  gvs[] >>
  `EVERY (\p. FST p <> v) (ZIP (outs,ret.iret_values))` by
    (simp[EVERY_MEM, MEM_ZIP] >> rpt strip_tac >> gvs[] >>
     `n < LENGTH outs` by simp[] >>
     drule_all listTheory.EL_MEM >> metis_tac[]) >>
  simp[dft_pending_lookup_outside] >>
  Cases_on `ret.iret_adopt_fmp` >>
  simp[adopt_return_fmp_def, merge_callee_state_def, lookup_var_def]
QED

Theorem dft_restore_labels:
  dft_restore outs ret cs s = SOME t ==> t.vs_labels = s.vs_labels
Proof
  simp[dft_restore_def] >> strip_tac >>
  qspec_then `\s. s.vs_labels` mp_tac bind_outputs_preserves >>
  simp[update_var_def] >> disch_then drule >>
  Cases_on `ret.iret_adopt_fmp` >>
  simp[adopt_return_fmp_def, merge_callee_state_def]
QED

Theorem dft_restore_operands:
  dft_restore outs ret cs s = SOME t /\
  (!v. MEM (Var v) inst.inst_operands ==> ~MEM v outs) ==>
  !op. MEM op inst.inst_operands ==> eval_operand op t = eval_operand op s
Proof
  rpt strip_tac >> drule dft_restore_labels >> strip_tac >>
  Cases_on `op` >> simp[eval_operand_def] >>
  irule dft_restore_lookup >> metis_tac[]
QED

Theorem dft_restored_ordinary_replay:
  ~is_pseudo x.inst_opcode /\ ~is_terminator x.inst_opcode /\
  x.inst_opcode <> ALLOCA /\ x.inst_opcode <> GAS /\
  read_effects x.inst_opcode = empty_effects /\
  write_effects x.inst_opcode = empty_effects /\
  (!v. MEM (Var v) x.inst_operands ==> ~MEM v outs) /\
  dft_restore outs ret cs s = SOME t /\ step_inst_base x s = OK r ==>
  ?us. EVERY (\p. MEM (FST p) x.inst_outputs) us /\
       r = dft_pending_apply us s /\
       step_inst_base x t = OK (dft_pending_apply us t)
Proof
  strip_tac >> rewrite_tac[dft_pending_apply_def] >>
  irule dft_ordinary_empty_effect_replay >> simp[] >>
  metis_tac[dft_restore_operands, dft_restore_contexts]
QED

Theorem dft_invoke_partner_return_replay:
  ~dft_must_order x call /\ call.inst_opcode = INVOKE /\
  ~is_pseudo x.inst_opcode /\ ~is_terminator x.inst_opcode /\
  x.inst_opcode <> ALLOCA /\ x.inst_opcode <> GAS /\
  (!v. MEM (Var v) x.inst_operands ==> ~MEM v call.inst_outputs) /\
  dft_restore call.inst_outputs ret cs s = SOME t /\
  step_inst_base x s = OK r ==>
  ?us. EVERY (\p. MEM (FST p) x.inst_outputs) us /\
       r = dft_pending_apply us s /\
       step_inst_base x t = OK (dft_pending_apply us t)
Proof
  strip_tac >> drule_all dft_invoke_inversion_disjoint >> strip_tac >>
  irule dft_restored_ordinary_replay >> metis_tac[]
QED

Theorem dft_invoke_partner_success:
  ~dft_must_order x call /\ call.inst_opcode = INVOKE /\ inst_wf x /\
  ~is_pseudo x.inst_opcode /\ ~is_terminator x.inst_opcode /\
  x.inst_opcode <> ALLOCA /\ x.inst_opcode <> GAS /\
  (!op. MEM op x.inst_operands ==> ?v. eval_operand op s = SOME v) ==>
  ?t. step_inst_base x s = OK t
Proof
  strip_tac >> drule_all dft_invoke_inversion_disjoint >> strip_tac >>
  `x.inst_outputs <> []` by fs[dft_must_order_def] >>
  irule dft_ordinary_nofail_total >> simp[] >>
  Cases_on `x.inst_opcode` >>
  gvs[is_alloca_op_def, opcode_fail_class_def, read_effects_def,
      write_effects_def, empty_effects_def, all_effects_def, inst_wf_def]
QED

Theorem dft_original_schedule_instructions_wf:
  dft_original_schedule f b q ==> EVERY inst_wf q.bb_instructions
Proof
  simp[dft_original_schedule_def] >> rpt strip_tac >> gvs[] >>
  rename1 `PERM current_body _` >>
  `EVERY inst_wf current_body` by
    (drule sortingTheory.PERM_EVERY >>
     disch_then (qspec_then `inst_wf` mp_tac) >>
     fs[EVERY_FILTER, EVERY_MEM] >> metis_tac[]) >>
  fs[EVERY_FILTER, EVERY_MEM] >> metis_tac[]
QED

Theorem dft_original_invoke_partner_return_replay:
  dft_original_cut f b q s /\
  q.bb_instructions = pp ++ done ++ x::todo /\
  pp = FILTER (\i. is_pseudo i.inst_opcode) b.bb_instructions /\
  s.vs_inst_idx = LENGTH (pp ++ done) /\
  (!l. MEM (Label l) x.inst_operands ==> l IN FDOM s.vs_labels) /\
  ~dft_must_order x call /\ call.inst_opcode = INVOKE /\
  ~is_pseudo x.inst_opcode /\ ~is_terminator x.inst_opcode /\
  x.inst_opcode <> ALLOCA /\ x.inst_opcode <> GAS /\
  (!v. MEM (Var v) x.inst_operands ==> ~MEM v call.inst_outputs) /\
  dft_restore call.inst_outputs ret cs s = SOME t ==>
  ?us. EVERY (\p. MEM (FST p) x.inst_outputs) us /\
       step_inst_base x s = OK (dft_pending_apply us s) /\
       step_inst_base x t = OK (dft_pending_apply us t)
Proof
  strip_tac >>
  `!op. MEM op x.inst_operands ==> ?v. eval_operand op s = SOME v` by
    metis_tac[dft_original_cut_eval_operand] >>
  `EVERY inst_wf q.bb_instructions` by
    metis_tac[dft_original_cut_def, dft_original_schedule_instructions_wf] >>
  `inst_wf x` by gvs[] >>
  `?r. step_inst_base x s = OK r` by
    (irule dft_invoke_partner_success >> metis_tac[]) >>
  drule_all dft_invoke_partner_return_replay >> strip_tac >>
  qexists `us` >> gvs[]
QED

Theorem dft_original_schedule_perm:
  dft_original_schedule f b q ==> PERM q.bb_instructions b.bb_instructions
Proof
  simp[dft_original_schedule_def] >> rpt strip_tac >> gvs[] >>
  irule sortingTheory.PERM_TRANS >>
  qexists `FILTER (\i. is_pseudo i.inst_opcode) b.bb_instructions ++
           FILTER (\i. ~is_pseudo i.inst_opcode) b.bb_instructions` >>
  conj_tac >- simp[sortingTheory.PERM_APPEND_IFF] >>
  once_rewrite_tac[sortingTheory.PERM_SYM] >>
  irule sortingTheory.PERM_SPLIT_IF >> simp[]
QED

Theorem dft_original_future_outputs_disjoint:
  dft_original_schedule f b q /\
  q.bb_instructions = pre ++ x::middle ++ call::post /\
  ~is_pseudo x.inst_opcode ==>
  !v. MEM (Var v) x.inst_operands ==> ~MEM v call.inst_outputs
Proof
  strip_tac >> drule dft_original_schedule_perm >> strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) b.bb_instructions)` by
    metis_tac[dft_original_schedule_def, wf_fn_block_inst_ids_distinct] >>
  `ALL_DISTINCT b.bb_instructions` by metis_tac[ALL_DISTINCT_MAP] >>
  `ALL_DISTINCT q.bb_instructions` by
    metis_tac[sortingTheory.ALL_DISTINCT_PERM] >>
  `MEM x b.bb_instructions /\ MEM call b.bb_instructions` by
    (drule sortingTheory.PERM_MEM_EQ >> simp[] >> metis_tac[]) >>
  rpt strip_tac >>
  `id_before (MAP (\i. i.inst_id) b.bb_instructions) call.inst_id x.inst_id` by
    metis_tac[dft_original_schedule_def, dft_local_producer_before] >>
  `id_before b.bb_instructions call x` by
    metis_tac[id_before_ids_invert] >>
  `dft_must_order call x` by
    (simp[dft_must_order_def, inst_defs_def, inst_uses_def,
          pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION,
          MEM_operand_vars_iff] >> metis_tac[]) >>
  `id_before q.bb_instructions call x` by
    metis_tac[dft_original_schedule_def, schedule_edges_def] >>
  gvs[dftSsaPreserveTheory.id_before_append,
      dftSsaPreserveTheory.id_before_cons, ALL_DISTINCT_APPEND] >>
  imp_res_tac dftScheduleOrderTheory.id_before_mem >> gvs[] >> metis_tac[]
QED

(* The schedule in this interface is the ordinary-first side, regardless
   of which orientation the surrounding edit has. *)
Theorem dft_legal_invoke_partner_return_replay:
  dft_original_cut f b q s /\
  q.bb_instructions = pp ++ done ++ x::call::todo /\
  pp = FILTER (\i. is_pseudo i.inst_opcode) b.bb_instructions /\
  s.vs_inst_idx = LENGTH (pp ++ done) /\
  (!l. MEM (Label l) x.inst_operands ==> l IN FDOM s.vs_labels) /\
  ~dft_must_order x call /\ call.inst_opcode = INVOKE /\
  ~is_pseudo x.inst_opcode /\ ~is_terminator x.inst_opcode /\
  x.inst_opcode <> ALLOCA /\ x.inst_opcode <> GAS /\
  dft_restore call.inst_outputs ret cs s = SOME t ==>
  ?us. EVERY (\p. MEM (FST p) x.inst_outputs) us /\
       step_inst_base x s = OK (dft_pending_apply us s) /\
       step_inst_base x t = OK (dft_pending_apply us t)
Proof
  strip_tac >>
  `dft_original_schedule f b q` by fs[dft_original_cut_def] >>
  `q.bb_instructions = (pp ++ done) ++ x::[] ++ call::todo` by
    simp[APPEND_ASSOC] >>
  `!v. MEM (Var v) x.inst_operands ==> ~MEM v call.inst_outputs` by
    metis_tac[dft_original_future_outputs_disjoint] >>
  irule dft_original_invoke_partner_return_replay >> metis_tac[]
QED

Theorem dft_invoke_partner_no_observations:
  ~dft_must_order x call /\ call.inst_opcode = INVOKE ==>
  inst_mem_ranges x s = [] /\ inst_mem_ranges x t = [] /\
  inst_mem_ranges call s = [] /\ inst_mem_ranges call t = []
Proof
  strip_tac >>
  `inst_mem_ranges x s = [] /\ inst_mem_ranges x t = []` by
    metis_tac[dft_invoke_partner_ranges] >>
  simp[inst_mem_ranges_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def]
QED

Theorem dft_gas_ordinary_observation_pair:
  gas.inst_opcode = GAS /\ ~is_terminator inst.inst_opcode /\
  ~MEM (Var v) inst.inst_operands ==>
  let u = (update_var v value s) with vs_inst_idx := idx in
    (inst_mem_ranges inst u <> [] ==>
      u.vs_memory = s.vs_memory /\
      (!op. MEM op inst.inst_operands ==> eval_operand op u = eval_operand op s) /\
      inst_mem_ranges inst u = inst_mem_ranges inst s) /\
    (inst_mem_ranges inst s <> [] ==>
      s.vs_memory = u.vs_memory /\
      (!op. MEM op inst.inst_operands ==> eval_operand op s = eval_operand op u) /\
      inst_mem_ranges inst s = inst_mem_ranges inst u) /\
    inst_mem_ranges gas s = [] /\ inst_mem_ranges gas u = []
Proof
  strip_tac >> drule_all dft_gas_ordinary_observation >>
  disch_then (qspecl_then [`value`, `s`, `idx`] mp_tac) >>
  simp[inst_mem_ranges_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def] >> metis_tac[]
QED
