(* Caller restoration retains the concrete callee's returned shared state. *)
Theory gasFocusLowerDloadCallReturn
Ancestors
  lowerDloadReturnInvokePop lowerDloadSafetyKernel venomExecSemantics
  finite_map pred_set list o1LowerDloadJointRestore venomState ptrDiscipline
  lowerDloadSafetyUpdates lowerDloadReturnCallContext lowerDloadOracleCallAssembly
  lowerDloadSafetyAllocation
Libs
  lowerDloadReturnPackageLib

Theorem ld_focus_invoke_pop_correlated:
  o1_ctx_shape C /\
  ld_sync lo P C vs0 stk PG G tn fn inst s t A (f::fs) N /\
  ^ld_probe_stable lo P Sigma names fs0 f0 A0 A (f::fs) /\
  fn' = ld_image f /\ ld_envelope f.lf_supply fn s s.vs_inst_idx [inst] p /\
  t.vs_inst_idx = p /\ lookup_block t.vs_current_bb fn'.fn_blocks = SOME bb /\
  inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  s.vs_gas_readings = t.vs_gas_readings /\
  (?sf rs cs' Ar fr tnr rinst se te PG' G' Nr.
    run_blocks sf C callee cs = IntRet rs cs' /\
    ld_sync lo P C vs0
      (<|cf_fn := fn; cf_inst := inst; cf_state := s; cf_params := PG;
         cf_prov := G; cf_tvar := tn.t_var|> :: stk)
      PG' G' tnr callee rinst se te Ar fr Nr /\
    ^ld_probe_stable lo P Sigma names (f::fs) fc A Ar fr /\
    rinst.inst_opcode = RET /\
    step_inst 0 C rinst se = IntRet rs cs' /\
    step_inst 0 C' rinst te = IntRet rt u /\
    rs.iret_values = rt.iret_values /\
    rs.iret_adopt_fmp = NONE /\ rt.iret_adopt_fmp = NONE /\
    ld_memory lo Ar tnr cs' u /\ ld_nonghost tnr cs' u /\
    (!a. a IN ld_slots Ar (f::fs) ==>
      FLOOKUP (DRESTRICT Ar (ld_slots Ar (f::fs))) a = FLOOKUP Ar a) /\
    cs'.vs_gas_readings = u.vs_gas_readings /\
    EVERY (\g. g.lf_src.vs_gas_readings = g.lf_tgt.vs_gas_readings /\
      LENGTH cs'.vs_gas_readings <= LENGTH g.lf_src.vs_gas_readings) fr) /\
  bind_outputs inst.inst_outputs rt.iret_values
    (adopt_return_fmp rt (merge_callee_state t u)) = SOME q /\
  active_inst fn' nexti (q with vs_inst_idx := SUC t.vs_inst_idx) ==>
  ?PG1 G1 tn1 inst1 s1 t1 A1 frames1 N1 X p1 h.
    ld_sync lo P C vs0 stk PG1 G1 tn1 fn inst1 s1 t1 A1 frames1 N1 /\
    ^ld_probe_stable lo P Sigma names fs0 f0 A0 A1 frames1 /\
    fn' = ld_image (HD frames1) /\
    ld_envelope (HD frames1).lf_supply fn s1 s1.vs_inst_idx X p1 /\
    ld_prefix C' fn' X p1 h t1 (q with vs_inst_idx := SUC t.vs_inst_idx) /\
    lookup_block (q with vs_inst_idx := SUC t.vs_inst_idx).vs_current_bb
      fn'.fn_blocks = SOME bb /\
    (!caller_cs. ld_return_cont C fn caller_cs s ==> ld_return_cont C fn caller_cs s1) /\
    s1.vs_gas_readings = t1.vs_gas_readings /\
    t1.vs_gas_readings = (q with vs_inst_idx := SUC t.vs_inst_idx).vs_gas_readings /\
    EVERY (\g. g.lf_src.vs_gas_readings = g.lf_tgt.vs_gas_readings /\
      LENGTH s1.vs_gas_readings <= LENGTH g.lf_src.vs_gas_readings) frames1
Proof
  qabbrev_tac `Stable = ^ld_probe_stable` >> BETA_TAC >> strip_tac >>
  `?sr. bind_outputs inst.inst_outputs rs.iret_values
      (adopt_return_fmp rs (merge_callee_state s cs')) = SOME sr /\
      step_inst sf C inst s = OK sr` by
    (irule lowerDloadReturnInterfaceProbeTheory.ld_invoke_from_return >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks)` by
    (qpat_x_assum `ld_sync _ _ _ _ (_::_) _ _ _ _ _ _ _ _ _ _` kall_tac >>
     drule_all ld_sync_fn_shape >> metis_tac[o1_fn_shape_components]) >>
  `EVERY inst_wf (fn_insts fn)` by
    (qpat_x_assum `ld_sync _ _ _ _ (_::_) _ _ _ _ _ _ _ _ _ _` kall_tac >>
     drule_all ld_sync_fn_shape >> strip_tac >>
     drule o1_fn_shape_components >>
     simp[venomWfTheory.fn_inst_wf_def, EVERY_MEM, venomInstTheory.fn_insts_def,
       venomInstTheory.fn_insts_blocks_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
     metis_tac[o1PassContractTheory.fn_insts_blocks_MEM]) >>
  `f.lf_src = s /\ f.lf_tgt = t /\ f.lf_fn = fn` by
    (qpat_assum `ld_sync _ _ _ _ stk _ _ _ _ _ _ _ _ (f::fs) _`
       (strip_assume_tac o MATCH_MP ld_sync_active) >> fs[]) >>
  `lower_dload_function_supply f.lf_supply fn =
    (fn', SND (lower_dload_function_supply f.lf_supply fn))` by fs[ld_image_def] >>
  `sr.vs_current_bb = s.vs_current_bb /\ q.vs_current_bb = t.vs_current_bb` by
    metis_tac[o1LowerDloadRunnerBoundaryTheory.ld_invoke_bind_control] >>
  `ALL_DISTINCT (MAP (\b. b.bb_label) fn'.fn_blocks)` by
    (drule o1ContractLowerDloadTheory.lower_dload_function_supply_labels >>
     simp[venomInstTheory.fn_labels_def]) >>
  `?ti. get_instruction bb (SUC t.vs_inst_idx) = SOME ti` by
    (drule_all lowerDloadSafetyAmbientTheory.ld_active_lookup >>
     simp[] >> strip_tac >> gvs[venomInstTheory.get_instruction_def]) >>
  `?next Y. active_inst fn next (sr with vs_inst_idx := SUC s.vs_inst_idx) /\
    ld_envelope f.lf_supply fn (sr with vs_inst_idx := SUC s.vs_inst_idx)
      (SUC s.vs_inst_idx) Y (p+1)` by
    (irule (SRULE [] (Q.INST [`X` |-> `[inst]`,
       `q` |-> `q with vs_inst_idx := SUC t.vs_inst_idx`]
       lowerDloadSafetyLocationsTheory.ld_envelope_successor_location)) >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`bb`, `inst`, `q with vs_inst_idx := SUC t.vs_inst_idx`,
       `s`, `t`, `ti`] >> simp[] >> metis_tac[ld_sync_control, pairTheory.FST]) >>
  drule_all ld_return_caller_frame_reachable >> strip_tac >>
  suspend "restore"
QED

Resume ld_focus_invoke_pop_correlated[restore]:
  `!caller_cs. ld_return_cont C fn caller_cs s ==>
    ld_return_cont C fn caller_cs (sr with vs_inst_idx := SUC s.vs_inst_idx)` by
    (rpt strip_tac >> irule ld_return_cont_next >>
     goal_assum (drule_at Any) >> simp[] >> qexistsl_tac [`inst`, `sf`] >>
     simp[venomInstTheory.is_terminator_def] >> metis_tac[ld_sync_source]) >>
  `cs'.vs_call_ctx = s.vs_call_ctx` by
    (drule_all ld_setup_return_call_ctx >> simp[]) >>
  `bind_outputs inst.inst_outputs rt.iret_values (merge_callee_state s cs') = SOME sr /\
   bind_outputs inst.inst_outputs rt.iret_values (merge_callee_state t u) = SOME q` by
    gvs[adopt_return_fmp_def] >>
  qabbrev_tac `B = DRESTRICT Ar (ld_slots Ar (f::fs))` >>
  qabbrev_tac `keep = COMPL (set inst.inst_outputs)` >>
  qabbrev_tac `g = f with <|lf_src := sr with vs_inst_idx := SUC s.vs_inst_idx;
    lf_tgt := q with vs_inst_idx := SUC t.vs_inst_idx;
    lf_H := DRESTRICT f.lf_H keep; lf_tv := DRESTRICT f.lf_tv keep|>` >>
  qabbrev_tac `tn1 = tnr with t_var := DRESTRICT tn.t_var keep` >>
  `ld_memory lo B tn1 (sr with vs_inst_idx := SUC s.vs_inst_idx)
      (q with vs_inst_idx := SUC t.vs_inst_idx) /\
   ld_nonghost tn1 (sr with vs_inst_idx := SUC s.vs_inst_idx)
      (q with vs_inst_idx := SUC t.vs_inst_idx)` by
    (qunabbrev_tac `B` >> qunabbrev_tac `tn1` >> irule ld_return_shared_restore >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[ld_sync_memory]) >>
  `EVERY (\h. ld_maps B h /\ ld_vars P B h) (f::fs) /\
   FDOM B = ld_slots B (f::fs)` by
    (qunabbrev_tac `B` >> qunabbrev_tac `Stable` >>
     drule_all ld_call_saved_alloc_restore >> simp[]) >>
  `bind_outputs inst.inst_outputs rt.iret_values (merge_callee_state f.lf_src cs') = SOME sr /\
   bind_outputs inst.inst_outputs rt.iret_values (merge_callee_state f.lf_tgt u) = SOME q` by simp[] >>
  `g = (f with <|lf_src := sr with vs_inst_idx := SUC s.vs_inst_idx;
    lf_tgt := q with vs_inst_idx := SUC t.vs_inst_idx;
    lf_H := DRESTRICT f.lf_H keep; lf_tv := DRESTRICT f.lf_tv keep|>)` by simp[Abbr `g`] >>
  `ld_global lo B (g::fs)` by
    (qunabbrev_tac `B` >> qunabbrev_tac `Stable` >>
     drule_all ld_call_global_return_restore >> simp[]) >>
  `EVERY (\h. h.lf_supply = Sigma h.lf_fn.fn_name) (f::fs) /\
   (!i k. i < k /\ k < LENGTH (f::fs) ==>
      list_precedes (EL i (f::fs)).lf_fn.fn_name (EL k (f::fs)).lf_fn.fn_name names)` by
    fs[Abbr `Stable`] >>
  drule_all ld_return_stack_geometry >> strip_tac >>
  suspend "maps"
QED

Resume ld_focus_invoke_pop_correlated[maps]:
  `!i. i < LENGTH stk ==>
    (EL i stk).cf_fn = (EL i fs).lf_fn /\
    (EL i stk).cf_state = (EL i fs).lf_src /\
    ld_ghost_ok (dyn_floor C vs0) B (EL i fs).lf_H (EL i stk).cf_prov /\
    ld_params_ok (dyn_floor C vs0) B (EL i fs).lf_Q (EL i stk).cf_params /\
    (EL i stk).cf_tvar = (EL i fs).lf_tv` by
    (rpt strip_tac >> qunabbrev_tac `B` >> qunabbrev_tac `Stable` >>
     drule_all ld_call_saved_stack_return >> simp[]) >>
  `set inst.inst_outputs SUBSET set (fn_ir_vars f.lf_fn)` by
    (simp[SUBSET_DEF] >> rpt strip_tac >> irule ld_inst_output_ir >>
     qexists_tac `inst` >> simp[] >> metis_tac[ld_sync_source, ld_active_inst_member]) >>
  `ld_vars P B g` by
    (qpat_assum `EVERY (\h. ld_maps B h /\ ld_vars P B h) (f::fs)`
       (strip_assume_tac o SRULE []) >>
     drule_all ld_vars_return_restore >> simp[Abbr `g`, Abbr `keep`]) >>
  drule_all ld_return_frame_geometry >> strip_tac >>
  `ld_maps B g` by
    (qpat_assum `EVERY (\h. ld_maps B h /\ ld_vars P B h) (f::fs)`
       (strip_assume_tac o SRULE []) >>
     `!d ai. ld_private g d ai = ld_private f d ai` by simp[ld_private_def] >>
     qpat_x_assum `ld_maps B f` mp_tac >> simp[ld_maps_def] >> strip_tac >> simp[]) >>
  `FDOM B = ld_slots B (g::fs)` by
    (qpat_x_assum `FDOM B = _` SUBST1_TAC >>
     qpat_x_assum `g.lf_serial = _` mp_tac >>
     qpat_x_assum `g.lf_src.vs_allocas = _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> simp[ld_slots_def, EXTENSION] >> metis_tac[]) >>
  `!a. a IN ld_slots A (f::fs) ==> FLOOKUP Ar a = FLOOKUP A a` by
    (fs[Abbr `Stable`] >> rpt strip_tac >> first_x_assum irule >> simp[] >>
     fs[ld_slots_def, FLOOKUP_DEF]) >>
  `ld_slots A (f::fs) SUBSET ld_slots Ar (f::fs)` by
    (irule lowerDloadReturnInvokeStackTheory.ld_slots_agree_subset >> simp[]) >>
  `!a. a IN FRANGE f.lf_H \/ MEM (SOME a) f.lf_Q ==> FLOOKUP B a = FLOOKUP A a` by
    (rpt strip_tac >>
     `a IN FDOM A` by
       (`ld_global lo A (f::fs)` by fs[Abbr `Stable`] >>
        irule ld_global_selected >> goal_assum (drule_at Any) >> qexists_tac `f` >> simp[]) >>
     `a IN ld_slots A (f::fs)` by metis_tac[ld_sync_def] >>
     simp[Abbr `B`, FLOOKUP_DRESTRICT] >> fs[SUBSET_DEF]) >>
  suspend "ghosts"
QED

Resume ld_focus_invoke_pop_correlated[ghosts]:
  `ld_erase B o_f f.lf_H = ld_erase A o_f f.lf_H` by
    (simp[fmap_eq_flookup, FLOOKUP_o_f] >> gen_tac >>
     Cases_on `FLOOKUP f.lf_H x` >> simp[] >>
     `FLOOKUP B x' = FLOOKUP A x'` by
       (first_x_assum irule >> simp[FRANGE_FLOOKUP] >> metis_tac[]) >> simp[ld_erase_def]) >>
  `MAP (OPTION_MAP (ld_erase B)) f.lf_Q = MAP (OPTION_MAP (ld_erase A)) f.lf_Q` by
    (irule MAP_CONG >> simp[] >> rpt strip_tac >> Cases_on `x` >> simp[ld_erase_def]) >>
  `ld_params_ok (dyn_floor C vs0) B g.lf_Q PG /\
   ld_ghost_ok (dyn_floor C vs0) B g.lf_H (DRESTRICT G keep)` by
    (qpat_assum `ld_sync _ _ _ _ stk _ _ _ _ _ _ _ _ (f::fs) _`
       (strip_assume_tac o SRULE [] o MATCH_MP ld_sync_ghosts) >>
     `ld_ghost_ok (dyn_floor C vs0) B f.lf_H G /\
      ld_params_ok (dyn_floor C vs0) B f.lf_Q PG` by
       metis_tac[ld_ghost_ok_erase_cong, ld_params_ok_erase_cong] >>
     simp[Abbr `g`, ld_ghost_ok_def, FLOOKUP_DRESTRICT] >>
     gvs[ld_ghost_ok_def, AllCaseEqs()] >> metis_tac[]) >>
  `ld_dyn_agree (dyn_floor C vs0) tnr.t_mem sr.vs_memory q.vs_memory` by
    (`cs' = se /\ u = te` by metis_tac[o1LowerDloadRunnerBoundaryTheory.ld_ret_endpoint] >>
     qpat_assum `bind_outputs _ _ (merge_callee_state s cs') = SOME sr`
       (assume_tac o MATCH_MP o1LowerDloadJointRestoreTheory.ld_bind_outputs_vars_only) >>
     qpat_assum `bind_outputs _ _ (merge_callee_state t u) = SOME q`
       (assume_tac o MATCH_MP o1LowerDloadJointRestoreTheory.ld_bind_outputs_vars_only) >>
     ntac 2 (pop_assum (fn th => once_rewrite_tac[th])) >>
     simp[merge_callee_state_def] >>
     qpat_assum `ld_sync _ _ _ _ _ PG' G' tnr _ _ _ _ _ _ _`
       (mp_tac o MATCH_MP ld_sync_dyn_agree) >> simp[]) >>
  `EVERY (\h. h.lf_serial < N /\ ld_maps B h /\ ld_vars P B h /\
      ld_intervals lo h.lf_src /\ ld_intervals lo h.lf_tgt /\
      h.lf_src.vs_prev_bb = h.lf_tgt.vs_prev_bb /\
      h.lf_src.vs_current_bb = h.lf_tgt.vs_current_bb /\ MEM h.lf_fn C.ctx_functions) (g::fs)` by
    (qpat_x_assum `EVERY (\h. h.lf_serial < N /\ _) (g::fs)` mp_tac >>
     qpat_x_assum `EVERY (\h. ld_maps B h /\ ld_vars P B h) (f::fs)` mp_tac >>
     qpat_x_assum `ld_maps B g` mp_tac >> qpat_x_assum `ld_vars P B g` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[EVERY_MEM] >> metis_tac[]) >>
  suspend "sync"
QED

Resume ld_focus_invoke_pop_correlated[sync]:
  `!i. i < LENGTH (g::fs) ==>
    ?X p. ld_envelope (EL i (g::fs)).lf_supply (EL i (g::fs)).lf_fn
      (EL i (g::fs)).lf_src (EL i (g::fs)).lf_src.vs_inst_idx X p /\
      (EL i (g::fs)).lf_tgt.vs_inst_idx = p` by
    (qpat_x_assum `!j. j < LENGTH fs ==> ?X p. _` mp_tac >>
     qpat_x_assum `ld_envelope _ _ (sr with vs_inst_idx := _) _ Y _` mp_tac >>
     qpat_x_assum `t.vs_inst_idx = p` mp_tac >> qpat_x_assum `f.lf_fn = fn` mp_tac >>
     qunabbrev_tac `g` >> rpt (pop_assum kall_tac) >> rpt strip_tac >>
     Cases_on `i` >> gvs[arithmeticTheory.ADD1] >> metis_tac[]) >>
  `ld_sync lo P C vs0 stk PG (DRESTRICT G keep) tn1 fn next
    (sr with vs_inst_idx := SUC s.vs_inst_idx)
    (q with vs_inst_idx := SUC t.vs_inst_idx) B (g::fs) N` by
    (qpat_assum `ld_sync _ _ _ _ stk _ _ _ _ _ _ _ _ (f::fs) _`
       (strip_assume_tac o SRULE [ld_sync_def]) >>
     pure_rewrite_tac[ld_sync_def, listTheory.HD] >>
     simp[Abbr `g`, Abbr `tn1`]) >>
  `fs0 = fs` by
    (qpat_assum `Stable lo P Sigma names fs0 f0 A0 A (f::fs)` mp_tac >>
     qunabbrev_tac `Stable` >> rpt (pop_assum kall_tac) >> simp[]) >>
  `fr = HD fr::f::fs` by
    (qpat_assum `Stable lo P Sigma names (f::fs) fc A Ar fr` mp_tac >>
     qunabbrev_tac `Stable` >> rpt (pop_assum kall_tac) >> Cases_on `fr` >> simp[] >> metis_tac[]) >>
  `Stable lo P Sigma names (f::fs) fc A Ar (HD fr::f::fs)` by metis_tac[] >>
  `(!a. a IN FDOM A0 INTER ld_slots A0 fs0 ==> FLOOKUP B a = FLOOKUP A0 a) /\
   (!h. MEM h fs0 ==> FRANGE h.lf_H SUBSET ld_slots Ar (f::fs) /\
      (!a. MEM (SOME a) h.lf_Q ==> a IN ld_slots Ar (f::fs)))` by
    (qunabbrev_tac `Stable` >> drule_all lowerDloadReturnInvokeStackTheory.ld_saved_slots_restore >>
     strip_tac >> qpat_x_assum `fs0 = fs` SUBST_ALL_TAC >> simp[Abbr `B`] >>
     rpt strip_tac >> qpat_assum `!h. MEM h fs ==> FRANGE h.lf_H SUBSET _ /\ _` drule >> simp[]) >>
  `ld_slots A fs0 SUBSET ld_slots B fs0` by
    (irule lowerDloadReturnInvokeStackTheory.ld_slots_agree_subset >> rpt strip_tac >>
     `a IN ld_slots A (f::fs)` by
       (qpat_x_assum `fs0 = fs` SUBST_ALL_TAC >>
        qpat_x_assum `a IN ld_slots A fs` mp_tac >> rpt (pop_assum kall_tac) >>
        simp[Once ld_slots_cons]) >>
     qunabbrev_tac `B` >>
     qpat_assum `!a. a IN ld_slots A (f::fs) ==> FLOOKUP Ar a = FLOOKUP A a` mp_tac >>
     qpat_assum `ld_slots A (f::fs) SUBSET ld_slots Ar (f::fs)` mp_tac >>
     qpat_assum `a IN ld_slots A (f::fs)` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[SUBSET_DEF, FLOOKUP_DRESTRICT]) >>
  suspend "stable"
QED

Resume ld_focus_invoke_pop_correlated[stable]:
  `Stable lo P Sigma names fs0 f0 A0 B (g::fs)` by
    (qpat_assum `Stable lo P Sigma names fs0 f0 A0 A (f::fs)` mp_tac >>
     qunabbrev_tac `Stable` >> BETA_TAC >>
     pure_rewrite_tac[listTheory.HD, listTheory.TL, listTheory.NOT_CONS_NIL] >> strip_tac >>
     conj_tac >- simp[] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- simp[Abbr `g`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac
     >- (qpat_assum `EVERY (\h. h.lf_supply = _) (f::fs)` mp_tac >>
         qunabbrev_tac `g` >> rpt (pop_assum kall_tac) >> simp[]) >>
     conj_tac
     >- (qpat_assum `EVERY (\h. !j a. _) (f::fs)` mp_tac >>
         qunabbrev_tac `g` >> rpt (pop_assum kall_tac) >> simp[]) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac
     >- (qpat_assum `!h. MEM h fs0 ==> FRANGE h.lf_H SUBSET ld_slots A fs0 /\ _` mp_tac >>
         qpat_assum `ld_slots A fs0 SUBSET ld_slots B fs0` mp_tac >>
         rpt (pop_assum kall_tac) >> simp[SUBSET_DEF] >> metis_tac[]) >>
     qpat_assum `!a. a IN FDOM A0 INTER _ ==> _` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[]) >>
  suspend "readings"
QED

Resume ld_focus_invoke_pop_correlated[readings]:
  `sr.vs_gas_readings = cs'.vs_gas_readings /\ q.vs_gas_readings = u.vs_gas_readings` by
    (qpat_assum `bind_outputs _ _ (merge_callee_state s cs') = SOME sr`
       (mp_tac o MATCH_MP ld_bind_outputs_vars_only) >>
     qpat_assum `bind_outputs _ _ (merge_callee_state t u) = SOME q`
       (mp_tac o MATCH_MP ld_bind_outputs_vars_only) >>
     rpt (pop_assum kall_tac) >>
     disch_then (fn th => once_rewrite_tac[th]) >>
     disch_then (fn th => once_rewrite_tac[th]) >>
     simp[merge_callee_state_def]) >>
  `EVERY (\h. h.lf_src.vs_gas_readings = h.lf_tgt.vs_gas_readings /\
    LENGTH cs'.vs_gas_readings <= LENGTH h.lf_src.vs_gas_readings) (f::fs)` by
    (qpat_x_assum `EVERY (\h. h.lf_src.vs_gas_readings = _) fr` mp_tac >>
     qpat_x_assum `fr = HD fr::f::fs` (fn th => once_rewrite_tac[th]) >>
     rpt (pop_assum kall_tac) >> simp[]) >>
  `EVERY (\h. h.lf_src.vs_gas_readings = h.lf_tgt.vs_gas_readings /\
    LENGTH sr.vs_gas_readings <= LENGTH h.lf_src.vs_gas_readings) (g::fs)` by
    (qpat_x_assum `EVERY (\h. h.lf_src.vs_gas_readings = _) (f::fs)` mp_tac >>
     simp[Abbr `g`]) >>
  qexistsl_tac [`PG`, `DRESTRICT G keep`, `tn1`, `next`,
    `sr with vs_inst_idx := SUC s.vs_inst_idx`,
    `q with vs_inst_idx := SUC t.vs_inst_idx`, `B`, `g::fs`, `N`, `Y`, `p+1`, `0`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  simp[NoAsms, listTheory.HD] >>
  conj_tac >- simp[Abbr `g`, ld_image_def] >>
  conj_tac >- simp[Abbr `g`] >>
  reverse conj_tac >- simp[] >>
  suspend "prefix"
QED

Resume ld_focus_invoke_pop_correlated[prefix]:
  FAIL_TAC "prefix"
QED

Finalise ld_focus_invoke_pop_correlated
