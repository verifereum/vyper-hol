Theory dftPositionalSegment
Ancestors
  dftPositionalCrossing dftPositionalStep dftPositionalReturn dftPositionalPhase
  dftPositionalRuntime dftRecursiveCallProvenance dftRecursiveReturnPhase
  dftRecursiveFixedSegment dftOccurrenceReplay dftOccurrenceMachine
  dftOpenMachine dftOpenErase contextRawReachable venomState list arithmetic

(* Account for half-open segments without identifying functions by value. *)
Definition dft_pos_segment_account_def:
  dft_pos_segment_account C D w a b l r <=>
    dft_occ_count (FUNPOW (dft_occ_oracle_next w C) a l) - dft_occ_count l =
    dft_occ_count (FUNPOW (dft_occ_oracle_next w D) b r) - dft_occ_count r /\
    (!inst addr.
      (?j. j < a /\ dft_occ_gas_event inst addr
        (FUNPOW (dft_occ_oracle_next w C) j l)) <=>
      (?k. k < b /\ dft_occ_gas_event inst addr
        (FUNPOW (dft_occ_oracle_next w D) k r))) /\
    (!j f inst s. j < a /\
      dft_open_observe f inst s
        (FUNPOW (dft_occ_oracle_next w C) j l).dft_occ_core /\
      inst_mem_ranges inst s <> [] ==>
      ?k g t. k < b /\ dft_pos_functions C D f g /\
        dft_open_observe g inst t
          (FUNPOW (dft_occ_oracle_next w D) k r).dft_occ_core /\
        t.vs_memory = s.vs_memory /\ inst_mem_ranges inst t = inst_mem_ranges inst s) /\
    (!k g inst t. k < b /\
      dft_open_observe g inst t
        (FUNPOW (dft_occ_oracle_next w D) k r).dft_occ_core /\
      inst_mem_ranges inst t <> [] ==>
      ?j f s. j < a /\ dft_pos_functions C D f g /\
        dft_open_observe f inst s
          (FUNPOW (dft_occ_oracle_next w C) j l).dft_occ_core /\
        t.vs_memory = s.vs_memory /\ inst_mem_ranges inst t = inst_mem_ranges inst s)
End

Theorem dft_pos_silent_account:
  (!j. j < a ==> dft_fixed_silent_cut (FUNPOW (dft_occ_oracle_next w C) j l)) /\
  (!k. k < b ==> dft_fixed_silent_cut (FUNPOW (dft_occ_oracle_next w D) k r)) /\
  dft_occ_count (FUNPOW (dft_occ_oracle_next w C) a l) - dft_occ_count l =
  dft_occ_count (FUNPOW (dft_occ_oracle_next w D) b r) - dft_occ_count r ==>
  dft_pos_segment_account C D w a b l r
Proof
  simp[dft_pos_segment_account_def, dft_fixed_silent_cut_def] >> metis_tac[]
QED

Theorem dft_pos_enter_account:
  l.dft_occ_core = DftOpen (DftEnter f 0 s) ls nL /\
  r.dft_occ_core = DftOpen (DftEnter g 0 s) rs nR ==>
  dft_pos_segment_account C D w 1 1 l r
Proof
  strip_tac >>
  `dft_occ_count (dft_occ_oracle_next w C l) = nL /\
   dft_occ_count (dft_occ_oracle_next w D r) = nR` by
    metis_tac[dft_pos_enter_count] >>
  simp[dft_pos_segment_account_def] >>
  gvs[dft_occ_count_def, dft_occ_gas_event_def, dft_occ_event_def,
      dft_open_observe_def]
QED

Theorem dft_pos_at_outside_account:
  D = dft_pos_edit_ctx fi bi pre x call post C /\
  dft_pos_runtime_ready C fi bi pre x call post /\
  dft_pos_slot C D j k f g bb bb' /\
  (j <> fi \/ k <> bi \/
    (s.vs_inst_idx <> LENGTH pre /\ s.vs_inst_idx <> SUC (LENGTH pre))) /\
  l.dft_occ_core = DftOpen (DftAt f 0 bb s) ls nL /\
  r.dft_occ_core = DftOpen (DftAt g 0 bb' s) rs nR /\
  l.dft_occ_path = r.dft_occ_path /\ l.dft_occ_visit = r.dft_occ_visit ==>
  dft_pos_segment_account C D w 1 1 l r
Proof
  strip_tac >>
  `dft_occ_count (dft_occ_oracle_next w C l) - dft_occ_count l =
   dft_occ_count (dft_occ_oracle_next w D r) - dft_occ_count r` by
    metis_tac[dft_pos_at_outside_count] >>
  `!inst addr. dft_occ_gas_event inst addr l <=> dft_occ_gas_event inst addr r` by
    metis_tac[dft_pos_at_outside_event] >>
  `get_instruction bb s.vs_inst_idx = get_instruction bb' s.vs_inst_idx` by
    metis_tac[dft_pos_slot_instruction_outside] >>
  `dft_pos_functions C D f g` by
    (fs[dft_pos_slot_def, dft_pos_functions_def] >> metis_tac[]) >>
  qpat_x_assum `D = _` kall_tac >>
  simp[dft_pos_segment_account_def] >> conj_tac
  >- (rpt strip_tac >> gvs[dft_open_observe_def] >> metis_tac[]) >>
  rpt strip_tac >> gvs[dft_open_observe_def] >> metis_tac[]
QED

Theorem dft_pos_done_one_account:
  l.dft_occ_core = DftOpen (DftDone result) ls nL /\
  r.dft_occ_core = DftOpen (DftDone result) rs nR ==>
  dft_pos_segment_account C D w 1 1 l r
Proof
  strip_tac >>
  `dft_occ_count (dft_occ_oracle_next w C l) = dft_occ_count l /\
   dft_occ_count (dft_occ_oracle_next w D r) = dft_occ_count r` by
    metis_tac[dft_fixed_done_count] >>
  irule dft_pos_silent_account >> simp[] >> metis_tac[dft_fixed_silent_done]
QED

Theorem dft_pos_pending_return_account:
  dft_crossing_evidence z /\
  l.dft_occ_core = DftOpen (DftDone (IntRet ret cs)) fl nL /\
  r.dft_occ_core = DftOpen (DftDone (IntRet ret cs))
    (DftCaller z.dft_cert_delayed_fn 0 z.dft_cert_after z.dft_cert_call
      z.dft_cert_start::rs) nR /\
  r.dft_occ_saved = (path,visit)::saved /\
  MAP (dft_fill_frame 0) rs = rs /\
  dft_restore z.dft_cert_call.inst_outputs ret cs z.dft_cert_start = SOME restored ==>
  dft_pos_segment_account C D w 1 2 l r
Proof
  strip_tac >>
  `z.dft_cert_call.inst_opcode = INVOKE` by fs[dft_crossing_evidence_def] >>
  `dft_occ_oracle_next w D r = r with
    <|dft_occ_core := DftOpen (DftAt z.dft_cert_delayed_fn 0 z.dft_cert_after
      (restored with vs_inst_idx := SUC z.dft_cert_start.vs_inst_idx)) rs nR;
      dft_occ_path := path; dft_occ_visit := visit; dft_occ_saved := saved|>` by
    metis_tac[dftOccurrenceSuspendedTheory.dft_suspend_pop] >>
  `inst_mem_ranges z.dft_cert_partner
    (restored with vs_inst_idx := SUC z.dft_cert_start.vs_inst_idx) = []` by
    metis_tac[dft_certificate_return_no_observations] >>
  drule dft_certificate_partner_ordinary >> strip_tac >>
  `dft_fixed_silent_cut (dft_occ_oracle_next w D r) /\
   dft_occ_count (dft_occ_oracle_next w D (dft_occ_oracle_next w D r)) =
     dft_occ_count (dft_occ_oracle_next w D r)` by
    (irule dft_fixed_silent_at >> simp[dft_certificate_delayed_lookup] >> metis_tac[]) >>
  `dft_fixed_silent_cut l /\ dft_fixed_silent_cut r` by
    metis_tac[dft_fixed_silent_done] >>
  `dft_occ_count (dft_occ_oracle_next w C l) = dft_occ_count l /\
   dft_occ_count (dft_occ_oracle_next w D r) = dft_occ_count r` by
    metis_tac[dft_fixed_done_count] >>
  irule dft_pos_silent_account >> simp[FUNPOW_2] >>
  `!j:num. j < 2 <=> j = 0 \/ j = 1` by decide_tac >>
  simp[] >> rpt strip_tac >> gvs[]
QED

Theorem dft_pos_empty_done_next[local]:
  l.dft_occ_core = DftOpen (DftDone result) [] n ==>
  dft_occ_oracle_next w C l = l with
    <|dft_occ_core := DftOpen (DftDone result) [] n; dft_occ_saved := []|>
Proof
  strip_tac >> Cases_on `result` >>
  simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
       dft_fill_def, dft_fill_control_def, dft_open_next_def,
       dft_open_return_def, dft_erase_def, dft_occ_update_def]
QED

Theorem dft_pos_done_segment:
  dft_pos_phase C D fi bi pre x call post l r /\
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  l.dft_occ_core = DftOpen (DftDone result) ls nL /\
  r.dft_occ_core = DftOpen (DftDone result) rs nR ==>
  ?b. (b = 1 \/ b = 2) /\
    dft_pos_phase C D fi bi pre x call post
      (dft_occ_oracle_next w C l) (FUNPOW (dft_occ_oracle_next w D) b r) /\
    dft_pos_segment_account C D w 1 b l r
Proof
  strip_tac >>
  `dft_pos_segment_account C D w 1 1 l r` by metis_tac[dft_pos_done_one_account] >>
  Cases_on `?ret cs. result = IntRet ret cs`
  >- (pop_assum strip_assume_tac >> gvs[] >> suspend "return") >>
  `!ret cs. result <> IntRet ret cs` by metis_tac[] >>
  `dft_occ_oracle_next w C l = l with
    <|dft_occ_core := DftOpen (DftDone result) [] nL; dft_occ_saved := []|> /\
   dft_occ_oracle_next w D r = r with
    <|dft_occ_core := DftOpen (DftDone result) [] nR; dft_occ_saved := []|>` by
    metis_tac[dft_pos_nonreturn_clear] >>
  qexists `1` >> simp[] >> metis_tac[dft_pos_cleared_phase]
QED

Resume dft_pos_done_segment[return]:
  `?certs. dft_pos_stack C D fi bi pre x call post certs ls rs /\
    LENGTH l.dft_occ_saved = LENGTH certs` by (fs[dft_pos_phase_def] >> metis_tac[]) >>
  Cases_on `certs`
  >- (fs[dft_pos_stack_def] >> gvs[] >>
      `dft_occ_oracle_next w C l = l with
        <|dft_occ_core := DftOpen (DftDone (IntRet ret cs)) [] nL; dft_occ_saved := []|> /\
       dft_occ_oracle_next w D r = r with
        <|dft_occ_core := DftOpen (DftDone (IntRet ret cs)) [] nR; dft_occ_saved := []|>` by
        metis_tac[dft_pos_empty_done_next] >>
      qexists `1` >> simp[] >> metis_tac[dft_pos_cleared_phase]) >>
  fs[dft_pos_stack_def] >> gvs[] >> Cases_on `h`
  >- suspend "plain" >>
  suspend "pending"
QED

Resume dft_pos_done_segment[plain]:
  qexists `1` >> simp[] >> Cases_on `l'` >>
  rename1 `DftCaller f fuel bb inst s` >>
  Cases_on `dft_restore inst.inst_outputs ret cs s`
  >- (`!f' fuel' bb' inst' s'.
         DftCaller f fuel bb inst s = DftCaller f' fuel' bb' inst' s' ==>
         dft_restore inst'.inst_outputs ret cs s' = NONE` by simp[] >>
      drule_all dft_pos_plain_return_failure >> strip_tac >>
      irule dft_pos_cleared_phase >> goal_assum (drule_at Any) >> metis_tac[]) >>
  irule dft_pos_plain_return_success >> goal_assum (drule_at Any) >>
  metis_tac[dft_open_frame_11]
QED

Resume dft_pos_done_segment[pending]:
  rename1 `dft_pos_frame C D fi bi pre x call post (SOME z) lf rf` >>
  Cases_on `dft_restore z.dft_cert_call.inst_outputs ret cs z.dft_cert_start`
  >- (drule_all dft_pos_pending_failure >> strip_tac >>
      qexists `1` >> simp[] >> metis_tac[dft_pos_cleared_phase]) >>
  suspend "pending_success"
QED

Resume dft_pos_done_segment[pending_success]:
  `z.dft_cert_forward` by fs[dft_pos_frame_def, dft_pos_certificate_def] >>
  `?a. dft_restore z.dft_cert_call.inst_outputs ret cs
    (z.dft_cert_result with vs_inst_idx := SUC z.dft_cert_start.vs_inst_idx) = SOME a` by
    metis_tac[dftOccurrenceReturnTheory.dft_restore_pair_failure,
              optionTheory.option_CASES, optionTheory.NOT_NONE_SOME] >>
  qexists `2` >> simp[] >> conj_tac
  >- (irule dft_pos_pending_return_success >> goal_assum (drule_at Any) >>
      metis_tac[dft_pos_stack_cons]) >>
  `l.dft_occ_saved = r.dft_occ_saved` by fs[dft_pos_phase_def] >>
  Cases_on `l.dft_occ_saved` >> gvs[] >> PairCases_on `h` >>
  drule dft_pos_stack_fill >> strip_tac >>
  fs[dft_pos_frame_def, dft_certificate_saved_def] >> gvs[] >>
  irule dft_pos_pending_return_account >> simp[] >> metis_tac[]
QED
Finalise dft_pos_done_segment

Theorem dft_pos_segment_next:
  D = dft_pos_edit_ctx fi bi pre x call post C /\
  dft_pos_runtime_ready C fi bi pre x call post /\
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  dft_pos_phase C D fi bi pre x call post l r /\
  (!f g bb bb' s ls n.
    dft_pos_slot C D fi bi f g bb bb' /\
    l.dft_occ_core = DftOpen (DftAt f 0 bb s) ls n /\ s.vs_inst_idx = LENGTH pre ==>
    ?f0 b0. dft_recursive_crossing_ready f0 b0 bb pre x call post s) ==>
  ?a b. (a = 1 \/ a = 2) /\ (b = 1 \/ b = 2) /\
    dft_pos_phase C D fi bi pre x call post
      (FUNPOW (dft_occ_oracle_next w C) a l) (FUNPOW (dft_occ_oracle_next w D) b r) /\
    dft_pos_segment_account C D w a b l r
Proof
  strip_tac >>
  `?ctl ctl' certs ls rs nL nR.
    l.dft_occ_core = DftOpen ctl ls nL /\ r.dft_occ_core = DftOpen ctl' rs nR /\
    dft_pos_control C D fi bi pre ctl ctl'` by
    (fs[dft_pos_phase_def] >> metis_tac[]) >>
  qpat_x_assum `dft_pos_control _ _ _ _ _ _ _` mp_tac >>
  simp[dft_pos_control_def] >> strip_tac
  >- suspend "enter"
  >- suspend "at" >>
  suspend "done"
QED

Resume dft_pos_segment_next[enter]:
  gvs[] >> qexistsl [`1`,`1`] >> pure_rewrite_tac[FUNPOW_1] >>
  simp[Once CONJ_ASSOC] >> conj_tac
  >- (irule dft_pos_enter_next >> goal_assum (drule_at Any) >> metis_tac[]) >>
  metis_tac[dft_pos_enter_account]
QED
Resume dft_pos_segment_next[done]:
  gvs[] >> drule_all dft_pos_done_segment >>
  disch_then (qspec_then `w` strip_assume_tac) >>
  qexistsl [`1`,`b`] >> pure_rewrite_tac[FUNPOW_1] >> simp[]
QED
Resume dft_pos_segment_next[at]:
  gvs[] >> Cases_on `j = fi /\ k = bi /\ s.vs_inst_idx = LENGTH pre`
  >- suspend "crossing" >>
  `j <> fi \/ k <> bi \/
    (s.vs_inst_idx <> LENGTH pre /\ s.vs_inst_idx <> SUC (LENGTH pre))` by metis_tac[] >>
  (qexistsl [`1`,`1`] >> pure_rewrite_tac[FUNPOW_1] >> simp[] >> conj_tac
   >- (irule dft_pos_at_outside_next >> goal_assum (drule_at Any) >> metis_tac[]) >>
   fs[dft_pos_phase_def] >> metis_tac[dft_pos_at_outside_account])
QED
Resume dft_pos_segment_next[crossing]:
  gvs[] >>
  `?f0 b0. dft_recursive_crossing_ready f0 b0 b pre x call post s` by metis_tac[] >>
  `dft_pos_phase C (dft_pos_edit_ctx fi bi pre x call post C) fi bi pre x call post
     (FUNPOW (dft_occ_oracle_next w C) 2 l)
     (dft_occ_oracle_next w (dft_pos_edit_ctx fi bi pre x call post C) r) /\
   dft_occ_count (FUNPOW (dft_occ_oracle_next w C) 2 l) = nL /\
   dft_occ_count (dft_occ_oracle_next w (dft_pos_edit_ctx fi bi pre x call post C) r) = nR` by
    metis_tac[dft_pos_crossing_next] >>
  `dft_occ_count l = nL /\ dft_occ_count r = nR` by simp[dft_occ_count_def] >>
  qexistsl [`2`,`1`] >> pure_rewrite_tac[FUNPOW_1] >> simp[] >>
  irule dft_pos_silent_account >> simp[] >>
  metis_tac[SRULE [] dft_pos_crossing_silent]
QED
Finalise dft_pos_segment_next
