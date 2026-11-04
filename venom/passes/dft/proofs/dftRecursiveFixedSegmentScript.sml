Theory dftRecursiveFixedSegment
Ancestors
  dftRecursiveFixedCrossing dftRecursiveFixedDone dftRecursiveFixedStep
  dftRecursiveFixedPhase dftRecursiveReturnPhase dftRecursiveActivePhase
  dftRecursiveCallProvenance dftOccurrenceSuspended
  dftOccurrenceReplay dftOccurrenceMachine dftOpenMachine dftOpenErase
  contextRawReachable venomExecSemantics venomState list arithmetic

(* Half-open cuts: the endpoint belongs to the following segment. *)
Definition dft_fixed_segment_account_def:
  dft_fixed_segment_account q pre x call post w C D a b c d <=>
    dft_occ_count (FUNPOW (dft_occ_oracle_next w C) a c) - dft_occ_count c =
    dft_occ_count (FUNPOW (dft_occ_oracle_next w D) b d) - dft_occ_count d /\
    (!inst addr.
      (?j. j < a /\ dft_occ_gas_event inst addr
        (FUNPOW (dft_occ_oracle_next w C) j c)) <=>
      (?k. k < b /\ dft_occ_gas_event inst addr
        (FUNPOW (dft_occ_oracle_next w D) k d))) /\
    (!j fn inst s. j < a /\
      dft_open_observe fn inst s
        (FUNPOW (dft_occ_oracle_next w C) j c).dft_occ_core /\
      inst_mem_ranges inst s <> [] ==>
      ?k t. k < b /\
        dft_open_observe (dft_gas_edit_fn q pre x call post fn) inst t
          (FUNPOW (dft_occ_oracle_next w D) k d).dft_occ_core /\
        t.vs_memory = s.vs_memory /\ inst_mem_ranges inst t = inst_mem_ranges inst s) /\
    (!k fn inst t. k < b /\
      dft_open_observe fn inst t
        (FUNPOW (dft_occ_oracle_next w D) k d).dft_occ_core /\
      inst_mem_ranges inst t <> [] ==>
      ?j f s. j < a /\ fn = dft_gas_edit_fn q pre x call post f /\
        dft_open_observe f inst s
          (FUNPOW (dft_occ_oracle_next w C) j c).dft_occ_core /\
        t.vs_memory = s.vs_memory /\ inst_mem_ranges inst t = inst_mem_ranges inst s)
End

Theorem dft_fixed_segment_enter_account:
  c.dft_occ_core = DftOpen (DftEnter fn 0 s) ls nL /\
  d.dft_occ_core = DftOpen (DftEnter (dft_gas_edit_fn q pre x call post fn) 0 s) rs nR ==>
  dft_fixed_segment_account q pre x call post w C D 1 1 c d
Proof
  strip_tac >>
  `dft_occ_count (dft_occ_oracle_next w C c) = nL /\
   dft_occ_count (dft_occ_oracle_next w D d) = nR` by
    metis_tac[dft_fixed_enter_count] >>
  simp[dft_fixed_segment_account_def] >>
  gvs[dft_occ_count_def, dft_occ_gas_event_def, dft_occ_event_def,
      dft_open_observe_def]
QED

Theorem dft_fixed_segment_at_account:
  q.bb_instructions = pre ++ [x;call] ++ post /\
  ~(bb = q /\ s.vs_inst_idx = LENGTH pre) /\
  ~(bb = q /\ s.vs_inst_idx = SUC (LENGTH pre)) /\
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) ls nL /\
  d.dft_occ_core = DftOpen (DftAt (dft_gas_edit_fn q pre x call post fn) 0
    (dft_gas_edit_block q pre x call post bb) s) rs nR /\
  c.dft_occ_path = d.dft_occ_path /\ c.dft_occ_visit = d.dft_occ_visit ==>
  dft_fixed_segment_account q pre x call post w C D 1 1 c d
Proof
  strip_tac >>
  `dft_occ_count (dft_occ_oracle_next w C c) - dft_occ_count c =
   dft_occ_count (dft_occ_oracle_next w D d) - dft_occ_count d` by
    metis_tac[dft_fixed_at_count_agree] >>
  `!inst addr. dft_occ_event inst addr c <=> dft_occ_event inst addr d` by
    metis_tac[dft_fixed_at_event_agree] >>
  drule_all dft_fixed_instruction_outside >> strip_tac >>
  simp[dft_fixed_segment_account_def, dft_occ_gas_event_def] >>
  conj_tac
  >- (rpt strip_tac >>
      fs[dft_open_observe_def] >> gvs[] >>
      qexists `s` >> simp[dft_open_observe_def] >> metis_tac[]) >>
  rpt strip_tac >> fs[dft_open_observe_def] >> gvs[] >>
  qexistsl [`fn`, `s`] >> simp[dft_open_observe_def] >> metis_tac[]
QED

Definition dft_fixed_silent_cut_def:
  dft_fixed_silent_cut c <=>
    (!inst addr. ~dft_occ_gas_event inst addr c) /\
    (!fn inst s. dft_open_observe fn inst s c.dft_occ_core ==>
       inst_mem_ranges inst s = [])
End

Theorem dft_fixed_silent_done:
  c.dft_occ_core = DftOpen (DftDone res) ls n ==> dft_fixed_silent_cut c
Proof
  simp[dft_fixed_silent_cut_def, dft_occ_gas_event_def,
       dft_occ_event_def, dft_open_observe_def]
QED

Theorem dft_fixed_silent_at:
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) ls n /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode <> GAS /\ inst_mem_ranges inst s = [] ==>
  dft_fixed_silent_cut c /\ dft_occ_count (dft_occ_oracle_next w C c) = dft_occ_count c
Proof
  strip_tac >> conj_tac
  >- simp[dft_fixed_silent_cut_def, dft_occ_gas_event_def,
          dft_occ_event_def, dft_open_observe_def] >>
  drule dft_fixed_at_count >> simp[dft_occ_count_def]
QED

Theorem dft_fixed_silent_account:
  (!j. j < a ==> dft_fixed_silent_cut (FUNPOW (dft_occ_oracle_next w C) j c)) /\
  (!k. k < b ==> dft_fixed_silent_cut (FUNPOW (dft_occ_oracle_next w D) k d)) /\
  dft_occ_count (FUNPOW (dft_occ_oracle_next w C) a c) - dft_occ_count c =
  dft_occ_count (FUNPOW (dft_occ_oracle_next w D) b d) - dft_occ_count d ==>
  dft_fixed_segment_account q pre x call post w C D a b c d
Proof
  simp[dft_fixed_segment_account_def, dft_fixed_silent_cut_def] >>
  metis_tac[]
QED

Theorem dft_fixed_done_count:
  c.dft_occ_core = DftOpen (DftDone res) ls n ==>
  dft_occ_count (dft_occ_oracle_next w C c) = dft_occ_count c
Proof
  strip_tac >>
  simp[dft_occ_count_def, dft_occ_oracle_next_def, dft_occ_next_def,
       dft_next_inf_def, dft_fill_def, dft_fill_control_def, dft_open_next_def] >>
  Cases_on `res` >> Cases_on `ls` >>
  simp[dft_open_return_def, dft_erase_def, dft_fill_def] >>
  rename1 `DftDone (IntRet ret cs)` >> Cases_on `h` >>
  simp[dft_fill_frame_def, dft_open_return_def] >>
  CASE_TAC >>
  simp[dft_erase_def, dft_fill_def, dft_open_deliver_def, dft_open_continue_def]
QED

Theorem dft_fixed_segment_done_one_account:
  c.dft_occ_core = DftOpen (DftDone res) ls nL /\
  d.dft_occ_core = DftOpen (DftDone res) rs nR ==>
  dft_fixed_segment_account q pre x call post w C D 1 1 c d
Proof
  strip_tac >>
  `dft_occ_count (dft_occ_oracle_next w C c) = dft_occ_count c /\
   dft_occ_count (dft_occ_oracle_next w D d) = dft_occ_count d` by
    metis_tac[dft_fixed_done_count] >>
  irule dft_fixed_silent_account >> simp[] >>
  metis_tac[dft_fixed_silent_done]
QED

Theorem dft_fixed_crossing_mid:
  dft_recursive_crossing_ready f b q pre x call post s /\
  c.dft_occ_core = DftOpen (DftAt fn 0 q s) ls n /\
  dft_fixed_stack q pre x call post certs ls rs /\
  LENGTH c.dft_occ_saved = LENGTH certs /\ step_inst_base x s = OK t ==>
  dft_occ_oracle_next w C c = c with
    <|dft_occ_core := DftOpen
       (DftAt fn 0 q (t with vs_inst_idx := SUC s.vs_inst_idx)) ls n;
      dft_occ_saved := c.dft_occ_saved|>
Proof
  strip_tac >> drule dft_recursive_crossing_positions >> strip_tac >>
  `dft_provenanced_frames (dft_gas_edit_fn q pre x call post)
    (dft_gas_edit_block q pre x call post) certs ls rs` by fs[dft_fixed_stack_def] >>
  drule dft_provenanced_frames_fill >> strip_tac >>
  drule_all dft_provenanced_frames_saved_empty >> strip_tac >>
  `x.inst_opcode <> INVOKE /\ x.inst_opcode <> GAS /\
   ~is_terminator x.inst_opcode` by
    (fs[dft_recursive_crossing_ready_def] >>
     drule_all dftOccurrenceFrameTheory.dft_invoke_inversion_disjoint >>
     Cases_on `x.inst_opcode = INVOKE` >>
     simp[venomEffectsTheory.read_effects_def,
          venomEffectsTheory.empty_effects_def, venomEffectsTheory.all_effects_def]) >>
  drule_all dftOccurrenceOrdinaryEditTheory.dft_occ_ordinary_next >>
  disch_then (qspecl_then [`w`, `C`] mp_tac) >>
  Cases_on `ls` >> gvs[] >> simp[dft_occ_config_component_equality]
QED

Theorem dft_fixed_crossing_account:
  dft_recursive_crossing_ready f b q pre x call post s /\
  c.dft_occ_core = DftOpen (DftAt fn 0 q s) ls nL /\
  d.dft_occ_core = DftOpen (DftAt (dft_gas_edit_fn q pre x call post fn) 0
    (dft_gas_edit_block q pre x call post q) s) rs nR /\
  dft_fixed_stack q pre x call post certs ls rs /\
  LENGTH c.dft_occ_saved = LENGTH certs ==>
  dft_fixed_segment_account q pre x call post w C
    (dft_gas_edit_ctx q pre x call post C) 2 1 c d
Proof
  strip_tac >> drule dft_recursive_crossing_partner_success >> strip_tac >>
  drule_all dft_fixed_crossing_mid >>
  disch_then (qspecl_then [`w`, `C`] assume_tac) >>
  drule dft_recursive_crossing_positions >> strip_tac >>
  `inst_mem_ranges x s = [] /\
   inst_mem_ranges call (t with vs_inst_idx := SUC s.vs_inst_idx) = [] /\
   inst_mem_ranges call s = []` by
    (fs[dft_recursive_crossing_ready_def] >>
     metis_tac[dftMixedCrossingTheory.dft_invoke_partner_no_observations]) >>
  `x.inst_opcode <> GAS /\ call.inst_opcode <> GAS` by
    fs[dft_recursive_crossing_ready_def] >>
  `dft_fixed_silent_cut c /\
   dft_occ_count (dft_occ_oracle_next w C c) = dft_occ_count c` by
    metis_tac[dft_fixed_silent_at] >>
  `dft_fixed_silent_cut d /\
   dft_occ_count (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x call post C) d) =
     dft_occ_count d` by metis_tac[dft_fixed_silent_at] >>
  `dft_fixed_silent_cut (dft_occ_oracle_next w C c) /\
   dft_occ_count (dft_occ_oracle_next w C (dft_occ_oracle_next w C c)) =
     dft_occ_count (dft_occ_oracle_next w C c)` by
    (irule dft_fixed_silent_at >> simp[] >> metis_tac[]) >>
  irule dft_fixed_silent_account >> simp[FUNPOW_2] >>
  `!j:num. j < 2 <=> j = 0 \/ j = 1` by decide_tac >>
  simp[] >> rpt strip_tac >> gvs[]
QED

Theorem dft_fixed_pending_return_account:
  dft_crossing_evidence z /\
  c.dft_occ_core = DftOpen (DftDone (IntRet ret cs)) fl nL /\
  d.dft_occ_core = DftOpen (DftDone (IntRet ret cs))
    (DftCaller z.dft_cert_delayed_fn 0 z.dft_cert_after z.dft_cert_call
      z.dft_cert_start::rs) nR /\
  d.dft_occ_saved = (path,visit)::saved /\
  MAP (dft_fill_frame 0) rs = rs /\
  dft_restore z.dft_cert_call.inst_outputs ret cs z.dft_cert_start = SOME restored ==>
  dft_fixed_segment_account q pre x call post w C D 1 2 c d
Proof
  strip_tac >>
  `z.dft_cert_call.inst_opcode = INVOKE` by fs[dft_crossing_evidence_def] >>
  `dft_occ_oracle_next w D d = d with
    <|dft_occ_core := DftOpen (DftAt z.dft_cert_delayed_fn 0 z.dft_cert_after
      (restored with vs_inst_idx := SUC z.dft_cert_start.vs_inst_idx)) rs nR;
      dft_occ_path := path; dft_occ_visit := visit; dft_occ_saved := saved|>` by
    metis_tac[dftOccurrenceSuspendedTheory.dft_suspend_pop] >>
  `inst_mem_ranges z.dft_cert_partner
    (restored with vs_inst_idx := SUC z.dft_cert_start.vs_inst_idx) = []` by
    metis_tac[dft_certificate_return_no_observations] >>
  drule dft_certificate_partner_ordinary >> strip_tac >>
  `dft_fixed_silent_cut (dft_occ_oracle_next w D d) /\
   dft_occ_count (dft_occ_oracle_next w D (dft_occ_oracle_next w D d)) =
     dft_occ_count (dft_occ_oracle_next w D d)` by
    (irule dft_fixed_silent_at >> simp[dft_certificate_delayed_lookup] >> metis_tac[]) >>
  `dft_fixed_silent_cut c /\ dft_fixed_silent_cut d` by
    metis_tac[dft_fixed_silent_done] >>
  `dft_occ_count (dft_occ_oracle_next w C c) = dft_occ_count c /\
   dft_occ_count (dft_occ_oracle_next w D d) = dft_occ_count d` by
    metis_tac[dft_fixed_done_count] >>
  irule dft_fixed_silent_account >> simp[FUNPOW_2] >>
  `!j:num. j < 2 <=> j = 0 \/ j = 1` by decide_tac >>
  simp[] >> rpt strip_tac >> gvs[]
QED
