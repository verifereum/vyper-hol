Theory dftRecursiveReturnPhase
Ancestors
  dftRecursiveReturnReplay dftRecursiveCallProvenance dftRecursiveCallResidual
  dftOccurrenceSuspended dftOccurrenceOrdinaryEdit dftOriginalRuntime
  dftOccurrenceMachine dftOccurrenceReplay dftOpenMachine venomExecSemantics
  dftOpenErase venomState venomInst list arithmetic

Definition dft_recursive_done_phase_def:
  dft_recursive_done_phase fm bm z certs ret cs path visit saved l r <=>
    ?fl fr ls rs nL nR.
      l.dft_occ_core = DftOpen (DftDone (IntRet ret cs)) (fl::ls) nL /\
      r.dft_occ_core = DftOpen (DftDone (IntRet ret cs)) (fr::rs) nR /\
      dft_provenanced_frame fm bm (SOME z) fl fr /\
      dft_provenanced_frames fm bm certs ls rs /\
      l.dft_occ_saved = (path,visit)::saved /\
      r.dft_occ_saved = (path,visit)::saved /\
      l.dft_occ_path = r.dft_occ_path /\ l.dft_occ_visit = r.dft_occ_visit /\
      LENGTH saved = LENGTH certs /\
      dft_original_ready l /\ dft_original_ready r
End

Theorem dft_provenanced_frames_fill:
  !certs ls rs. dft_provenanced_frames fm bm certs ls rs ==>
    MAP (dft_fill_frame 0) ls = ls /\ MAP (dft_fill_frame 0) rs = rs
Proof
  Induct >> simp[dft_provenanced_frames_def] >> rpt strip_tac >> gvs[] >>
  drule dft_provenanced_frame_projection >>
  Cases_on `l` >> Cases_on `r` >>
  simp[dft_recursive_frame_def] >> strip_tac >> gvs[] >>
  first_x_assum drule >> simp[dft_fill_frame_def]
QED

Theorem dft_provenanced_frames_saved_empty:
  dft_provenanced_frames fm bm certs ls rs /\ LENGTH saved = LENGTH certs ==>
  (ls = [] ==> saved = []) /\ (rs = [] ==> saved = [])
Proof
  strip_tac >> drule dft_provenanced_frames_projection >> strip_tac >>
  drule dft_recursive_frames_lengths >> simp[] >> metis_tac[LENGTH_NIL]
QED

Theorem dft_certificate_delayed_lookup:
  dft_crossing_evidence z ==>
  get_instruction z.dft_cert_after (SUC z.dft_cert_start.vs_inst_idx) =
    SOME z.dft_cert_partner
Proof
  simp[dft_crossing_evidence_def] >> rpt strip_tac >>
  simp[get_instruction_def, APPEND_ASSOC, EL_APPEND_EQN]
QED

Theorem dft_certificate_partner_ordinary:
  dft_crossing_evidence z ==>
  z.dft_cert_partner.inst_opcode <> INVOKE /\
  z.dft_cert_partner.inst_opcode <> GAS /\
  ~is_terminator z.dft_cert_partner.inst_opcode
Proof
  simp[dft_crossing_evidence_def] >> strip_tac >>
  drule_all dftOccurrenceFrameTheory.dft_invoke_inversion_disjoint >>
  Cases_on `z.dft_cert_partner.inst_opcode = INVOKE` >>
  simp[venomEffectsTheory.read_effects_def, venomEffectsTheory.empty_effects_def,
       venomEffectsTheory.all_effects_def]
QED

Theorem dft_certificate_delayed_next:
  dft_crossing_evidence z /\
  dft_restore z.dft_cert_call.inst_outputs ret cs
    (z.dft_cert_result with vs_inst_idx := SUC z.dft_cert_start.vs_inst_idx) = SOME a /\
  dft_restore z.dft_cert_call.inst_outputs ret cs z.dft_cert_start = SOME b /\
  c.dft_occ_core = DftOpen
    (DftAt z.dft_cert_delayed_fn 0 z.dft_cert_after
      (b with vs_inst_idx := SUC z.dft_cert_start.vs_inst_idx)) stack n /\
  MAP (dft_fill_frame 0) stack = stack /\
  (stack = [] ==> c.dft_occ_saved = []) ==>
  dft_occ_oracle_next w C c = c with dft_occ_core := DftOpen
    (DftAt z.dft_cert_delayed_fn 0 z.dft_cert_after
      (a with vs_inst_idx := SUC (SUC z.dft_cert_start.vs_inst_idx))) stack n
Proof
  strip_tac >> drule_all dft_certificate_return_replay_equal >> strip_tac >>
  drule dft_certificate_partner_ordinary >> strip_tac >>
  `get_instruction z.dft_cert_after
     (b with vs_inst_idx := SUC z.dft_cert_start.vs_inst_idx).vs_inst_idx =
     SOME z.dft_cert_partner` by simp[dft_certificate_delayed_lookup] >>
  drule_all dft_occ_ordinary_next >>
  disch_then (qspecl_then [`w`, `C`] mp_tac) >> simp[] >>
  Cases_on `stack` >> gvs[] >>
  simp[dft_occ_config_component_equality]
QED

Theorem dft_certificate_done_segment:
  dft_crossing_evidence z /\
  l.dft_occ_core = DftOpen (DftDone (IntRet ret cs))
    (DftCaller z.dft_cert_ordinary_fn 0 z.dft_cert_before z.dft_cert_call
      (z.dft_cert_result with vs_inst_idx := SUC z.dft_cert_start.vs_inst_idx)::ls) nL /\
  r.dft_occ_core = DftOpen (DftDone (IntRet ret cs))
    (DftCaller z.dft_cert_delayed_fn 0 z.dft_cert_after z.dft_cert_call
      z.dft_cert_start::rs) nR /\
  l.dft_occ_saved = (path,visit)::saved /\
  r.dft_occ_saved = (path,visit)::saved /\
  MAP (dft_fill_frame 0) ls = ls /\ MAP (dft_fill_frame 0) rs = rs /\
  (rs = [] ==> saved = []) /\
  dft_restore z.dft_cert_call.inst_outputs ret cs
    (z.dft_cert_result with vs_inst_idx := SUC z.dft_cert_start.vs_inst_idx) = SOME a /\
  dft_restore z.dft_cert_call.inst_outputs ret cs z.dft_cert_start = SOME b ==>
  dft_occ_oracle_next w C l = l with
    <|dft_occ_core := DftOpen (DftAt z.dft_cert_ordinary_fn 0 z.dft_cert_before
        (a with vs_inst_idx := SUC (SUC z.dft_cert_start.vs_inst_idx))) ls nL;
      dft_occ_path := path; dft_occ_visit := visit; dft_occ_saved := saved|> /\
  FUNPOW (dft_occ_oracle_next w D) 2 r = r with
    <|dft_occ_core := DftOpen (DftAt z.dft_cert_delayed_fn 0 z.dft_cert_after
        (a with vs_inst_idx := SUC (SUC z.dft_cert_start.vs_inst_idx))) rs nR;
      dft_occ_path := path; dft_occ_visit := visit; dft_occ_saved := saved|>
Proof
  strip_tac >>
  `z.dft_cert_call.inst_opcode = INVOKE` by fs[dft_crossing_evidence_def] >>
  conj_tac
  >- (qpat_x_assum `r.dft_occ_core = _` kall_tac >>
      drule_all dft_suspend_pop >>
      disch_then (qspecl_then [`w`, `C`] mp_tac) >> simp[]) >>
  `dft_occ_oracle_next w D r = r with
    <|dft_occ_core := DftOpen (DftAt z.dft_cert_delayed_fn 0 z.dft_cert_after
        (b with vs_inst_idx := SUC z.dft_cert_start.vs_inst_idx)) rs nR;
      dft_occ_path := path; dft_occ_visit := visit; dft_occ_saved := saved|>` by
    (drule_all dft_suspend_pop >>
     disch_then (qspecl_then [`w`, `D`] mp_tac) >> simp[]) >>
  rewrite_tac[FUNPOW_2] >> asm_rewrite_tac[] >>
  irule EQ_TRANS >>
  irule_at Any dft_certificate_delayed_next >> simp[] >>
  qexistsl [`z`, `ret`, `cs`, `b`, `a`] >> simp[]
QED

Theorem dft_recursive_done_success:
  dft_recursive_done_phase fm bm z certs ret cs path visit saved l r /\
  dft_restore z.dft_cert_call.inst_outputs ret cs
    (z.dft_cert_result with vs_inst_idx := SUC z.dft_cert_start.vs_inst_idx) = SOME a /\
  dft_restore z.dft_cert_call.inst_outputs ret cs z.dft_cert_start = SOME b ==>
  ?ls rs nL nR.
    dft_provenanced_frames fm bm certs ls rs /\
    FUNPOW (dft_occ_oracle_next w C) (if z.dft_cert_forward then 1 else 2) l =
      l with <|dft_occ_core := DftOpen
        (DftAt (if z.dft_cert_forward then z.dft_cert_ordinary_fn else z.dft_cert_delayed_fn) 0
          (if z.dft_cert_forward then z.dft_cert_before else z.dft_cert_after)
          (a with vs_inst_idx := SUC (SUC z.dft_cert_start.vs_inst_idx))) ls nL;
        dft_occ_path := path; dft_occ_visit := visit; dft_occ_saved := saved|> /\
    FUNPOW (dft_occ_oracle_next w D) (if z.dft_cert_forward then 2 else 1) r =
      r with <|dft_occ_core := DftOpen
        (DftAt (if z.dft_cert_forward then z.dft_cert_delayed_fn else z.dft_cert_ordinary_fn) 0
          (if z.dft_cert_forward then z.dft_cert_after else z.dft_cert_before)
          (a with vs_inst_idx := SUC (SUC z.dft_cert_start.vs_inst_idx))) rs nR;
        dft_occ_path := path; dft_occ_visit := visit; dft_occ_saved := saved|>
Proof
  strip_tac >>
  qpat_x_assum `dft_recursive_done_phase _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[dft_recursive_done_phase_def] >> strip_tac >>
  drule dft_provenanced_frames_fill >> strip_tac >>
  drule_all dft_provenanced_frames_saved_empty >> strip_tac >>
  qpat_x_assum `dft_provenanced_frame _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[dft_provenanced_frame_def, dft_certificate_saved_def, LET_THM] >>
  Cases_on `z.dft_cert_forward` >> simp[] >> strip_tac >> gvs[] >>
  qexistsl [`ls`, `rs`, `nL`, `nR`] >> simp[FUNPOW_1] >>
  drule_all dft_certificate_done_segment
  >- (disch_then (qspecl_then [`w`, `D`, `C`] mp_tac) >> simp[]) >>
  disch_then (qspecl_then [`w`, `C`, `D`] mp_tac) >> simp[] >> metis_tac[]
QED

Theorem dft_recursive_done_ready:
  dft_recursive_done_phase fm bm z certs ret cs path visit saved l r /\
  dft_original_context Corig C /\ dft_original_context Dorig D ==>
  dft_original_ready
    (FUNPOW (dft_occ_oracle_next w C) (if z.dft_cert_forward then 1 else 2) l) /\
  dft_original_ready
    (FUNPOW (dft_occ_oracle_next w D) (if z.dft_cert_forward then 2 else 1) r)
Proof
  strip_tac >>
  `dft_original_ready l /\ dft_original_ready r` by
    fs[dft_recursive_done_phase_def] >>
  metis_tac[dft_original_runtime_iter]
QED

Theorem dft_recursive_done_failure:
  dft_recursive_done_phase fm bm z certs ret cs path visit saved l r /\
  dft_restore z.dft_cert_call.inst_outputs ret cs z.dft_cert_start = NONE ==>
  ?nL nR.
    (dft_occ_oracle_next w C l).dft_occ_core =
      DftOpen (DftDone (Error "invoke: return arity mismatch")) [] nL /\
    (dft_occ_oracle_next w D r).dft_occ_core =
      DftOpen (DftDone (Error "invoke: return arity mismatch")) [] nR /\
    (dft_occ_oracle_next w C l).dft_occ_saved = [] /\
    (dft_occ_oracle_next w D r).dft_occ_saved = []
Proof
  strip_tac >>
  qpat_x_assum `dft_recursive_done_phase _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[dft_recursive_done_phase_def] >> strip_tac >>
  qpat_x_assum `dft_provenanced_frame _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[dft_provenanced_frame_def, dft_certificate_saved_def, LET_THM] >>
  Cases_on `z.dft_cert_forward` >> simp[] >> strip_tac >> gvs[] >>
  `dft_restore z.dft_cert_call.inst_outputs ret cs
    (z.dft_cert_result with vs_inst_idx := SUC z.dft_cert_start.vs_inst_idx) = NONE` by
    metis_tac[dftOccurrenceReturnTheory.dft_restore_pair_failure] >>
  qexistsl [`nL`, `nR`] >>
  rpt conj_tac >> metis_tac[dft_suspend_pop_failure]
QED

Theorem dft_certificate_return_no_observations:
  dft_crossing_evidence z ==>
  inst_mem_ranges z.dft_cert_partner s = [] /\
  inst_mem_ranges z.dft_cert_call t = []
Proof
  strip_tac >>
  `~dft_must_order z.dft_cert_partner z.dft_cert_call /\
   z.dft_cert_call.inst_opcode = INVOKE` by fs[dft_crossing_evidence_def] >>
  drule_all dftMixedCrossingTheory.dft_invoke_partner_no_observations >> simp[]
QED
