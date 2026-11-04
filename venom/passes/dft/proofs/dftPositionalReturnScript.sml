Theory dftPositionalReturn
Ancestors
  dftPositionalPhase dftRecursiveReturnPhase dftRecursiveCallProvenance
  dftOriginalRuntime dftOccurrenceMachine dftOccurrenceReplay dftOccurrenceReturn
  dftOccurrenceSuspended dftOpenMachine dftOpenErase
  venomExecSemantics venomState list arithmetic

Theorem dft_pos_stack_cons[simp]:
  dft_pos_stack C D fi bi pre x call post (z::zs) (l::ls) (r::rs) <=>
  dft_pos_frame C D fi bi pre x call post z l r /\
  dft_pos_stack C D fi bi pre x call post zs ls rs
Proof simp[dft_pos_stack_def]
QED

Theorem dft_pos_stack_lengths:
  !zs ls rs. dft_pos_stack C D fi bi pre x call post zs ls rs ==>
    LENGTH ls = LENGTH zs /\ LENGTH rs = LENGTH zs
Proof
  Induct >> simp[dft_pos_stack_def] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule >> simp[]
QED

Theorem dft_pos_frame_fill:
  dft_pos_frame C D fi bi pre x call post z l r ==>
  dft_fill_frame 0 l = l /\ dft_fill_frame 0 r = r
Proof
  Cases_on `z` >> simp[dft_pos_frame_def] >> rpt strip_tac >> gvs[]
  >- simp[dft_fill_frame_def] >>
  fs[dft_pos_certificate_def, dft_certificate_saved_def] >> gvs[] >>
  simp[dft_fill_frame_def]
QED

Theorem dft_pos_stack_fill:
  !zs ls rs. dft_pos_stack C D fi bi pre x call post zs ls rs ==>
  MAP (dft_fill_frame 0) ls = ls /\ MAP (dft_fill_frame 0) rs = rs
Proof
  Induct >> simp[dft_pos_stack_def] >> rpt strip_tac >> gvs[] >>
  drule dft_pos_frame_fill >> strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem dft_pos_stack_saved_empty:
  dft_pos_stack C D fi bi pre x call post zs ls rs /\ LENGTH saved = LENGTH zs ==>
  (ls = [] ==> saved = []) /\ (rs = [] ==> saved = [])
Proof
  strip_tac >> drule dft_pos_stack_lengths >> simp[] >> metis_tac[LENGTH_NIL]
QED

Theorem dft_pos_pending_replay[local]:
  dft_pos_frame C D fi bi pre x call post (SOME z) lf rf /\
  l.dft_occ_core = DftOpen (DftDone (IntRet ret cs)) (lf::ls) nL /\
  r.dft_occ_core = DftOpen (DftDone (IntRet ret cs)) (rf::rs) nR /\
  l.dft_occ_saved = (path,visit)::saved /\
  r.dft_occ_saved = (path,visit)::saved /\
  dft_pos_stack C D fi bi pre x call post certs ls rs /\
  LENGTH saved = LENGTH certs /\
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
  strip_tac >> drule dft_pos_stack_fill >> strip_tac >>
  drule_all dft_pos_stack_saved_empty >> strip_tac >>
  `z.dft_cert_forward` by fs[dft_pos_frame_def, dft_pos_certificate_def] >>
  fs[dft_pos_frame_def, dft_certificate_saved_def] >> gvs[] >>
  drule_all dft_certificate_done_segment >> simp[]
QED

Theorem dft_pos_pending_return_success:
  dft_pos_phase C D fi bi pre x call post l r /\
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  l.dft_occ_core = DftOpen (DftDone (IntRet ret cs)) (lf::ls) nL /\
  r.dft_occ_core = DftOpen (DftDone (IntRet ret cs)) (rf::rs) nR /\
  dft_pos_frame C D fi bi pre x call post (SOME z) lf rf /\
  dft_pos_stack C D fi bi pre x call post (SOME z::certs) (lf::ls) (rf::rs) /\
  LENGTH l.dft_occ_saved = SUC (LENGTH certs) /\
  dft_restore z.dft_cert_call.inst_outputs ret cs
    (z.dft_cert_result with vs_inst_idx := SUC z.dft_cert_start.vs_inst_idx) = SOME a /\
  dft_restore z.dft_cert_call.inst_outputs ret cs z.dft_cert_start = SOME b ==>
  dft_pos_phase C D fi bi pre x call post
    (dft_occ_oracle_next w C l) (FUNPOW (dft_occ_oracle_next w D) 2 r)
Proof
  strip_tac >>
  `l.dft_occ_saved = r.dft_occ_saved /\ dft_original_ready l /\ dft_original_ready r` by
    fs[dft_pos_phase_def] >>
  Cases_on `l.dft_occ_saved` >> gvs[] >> PairCases_on `h` >>
  `dft_original_ready (dft_occ_oracle_next w C l)` by
    metis_tac[dft_original_runtime_next] >>
  `dft_original_ready (FUNPOW (dft_occ_oracle_next w D) 2 r)` by
    metis_tac[dft_original_runtime_iter] >>
  `l.dft_occ_saved = (h0,h1)::t /\ r.dft_occ_saved = (h0,h1)::t` by metis_tac[] >>
  drule_all dft_pos_pending_replay >> strip_tac >>
  asm_rewrite_tac[] >> simp[dft_pos_phase_def] >> qexists `certs` >>
  fs[dft_pos_frame_def, dft_pos_certificate_def] >>
  simp[dft_pos_control_def] >> metis_tac[]
QED

Theorem dft_pos_return_clear[local]:
  c.dft_occ_core = DftOpen (DftDone result) stack n /\
  dft_open_return result (MAP (dft_fill_frame 1) stack) n =
    DftOpen (DftDone out) [] n ==>
  dft_occ_oracle_next w C c = c with
    <|dft_occ_core := DftOpen (DftDone out) [] n; dft_occ_saved := []|>
Proof
  simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
    dft_fill_def, dft_fill_control_def, dft_open_next_def,
    dft_erase_def, dft_occ_update_def]
QED

Theorem dft_pos_cleared_phase[local]:
  dft_pos_phase C D fi bi pre x call post l r /\
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  dft_occ_oracle_next w C l = l with
    <|dft_occ_core := DftOpen (DftDone out) [] nL; dft_occ_saved := []|> /\
  dft_occ_oracle_next w D r = r with
    <|dft_occ_core := DftOpen (DftDone out) [] nR; dft_occ_saved := []|> ==>
  dft_pos_phase C D fi bi pre x call post
    (dft_occ_oracle_next w C l) (dft_occ_oracle_next w D r)
Proof
  strip_tac >>
  `dft_original_ready l /\ dft_original_ready r` by fs[dft_pos_phase_def] >>
  `dft_original_ready (dft_occ_oracle_next w C l) /\
   dft_original_ready (dft_occ_oracle_next w D r)` by
    metis_tac[dft_original_runtime_next] >>
  asm_rewrite_tac[] >> simp[dft_pos_phase_def] >>
  fs[dft_pos_phase_def, dft_pos_stack_def, dft_pos_control_def] >> metis_tac[]
QED

Theorem dft_pos_pending_failure[local]:
  dft_pos_frame C D fi bi pre x call post (SOME z) lf rf /\
  l.dft_occ_core = DftOpen (DftDone (IntRet ret cs)) (lf::ls) nL /\
  r.dft_occ_core = DftOpen (DftDone (IntRet ret cs)) (rf::rs) nR /\
  dft_restore z.dft_cert_call.inst_outputs ret cs z.dft_cert_start = NONE ==>
  dft_occ_oracle_next w C l = l with
    <|dft_occ_core := DftOpen (DftDone (Error "invoke: return arity mismatch")) [] nL;
      dft_occ_saved := []|> /\
  dft_occ_oracle_next w D r = r with
    <|dft_occ_core := DftOpen (DftDone (Error "invoke: return arity mismatch")) [] nR;
      dft_occ_saved := []|>
Proof
  strip_tac >>
  `z.dft_cert_forward` by fs[dft_pos_frame_def, dft_pos_certificate_def] >>
  `dft_restore z.dft_cert_call.inst_outputs ret cs
    (z.dft_cert_result with vs_inst_idx := SUC z.dft_cert_start.vs_inst_idx) = NONE` by
    metis_tac[dft_restore_pair_failure] >>
  fs[dft_pos_frame_def, dft_certificate_saved_def] >> gvs[] >>
  conj_tac >> irule dft_pos_return_clear >> simp[] >>
  simp[dft_open_return_def, dft_fill_frame_def, GSYM dft_restore_def]
QED

Theorem dft_pos_nonreturn_clear[local]:
  c.dft_occ_core = DftOpen (DftDone result) stack n /\
  (!ret cs. result <> IntRet ret cs) ==>
  dft_occ_oracle_next w C c = c with
    <|dft_occ_core := DftOpen (DftDone result) [] n; dft_occ_saved := []|>
Proof
  strip_tac >> irule dft_pos_return_clear >> simp[] >>
  Cases_on `result` >> gvs[dft_open_return_def]
QED

Theorem dft_pos_pending_return:
  dft_pos_phase C D fi bi pre x call post l r /\
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  l.dft_occ_core = DftOpen (DftDone result) (lf::ls) nL /\
  r.dft_occ_core = DftOpen (DftDone result) (rf::rs) nR /\
  dft_pos_frame C D fi bi pre x call post (SOME z) lf rf /\
  dft_pos_stack C D fi bi pre x call post (SOME z::certs) (lf::ls) (rf::rs) /\
  LENGTH l.dft_occ_saved = SUC (LENGTH certs) ==>
  ?b. (b = 1 \/ b = 2) /\
    dft_pos_phase C D fi bi pre x call post
      (dft_occ_oracle_next w C l) (FUNPOW (dft_occ_oracle_next w D) b r)
Proof
  strip_tac >> Cases_on `?ret cs. result = IntRet ret cs`
  >- (pop_assum strip_assume_tac >> gvs[] >>
      Cases_on `dft_restore z.dft_cert_call.inst_outputs ret cs z.dft_cert_start`
      >- (drule_all dft_pos_pending_failure >> strip_tac >>
          qexists `1` >> pure_rewrite_tac[FUNPOW_1] >>
          conj_tac >- simp[] >> irule dft_pos_cleared_phase >>
          goal_assum (drule_at Any) >> metis_tac[]) >>
      `?a. dft_restore z.dft_cert_call.inst_outputs ret cs
        (z.dft_cert_result with vs_inst_idx := SUC z.dft_cert_start.vs_inst_idx) = SOME a` by
        metis_tac[dft_restore_pair_failure, optionTheory.option_CASES, optionTheory.NOT_NONE_SOME] >>
      qexists `2` >> simp[] >> irule dft_pos_pending_return_success >>
      goal_assum (drule_at Any) >> metis_tac[dft_pos_stack_cons]) >>
  `!ret cs. result <> IntRet ret cs` by metis_tac[] >>
  `dft_occ_oracle_next w C l = l with
    <|dft_occ_core := DftOpen (DftDone result) [] nL; dft_occ_saved := []|>` by
    (irule dft_pos_nonreturn_clear >> simp[]) >>
  `dft_occ_oracle_next w D r = r with
    <|dft_occ_core := DftOpen (DftDone result) [] nR; dft_occ_saved := []|>` by
    (irule dft_pos_nonreturn_clear >> simp[]) >>
  qexists `1` >> pure_rewrite_tac[FUNPOW_1] >>
          conj_tac >- simp[] >> irule dft_pos_cleared_phase >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem dft_pos_plain_return_success[local]:
  dft_pos_phase C D fi bi pre x call post l r /\
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  l.dft_occ_core = DftOpen (DftDone (IntRet ret cs)) (lf::ls) nL /\
  r.dft_occ_core = DftOpen (DftDone (IntRet ret cs)) (rf::rs) nR /\
  dft_pos_frame C D fi bi pre x call post NONE lf rf /\
  dft_pos_stack C D fi bi pre x call post certs ls rs /\
  LENGTH l.dft_occ_saved = SUC (LENGTH certs) /\
  (!f fuel bb inst s. lf = DftCaller f fuel bb inst s ==>
    ?a. dft_restore inst.inst_outputs ret cs s = SOME a) ==>
  dft_pos_phase C D fi bi pre x call post
    (dft_occ_oracle_next w C l) (dft_occ_oracle_next w D r)
Proof
  strip_tac >>
  `l.dft_occ_saved = r.dft_occ_saved /\ dft_original_ready l /\ dft_original_ready r` by
    fs[dft_pos_phase_def] >>
  `dft_original_ready (dft_occ_oracle_next w C l) /\
   dft_original_ready (dft_occ_oracle_next w D r)` by
    metis_tac[dft_original_runtime_next] >>
  Cases_on `l.dft_occ_saved` >> gvs[] >> PairCases_on `h` >>
  drule dft_pos_stack_fill >> strip_tac >>
  fs[dft_pos_frame_def] >> gvs[] >>
  `dft_occ_oracle_next w C l = l with
    <|dft_occ_core := DftOpen (DftAt f 0 b
      (a with vs_inst_idx := SUC s.vs_inst_idx)) ls nL;
      dft_occ_path := h0; dft_occ_visit := h1; dft_occ_saved := t|>` by
    (irule dft_suspend_pop >> simp[]) >>
  `dft_occ_oracle_next w D r = r with
    <|dft_occ_core := DftOpen (DftAt g 0 b'
      (a with vs_inst_idx := SUC s.vs_inst_idx)) rs nR;
      dft_occ_path := h0; dft_occ_visit := h1; dft_occ_saved := t|>` by
    (irule dft_suspend_pop >> simp[]) >>
  asm_rewrite_tac[] >> simp[dft_pos_phase_def] >> qexists `certs` >>
  gvs[dft_pos_control_def] >> metis_tac[]
QED

Theorem dft_pos_plain_return_failure[local]:
  dft_pos_frame C D fi bi pre x call post NONE lf rf /\
  l.dft_occ_core = DftOpen (DftDone (IntRet ret cs)) (lf::ls) nL /\
  r.dft_occ_core = DftOpen (DftDone (IntRet ret cs)) (rf::rs) nR /\
  (!f fuel bb inst s. lf = DftCaller f fuel bb inst s ==>
    dft_restore inst.inst_outputs ret cs s = NONE) ==>
  dft_occ_oracle_next w C l = l with
    <|dft_occ_core := DftOpen (DftDone (Error "invoke: return arity mismatch")) [] nL;
      dft_occ_saved := []|> /\
  dft_occ_oracle_next w D r = r with
    <|dft_occ_core := DftOpen (DftDone (Error "invoke: return arity mismatch")) [] nR;
      dft_occ_saved := []|>
Proof
  strip_tac >> fs[dft_pos_frame_def] >> gvs[] >>
  conj_tac >> irule dft_pos_return_clear >> simp[] >>
  simp[dft_open_return_def, dft_fill_frame_def, GSYM dft_restore_def]
QED

Theorem dft_pos_done_next:
  dft_pos_phase C D fi bi pre x call post l r /\
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  l.dft_occ_core = DftOpen (DftDone result) ls nL /\
  r.dft_occ_core = DftOpen (DftDone result) rs nR ==>
  ?b. (b = 1 \/ b = 2) /\
    dft_pos_phase C D fi bi pre x call post
      (dft_occ_oracle_next w C l) (FUNPOW (dft_occ_oracle_next w D) b r)
Proof
  strip_tac >>
  `?certs. dft_pos_stack C D fi bi pre x call post certs ls rs /\
    LENGTH l.dft_occ_saved = LENGTH certs` by (fs[dft_pos_phase_def] >> metis_tac[]) >>
  Cases_on `certs`
  >- (fs[dft_pos_stack_def] >> gvs[] >>
      `dft_occ_oracle_next w C l = l with
        <|dft_occ_core := DftOpen (DftDone result) [] nL; dft_occ_saved := []|>` by
        (irule dft_pos_return_clear >> simp[] >> Cases_on `result` >>
         simp[dft_open_return_def]) >>
      `dft_occ_oracle_next w D r = r with
        <|dft_occ_core := DftOpen (DftDone result) [] nR; dft_occ_saved := []|>` by
        (irule dft_pos_return_clear >> simp[] >> Cases_on `result` >>
         simp[dft_open_return_def]) >>
      qexists `1` >> pure_rewrite_tac[FUNPOW_1] >> conj_tac >- simp[] >>
      irule dft_pos_cleared_phase >> goal_assum (drule_at Any) >> metis_tac[]) >>
  fs[dft_pos_stack_def] >> gvs[] >> Cases_on `h`
  >- suspend "plain" >>
  irule dft_pos_pending_return >> goal_assum (drule_at Any) >>
  metis_tac[dft_pos_stack_cons]
QED

Resume dft_pos_done_next[plain]:
  qexists `1` >> pure_rewrite_tac[FUNPOW_1] >> conj_tac >- simp[] >>
  Cases_on `?ret cs. result = IntRet ret cs`
  >- (pop_assum strip_assume_tac >> gvs[] >> Cases_on `l'` >>
      rename1 `DftCaller f fuel bb inst s` >>
      Cases_on `dft_restore inst.inst_outputs ret cs s`
      >- (`!f' fuel' bb' inst' s'.
             DftCaller f fuel bb inst s = DftCaller f' fuel' bb' inst' s' ==>
             dft_restore inst'.inst_outputs ret cs s' = NONE` by simp[] >>
          drule_all dft_pos_plain_return_failure >> strip_tac >>
          irule dft_pos_cleared_phase >> goal_assum (drule_at Any) >> metis_tac[]) >>
      irule dft_pos_plain_return_success >> goal_assum (drule_at Any) >>
      metis_tac[dft_open_frame_11]) >>
  `!ret cs. result <> IntRet ret cs` by metis_tac[] >>
  `dft_occ_oracle_next w C l = l with
    <|dft_occ_core := DftOpen (DftDone result) [] nL; dft_occ_saved := []|>` by
    (irule dft_pos_nonreturn_clear >> simp[]) >>
  `dft_occ_oracle_next w D r = r with
    <|dft_occ_core := DftOpen (DftDone result) [] nR; dft_occ_saved := []|>` by
    (irule dft_pos_nonreturn_clear >> simp[]) >>
  irule dft_pos_cleared_phase >> goal_assum (drule_at Any) >> metis_tac[]
QED
Finalise dft_pos_done_next
