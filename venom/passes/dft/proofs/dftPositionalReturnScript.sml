Theory dftPositionalReturn
Ancestors
  dftPositionalPhase dftRecursiveReturnPhase dftRecursiveCallProvenance
  dftOriginalRuntime dftOccurrenceMachine dftOpenMachine dftOpenErase
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
