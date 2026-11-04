Theory dftRecursiveFixedPhase
Ancestors
  dftRecursiveActivePhase dftRecursiveReturnPhase dftRecursiveCallProvenance
  dftRecursiveCallResidual dftOccurrenceGasEdit dftOriginalRuntime
  dftOccurrenceMachine dftOpenMachine venomExecSemantics venomState list arithmetic

Definition dft_fixed_certificate_def:
  dft_fixed_certificate q pre x call post z <=>
    z.dft_cert_forward /\ z.dft_cert_before = q /\
    z.dft_cert_after = dft_gas_edit_block q pre x call post q /\
    z.dft_cert_partner = x /\ z.dft_cert_call = call /\
    z.dft_cert_start.vs_inst_idx = LENGTH pre /\
    z.dft_cert_delayed_fn = dft_gas_edit_fn q pre x call post z.dft_cert_ordinary_fn
End

Definition dft_fixed_coordinate_def:
  (dft_fixed_coordinate q pre x call post NONE (DftCaller f fuel bb inst s) <=>
    ~(bb = q /\ s.vs_inst_idx = LENGTH pre)) /\
  (dft_fixed_coordinate q pre x call post (SOME z) frame <=>
    dft_fixed_certificate q pre x call post z)
End

Definition dft_fixed_stack_def:
  dft_fixed_stack q pre x call post certs ls rs <=>
    dft_provenanced_frames (dft_gas_edit_fn q pre x call post)
      (dft_gas_edit_block q pre x call post) certs ls rs /\
    LIST_REL (dft_fixed_coordinate q pre x call post) certs ls
End

Definition dft_fixed_control_def:
  dft_fixed_control q pre x call post ctl ctl' <=>
    (?f s. ctl = DftEnter f 0 s /\
       ctl' = DftEnter (dft_gas_edit_fn q pre x call post f) 0 s) \/
    (?f bb s. ctl = DftAt f 0 bb s /\
       ctl' = DftAt (dft_gas_edit_fn q pre x call post f) 0
         (dft_gas_edit_block q pre x call post bb) s /\
       ~(bb = q /\ s.vs_inst_idx = SUC (LENGTH pre))) \/
    (?res. ctl = DftDone res /\ ctl' = DftDone res)
End

Definition dft_fixed_phase_def:
  dft_fixed_phase q pre x call post c d <=>
    ?ctl ctl' certs ls rs nL nR.
      c.dft_occ_core = DftOpen ctl ls nL /\
      d.dft_occ_core = DftOpen ctl' rs nR /\
      dft_fixed_control q pre x call post ctl ctl' /\
      dft_fixed_stack q pre x call post certs ls rs /\
      c.dft_occ_path = d.dft_occ_path /\ c.dft_occ_visit = d.dft_occ_visit /\
      c.dft_occ_saved = d.dft_occ_saved /\
      LENGTH c.dft_occ_saved = LENGTH certs /\
      dft_original_ready c /\ dft_original_ready d
End

Theorem dft_fixed_stack_nil[simp]:
  dft_fixed_stack q pre x call post [] [] []
Proof
  simp[dft_fixed_stack_def]
QED

Theorem dft_fixed_stack_cons:
  dft_fixed_stack q pre x call post (z::certs) (l::ls) (r::rs) <=>
  dft_provenanced_frame (dft_gas_edit_fn q pre x call post)
    (dft_gas_edit_block q pre x call post) z l r /\
  dft_fixed_coordinate q pre x call post z l /\
  dft_fixed_stack q pre x call post certs ls rs
Proof
  simp[dft_fixed_stack_def] >> metis_tac[]
QED

Theorem dft_fixed_enter_root:
  c.dft_occ_core = DftOpen (DftEnter f 0 s) [] nL /\
  d.dft_occ_core = DftOpen (DftEnter (dft_gas_edit_fn q pre x call post f) 0 s) [] nR /\
  c.dft_occ_path = d.dft_occ_path /\ c.dft_occ_visit = d.dft_occ_visit /\
  c.dft_occ_saved = [] /\ d.dft_occ_saved = [] /\
  dft_original_ready c /\ dft_original_ready d ==>
  dft_fixed_phase q pre x call post c d
Proof
  strip_tac >> simp[dft_fixed_phase_def, dft_fixed_control_def]
QED

Theorem dft_fixed_forward_certificate:
  s.vs_inst_idx = LENGTH pre ==>
  dft_fixed_certificate q pre x call post
    (dft_forward_certificate f fn b q pre done x call post s t us)
Proof
  simp[dft_fixed_certificate_def, dft_forward_certificate_def]
QED

Theorem dft_fixed_enter_intro:
  c.dft_occ_core = DftOpen (DftEnter f 0 s) ls nL /\
  d.dft_occ_core = DftOpen (DftEnter (dft_gas_edit_fn q pre x call post f) 0 s) rs nR /\
  dft_fixed_stack q pre x call post certs ls rs /\
  c.dft_occ_path = d.dft_occ_path /\ c.dft_occ_visit = d.dft_occ_visit /\
  c.dft_occ_saved = d.dft_occ_saved /\ LENGTH c.dft_occ_saved = LENGTH certs /\
  dft_original_ready c /\ dft_original_ready d ==>
  dft_fixed_phase q pre x call post c d
Proof
  strip_tac >> simp[dft_fixed_phase_def] >>
  qexists `certs` >> simp[dft_fixed_control_def] >> metis_tac[]
QED

Theorem dft_fixed_at_intro:
  c.dft_occ_core = DftOpen (DftAt f 0 bb s) ls nL /\
  d.dft_occ_core = DftOpen (DftAt (dft_gas_edit_fn q pre x call post f) 0
    (dft_gas_edit_block q pre x call post bb) s) rs nR /\
  ~(bb = q /\ s.vs_inst_idx = SUC (LENGTH pre)) /\
  dft_fixed_stack q pre x call post certs ls rs /\
  c.dft_occ_path = d.dft_occ_path /\ c.dft_occ_visit = d.dft_occ_visit /\
  c.dft_occ_saved = d.dft_occ_saved /\ LENGTH c.dft_occ_saved = LENGTH certs /\
  dft_original_ready c /\ dft_original_ready d ==>
  dft_fixed_phase q pre x call post c d
Proof
  strip_tac >> simp[dft_fixed_phase_def] >>
  qexists `certs` >> simp[dft_fixed_control_def] >> metis_tac[]
QED

Theorem dft_fixed_plain_push:
  dft_fixed_stack q pre x call post certs ls rs /\
  dft_provenanced_frame (dft_gas_edit_fn q pre x call post)
    (dft_gas_edit_block q pre x call post) NONE
    (DftCaller f 0 bb inst s) fr /\
  ~(bb = q /\ s.vs_inst_idx = LENGTH pre) ==>
  dft_fixed_stack q pre x call post (NONE::certs)
    (DftCaller f 0 bb inst s::ls) (fr::rs)
Proof
  simp[dft_fixed_stack_cons, dft_fixed_coordinate_def]
QED

Theorem dft_fixed_pending_push:
  dft_fixed_stack q pre x call post certs ls rs /\
  dft_provenanced_frame (dft_gas_edit_fn q pre x call post)
    (dft_gas_edit_block q pre x call post) (SOME z) fl fr /\
  dft_fixed_certificate q pre x call post z ==>
  dft_fixed_stack q pre x call post (SOME z::certs) (fl::ls) (fr::rs)
Proof
  simp[dft_fixed_stack_cons, dft_fixed_coordinate_def]
QED

Theorem dft_fixed_plain_resume_safe:
  dft_fixed_coordinate q pre x call post NONE (DftCaller f fuel bb inst s) ==>
  ~(bb = q /\ SUC s.vs_inst_idx = SUC (LENGTH pre))
Proof
  simp[dft_fixed_coordinate_def]
QED

Theorem dft_fixed_done_reentry:
  dft_crossing_evidence z /\ dft_fixed_certificate q pre x call post z /\
  l.dft_occ_core = DftOpen (DftDone (IntRet ret cs))
    (DftCaller z.dft_cert_ordinary_fn 0 z.dft_cert_before z.dft_cert_call
      (z.dft_cert_result with vs_inst_idx := SUC z.dft_cert_start.vs_inst_idx)::ls) nL /\
  r.dft_occ_core = DftOpen (DftDone (IntRet ret cs))
    (DftCaller z.dft_cert_delayed_fn 0 z.dft_cert_after z.dft_cert_call
      z.dft_cert_start::rs) nR /\
  l.dft_occ_saved = (path,visit)::saved /\
  r.dft_occ_saved = (path,visit)::saved /\
  dft_fixed_stack q pre x call post certs ls rs /\ LENGTH saved = LENGTH certs /\
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  dft_original_ready l /\ dft_original_ready r /\
  dft_restore z.dft_cert_call.inst_outputs ret cs
    (z.dft_cert_result with vs_inst_idx := SUC z.dft_cert_start.vs_inst_idx) = SOME a /\
  dft_restore z.dft_cert_call.inst_outputs ret cs z.dft_cert_start = SOME b ==>
  dft_fixed_phase q pre x call post
    (dft_occ_oracle_next w C l) (FUNPOW (dft_occ_oracle_next w D) 2 r)
Proof
  strip_tac >>
  `dft_provenanced_frames (dft_gas_edit_fn q pre x call post)
    (dft_gas_edit_block q pre x call post) certs ls rs` by fs[dft_fixed_stack_def] >>
  drule dft_provenanced_frames_fill >> strip_tac >>
  drule_all dft_provenanced_frames_saved_empty >> strip_tac >>
  drule_all dft_certificate_done_segment >>
  disch_then (qspecl_then [`w`, `D`, `C`] strip_assume_tac) >>
  `dft_original_ready (dft_occ_oracle_next w C l)` by
    metis_tac[dft_original_runtime_next] >>
  `dft_original_ready (FUNPOW (dft_occ_oracle_next w D) 2 r)` by
    metis_tac[dft_original_runtime_iter] >>
  irule dft_fixed_at_intro >> simp[] >>
  fs[dft_fixed_certificate_def] >> simp[] >>
  qexists `certs` >> simp[]
QED

Theorem dft_fixed_crossing_enter:
  dft_recursive_crossing_ready f b q pre x call post s /\
  c.dft_occ_core = DftOpen (DftAt fn 0 q s) ls nL /\
  d.dft_occ_core = DftOpen (DftAt (dft_gas_edit_fn q pre x call post fn) 0
    (dft_gas_edit_block q pre x call post q) s) rs nR /\
  dft_fixed_stack q pre x call post certs ls rs /\
  c.dft_occ_path = d.dft_occ_path /\ c.dft_occ_visit = d.dft_occ_visit /\
  c.dft_occ_saved = d.dft_occ_saved /\ LENGTH c.dft_occ_saved = LENGTH certs /\
  dft_original_ready c /\ dft_original_ready d /\
  dft_original_context Corig C /\
  dft_original_context Dorig (dft_gas_edit_ctx q pre x call post C) /\
  step_inst_base x s = OK t /\ decode_invoke call = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops (t with vs_inst_idx := SUC s.vs_inst_idx) = SOME args /\
  setup_callee callee args (t with vs_inst_idx := SUC s.vs_inst_idx) = SOME cs ==>
  dft_fixed_phase q pre x call post (FUNPOW (dft_occ_oracle_next w C) 2 c)
    (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x call post C) d)
Proof
  strip_tac >>
  `dft_recursive_pre_phase f b q pre x call post certs fn s c d` by
    (simp[dft_recursive_pre_phase_def] >>
     fs[dft_fixed_stack_def] >> metis_tac[]) >>
  drule_all dft_recursive_crossing_enter_exact >>
  disch_then (qspec_then `w` strip_assume_tac) >>
  `s.vs_inst_idx = LENGTH pre` by fs[dft_recursive_crossing_ready_def] >>
  `dft_original_ready (FUNPOW (dft_occ_oracle_next w C) 2 c)` by
    metis_tac[dft_original_runtime_iter] >>
  `dft_original_ready (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x call post C) d)` by
    metis_tac[dft_original_runtime_next] >>
  `dft_fixed_certificate q pre x call post cert` by
    simp[dft_fixed_forward_certificate] >>
  `dft_fixed_stack q pre x call post (SOME cert::certs)
    (DftCaller fn 0 q call (t with vs_inst_idx := SUC s.vs_inst_idx)::ls)
    (DftCaller (dft_gas_edit_fn q pre x call post fn) 0
      (dft_gas_edit_block q pre x call post q) call s::rs)` by
    (irule dft_fixed_pending_push >> simp[] >>
     fs[dft_recursive_enter_phase_def] >>
     first_x_assum (qspecl_then [`ls`, `rs`, `nL`, `nR`] mp_tac) >>
     simp[] >> strip_tac >> gvs[] >> fs[]) >>
  irule dft_fixed_enter_intro >> simp[] >>
  first_x_assum (qspecl_then [`ls`, `rs`, `nL`, `nR`] mp_tac) >>
  simp[] >> strip_tac >> simp[] >>
  qexists `SOME cert::certs` >> simp[] >> gvs[]
QED
