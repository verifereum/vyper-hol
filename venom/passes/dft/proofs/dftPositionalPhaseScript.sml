Theory dftPositionalPhase
Ancestors
  dftPositionalRuntime dftPositionalEdit dftRelationalEdit
  dftRecursiveCallProvenance dftRecursiveCallResidual dftOriginalRuntime
  dftOccurrenceMachine dftOpenMachine venomExecSemantics venomInst list

(* Explicit occurrence witnesses; block equality is not a position test. *)
Definition dft_pos_slot_def:
  dft_pos_slot C D j k f g b b' <=>
    j < LENGTH C.ctx_functions /\
    f = EL j C.ctx_functions /\ g = EL j D.ctx_functions /\
    k < LENGTH f.fn_blocks /\ b = EL k f.fn_blocks /\ b' = EL k g.fn_blocks
End

Definition dft_pos_certificate_def:
  dft_pos_certificate C D fi bi pre x call post z <=>
    z.dft_cert_forward /\
    dft_pos_slot C D fi bi z.dft_cert_ordinary_fn z.dft_cert_delayed_fn
      z.dft_cert_before z.dft_cert_after /\
    z.dft_cert_before.bb_instructions = pre ++ [x;call] ++ post /\
    z.dft_cert_after.bb_instructions = pre ++ [call;x] ++ post /\
    z.dft_cert_partner = x /\ z.dft_cert_call = call /\
    z.dft_cert_start.vs_inst_idx = LENGTH pre
End

Definition dft_pos_frame_def:
  dft_pos_frame C D fi bi pre x call post z l r <=>
    case z of
      NONE =>
        dft_rel_frame (dft_pos_functions C D) (dft_pos_blocks C D) l r /\
        (?f g b b' inst s j k.
          l = DftCaller f 0 b inst s /\ r = DftCaller g 0 b' inst s /\
          dft_pos_slot C D j k f g b b' /\
          ~(j = fi /\ k = bi /\ s.vs_inst_idx = LENGTH pre) /\
          inst.inst_opcode = INVOKE /\
          get_instruction b s.vs_inst_idx = SOME inst /\
          get_instruction b' s.vs_inst_idx = SOME inst)
    | SOME cert =>
        dft_pos_certificate C D fi bi pre x call post cert /\
        dft_crossing_evidence cert /\ dft_certificate_saved cert l r /\
        dft_recursive_payload (dft_certificate_annotation (SOME cert)) call
          (case l of DftCaller f fuel b inst s => s)
          (case r of DftCaller f fuel b inst s => s)
End

Definition dft_pos_stack_def:
  (dft_pos_stack C D fi bi pre x call post [] ls rs <=> ls = [] /\ rs = []) /\
  (dft_pos_stack C D fi bi pre x call post (z::zs) ls rs <=>
    ?l r lt rt. ls = l::lt /\ rs = r::rt /\
      dft_pos_frame C D fi bi pre x call post z l r /\
      dft_pos_stack C D fi bi pre x call post zs lt rt)
End

Definition dft_pos_control_def:
  dft_pos_control C D fi bi pre ctl ctl' <=>
    (?f g s. ctl = DftEnter f 0 s /\ ctl' = DftEnter g 0 s /\
      dft_pos_functions C D f g) \/
    (?f g b b' s j k. ctl = DftAt f 0 b s /\ ctl' = DftAt g 0 b' s /\
      dft_pos_slot C D j k f g b b' /\
      ~(j = fi /\ k = bi /\ s.vs_inst_idx = SUC (LENGTH pre))) \/
    (?r. ctl = DftDone r /\ ctl' = DftDone r)
End

Definition dft_pos_phase_def:
  dft_pos_phase C D fi bi pre x call post c d <=>
    ?ctl ctl' certs ls rs nL nR.
      c.dft_occ_core = DftOpen ctl ls nL /\
      d.dft_occ_core = DftOpen ctl' rs nR /\
      dft_pos_control C D fi bi pre ctl ctl' /\
      dft_pos_stack C D fi bi pre x call post certs ls rs /\
      c.dft_occ_path = d.dft_occ_path /\ c.dft_occ_visit = d.dft_occ_visit /\
      c.dft_occ_saved = d.dft_occ_saved /\ LENGTH c.dft_occ_saved = LENGTH certs /\
      dft_original_ready c /\ dft_original_ready d
End

Theorem dft_pos_phase_root:
  dft_pos_functions C D f g /\
  c.dft_occ_core = DftOpen (DftEnter f 0 s) [] nL /\
  d.dft_occ_core = DftOpen (DftEnter g 0 s) [] nR /\
  c.dft_occ_path = d.dft_occ_path /\ c.dft_occ_visit = d.dft_occ_visit /\
  c.dft_occ_saved = [] /\ d.dft_occ_saved = [] /\
  dft_original_ready c /\ dft_original_ready d ==>
  dft_pos_phase C D fi bi pre x call post c d
Proof
  strip_tac >> simp[dft_pos_phase_def, dft_pos_stack_def, dft_pos_control_def] >>
  metis_tac[]
QED

Theorem dft_pos_plain_frame_projection:
  dft_pos_frame C D fi bi pre x call post NONE l r ==>
  dft_rel_frame (dft_pos_functions C D) (dft_pos_blocks C D) l r
Proof simp[dft_pos_frame_def]
QED

Theorem dft_pos_plain_frame:
  dft_pos_slot C D j k f g b b' /\
  ~(j = fi /\ k = bi /\ s.vs_inst_idx = LENGTH pre) /\
  inst.inst_opcode = INVOKE /\
  get_instruction b s.vs_inst_idx = SOME inst /\
  get_instruction b' s.vs_inst_idx = SOME inst ==>
  dft_pos_frame C D fi bi pre x call post NONE
    (DftCaller f 0 b inst s) (DftCaller g 0 b' inst s)
Proof
  simp[dft_pos_frame_def, dft_rel_frame_def, dft_pos_functions_def,
    dft_pos_blocks_def, dft_pos_slot_def] >> metis_tac[]
QED

Theorem dft_pos_phase_isolation:
  fi < LENGTH C.ctx_functions /\ bi < LENGTH (EL fi C.ctx_functions).fn_blocks /\
  j < LENGTH C.ctx_functions /\ k < LENGTH (EL j C.ctx_functions).fn_blocks /\
  (j <> fi \/ k <> bi) ==>
  EL k (EL j (dft_pos_edit_ctx fi bi pre x call post C).ctx_functions).fn_blocks =
  EL k (EL j C.ctx_functions).fn_blocks
Proof
  strip_tac >> Cases_on `j = fi` >> gvs[] >>
  simp[dft_pos_edit_ctx_selected, dft_pos_edit_fn_other, dft_pos_edit_ctx_other]
QED
