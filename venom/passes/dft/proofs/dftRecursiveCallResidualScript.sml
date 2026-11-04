(* Algebraic saved callers. Pending lists here carry no execution provenance. *)
Theory dftRecursiveCallResidual
Ancestors
  dftOccurrenceResidual dftPendingSuspension dftOccurrenceGasEdit
  dftOpenMachine venomExecSemantics venomState venomInst list arithmetic

Datatype:
  dft_call_annotation = DftPlain | DftPending ((string # bytes32) list)
                                               ((string # bytes32) list)
End

Definition dft_recursive_payload_def:
  (dft_recursive_payload DftPlain call s t <=> s = t) /\
  (dft_recursive_payload (DftPending us vs) call s t <=>
    dft_cut_pair us vs s t /\
    EVERY (\p. ~MEM (Var (FST p)) call.inst_operands /\
                ~MEM (FST p) call.inst_outputs) us /\
    EVERY (\p. ~MEM (Var (FST p)) call.inst_operands /\
                ~MEM (FST p) call.inst_outputs) vs)
End

Definition dft_recursive_frame_def:
  dft_recursive_frame fm bm a
    (DftCaller f b bb call s) (DftCaller g c cc other t) <=>
    b = 0 /\ c = 0 /\ g = fm f /\ cc = bm bb /\ other = call /\
    call.inst_opcode = INVOKE /\
    get_instruction bb s.vs_inst_idx = SOME call /\
    get_instruction cc t.vs_inst_idx = SOME call /\
    dft_recursive_payload a call s t
End

Definition dft_recursive_frames_def:
  (dft_recursive_frames fm bm [] ls rs <=> ls = [] /\ rs = []) /\
  (dft_recursive_frames fm bm (a::anns) ls rs <=>
    ?l r lt rt. ls = l::lt /\ rs = r::rt /\
      dft_recursive_frame fm bm a l r /\
      dft_recursive_frames fm bm anns lt rt)
End

Theorem dft_recursive_frames_nil[simp]:
  dft_recursive_frames fm bm [] ls rs <=> ls = [] /\ rs = []
Proof
  simp[dft_recursive_frames_def]
QED

Theorem dft_recursive_frames_cons[simp]:
  dft_recursive_frames fm bm (a::anns) (l::lt) (r::rt) <=>
  dft_recursive_frame fm bm a l r /\ dft_recursive_frames fm bm anns lt rt
Proof
  simp[dft_recursive_frames_def]
QED

Theorem dft_recursive_frames_cons_inv:
  dft_recursive_frames fm bm (a::anns) ls rs ==>
  ?l r lt rt. ls = l::lt /\ rs = r::rt /\
    dft_recursive_frame fm bm a l r /\ dft_recursive_frames fm bm anns lt rt
Proof
  simp[dft_recursive_frames_def]
QED

Theorem dft_recursive_frames_lengths:
  !anns ls rs. dft_recursive_frames fm bm anns ls rs ==>
    LENGTH ls = LENGTH anns /\ LENGTH rs = LENGTH anns
Proof
  Induct >> simp[dft_recursive_frames_def] >> rpt strip_tac >>
  gvs[] >> first_x_assum drule >> simp[]
QED

Theorem dft_recursive_frames_nested:
  dft_recursive_frame fm bm (DftPending us1 vs1) l1 r1 /\
  dft_recursive_frame fm bm (DftPending us2 vs2) l2 r2 /\
  dft_recursive_frames fm bm anns lt rt ==>
  dft_recursive_frames fm bm (DftPending us1 vs1::DftPending us2 vs2::anns)
    (l1::l2::lt) (r1::r2::rt)
Proof
  simp[]
QED

Theorem dft_recursive_frame_plain:
  call.inst_opcode = INVOKE /\
  get_instruction bb s.vs_inst_idx = SOME call /\
  get_instruction (bm bb) s.vs_inst_idx = SOME call ==>
  dft_recursive_frame fm bm DftPlain
    (DftCaller f 0 bb call s) (DftCaller (fm f) 0 (bm bb) call s)
Proof
  simp[dft_recursive_frame_def, dft_recursive_payload_def]
QED
