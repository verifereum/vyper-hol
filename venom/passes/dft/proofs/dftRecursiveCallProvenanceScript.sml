Theory dftRecursiveCallProvenance
Ancestors
  dftRecursiveCallResidual dftRecursiveCallBoundary dftRecursiveCallReturn
  dftMixedCrossing dftProtectedRuntime dftOccurrenceResidual
  dftOpenMachine venomExecSemantics venomState venomInst finite_map list

(* The ordinary-first schedule and its adjacent edit are stored explicitly.
   forward=T means that the left caller has already executed the partner. *)
Datatype:
  dft_crossing_certificate = <|
    dft_cert_forward : bool;
    dft_cert_original_fn : ir_function;
    dft_cert_ordinary_fn : ir_function;
    dft_cert_delayed_fn : ir_function;
    dft_cert_original_bb : basic_block;
    dft_cert_before : basic_block;
    dft_cert_after : basic_block;
    dft_cert_pseudos : instruction list;
    dft_cert_done : instruction list;
    dft_cert_todo : instruction list;
    dft_cert_partner : instruction;
    dft_cert_call : instruction;
    dft_cert_start : venom_state;
    dft_cert_result : venom_state;
    dft_cert_updates : (string # bytes32) list
  |>
End

Definition dft_certificate_annotation_def:
  (dft_certificate_annotation NONE = DftPlain) /\
  (dft_certificate_annotation (SOME c) =
    if c.dft_cert_forward then DftPending c.dft_cert_updates []
    else DftPending [] c.dft_cert_updates)
End

Definition dft_crossing_evidence_def:
  dft_crossing_evidence c <=>
    dft_original_cut c.dft_cert_original_fn c.dft_cert_original_bb
      c.dft_cert_before c.dft_cert_start /\
    c.dft_cert_before.bb_instructions =
      c.dft_cert_pseudos ++ c.dft_cert_done ++
      c.dft_cert_partner::c.dft_cert_call::c.dft_cert_todo /\
    c.dft_cert_after = c.dft_cert_before with bb_instructions :=
      c.dft_cert_pseudos ++ c.dft_cert_done ++
      c.dft_cert_call::c.dft_cert_partner::c.dft_cert_todo /\
    c.dft_cert_pseudos = FILTER (\i. is_pseudo i.inst_opcode)
      c.dft_cert_original_bb.bb_instructions /\
    c.dft_cert_start.vs_inst_idx =
      LENGTH (c.dft_cert_pseudos ++ c.dft_cert_done) /\
    (!l. MEM (Label l) c.dft_cert_partner.inst_operands ==>
         l IN FDOM c.dft_cert_start.vs_labels) /\
    ~dft_must_order c.dft_cert_partner c.dft_cert_call /\
    c.dft_cert_call.inst_opcode = INVOKE /\
    ~is_pseudo c.dft_cert_partner.inst_opcode /\
    ~is_terminator c.dft_cert_partner.inst_opcode /\
    c.dft_cert_partner.inst_opcode <> ALLOCA /\
    c.dft_cert_partner.inst_opcode <> GAS /\
    step_inst_base c.dft_cert_partner c.dft_cert_start = OK c.dft_cert_result /\
    c.dft_cert_result = dft_pending_apply c.dft_cert_updates c.dft_cert_start /\
    EVERY (\p. MEM (FST p) c.dft_cert_partner.inst_outputs) c.dft_cert_updates
End

Definition dft_certificate_saved_def:
  dft_certificate_saved c l r <=>
    let ordinary = DftCaller c.dft_cert_ordinary_fn 0 c.dft_cert_before
          c.dft_cert_call (c.dft_cert_result with vs_inst_idx :=
            SUC c.dft_cert_start.vs_inst_idx) in
    let delayed = DftCaller c.dft_cert_delayed_fn 0 c.dft_cert_after
          c.dft_cert_call c.dft_cert_start in
    if c.dft_cert_forward then l = ordinary /\ r = delayed
    else l = delayed /\ r = ordinary
End

Definition dft_provenanced_frame_def:
  (dft_provenanced_frame fm bm NONE l r <=>
    dft_recursive_frame fm bm DftPlain l r) /\
  (dft_provenanced_frame fm bm (SOME c) l r <=>
    dft_crossing_evidence c /\ dft_certificate_saved c l r /\
    dft_recursive_frame fm bm (dft_certificate_annotation (SOME c)) l r)
End

Definition dft_provenanced_frames_def:
  (dft_provenanced_frames fm bm [] ls rs <=> ls = [] /\ rs = []) /\
  (dft_provenanced_frames fm bm (c::cs) ls rs <=>
    ?l r lt rt. ls = l::lt /\ rs = r::rt /\
      dft_provenanced_frame fm bm c l r /\
      dft_provenanced_frames fm bm cs lt rt)
End

Theorem dft_provenanced_pending:
  dft_crossing_evidence c /\ dft_certificate_saved c l r /\
  dft_recursive_frame fm bm (dft_certificate_annotation (SOME c)) l r ==>
  dft_provenanced_frame fm bm (SOME c) l r
Proof
  simp[dft_provenanced_frame_def]
QED

Theorem dft_provenanced_frame_projection:
  dft_provenanced_frame fm bm c l r ==>
  dft_recursive_frame fm bm (dft_certificate_annotation c) l r
Proof
  Cases_on `c` >> simp[dft_provenanced_frame_def, dft_certificate_annotation_def]
QED

Theorem dft_provenanced_frames_nil[simp]:
  dft_provenanced_frames fm bm [] ls rs <=> ls = [] /\ rs = []
Proof
  simp[dft_provenanced_frames_def]
QED

Theorem dft_provenanced_frames_cons[simp]:
  dft_provenanced_frames fm bm (c::cs) (l::lt) (r::rt) <=>
  dft_provenanced_frame fm bm c l r /\ dft_provenanced_frames fm bm cs lt rt
Proof
  simp[dft_provenanced_frames_def]
QED

Theorem dft_provenanced_frames_cons_inv:
  dft_provenanced_frames fm bm (c::cs) ls rs ==>
  ?l r lt rt. ls = l::lt /\ rs = r::rt /\
    dft_provenanced_frame fm bm c l r /\ dft_provenanced_frames fm bm cs lt rt
Proof
  simp[dft_provenanced_frames_def]
QED

Theorem dft_provenanced_frames_projection:
  !cs ls rs. dft_provenanced_frames fm bm cs ls rs ==>
  dft_recursive_frames fm bm (MAP dft_certificate_annotation cs) ls rs
Proof
  Induct >> simp[dft_provenanced_frames_def] >> rpt strip_tac >> gvs[] >>
  metis_tac[dft_provenanced_frame_projection]
QED

Theorem dft_provenanced_frames_nested:
  dft_provenanced_frame fm bm (SOME c1) l1 r1 /\
  dft_provenanced_frame fm bm (SOME c2) l2 r2 /\
  dft_provenanced_frames fm bm cs lt rt ==>
  dft_provenanced_frames fm bm (SOME c1::SOME c2::cs)
    (l1::l2::lt) (r1::r2::rt)
Proof
  simp[]
QED

(* This is the local constructor obligation, with no callee-run premise.
   The saved-shape and algebraic frame premises remain explicit: a local
   crossing consumer must discharge them from its actual push states. *)
Theorem dft_provenanced_pending_from_step:
  dft_original_cut c.dft_cert_original_fn c.dft_cert_original_bb
    c.dft_cert_before c.dft_cert_start /\
  c.dft_cert_before.bb_instructions = c.dft_cert_pseudos ++ c.dft_cert_done ++
    c.dft_cert_partner::c.dft_cert_call::c.dft_cert_todo /\
  c.dft_cert_after = c.dft_cert_before with bb_instructions :=
    c.dft_cert_pseudos ++ c.dft_cert_done ++
    c.dft_cert_call::c.dft_cert_partner::c.dft_cert_todo /\
  c.dft_cert_pseudos = FILTER (\i. is_pseudo i.inst_opcode)
    c.dft_cert_original_bb.bb_instructions /\
  c.dft_cert_start.vs_inst_idx = LENGTH (c.dft_cert_pseudos ++ c.dft_cert_done) /\
  (!lab. MEM (Label lab) c.dft_cert_partner.inst_operands ==>
    lab IN FDOM c.dft_cert_start.vs_labels) /\
  ~dft_must_order c.dft_cert_partner c.dft_cert_call /\
  c.dft_cert_call.inst_opcode = INVOKE /\
  ~is_pseudo c.dft_cert_partner.inst_opcode /\
  ~is_terminator c.dft_cert_partner.inst_opcode /\
  c.dft_cert_partner.inst_opcode <> ALLOCA /\
  c.dft_cert_partner.inst_opcode <> GAS /\
  step_inst_base c.dft_cert_partner c.dft_cert_start = OK c.dft_cert_result /\
  c.dft_cert_result = dft_pending_apply c.dft_cert_updates c.dft_cert_start /\
  EVERY (\p. MEM (FST p) c.dft_cert_partner.inst_outputs) c.dft_cert_updates /\
  dft_certificate_saved c l r /\
  dft_recursive_frame fm bm (dft_certificate_annotation (SOME c)) l r ==>
  dft_provenanced_frame fm bm (SOME c) l r
Proof
  simp[dft_provenanced_frame_def, dft_crossing_evidence_def]
QED
