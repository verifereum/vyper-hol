Theory dftPositionalCrossing
Ancestors
  dftPositionalStep dftPositionalPhase dftPositionalRuntime dftPositionalEdit
  dftRecursiveActivePhase dftRecursiveCallProvenance dftRecursiveCallResidual
  dftOriginalRuntime dftOriginalOrbit dftProtectedRuntime dftMixedCrossing
  dftRelationalEdit dftOccurrenceOrdinaryEdit dftOccurrenceResidual
  dftInvokeOrdinaryBoundary dftOccurrenceMachine dftOpenErase venomEffects
  dftPositionalReturn dftOccurrenceFrame
  venomExecSemantics venomState venomInst list arithmetic

Theorem dft_pos_crossing_blocks[local]:
  D = dft_pos_edit_ctx fi bi pre x call post C /\
  dft_pos_runtime_ready C fi bi pre x call post /\
  dft_pos_slot C D fi bi f g b b' ==>
  b.bb_instructions = pre ++ [x;call] ++ post /\
  b' = b with bb_instructions := pre ++ [call;x] ++ post
Proof
  simp[dft_pos_runtime_ready_def, dft_pos_slot_def] >> strip_tac >>
  gvs[dft_pos_edit_ctx_selected, dft_pos_edit_fn_selected]
QED

Theorem dft_pos_crossing_certificate:
  D = dft_pos_edit_ctx fi bi pre x call post C /\
  dft_pos_runtime_ready C fi bi pre x call post /\
  dft_pos_slot C D fi bi f g b b' /\
  dft_recursive_crossing_ready f0 b0 b pre x call post s /\
  step_inst_base x s = OK t ==>
  ?us cert. t = dft_pending_apply us s /\
    EVERY (\p. MEM (FST p) x.inst_outputs) us /\
    dft_certificate_annotation (SOME cert) = DftPending us [] /\
    dft_pos_frame C D fi bi pre x call post (SOME cert)
      (DftCaller f 0 b call (t with vs_inst_idx := SUC s.vs_inst_idx))
      (DftCaller g 0 b' call s)
Proof
  strip_tac >> drule_all dft_pos_crossing_blocks >> strip_tac >>
  drule_all dft_recursive_partner_updates >> strip_tac >>
  `?done. pre = FILTER (\i. is_pseudo i.inst_opcode) b0.bb_instructions ++ done` by
    (irule dft_original_crossing_cut >> fs[dft_recursive_crossing_ready_def] >>
     metis_tac[]) >>
  `!v. MEM v x.inst_outputs ==>
    ~MEM (Var v) call.inst_operands /\ ~MEM v call.inst_outputs` by
    metis_tac[dft_recursive_partner_disjoint] >>
  `dft_cut_pair us [] (t with vs_inst_idx := SUC s.vs_inst_idx) s` by
    metis_tac[dft_recursive_pending_cut] >>
  qexistsl [`us`, `<| dft_cert_forward := T;
    dft_cert_original_fn := f0; dft_cert_ordinary_fn := f;
    dft_cert_delayed_fn := g; dft_cert_original_bb := b0;
    dft_cert_before := b; dft_cert_after := b';
    dft_cert_pseudos := FILTER (\i. is_pseudo i.inst_opcode) b0.bb_instructions;
    dft_cert_done := done; dft_cert_todo := post;
    dft_cert_partner := x; dft_cert_call := call;
    dft_cert_start := s; dft_cert_result := t; dft_cert_updates := us |>`] >>
  simp[dft_certificate_annotation_def, dft_pos_frame_def,
    dft_pos_certificate_def, dft_certificate_saved_def, dft_recursive_payload_def] >>
  fs[dft_crossing_evidence_def, dft_recursive_crossing_ready_def,
    EVERY_MEM, APPEND_ASSOC] >>
  conj_tac >- metis_tac[] >>
  conj_tac
  >- (pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> REFL_TAC) >>
  metis_tac[]
QED

