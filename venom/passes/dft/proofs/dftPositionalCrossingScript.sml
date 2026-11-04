Theory dftPositionalCrossing
Ancestors
  dftPositionalStep dftPositionalPhase dftPositionalRuntime dftPositionalEdit
  dftRecursiveActivePhase dftRecursiveCallProvenance dftRecursiveCallResidual
  dftOriginalRuntime dftOriginalOrbit dftProtectedRuntime dftMixedCrossing
  dftRelationalEdit dftOccurrenceOrdinaryEdit dftOccurrenceResidual
  dftInvokeOrdinaryBoundary dftOccurrenceMachine dftOpenErase venomEffects
  dftPositionalReturn dftOccurrenceFrame dftRecursiveFixedSegment
  dftOccurrenceReplay dftOpenMachine
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

Theorem dft_pos_phase_enter:
  c.dft_occ_core = DftOpen (DftEnter f 0 s) ls nL /\
  d.dft_occ_core = DftOpen (DftEnter g 0 s) rs nR /\
  dft_pos_functions C D f g /\
  dft_pos_stack C D fi bi pre x call post certs ls rs /\
  c.dft_occ_path = d.dft_occ_path /\ c.dft_occ_visit = d.dft_occ_visit /\
  c.dft_occ_saved = d.dft_occ_saved /\ LENGTH c.dft_occ_saved = LENGTH certs /\
  dft_original_ready c /\ dft_original_ready d ==>
  dft_pos_phase C D fi bi pre x call post c d
Proof
  strip_tac >> simp[dft_pos_phase_def] >>
  qexists_tac `certs` >>
  simp[dft_pos_control_def] >> metis_tac[]
QED

Theorem dft_pos_decode_support[local]:
  decode_invoke call = SOME (nm,ops) /\
  EVERY (\p. ~MEM (Var (FST p)) call.inst_operands) us ==>
  EVERY (\p. ~MEM (Var (FST p)) ops) us
Proof
  simp[decode_invoke_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  fs[EVERY_MEM] >> metis_tac[MEM]
QED

Theorem dft_pos_crossing_push_fields[local]:
  dft_cut_pair us [] sL sR /\
  EVERY (\p. ~MEM (Var (FST p)) ops) us /\
  eval_operands ops sL = SOME args /\
  setup_callee calleeL args sL = SOME cs /\
  setup_callee calleeR args sR = SOME cs /\
  l.dft_occ_core = DftOpen (DftAt f 0 b sL) ls nL /\
  r.dft_occ_core = DftOpen (DftAt g 0 b' sR) rs nR /\
  get_instruction b sL.vs_inst_idx = SOME call /\
  get_instruction b' sR.vs_inst_idx = SOME call /\
  call.inst_opcode = INVOKE /\ decode_invoke call = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME calleeL /\
  lookup_function nm D.ctx_functions = SOME calleeR /\
  l.dft_occ_path = path /\ r.dft_occ_path = path /\
  l.dft_occ_visit = visit /\ r.dft_occ_visit = visit ==>
  (dft_occ_oracle_next w C l).dft_occ_core =
    DftOpen (DftEnter calleeL 0 cs)
      (DftCaller f 0 b call sL :: MAP (dft_fill_frame 0) ls) nL /\
  (dft_occ_oracle_next w D r).dft_occ_core =
    DftOpen (DftEnter calleeR 0 cs)
      (DftCaller g 0 b' call sR :: MAP (dft_fill_frame 0) rs) nR /\
  dft_occ_count (dft_occ_oracle_next w C l) = nL /\
  dft_occ_count (dft_occ_oracle_next w D r) = nR /\
  (dft_occ_oracle_next w C l).dft_occ_path = path ++ [(visit,call.inst_id)] /\
  (dft_occ_oracle_next w D r).dft_occ_path = path ++ [(visit,call.inst_id)] /\
  (dft_occ_oracle_next w C l).dft_occ_visit = 0 /\
  (dft_occ_oracle_next w D r).dft_occ_visit = 0 /\
  (dft_occ_oracle_next w C l).dft_occ_saved = (path,visit)::l.dft_occ_saved /\
  (dft_occ_oracle_next w D r).dft_occ_saved = (path,visit)::r.dft_occ_saved /\
  (nL = nR ==> dft_occ_count (dft_occ_oracle_next w C l) =
    dft_occ_count (dft_occ_oracle_next w D r))
Proof
  strip_tac >> irule dft_pending_two_context_push_fields >> simp[] >>
  qexists_tac `us` >> simp[]
QED

Theorem dft_pos_crossing_enter:
  D = dft_pos_edit_ctx fi bi pre x call post C /\
  dft_pos_runtime_ready C fi bi pre x call post /\
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  dft_pos_phase C D fi bi pre x call post l r /\
  dft_pos_slot C D fi bi f g b b' /\
  l.dft_occ_core = DftOpen (DftAt f 0 b s) ls nL /\
  r.dft_occ_core = DftOpen (DftAt g 0 b' s) rs nR /\
  dft_recursive_crossing_ready f0 b0 b pre x call post s /\
  decode_invoke call = SOME (nm,ops) /\
  lookup_function nm D.ctx_functions = SOME calleeR /\
  eval_operands ops s = SOME args /\
  setup_callee calleeR args s = SOME cs ==>
  dft_pos_phase C D fi bi pre x call post
    (FUNPOW (dft_occ_oracle_next w C) 2 l) (dft_occ_oracle_next w D r) /\
  dft_occ_count (FUNPOW (dft_occ_oracle_next w C) 2 l) = nL /\
  dft_occ_count (dft_occ_oracle_next w D r) = nR /\
  (?calleeL cert certs t.
    step_inst_base x s = OK t /\
    dft_pos_functions C D calleeL calleeR /\
    dft_pos_frame C D fi bi pre x call post (SOME cert)
      (DftCaller f 0 b call
        (t with vs_inst_idx := SUC s.vs_inst_idx))
      (DftCaller g 0 b' call s) /\
    dft_pos_stack C D fi bi pre x call post certs ls rs /\
    (FUNPOW (dft_occ_oracle_next w C) 2 l).dft_occ_core =
      DftOpen (DftEnter calleeL 0 cs)
        (DftCaller f 0 b call
          (t with vs_inst_idx := SUC s.vs_inst_idx)::ls) nL /\
    (dft_occ_oracle_next w D r).dft_occ_core =
      DftOpen (DftEnter calleeR 0 cs) (DftCaller g 0 b' call s::rs) nR) /\
  (FUNPOW (dft_occ_oracle_next w C) 2 l).dft_occ_path =
    l.dft_occ_path ++ [(l.dft_occ_visit,call.inst_id)] /\
  (dft_occ_oracle_next w D r).dft_occ_path =
    l.dft_occ_path ++ [(l.dft_occ_visit,call.inst_id)] /\
  (FUNPOW (dft_occ_oracle_next w C) 2 l).dft_occ_visit = 0 /\
  (dft_occ_oracle_next w D r).dft_occ_visit = 0 /\
  (FUNPOW (dft_occ_oracle_next w C) 2 l).dft_occ_saved =
    (l.dft_occ_path,l.dft_occ_visit)::l.dft_occ_saved /\
  (dft_occ_oracle_next w D r).dft_occ_saved =
    (l.dft_occ_path,l.dft_occ_visit)::r.dft_occ_saved /\
  (!i addr. dft_occ_event i addr l <=>
     i = x /\ addr = l.dft_occ_path ++ [(l.dft_occ_visit,x.inst_id)]) /\
  (!i addr. dft_occ_event i addr (dft_occ_oracle_next w C l) <=>
     i = call /\ addr = l.dft_occ_path ++ [(l.dft_occ_visit,call.inst_id)]) /\
  (!i addr. dft_occ_event i addr r <=>
     i = call /\ addr = r.dft_occ_path ++ [(r.dft_occ_visit,call.inst_id)])
Proof
  strip_tac >>
  drule dft_recursive_crossing_partner_success >> strip_tac >>
  drule_all dft_pos_crossing_certificate >> strip_tac >>
  drule_all dft_pos_crossing_blocks >> strip_tac >>
  `?certs. dft_pos_stack C D fi bi pre x call post certs ls rs /\
    LENGTH l.dft_occ_saved = LENGTH certs /\
    l.dft_occ_path = r.dft_occ_path /\ l.dft_occ_visit = r.dft_occ_visit /\
    l.dft_occ_saved = r.dft_occ_saved` by
    (fs[dft_pos_phase_def] >> metis_tac[]) >>
  drule dft_pos_stack_fill >> strip_tac >>
  `?calleeL. lookup_function nm C.ctx_functions = SOME calleeL /\
     dft_pos_functions C D calleeL calleeR` by
    (`OPTREL (dft_pos_functions C D)
       (lookup_function nm C.ctx_functions) (lookup_function nm D.ctx_functions)` by
       metis_tac[dft_pos_edit_function_lookup] >>
     qpat_x_assum `OPTREL _ _ _` mp_tac >>
     simp[optionTheory.OPTREL_def] >> metis_tac[]) >>
  `dft_cut_pair us [] (t with vs_inst_idx := SUC s.vs_inst_idx) s` by
    metis_tac[dft_recursive_pending_cut] >>
  `EVERY (\p. ~MEM (Var (FST p)) ops) us` by
    (irule dft_pos_decode_support >> qexists_tac `call` >> simp[] >>
     drule dft_recursive_partner_disjoint >> strip_tac >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  `setup_callee calleeL args (t with vs_inst_idx := SUC s.vs_inst_idx) = SOME cs` by
    (`setup_callee calleeL args s = SOME cs` by
       metis_tac[dft_pos_edit_setup] >>
     drule dft_cut_pair_setup_callee >> metis_tac[]) >>
  `eval_operands ops (t with vs_inst_idx := SUC s.vs_inst_idx) = SOME args` by
    (`eval_operands ops (t with vs_inst_idx := SUC s.vs_inst_idx) =
       eval_operands ops s` by
       (irule dft_cut_pair_eval_operands >> qexistsl_tac [`us`, `[]`] >> simp[]) >>
     simp[]) >>
  suspend "ordinary"
QED

Resume dft_pos_crossing_enter[ordinary]:
  drule dft_recursive_crossing_positions >> strip_tac >>
  `x.inst_opcode <> INVOKE /\ x.inst_opcode <> GAS /\
   ~is_terminator x.inst_opcode /\ call.inst_opcode = INVOKE` by
    (fs[dft_recursive_crossing_ready_def] >>
     drule_all dft_invoke_inversion_disjoint >>
     Cases_on `x.inst_opcode = INVOKE` >>
     simp[venomEffectsTheory.read_effects_def,
          venomEffectsTheory.empty_effects_def, venomEffectsTheory.all_effects_def]) >>
  drule_all dft_pos_stack_saved_empty >> strip_tac >>
  `dft_occ_oracle_next w C l = l with
    <|dft_occ_core := DftOpen (DftAt f 0 b
       (t with vs_inst_idx := SUC s.vs_inst_idx)) ls nL;
      dft_occ_saved := l.dft_occ_saved|>` by
    (drule_all dft_occ_ordinary_next >>
     disch_then (qspecl_then [`w`, `C`] mp_tac) >>
     Cases_on `ls` >> gvs[] >> simp[dft_occ_config_component_equality]) >>
  qmatch_asmsub_abbrev_tac `dft_occ_oracle_next w C l = mid` >>
  `mid.dft_occ_core = DftOpen (DftAt f 0 b
      (t with vs_inst_idx := SUC s.vs_inst_idx)) ls nL /\
    mid.dft_occ_path = l.dft_occ_path /\ mid.dft_occ_visit = l.dft_occ_visit /\
    mid.dft_occ_saved = l.dft_occ_saved` by simp[Abbr `mid`] >>
  `get_instruction b' s.vs_inst_idx = SOME call` by
    (fs[dft_recursive_crossing_ready_def] >>
     simp[get_instruction_def, EL_APPEND_EQN]) >>
  suspend "push"
QED

Resume dft_pos_crossing_enter[push]:
  `dft_original_ready (dft_occ_oracle_next w C mid) /\
   dft_original_ready (dft_occ_oracle_next w D r)` by
    (fs[dft_pos_phase_def] >> metis_tac[dft_original_runtime_next]) >>
  qpat_x_assum `dft_recursive_crossing_ready _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `dft_pos_runtime_ready _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `dft_pos_phase _ _ _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `dft_pos_slot _ _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `b' = _` kall_tac >>
  qpat_x_assum `b.bb_instructions = _` kall_tac >>
  qpat_x_assum `t = _` kall_tac >>
  `(dft_occ_oracle_next w C mid).dft_occ_core =
    DftOpen (DftEnter calleeL 0 cs)
      (DftCaller f 0 b call (t with vs_inst_idx := SUC s.vs_inst_idx) ::
        MAP (dft_fill_frame 0) ls) nL /\
   (dft_occ_oracle_next w D r).dft_occ_core =
    DftOpen (DftEnter calleeR 0 cs)
      (DftCaller g 0 b' call s :: MAP (dft_fill_frame 0) rs) nR /\
   dft_occ_count (dft_occ_oracle_next w C mid) = nL /\
   dft_occ_count (dft_occ_oracle_next w D r) = nR /\
   (dft_occ_oracle_next w C mid).dft_occ_path = l.dft_occ_path ++ [(l.dft_occ_visit,call.inst_id)] /\
   (dft_occ_oracle_next w D r).dft_occ_path = l.dft_occ_path ++ [(l.dft_occ_visit,call.inst_id)] /\
   (dft_occ_oracle_next w C mid).dft_occ_visit = 0 /\
   (dft_occ_oracle_next w D r).dft_occ_visit = 0 /\
   (dft_occ_oracle_next w C mid).dft_occ_saved = (l.dft_occ_path,l.dft_occ_visit)::mid.dft_occ_saved /\
   (dft_occ_oracle_next w D r).dft_occ_saved = (l.dft_occ_path,l.dft_occ_visit)::r.dft_occ_saved /\
   (nL = nR ==> dft_occ_count (dft_occ_oracle_next w C mid) =
     dft_occ_count (dft_occ_oracle_next w D r))` by
    (irule dft_pos_crossing_push_fields >> simp[] >>
     qexists_tac `us` >> simp[] >> metis_tac[]) >>
  suspend "assemble"
QED

Resume dft_pos_crossing_enter[assemble]:
  qpat_x_assum `D = _` kall_tac >>
  simp[FUNPOW_2] >> conj_tac
  >- (irule dft_pos_phase_enter >> simp[] >>
      qexists_tac `SOME cert::certs` >> simp[dft_pos_stack_def] >> metis_tac[]) >>
  simp[dft_occ_event_def] >> metis_tac[]
QED
Finalise dft_pos_crossing_enter

Theorem dft_pos_crossing_mid[local]:
  dft_recursive_crossing_ready f0 b0 b pre x call post s /\
  l.dft_occ_core = DftOpen (DftAt f 0 b s) ls n /\
  dft_pos_stack C D fi bi pre x call post certs ls rs /\
  LENGTH l.dft_occ_saved = LENGTH certs /\ step_inst_base x s = OK t ==>
  dft_occ_oracle_next w C l = l with
    <|dft_occ_core := DftOpen
       (DftAt f 0 b (t with vs_inst_idx := SUC s.vs_inst_idx)) ls n;
      dft_occ_saved := l.dft_occ_saved|>
Proof
  strip_tac >> drule dft_recursive_crossing_positions >> strip_tac >>
  drule dft_pos_stack_fill >> strip_tac >>
  drule_all dft_pos_stack_saved_empty >> strip_tac >>
  `x.inst_opcode <> INVOKE /\ x.inst_opcode <> GAS /\
   ~is_terminator x.inst_opcode` by
    (fs[dft_recursive_crossing_ready_def] >>
     drule_all dft_invoke_inversion_disjoint >>
     Cases_on `x.inst_opcode = INVOKE` >>
     simp[venomEffectsTheory.read_effects_def,
          venomEffectsTheory.empty_effects_def, venomEffectsTheory.all_effects_def]) >>
  drule_all dft_occ_ordinary_next >>
  disch_then (qspecl_then [`w`, `C`] mp_tac) >>
  Cases_on `ls` >> gvs[] >> simp[dft_occ_config_component_equality]
QED

Theorem dft_pos_invoke_failed_next[local]:
  c.dft_occ_core = DftOpen (DftAt f 0 b s) ls n /\
  get_instruction b s.vs_inst_idx = SOME call /\ call.inst_opcode = INVOKE /\
  dft_open_invoke C f 1 b call s (MAP (dft_fill_frame 1) ls) n =
    DftOpen (DftDone res) [] n ==>
  dft_occ_oracle_next w C c = c with
    <|dft_occ_core := DftOpen (DftDone res) [] n; dft_occ_saved := []|>
Proof
  strip_tac >>
  simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
       dft_fill_def, dft_fill_control_def, dft_open_next_def,
       dft_erase_def, dft_occ_update_def]
QED

Theorem dft_pos_crossing_failed[local]:
  D = dft_pos_edit_ctx fi bi pre x call post C /\
  dft_pos_runtime_ready C fi bi pre x call post /\
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  dft_pos_phase C D fi bi pre x call post l r /\
  dft_pos_slot C D fi bi f g b b' /\
  l.dft_occ_core = DftOpen (DftAt f 0 b s) ls nL /\
  r.dft_occ_core = DftOpen (DftAt g 0 b' s) rs nR /\
  dft_recursive_crossing_ready f0 b0 b pre x call post s /\
  step_inst_base x s = OK t /\
  dft_open_invoke C f 1 b call (t with vs_inst_idx := SUC s.vs_inst_idx)
    (MAP (dft_fill_frame 1) ls) nL = DftOpen (DftDone res) [] nL /\
  dft_open_invoke D g 1 b' call s
    (MAP (dft_fill_frame 1) rs) nR = DftOpen (DftDone res) [] nR ==>
  dft_pos_phase C D fi bi pre x call post
    (FUNPOW (dft_occ_oracle_next w C) 2 l) (dft_occ_oracle_next w D r) /\
  dft_occ_count (FUNPOW (dft_occ_oracle_next w C) 2 l) = nL /\
  dft_occ_count (dft_occ_oracle_next w D r) = nR
Proof
  strip_tac >> drule_all dft_pos_crossing_blocks >> strip_tac >>
  `?certs. dft_pos_stack C D fi bi pre x call post certs ls rs /\
    LENGTH l.dft_occ_saved = LENGTH certs` by
    (fs[dft_pos_phase_def] >> metis_tac[]) >>
  drule_all dft_pos_crossing_mid >> disch_then (qspec_then `w` assume_tac) >>
  qmatch_asmsub_abbrev_tac `dft_occ_oracle_next w C l = mid` >>
  `mid.dft_occ_core = DftOpen
     (DftAt f 0 b (t with vs_inst_idx := SUC s.vs_inst_idx)) ls nL /\
   mid.dft_occ_path = l.dft_occ_path /\ mid.dft_occ_visit = l.dft_occ_visit` by
    simp[Abbr `mid`] >>
  `get_instruction b (t with vs_inst_idx := SUC s.vs_inst_idx).vs_inst_idx = SOME call /\
   get_instruction b' s.vs_inst_idx = SOME call /\ call.inst_opcode = INVOKE` by
    (fs[dft_recursive_crossing_ready_def] >> simp[get_instruction_def, EL_APPEND_EQN]) >>
  `dft_occ_oracle_next w C mid = mid with
     <|dft_occ_core := DftOpen (DftDone res) [] nL; dft_occ_saved := []|>` by
    (irule dft_pos_invoke_failed_next >> simp[] >>
     qexists_tac `call` >> gvs[]) >>
  `dft_occ_oracle_next w D r = r with
     <|dft_occ_core := DftOpen (DftDone res) [] nR; dft_occ_saved := []|>` by
    (irule dft_pos_invoke_failed_next >> simp[] >>
     qexists_tac `call` >> gvs[]) >>
  `dft_original_ready (dft_occ_oracle_next w C mid) /\
   dft_original_ready (dft_occ_oracle_next w D r)` by
    (fs[dft_pos_phase_def] >> metis_tac[dft_original_runtime_next]) >>
  qpat_x_assum `D = _` kall_tac >>
  simp[FUNPOW_2, dft_occ_count_def] >>
  simp[dft_pos_phase_def, dft_pos_control_def, dft_pos_stack_def] >>
  fs[dft_pos_phase_def] >> metis_tac[]
QED

Theorem dft_pos_crossing_next:
  D = dft_pos_edit_ctx fi bi pre x call post C /\
  dft_pos_runtime_ready C fi bi pre x call post /\
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  dft_pos_phase C D fi bi pre x call post l r /\
  dft_pos_slot C D fi bi f g b b' /\
  l.dft_occ_core = DftOpen (DftAt f 0 b s) ls nL /\
  r.dft_occ_core = DftOpen (DftAt g 0 b' s) rs nR /\
  dft_recursive_crossing_ready f0 b0 b pre x call post s ==>
  dft_pos_phase C D fi bi pre x call post
    (FUNPOW (dft_occ_oracle_next w C) 2 l) (dft_occ_oracle_next w D r) /\
  dft_occ_count (FUNPOW (dft_occ_oracle_next w C) 2 l) = nL /\
  dft_occ_count (dft_occ_oracle_next w D r) = nR
Proof
  strip_tac >> drule dft_recursive_crossing_partner_success >> strip_tac >>
  drule_all dft_recursive_partner_updates >> strip_tac >>
  `dft_cut_pair us [] (t with vs_inst_idx := SUC s.vs_inst_idx) s` by
    metis_tac[dft_recursive_pending_cut] >>
  `EVERY (\p. ~MEM (Var (FST p)) call.inst_operands) us` by
    (drule dft_recursive_partner_disjoint >> strip_tac >>
     fs[EVERY_MEM] >> metis_tac[]) >>
  qpat_x_assum `t = _` kall_tac >>
  Cases_on `decode_invoke call`
  >- (irule dft_pos_crossing_failed >> simp[dft_open_invoke_def] >> metis_tac[]) >>
  rename1 `decode_invoke call = SOME pair` >> PairCases_on `pair` >>
  rename1 `decode_invoke call = SOME (nm,ops)` >>
  `eval_operands ops (t with vs_inst_idx := SUC s.vs_inst_idx) = eval_operands ops s` by
    (irule dft_cut_pair_eval_operands >> qexistsl_tac [`us`, `[]`] >> simp[] >>
     metis_tac[dft_pos_decode_support]) >>
  `OPTREL (dft_pos_functions C D)
     (lookup_function nm C.ctx_functions) (lookup_function nm D.ctx_functions)` by
    metis_tac[dft_pos_edit_function_lookup] >>
  Cases_on `lookup_function nm C.ctx_functions`
  >- suspend "missing" >>
  rename1 `lookup_function nm C.ctx_functions = SOME calleeL` >>
  `?calleeR. lookup_function nm D.ctx_functions = SOME calleeR /\
     dft_pos_functions C D calleeL calleeR` by
    (qpat_x_assum `OPTREL _ _ _` mp_tac >> simp[optionTheory.OPTREL_def]) >>
  `setup_callee calleeL args (t with vs_inst_idx := SUC s.vs_inst_idx) =
   setup_callee calleeR args s` by
    (drule dft_cut_pair_setup_callee >>
     metis_tac[dft_pos_edit_setup]) >>
  Cases_on `eval_operands ops s`
  >- suspend "operands" >>
  rename1 `eval_operands ops s = SOME args'` >>
  `setup_callee calleeL args' (t with vs_inst_idx := SUC s.vs_inst_idx) =
   setup_callee calleeR args' s` by
    (drule dft_cut_pair_setup_callee >> metis_tac[dft_pos_edit_setup]) >>
  Cases_on `setup_callee calleeR args' s`
  >- suspend "setup" >>
  drule_all dft_pos_crossing_enter >>
  disch_then (qspec_then `w` strip_assume_tac) >> simp[]
QED

Resume dft_pos_crossing_next[missing]:
  `lookup_function nm D.ctx_functions = NONE` by
    (qpat_x_assum `OPTREL _ _ _` mp_tac >> simp[optionTheory.OPTREL_def]) >>
  gvs[] >> irule dft_pos_crossing_failed >> simp[dft_open_invoke_def] >> metis_tac[]
QED
Resume dft_pos_crossing_next[operands]:
  gvs[] >> irule dft_pos_crossing_failed >> simp[dft_open_invoke_def] >> metis_tac[]
QED
Resume dft_pos_crossing_next[setup]:
  gvs[] >> irule dft_pos_crossing_failed >> simp[dft_open_invoke_def] >> metis_tac[]
QED
Finalise dft_pos_crossing_next

Theorem dft_pos_crossing_silent:
  D = dft_pos_edit_ctx fi bi pre x call post C /\
  dft_pos_runtime_ready C fi bi pre x call post /\
  dft_original_context Corig C /\ dft_original_context Dorig D /\
  dft_pos_phase C D fi bi pre x call post l r /\
  dft_pos_slot C D fi bi f g b b' /\
  l.dft_occ_core = DftOpen (DftAt f 0 b s) ls nL /\
  r.dft_occ_core = DftOpen (DftAt g 0 b' s) rs nR /\
  dft_recursive_crossing_ready f0 b0 b pre x call post s ==>
  (!j. j < 2 ==> dft_fixed_silent_cut (FUNPOW (dft_occ_oracle_next w C) j l)) /\
  (!k. k < 1 ==> dft_fixed_silent_cut (FUNPOW (dft_occ_oracle_next w D) k r))
Proof
  strip_tac >> drule_all dft_pos_crossing_blocks >> strip_tac >>
  drule dft_recursive_crossing_partner_success >> strip_tac >>
  `?certs. dft_pos_stack C D fi bi pre x call post certs ls rs /\
    LENGTH l.dft_occ_saved = LENGTH certs` by
    (fs[dft_pos_phase_def] >> metis_tac[]) >>
  drule_all dft_pos_crossing_mid >> disch_then (qspec_then `w` assume_tac) >>
  drule dft_recursive_crossing_positions >> strip_tac >>
  `inst_mem_ranges x s = [] /\
   inst_mem_ranges call (t with vs_inst_idx := SUC s.vs_inst_idx) = [] /\
   inst_mem_ranges call s = []` by
    (fs[dft_recursive_crossing_ready_def] >>
     metis_tac[dft_invoke_partner_no_observations]) >>
  `x.inst_opcode <> GAS /\ call.inst_opcode <> GAS` by
    fs[dft_recursive_crossing_ready_def] >>
  `get_instruction b' s.vs_inst_idx = SOME call` by
    gvs[dftOccurrenceGasEditTheory.dft_gas_edit_block_def] >>
  `dft_fixed_silent_cut l /\ dft_fixed_silent_cut r` by
    metis_tac[dft_fixed_silent_at] >>
  `dft_fixed_silent_cut (dft_occ_oracle_next w C l)` by
    (irule (cj 1 dft_fixed_silent_at) >> simp[] >> metis_tac[]) >>
  `!j:num. j < 2 <=> j = 0 \/ j = 1` by decide_tac >>
  simp[] >> rpt strip_tac >> gvs[]
QED
