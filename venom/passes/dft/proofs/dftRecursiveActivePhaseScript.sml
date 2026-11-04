Theory dftRecursiveActivePhase
Ancestors
  dftRecursiveCertifiedPush dftRecursiveCallProvenance dftRecursiveCallResidual
  dftOriginalOrbit dftMixedCrossing dftOccurrenceOrdinaryEdit
  dftOccurrenceGasEdit dftOrdinarySwap dftOccurrenceResidual
  dftProtectedRuntime dftOccurrenceFrame dftOccurrenceMachine dftOccurrenceReplay
  dftOpenMachine dftOpenErase venomExecSemantics venomWf venomInst venomState
  dftScheduleOrder dftScheduleEdits dftOriginalScheduleRuntime dftCorrectness
  finite_map pred_set list sorting arithmetic

Definition dft_recursive_enter_phase_def:
  dft_recursive_enter_phase fm bm certs c d <=>
    ?f s ls rs nL nR path visit saved.
      c.dft_occ_core = DftOpen (DftEnter f 0 s) ls nL /\
      d.dft_occ_core = DftOpen (DftEnter (fm f) 0 s) rs nR /\
      dft_provenanced_frames fm bm certs ls rs /\
      c.dft_occ_path = path /\ d.dft_occ_path = path /\
      c.dft_occ_visit = visit /\ d.dft_occ_visit = visit /\
      c.dft_occ_saved = saved /\ d.dft_occ_saved = saved /\
      LENGTH saved = LENGTH certs
End

Definition dft_recursive_crossing_ready_def:
  dft_recursive_crossing_ready f b q pre x call post s <=>
    dft_original_block f b q /\ dft_original_cut f b q s /\
    q.bb_instructions = pre ++ [x;call] ++ post /\
    s.vs_inst_idx = LENGTH pre /\
    (!lab. MEM (Label lab) x.inst_operands ==> lab IN FDOM s.vs_labels) /\
    ~dft_must_order x call /\ call.inst_opcode = INVOKE /\
    ~is_pseudo x.inst_opcode /\ ~is_terminator x.inst_opcode /\
    x.inst_opcode <> ALLOCA /\ x.inst_opcode <> GAS /\
    inst_wf x /\ inst_wf call
End

Theorem dft_recursive_partner_updates:
  dft_recursive_crossing_ready f b q pre x call post s /\
  step_inst_base x s = OK t ==>
  ?us. EVERY (\p. MEM (FST p) x.inst_outputs) us /\
       t = dft_pending_apply us s
Proof
  strip_tac >>
  `write_effects x.inst_opcode = empty_effects /\
   read_effects x.inst_opcode = empty_effects` by
    (fs[dft_recursive_crossing_ready_def] >>
     drule_all dft_invoke_inversion_disjoint >> simp[]) >>
  `?us. EVERY (\p. MEM (FST p) x.inst_outputs) us /\
        t = FOLDL (\u p. update_var (FST p) (SND p) u) s us /\
        step_inst_base x s = OK (FOLDL (\u p. update_var (FST p) (SND p) u) s us)` by
    (irule dft_ordinary_empty_effect_replay >>
     fs[dft_recursive_crossing_ready_def]) >>
  metis_tac[dft_pending_apply_def]
QED

Theorem dft_recursive_output_lists[local]:
  !xs. ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) xs)) /\
    MEM x xs /\ MEM y xs /\ x <> y /\ MEM v x.inst_outputs ==>
    ~MEM v y.inst_outputs
Proof
  Induct >> simp[] >> rpt strip_tac >>
  gvs[ALL_DISTINCT_APPEND] >> metis_tac[MEM_FLAT, MEM_MAP]
QED

Theorem dft_recursive_partner_disjoint:
  dft_recursive_crossing_ready f b q pre x call post s ==>
  !v. MEM v x.inst_outputs ==>
      ~MEM (Var v) call.inst_operands /\ ~MEM v call.inst_outputs
Proof
  simp[dft_recursive_crossing_ready_def] >> strip_tac >>
  `!v. MEM v x.inst_outputs ==> ~MEM (Var v) call.inst_operands` by
    (fs[dft_must_order_def, inst_defs_def, inst_uses_def,
        DISJOINT_DEF, EXTENSION, MEM_operand_vars_iff] >> metis_tac[]) >>
  `ssa_form f /\ MEM b f.fn_blocks` by
    fs[dft_original_block_def, dft_original_schedule_def, wf_ssa_def] >>
  `MEM x b.bb_instructions /\ MEM call b.bb_instructions` by
    (drule dft_original_block_mem >> simp[] >> metis_tac[]) >>
  `MEM x (fn_insts f) /\ MEM call (fn_insts f)` by
    (simp[fn_insts_def, o1PassContractTheory.fn_insts_blocks_MEM] >>
     conj_tac >> qexists `b` >> simp[]) >>
  `x <> call` by
    (strip_tac >> gvs[] >> drule_all dft_invoke_inversion_disjoint >>
     simp[venomEffectsTheory.read_effects_def,
          venomEffectsTheory.empty_effects_def,
          venomEffectsTheory.all_effects_def]) >>
  fs[ssa_form_def] >> metis_tac[dft_recursive_output_lists]
QED

Definition dft_forward_certificate_def:
  dft_forward_certificate f fn b q pre done x call post s t us = <|
    dft_cert_forward := T;
    dft_cert_original_fn := f;
    dft_cert_ordinary_fn := fn;
    dft_cert_delayed_fn := dft_gas_edit_fn q pre x call post fn;
    dft_cert_original_bb := b;
    dft_cert_before := q;
    dft_cert_after := dft_gas_edit_block q pre x call post q;
    dft_cert_pseudos := FILTER (\i. is_pseudo i.inst_opcode) b.bb_instructions;
    dft_cert_done := done;
    dft_cert_todo := post;
    dft_cert_partner := x;
    dft_cert_call := call;
    dft_cert_start := s;
    dft_cert_result := t;
    dft_cert_updates := us |>
End

Theorem dft_recursive_pending_cut:
  t = dft_pending_apply us s ==>
  dft_cut_pair us [] (t with vs_inst_idx := SUC s.vs_inst_idx) s
Proof
  strip_tac >> simp[dft_cut_pair_def] >>
  qexists `dft_cut_data s` >>
  simp[GSYM dft_cut_data_pending, dft_cut_data_def,
       dft_pending_apply_def]
QED

Theorem dft_recursive_crossing_positions:
  dft_recursive_crossing_ready f b q pre x call post s ==>
  get_instruction q s.vs_inst_idx = SOME x /\
  get_instruction q (SUC s.vs_inst_idx) = SOME call /\
  get_instruction (dft_gas_edit_block q pre x call post q) s.vs_inst_idx = SOME call
Proof
  simp[dft_recursive_crossing_ready_def] >> strip_tac >>
  simp[get_instruction_def, dft_gas_edit_block_def, EL_APPEND_EQN]
QED

Theorem dft_recursive_crossing_certificate_witness:
  dft_recursive_crossing_ready f b q pre x call post s /\
  step_inst_base x s = OK t ==>
  ?us cert.
    (?done. cert = dft_forward_certificate f fn b q pre done x call post s t us) /\
    t = dft_pending_apply us s /\ 
    EVERY (\p. MEM (FST p) x.inst_outputs) us /\
    dft_certificate_annotation (SOME cert) = DftPending us [] /\
    dft_provenanced_frame (dft_gas_edit_fn q pre x call post)
      (dft_gas_edit_block q pre x call post) (SOME cert)
      (DftCaller fn 0 q call (t with vs_inst_idx := SUC s.vs_inst_idx))
      (DftCaller (dft_gas_edit_fn q pre x call post fn) 0
        (dft_gas_edit_block q pre x call post q) call s)
Proof
  strip_tac >> drule_all dft_recursive_partner_updates >> strip_tac >>
  `?done. pre = FILTER (\i. is_pseudo i.inst_opcode) b.bb_instructions ++ done` by
    (irule dft_original_crossing_cut >> fs[dft_recursive_crossing_ready_def] >>
     metis_tac[]) >>
  `!v. MEM v x.inst_outputs ==>
    ~MEM (Var v) call.inst_operands /\ ~MEM v call.inst_outputs` by
    metis_tac[dft_recursive_partner_disjoint] >>
  `dft_cut_pair us [] (t with vs_inst_idx := SUC s.vs_inst_idx) s` by
    metis_tac[dft_recursive_pending_cut] >>
  drule dft_recursive_crossing_positions >> strip_tac >>
  qexistsl_tac [`us`, `dft_forward_certificate f fn b q pre done x call post s t us`] >>
  simp[dft_forward_certificate_def, dft_certificate_annotation_def,
       dft_provenanced_frame_def, dft_certificate_saved_def,
       dft_recursive_frame_def, dft_recursive_payload_def] >>
  conj_tac
  >- (fs[dft_crossing_evidence_def, dft_forward_certificate_def,
         dft_recursive_crossing_ready_def, dft_gas_edit_block_def,
         APPEND_ASSOC] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> REFL_TAC) >>
  fs[EVERY_MEM, dft_recursive_crossing_ready_def] >> metis_tac[]
QED

Theorem dft_recursive_crossing_certificate:
  dft_recursive_crossing_ready f b q pre x call post s /\
  step_inst_base x s = OK t ==>
  ?us cert.
    t = dft_pending_apply us s /\
    EVERY (\p. MEM (FST p) x.inst_outputs) us /\
    dft_certificate_annotation (SOME cert) = DftPending us [] /\
    dft_provenanced_frame (dft_gas_edit_fn q pre x call post)
      (dft_gas_edit_block q pre x call post) (SOME cert)
      (DftCaller fn 0 q call (t with vs_inst_idx := SUC s.vs_inst_idx))
      (DftCaller (dft_gas_edit_fn q pre x call post fn) 0
        (dft_gas_edit_block q pre x call post q) call s)
Proof
  strip_tac >> drule_all dft_recursive_crossing_certificate_witness >> metis_tac[]
QED

Definition dft_recursive_pre_phase_def:
  dft_recursive_pre_phase f b q pre x call post certs fn s c d <=>
    dft_recursive_crossing_ready f b q pre x call post s /\
    ?ls rs nL nR path visit saved.
      c.dft_occ_core = DftOpen (DftAt fn 0 q s) ls nL /\
      d.dft_occ_core = DftOpen
        (DftAt (dft_gas_edit_fn q pre x call post fn) 0
          (dft_gas_edit_block q pre x call post q) s) rs nR /\
      dft_provenanced_frames (dft_gas_edit_fn q pre x call post)
        (dft_gas_edit_block q pre x call post) certs ls rs /\
      c.dft_occ_path = path /\ d.dft_occ_path = path /\
      c.dft_occ_visit = visit /\ d.dft_occ_visit = visit /\
      c.dft_occ_saved = saved /\ d.dft_occ_saved = saved /\
      LENGTH saved = LENGTH certs
End

Theorem dft_recursive_frames_ready[local]:
  !cs ls rs. dft_provenanced_frames fm bm cs ls rs ==>
    MAP (dft_fill_frame 0) ls = ls /\ MAP (dft_fill_frame 0) rs = rs /\
    LENGTH ls = LENGTH cs /\ LENGTH rs = LENGTH cs
Proof
  Induct >> simp[dft_provenanced_frames_def] >> rpt strip_tac >> gvs[] >>
  first_x_assum drule >> strip_tac >>
  drule dft_provenanced_frame_projection >>
  Cases_on `l` >> Cases_on `r` >>
  simp[dft_recursive_frame_def, dft_fill_frame_def] >> strip_tac >> gvs[]
QED

Theorem dft_recursive_decode_support[local]:
  decode_invoke call = SOME (nm,ops) /\
  EVERY (\p. ~MEM (Var (FST p)) call.inst_operands) us ==>
  EVERY (\p. ~MEM (Var (FST p)) ops) us
Proof
  simp[decode_invoke_def, AllCaseEqs()] >> rpt strip_tac >> gvs[] >>
  fs[EVERY_MEM] >> metis_tac[MEM]
QED

Theorem dft_recursive_crossing_enter_exact:
  dft_recursive_pre_phase f b q pre x call post certs fn s c d /\
  step_inst_base x s = OK t /\
  decode_invoke call = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops (t with vs_inst_idx := SUC s.vs_inst_idx) = SOME args /\
  setup_callee callee args (t with vs_inst_idx := SUC s.vs_inst_idx) = SOME cs ==>
  ?cert.
    (?done us. cert = dft_forward_certificate f fn b q pre done x call post s t us) /\
    (!ls rs nL nR.
      c.dft_occ_core = DftOpen (DftAt fn 0 q s) ls nL /\
      d.dft_occ_core = DftOpen (DftAt (dft_gas_edit_fn q pre x call post fn) 0
        (dft_gas_edit_block q pre x call post q) s) rs nR ==>
      (FUNPOW (dft_occ_oracle_next w C) 2 c).dft_occ_core =
        DftOpen (DftEnter callee 0 cs)
          (DftCaller fn 0 q call (t with vs_inst_idx := SUC s.vs_inst_idx)::ls) nL /\
      (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x call post C) d).dft_occ_core =
        DftOpen (DftEnter (dft_gas_edit_fn q pre x call post callee) 0 cs)
          (DftCaller (dft_gas_edit_fn q pre x call post fn) 0
            (dft_gas_edit_block q pre x call post q) call s::rs) nR) /\
    dft_recursive_enter_phase (dft_gas_edit_fn q pre x call post)
      (dft_gas_edit_block q pre x call post) (SOME cert::certs)
      (FUNPOW (dft_occ_oracle_next w C) 2 c)
      (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x call post C) d) /\
    (FUNPOW (dft_occ_oracle_next w C) 2 c).dft_occ_path =
      c.dft_occ_path ++ [(c.dft_occ_visit,call.inst_id)] /\
    (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x call post C) d).dft_occ_path =
      c.dft_occ_path ++ [(c.dft_occ_visit,call.inst_id)] /\
    (FUNPOW (dft_occ_oracle_next w C) 2 c).dft_occ_visit = 0 /\
    (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x call post C) d).dft_occ_visit = 0 /\
    (FUNPOW (dft_occ_oracle_next w C) 2 c).dft_occ_saved =
      (c.dft_occ_path,c.dft_occ_visit)::c.dft_occ_saved /\
    (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x call post C) d).dft_occ_saved =
      (c.dft_occ_path,c.dft_occ_visit)::c.dft_occ_saved /\
    dft_occ_count (FUNPOW (dft_occ_oracle_next w C) 2 c) = dft_occ_count c /\
    dft_occ_count (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x call post C) d) =
      dft_occ_count d
Proof
  strip_tac >> fs[dft_recursive_pre_phase_def] >>
  drule_all dft_recursive_crossing_certificate_witness >>
  disch_then (qspec_then `fn` strip_assume_tac) >>
  drule dft_recursive_frames_ready >> strip_tac >>
  drule dft_recursive_crossing_positions >> strip_tac >>
  `dft_cut_pair us [] (t with vs_inst_idx := SUC s.vs_inst_idx) s` by
    metis_tac[dft_recursive_pending_cut] >>
  `EVERY (\p. ~MEM (Var (FST p)) call.inst_operands) us` by
    (drule dft_recursive_partner_disjoint >> fs[EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\p. ~MEM (Var (FST p)) ops) us` by
    metis_tac[dft_recursive_decode_support] >>
  `setup_callee (dft_gas_edit_fn q pre x call post callee) args s = SOME cs` by
    (simp[dft_gas_edit_setup_callee] >>
     drule dft_cut_pair_setup_callee >> metis_tac[]) >>
  `lookup_function nm (dft_gas_edit_ctx q pre x call post C).ctx_functions =
      SOME (dft_gas_edit_fn q pre x call post callee)` by
    simp[dft_gas_edit_lookup_function] >>
  `dft_occ_oracle_next w C c = c with
    <| dft_occ_core := DftOpen
       (DftAt fn 0 q (t with vs_inst_idx := SUC s.vs_inst_idx)) ls nL;
       dft_occ_saved := c.dft_occ_saved |>` by
    (`x.inst_opcode <> INVOKE /\ x.inst_opcode <> GAS /\
      ~is_terminator x.inst_opcode` by
       (fs[dft_recursive_crossing_ready_def] >>
        drule_all dft_invoke_inversion_disjoint >>
        Cases_on `x.inst_opcode = INVOKE` >>
        simp[venomEffectsTheory.read_effects_def,
             venomEffectsTheory.empty_effects_def,
             venomEffectsTheory.all_effects_def]) >>
     drule_all dft_occ_ordinary_next >>
     disch_then (qspecl_then [`w`, `C`] mp_tac) >>
     Cases_on `ls` >> gvs[] >>
     simp[dft_occ_config_component_equality]) >>
  qmatch_asmsub_abbrev_tac `dft_occ_oracle_next w C c = mid` >>
  `mid.dft_occ_core = DftOpen
     (DftAt fn 0 q (t with vs_inst_idx := SUC s.vs_inst_idx)) ls nL` by
    simp[Abbr `mid`] >>
  `mid.dft_occ_path = c.dft_occ_path /\ mid.dft_occ_visit = c.dft_occ_visit /\
   mid.dft_occ_saved = c.dft_occ_saved` by
    simp[Abbr `mid`] >>
  `call.inst_opcode = INVOKE /\
   get_instruction q (t with vs_inst_idx := SUC s.vs_inst_idx).vs_inst_idx = SOME call` by
    (fs[dft_recursive_crossing_ready_def] >> metis_tac[]) >>
  drule_all dft_provenanced_pending_push >>
  disch_then (qspec_then `w` strip_assume_tac) >>
  drule_all dftInvokeOrdinaryBoundaryTheory.dft_pending_two_context_push_fields >>
  disch_then (qspec_then `w` strip_assume_tac) >>
  qexists `cert` >>
  simp[FUNPOW_2, dft_occ_count_def] >>
  simp[dft_recursive_enter_phase_def] >>
  metis_tac[]
QED

Theorem dft_recursive_crossing_enter_witness:
  dft_recursive_pre_phase f b q pre x call post certs fn s c d /\
  step_inst_base x s = OK t /\
  decode_invoke call = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops (t with vs_inst_idx := SUC s.vs_inst_idx) = SOME args /\
  setup_callee callee args (t with vs_inst_idx := SUC s.vs_inst_idx) = SOME cs ==>
  ?cert.
    (?done us. cert = dft_forward_certificate f fn b q pre done x call post s t us) /\
    dft_recursive_enter_phase (dft_gas_edit_fn q pre x call post)
      (dft_gas_edit_block q pre x call post) (SOME cert::certs)
      (FUNPOW (dft_occ_oracle_next w C) 2 c)
      (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x call post C) d) /\
    (FUNPOW (dft_occ_oracle_next w C) 2 c).dft_occ_path =
      c.dft_occ_path ++ [(c.dft_occ_visit,call.inst_id)] /\
    (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x call post C) d).dft_occ_path =
      c.dft_occ_path ++ [(c.dft_occ_visit,call.inst_id)] /\
    (FUNPOW (dft_occ_oracle_next w C) 2 c).dft_occ_visit = 0 /\
    (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x call post C) d).dft_occ_visit = 0 /\
    (FUNPOW (dft_occ_oracle_next w C) 2 c).dft_occ_saved =
      (c.dft_occ_path,c.dft_occ_visit)::c.dft_occ_saved /\
    (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x call post C) d).dft_occ_saved =
      (c.dft_occ_path,c.dft_occ_visit)::c.dft_occ_saved /\
    dft_occ_count (FUNPOW (dft_occ_oracle_next w C) 2 c) = dft_occ_count c /\
    dft_occ_count (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x call post C) d) =
      dft_occ_count d
Proof
  strip_tac >> drule_all dft_recursive_crossing_enter_exact >> metis_tac[]
QED

Theorem dft_recursive_crossing_enter:
  dft_recursive_pre_phase f b q pre x call post certs fn s c d /\
  step_inst_base x s = OK t /\
  decode_invoke call = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops (t with vs_inst_idx := SUC s.vs_inst_idx) = SOME args /\
  setup_callee callee args (t with vs_inst_idx := SUC s.vs_inst_idx) = SOME cs ==>
  ?cert.
    dft_recursive_enter_phase (dft_gas_edit_fn q pre x call post)
      (dft_gas_edit_block q pre x call post) (SOME cert::certs)
      (FUNPOW (dft_occ_oracle_next w C) 2 c)
      (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x call post C) d) /\
    (FUNPOW (dft_occ_oracle_next w C) 2 c).dft_occ_path =
      c.dft_occ_path ++ [(c.dft_occ_visit,call.inst_id)] /\
    (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x call post C) d).dft_occ_path =
      c.dft_occ_path ++ [(c.dft_occ_visit,call.inst_id)] /\
    (FUNPOW (dft_occ_oracle_next w C) 2 c).dft_occ_visit = 0 /\
    (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x call post C) d).dft_occ_visit = 0 /\
    (FUNPOW (dft_occ_oracle_next w C) 2 c).dft_occ_saved =
      (c.dft_occ_path,c.dft_occ_visit)::c.dft_occ_saved /\
    (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x call post C) d).dft_occ_saved =
      (c.dft_occ_path,c.dft_occ_visit)::c.dft_occ_saved /\
    dft_occ_count (FUNPOW (dft_occ_oracle_next w C) 2 c) = dft_occ_count c /\
    dft_occ_count (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x call post C) d) =
      dft_occ_count d
Proof
  strip_tac >> drule_all dft_recursive_crossing_enter_witness >> metis_tac[]
QED
