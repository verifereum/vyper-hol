(* Eventwise replay: the oracle is consulted only at a successful GAS. *)
Theory dftOccurrenceReplay
Ancestors
  dftOccurrenceFreshness dftOccurrenceMachine dftOpenErase dftOpenMachine
  dftOpenRawAdequacy dftOpenReverseRaw dftOpenAdequacy
  venomExecSemantics venomInst arithmetic list

Definition dft_occ_address_def:
  dft_occ_address c =
    case c.dft_occ_core of DftOpen ctl stack n =>
      case ctl of DftAt fn b bb s =>
        (case get_instruction bb s.vs_inst_idx of
           SOME inst => c.dft_occ_path ++ [(c.dft_occ_visit,inst.inst_id)]
         | NONE => [])
      | _ => []
End

Definition dft_occ_count_def:
  dft_occ_count c = case c.dft_occ_core of DftOpen ctl stack n => n
End

Definition dft_occ_oracle_next_def:
  dft_occ_oracle_next w ctx c =
    dft_occ_next (\n. w (dft_occ_address c)) ctx c
End

Definition dft_occ_compatible_def:
  dft_occ_compatible w a c <=>
    !inst addr. dft_occ_gas_event inst addr c ==>
      w addr = a (dft_occ_count c)
End

Definition dft_occ_prefix_compatible_def:
  dft_occ_prefix_compatible w a ctx c j <=>
    !h. h < j ==> dft_occ_compatible w a
      (FUNPOW (dft_occ_oracle_next w ctx) h c)
End

Definition dft_occ_numeric_compatible_def:
  dft_occ_numeric_compatible w a ctx c j <=>
    !h. h < j ==> dft_occ_compatible w a
      (FUNPOW (dft_occ_next a ctx) h c)
End

Theorem dft_occ_gas_address:
  dft_occ_gas_event inst addr c ==> dft_occ_address c = addr
Proof
  simp[dft_occ_gas_event_def, dft_occ_event_def] >> rpt strip_tac >>
  simp[dft_occ_address_def]
QED

Theorem dft_occ_oracle_step:
  dft_occ_compatible w a c ==>
  dft_occ_oracle_next w ctx c = dft_occ_next a ctx c
Proof
  Cases_on `c.dft_occ_core` >> rename1 `c.dft_occ_core = DftOpen ctl stack n` >>
  Cases_on `ctl`
  >- simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
          dft_fill_def, dft_fill_control_def, dft_open_next_def]
  >- suspend "at"
  >- simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
          dft_fill_def, dft_fill_control_def, dft_open_next_def]
QED

Resume dft_occ_oracle_step[at]:
  rename1 `c.dft_occ_core = DftOpen (DftAt fn budget bb s) stack n` >>
  strip_tac >> Cases_on `get_instruction bb s.vs_inst_idx`
  >- simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
          dft_fill_def, dft_fill_control_def, dft_open_next_def] >>
  rename1 `get_instruction _ _ = SOME inst` >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
          dft_fill_def, dft_fill_control_def, dft_open_next_def] >>
  Cases_on `inst.inst_opcode = GAS`
  >- (Cases_on `inst.inst_outputs` >>
      simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
           dft_fill_def, dft_fill_control_def, dft_open_next_def] >>
      rename1 `inst.inst_outputs = out::outs` >> Cases_on `outs` >>
      simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
           dft_fill_def, dft_fill_control_def, dft_open_next_def] >>
      `w (dft_occ_address c) = a n` by
        (qpat_x_assum `dft_occ_compatible _ _ _` mp_tac >>
         simp[dft_occ_compatible_def, dft_occ_gas_event_def, dft_occ_event_def,
              dft_occ_address_def, dft_occ_count_def] >> metis_tac[]) >> simp[]) >>
  simp[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
       dft_fill_def, dft_fill_control_def, dft_open_next_def]
QED

Finalise dft_occ_oracle_step

Theorem dft_occ_prefix_replay:
  !j. dft_occ_prefix_compatible w a ctx c j ==>
    FUNPOW (dft_occ_oracle_next w ctx) j c = FUNPOW (dft_occ_next a ctx) j c
Proof
  Induct >> simp[FUNPOW_SUC] >> strip_tac >>
  `dft_occ_prefix_compatible w a ctx c j` by
    (gvs[dft_occ_prefix_compatible_def] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  `dft_occ_compatible w a (FUNPOW (dft_occ_oracle_next w ctx) j c)` by
    gvs[dft_occ_prefix_compatible_def] >>
  drule dft_occ_oracle_step >> metis_tac[]
QED

Theorem dft_occ_numeric_replay:
  !j. dft_occ_numeric_compatible w a ctx c j ==>
    FUNPOW (dft_occ_oracle_next w ctx) j c = FUNPOW (dft_occ_next a ctx) j c
Proof
  Induct >> simp[FUNPOW_SUC] >> strip_tac >>
  `dft_occ_numeric_compatible w a ctx c j` by
    (gvs[dft_occ_numeric_compatible_def] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  `dft_occ_compatible w a (FUNPOW (dft_occ_next a ctx) j c)` by
    gvs[dft_occ_numeric_compatible_def] >>
  drule dft_occ_oracle_step >> metis_tac[]
QED

Theorem dft_occ_prefix_compatible_iff:
  dft_occ_prefix_compatible w a ctx c j <=>
  dft_occ_numeric_compatible w a ctx c j
Proof
  eq_tac >> strip_tac
  >- (simp[dft_occ_numeric_compatible_def] >> rpt strip_tac >>
      `dft_occ_prefix_compatible w a ctx c h` by
        (gvs[dft_occ_prefix_compatible_def] >> rpt strip_tac >>
         first_x_assum irule >> decide_tac) >>
      drule dft_occ_prefix_replay >> strip_tac >>
      gvs[dft_occ_prefix_compatible_def] >> metis_tac[]) >>
  simp[dft_occ_prefix_compatible_def] >> rpt strip_tac >>
  `dft_occ_numeric_compatible w a ctx c h` by
    (gvs[dft_occ_numeric_compatible_def] >> rpt strip_tac >>
     first_x_assum irule >> decide_tac) >>
  drule dft_occ_numeric_replay >> strip_tac >>
  gvs[dft_occ_numeric_compatible_def]
QED

Theorem dft_inf_observation_raw:
  ctx.ctx_entry = SOME name /\ lookup_function name ctx.ctx_functions = SOME entry /\
  fn_entry_label entry = SOME lbl /\ dft_sparse_oracle a vs0.vs_gas_readings /\
  FUNPOW (dft_next_inf a ctx) j
    (DftOpen (DftEnter entry 0
      (vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)) [] 0) =
    DftOpen (DftAt fn 0 bb ghost) stack n /\
  get_instruction bb ghost.vs_inst_idx = SOME inst ==>
  raw_reachable vs0 ctx fn inst (dft_open_materialize vs0.vs_gas_readings n ghost)
Proof
  strip_tac >>
  qmatch_asmsub_abbrev_tac `FUNPOW (dft_next_inf a ctx) j start` >>
  `dft_erase (FUNPOW (dft_open_next a ctx) j (dft_fill j start)) =
   FUNPOW (dft_next_inf a ctx) j (dft_erase start)` by
    (irule dft_fill_decorates >> simp[]) >>
  gvs[Abbr `start`, dft_erase_def, dft_fill_def, dft_fill_control_def] >>
  Cases_on `FUNPOW (dft_open_next a ctx) j
    (DftOpen (DftEnter entry j
      (vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)) [] 0)` >>
  rename1 `dft_fill 0 (DftOpen ctl frames n0) = _` >> Cases_on `ctl` >>
  gvs[dft_fill_def, dft_fill_control_def] >>
  irule dft_open_observation_raw >> goal_assum (drule_at Any) >> simp[]
QED

Definition dft_occ_start_def:
  dft_occ_start entry lbl vs0 = dft_occ_init
    (DftOpen (DftEnter entry 0
      (vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>)) [] 0)
End

Theorem dft_occ_observation_raw:
  ctx.ctx_entry = SOME name /\ lookup_function name ctx.ctx_functions = SOME entry /\
  fn_entry_label entry = SOME lbl /\ dft_sparse_oracle a vs0.vs_gas_readings /\
  dft_occ_prefix_compatible w a ctx (dft_occ_start entry lbl vs0) j /\
  (FUNPOW (dft_occ_oracle_next w ctx) j (dft_occ_start entry lbl vs0)).dft_occ_core =
    dft_erase (DftOpen (DftAt fn 0 bb ghost) stack n) /\
  get_instruction bb ghost.vs_inst_idx = SOME inst ==>
  raw_reachable vs0 ctx fn inst (dft_open_materialize vs0.vs_gas_readings n ghost)
Proof
  strip_tac >> drule dft_occ_prefix_replay >> strip_tac >>
  gvs[dft_occ_iter_projection, dft_occ_start_def, dft_occ_init_def,
      dft_erase_def, dft_fill_def, dft_fill_control_def] >>
  irule dft_inf_observation_raw >> goal_assum (drule_at Any) >> simp[] >>
  metis_tac[]
QED

Theorem dft_raw_occ_adequacy:
  ctx.ctx_entry = SOME name /\ lookup_function name ctx.ctx_functions = SOME entry /\
  fn_entry_label entry = SOME lbl /\
  EVERY (\f. ALL_DISTINCT (MAP (\b. b.bb_label) f.fn_blocks)) ctx.ctx_functions /\
  dft_sparse_oracle a vs0.vs_gas_readings /\
  (!j. dft_occ_numeric_compatible w a ctx (dft_occ_start entry lbl vs0) j) /\
  raw_reachable vs0 ctx fn inst observed ==>
  ?j bb ghost stack n.
    (FUNPOW (dft_occ_oracle_next w ctx) j (dft_occ_start entry lbl vs0)).dft_occ_core =
      dft_erase (DftOpen (DftAt fn 0 bb ghost) stack n) /\
    get_instruction bb ghost.vs_inst_idx = SOME inst /\
    observed = dft_open_materialize vs0.vs_gas_readings n ghost
Proof
  strip_tac >> drule_all dft_raw_inf_adequacy >> strip_tac >>
  qexistsl_tac [`j`, `bb`, `ghost`, `stack`, `n`] >> simp[] >>
  `FUNPOW (dft_occ_oracle_next w ctx) j (dft_occ_start entry lbl vs0) =
   FUNPOW (dft_occ_next a ctx) j (dft_occ_start entry lbl vs0)` by
    (irule dft_occ_numeric_replay >> simp[]) >>
  gvs[dft_occ_iter_projection, dft_occ_start_def, dft_occ_init_def,
      dft_erase_def, dft_fill_def, dft_fill_control_def]
QED

(* A budget exhaustion is a native Error, not a fuel-free terminal event.
   Erasure is used only on prefixes which have not taken that extra step. *)
Theorem dft_nonexhausting_erase:
  !j c. (!h. h < j ==> ~dft_zero_entry (FUNPOW (dft_open_next a ctx) h c)) ==>
    dft_erase (FUNPOW (dft_open_next a ctx) j c) =
      FUNPOW (dft_next_inf a ctx) j (dft_erase c)
Proof
  Induct >> simp[FUNPOW_SUC] >> rpt strip_tac >>
  `!h. h < j ==> ~dft_zero_entry (FUNPOW (dft_open_next a ctx) h c)` by
    (gen_tac >> disch_tac >> first_x_assum irule >> decide_tac) >>
  `~dft_zero_entry (FUNPOW (dft_open_next a ctx) j c)` by simp[] >>
  simp[dft_erase_next]
QED

Theorem dft_occ_budget_prefix_replay:
  c.dft_occ_core = dft_erase budgeted /\
  dft_occ_prefix_compatible w a ctx c j /\
  (!h. h < j ==> ~dft_zero_entry (FUNPOW (dft_open_next a ctx) h budgeted)) ==>
  (FUNPOW (dft_occ_oracle_next w ctx) j c).dft_occ_core =
    dft_erase (FUNPOW (dft_open_next a ctx) j budgeted)
Proof
  strip_tac >> drule dft_occ_prefix_replay >> strip_tac >>
  simp[dft_occ_iter_projection] >>
  sym_tac >> irule dft_nonexhausting_erase >> simp[]
QED

(* The specified fuel remains in this certificate even when it exhausts.
   Error text is intentionally governed by dft_open_result_eq. *)
Theorem dft_occ_native_result:
  dft_sparse_oracle a xs ==>
  (dft_open_result_eq
     (run_blocks fuel ctx fn (dft_open_materialize xs n s)) r <=>
   ?rr m k d. n <= m /\ 0 < k /\
     dft_open_result_eq (dft_open_materialize_result xs m rr) r /\
     (!t. rr <> OK t) /\
     dft_first_hit (dft_open_next a ctx) (dft_open_stack_exit stack)
       (DftOpen (DftEnter fn fuel s) stack n) k d /\
     dft_open_classified_exit stack rr d m)
Proof
  strip_tac >> drule dft_open_run_segment_iff >>
  simp[dft_open_run_segment_def]
QED
