Theory dftOrdinaryEventTrace
Ancestors
  dftOriginalOrbit dftOriginalSegment dftOriginalRuntime dftOriginalOperands
  dftOriginalScheduleRuntime dftProtectedRuntime
  dftLocalOrdinaryClosure dftOccurrenceOrdinaryClosure dftOccurrenceMachine
  dftOccurrenceGasEdit dftOrdinarySwap dftOccurrenceOrdinaryStop
  dftOpenMachine dftOpenErase dftOccurrenceReplay venomExecSemantics venomInst list arithmetic

Definition dft_segment_gas_cover_def:
  dft_segment_gas_cover w CL CR c d k j <=>
    (!h i a. h < k /\ dft_occ_gas_event i a
        (FUNPOW (dft_occ_oracle_next w CL) h c) ==>
      ?t. t < j /\ dft_occ_gas_event i a
        (FUNPOW (dft_occ_oracle_next w CR) t d)) /\
    (!t i a. t < j /\ dft_occ_gas_event i a
        (FUNPOW (dft_occ_oracle_next w CR) t d) ==>
      ?h. h < k /\ dft_occ_gas_event i a
        (FUNPOW (dft_occ_oracle_next w CL) h c))
End

Theorem dft_done_no_gas_event:
  c.dft_occ_core = DftOpen (DftDone result) stack n ==>
  ~dft_occ_gas_event i a c
Proof
  simp[dft_occ_gas_event_def, dft_occ_event_def]
QED

Theorem dft_at_no_gas_event:
  c.dft_occ_core = DftOpen (DftAt fn b bb s) stack n /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ inst.inst_opcode <> GAS ==>
  ~dft_occ_gas_event i a c
Proof
  simp[dft_occ_gas_event_def, dft_occ_event_def] >> metis_tac[]
QED

Theorem dft_ordinary_stopped_gas_cover:
  dft_ordinary_stopped c d ==> dft_segment_gas_cover w C C' c d 1 1
Proof
  simp[dft_ordinary_stopped_def, dft_segment_gas_cover_def,
       dft_occ_gas_event_def, dft_occ_event_def] >> rpt strip_tac >> gvs[]
QED

Theorem dft_ordinary_sync_outside_gas_event:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  dft_ordinary_sync bb0 pre x y post c d /\
  ~dft_edit_before bb0 (LENGTH pre) c ==>
  (dft_occ_gas_event i a c <=> dft_occ_gas_event i a d)
Proof
  simp[dft_ordinary_sync_def] >> strip_tac >>
  Cases_on `c.dft_occ_core` >> rename1 `c.dft_occ_core = DftOpen ctl stack n` >>
  Cases_on `ctl` >>
  gvs[dft_occ_gas_event_def, dft_occ_event_def,
      dft_edit_occ_def, dft_edit_core_def, dft_edit_control_def] >>
  rename1 `c.dft_occ_core = DftOpen (DftAt fn fuel bb s) stack n` >>
  `bb <> bb0 \/ (s.vs_inst_idx <> LENGTH pre /\
                  s.vs_inst_idx <> SUC (LENGTH pre))` by
    (fs[dft_edit_safe_def, dft_edit_safe_core_def, dft_edit_control_safe_def,
        dft_edit_cut_def, dft_edit_before_def] >> metis_tac[]) >>
  metis_tac[dft_gas_edit_instruction_outside]
QED

Theorem dft_ordinary_sync_outside_gas_cover:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  dft_ordinary_sync bb0 pre x y post c d /\
  ~dft_edit_before bb0 (LENGTH pre) c ==>
  dft_segment_gas_cover w C C' c d 1 1
Proof
  strip_tac >> drule_all dft_ordinary_sync_outside_gas_event >>
  simp[dft_segment_gas_cover_def] >> metis_tac[]
QED

Theorem dft_gas_event_successor_not_done:
  dft_occ_gas_event i a c ==>
  (dft_occ_oracle_next w C c).dft_occ_core <> DftOpen (DftDone result) stack n
Proof
  simp[dft_occ_gas_event_def, dft_occ_event_def] >> rpt strip_tac >>
  gvs[dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
      dft_fill_def, dft_fill_control_def, dft_open_next_def,
      dft_open_deliver_def, dft_open_continue_def, dft_erase_def,
      is_terminator_def]
QED

Theorem dft_pair_prefix_two_no_gas:
  c.dft_occ_core = DftOpen (DftAt fn 0 bb s) stack n /\
  get_instruction bb s.vs_inst_idx = SOME x /\
  get_instruction bb (SUC s.vs_inst_idx) = SOME y /\
  x.inst_opcode <> GAS /\ x.inst_opcode <> INVOKE /\
  ~is_terminator x.inst_opcode /\ y.inst_opcode <> GAS /\ h < 2 ==>
  ~dft_occ_gas_event i a (FUNPOW (dft_occ_oracle_next w C) h c)
Proof
  strip_tac >> `h = 0 \/ h = 1` by decide_tac
  >- (gvs[FUNPOW] >> metis_tac[dft_at_no_gas_event]) >>
  gvs[FUNPOW] >>
  Cases_on `step_inst_base x s` >>
  gvs[dft_occ_gas_event_def, dft_occ_event_def,
      dft_occ_oracle_next_def, dft_occ_next_def, dft_next_inf_def,
      dft_fill_def, dft_fill_control_def, dft_open_next_def,
      dft_open_deliver_def, dft_open_continue_def, dft_erase_def] >>
  metis_tac[]
QED

Theorem dft_prefix_gas_free_pad:
  (!h i a. h < 2 ==> ~dft_occ_gas_event i a
     (FUNPOW (dft_occ_oracle_next w C) h c)) /\ k <= 3 /\
  (2 < k ==> ?result stack n.
     (FUNPOW (dft_occ_oracle_next w C) k c).dft_occ_core =
       DftOpen (DftDone result) stack n) ==>
  !h i a. h < k ==> ~dft_occ_gas_event i a
     (FUNPOW (dft_occ_oracle_next w C) h c)
Proof
  rpt strip_tac >> Cases_on `h < 2` >- metis_tac[] >>
  `k = 3 /\ h = 2` by decide_tac >> gvs[] >>
  drule dft_gas_event_successor_not_done >>
  disch_then (qspecl_then [`w`, `stack`, `result`, `n`, `C`] mp_tac) >>
  simp[GSYM FUNPOW_SUC]
QED

Theorem dft_ordinary_pair_gas_cover:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  dft_ordinary_swap_pair x y /\ dft_ordinary_sync bb0 pre x y post c d /\
  c.dft_occ_core = DftOpen (DftAt fn 0 bb0 s) stack n /\
  s.vs_inst_idx = LENGTH pre /\ k <= 3 /\ j <= 3 /\
  ((k <= 2 /\ j <= 2) \/ dft_ordinary_stopped
    (FUNPOW (dft_occ_oracle_next w C) k c)
    (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C)) j d)) ==>
  dft_segment_gas_cover w C (dft_gas_edit_ctx bb0 pre x y post C) c d k j
Proof
  strip_tac >> drule_all dft_ordinary_sync_fetch >> strip_tac >>
  `!h i a. h < 2 ==> ~dft_occ_gas_event i a
      (FUNPOW (dft_occ_oracle_next w C) h c)` by
    (rpt gen_tac >> disch_tac >> irule dft_pair_prefix_two_no_gas >>
     fs[dft_ordinary_swap_pair_def] >> metis_tac[]) >>
  `!h i a. h < 2 ==> ~dft_occ_gas_event i a
      (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C)) h d)` by
    (rpt gen_tac >> disch_tac >> irule dft_pair_prefix_two_no_gas >>
     fs[dft_ordinary_swap_pair_def] >> metis_tac[]) >>
  `(!h i a. h < k ==> ~dft_occ_gas_event i a
      (FUNPOW (dft_occ_oracle_next w C) h c)) /\
   (!h i a. h < j ==> ~dft_occ_gas_event i a
      (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C)) h d))` by
    (conj_tac
     >- (rpt gen_tac >> disch_tac >> irule dft_prefix_gas_free_pad >> simp[] >>
         qexists `k` >> simp[] >> fs[dft_ordinary_stopped_def] >> metis_tac[]) >>
     rpt gen_tac >> disch_tac >> irule dft_prefix_gas_free_pad >> simp[] >>
     qexists `j` >> simp[] >> fs[dft_ordinary_stopped_def] >> metis_tac[]) >>
  simp[dft_segment_gas_cover_def] >> metis_tac[]
QED

Theorem dft_ordinary_pair_event_segment:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  dft_ordinary_swap_pair x y /\ inst_wf x /\ inst_wf y /\
  ~dft_must_order x y /\
  ~is_pseudo x.inst_opcode /\ ~is_pseudo y.inst_opcode /\
  x.inst_opcode <> ALLOCA /\ y.inst_opcode <> ALLOCA /\
  ~MEM x.inst_opcode [DELEGATECALL; CREATE; CREATE2] /\
  ~MEM y.inst_opcode [DELEGATECALL; CREATE; CREATE2] /\
  (!op. MEM op x.inst_operands ==> ?v. eval_operand op s = SOME v) /\
  (!sx. step_inst_base x s = OK sx ==> !op. MEM op y.inst_operands ==>
    ?v. eval_operand op (sx with vs_inst_idx := SUC s.vs_inst_idx) = SOME v) /\
  (!op. MEM op y.inst_operands ==> ?v. eval_operand op s = SOME v) /\
  dft_ordinary_sync bb0 pre x y post c d /\
  c.dft_occ_core = DftOpen (DftAt fn 0 bb0 s) stack n /\
  s.vs_inst_idx = LENGTH pre ==>
  ?k j. 0 < k /\ k <= 3 /\ 0 < j /\ j <= 3 /\
    dft_ordinary_endpoint bb0 pre x y post
      (FUNPOW (dft_occ_oracle_next w C) k c)
      (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C)) j d) /\
    dft_ordinary_prefix_cover (dft_gas_edit_fn bb0 pre x y post) w C
      (dft_gas_edit_ctx bb0 pre x y post C) c d k j /\
    dft_segment_gas_cover w C (dft_gas_edit_ctx bb0 pre x y post C) c d k j
Proof
  strip_tac >>
  `~is_terminator x.inst_opcode /\ ~is_terminator y.inst_opcode /\
   x.inst_opcode <> GAS /\ x.inst_opcode <> INVOKE /\
   y.inst_opcode <> GAS /\ y.inst_opcode <> INVOKE` by
    fs[dft_ordinary_swap_pair_def] >>
  `(?sx. step_inst_base x s = OK sx) \/
   (?a t. step_inst_base x s = Abort a t)` by
    (irule dft_shaped_ordinary_outcome >> simp[]) >>
  pop_assum strip_assume_tac
  >- (rename1 `step_inst_base x s = OK sx` >>
      `(?sy. step_inst_base y (sx with vs_inst_idx := SUC s.vs_inst_idx) = OK sy) \/
       (?a t. step_inst_base y (sx with vs_inst_idx := SUC s.vs_inst_idx) = Abort a t)` by
        (irule dft_shaped_ordinary_outcome >> simp[]) >>
      pop_assum strip_assume_tac
      >- (qexistsl_tac [`2`, `2`] >> simp[] >> conj_tac
          >- (simp[dft_ordinary_endpoint_def] >> disj1_tac >>
              irule dft_ordinary_sync_success >> metis_tac[]) >>
          conj_tac
          >- (irule dft_ordinary_sync_success_cover >> metis_tac[]) >>
          irule dft_ordinary_pair_gas_cover >> simp[] >> metis_tac[]) >>
      drule_all dft_ordinary_second_abort_segment >>
      disch_then (qspecl_then [`w`, `C`] strip_assume_tac) >>
      qexistsl_tac [`3`, `2`] >> simp[dft_ordinary_endpoint_def] >>
      irule dft_ordinary_pair_gas_cover >> simp[] >> metis_tac[]) >>
  drule_all dft_ordinary_first_abort_segment >>
  disch_then (qspecl_then [`w`, `C`] strip_assume_tac) >>
  qexistsl_tac [`2`, `j`] >> simp[dft_ordinary_endpoint_def] >>
  irule dft_ordinary_pair_gas_cover >> simp[] >> metis_tac[]
QED

Theorem dft_original_sync_event_segment:
  dft_original_ordinary_environment Corig C L q pre x y post /\
  dft_original_label_ready C L c /\ dft_ordinary_sync q pre x y post c d ==>
  ?k j. 0 < k /\ k <= 3 /\ 0 < j /\ j <= 3 /\
    dft_ordinary_endpoint q pre x y post
      (FUNPOW (dft_occ_oracle_next w C) k c)
      (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x y post C)) j d) /\
    dft_ordinary_prefix_cover (dft_gas_edit_fn q pre x y post) w C
      (dft_gas_edit_ctx q pre x y post C) c d k j /\
    dft_segment_gas_cover w C (dft_gas_edit_ctx q pre x y post C) c d k j
Proof
  strip_tac >> Cases_on `dft_edit_before q (LENGTH pre) c`
  >- (fs[dft_edit_before_def] >>
      `?f b. dft_original_block f b q /\ dft_original_cut f b q s` by
        (fs[dft_original_label_ready_def] >>
         drule_all dft_original_runtime_at_projection >> metis_tac[]) >>
      `?done. pre = FILTER (\i. is_pseudo i.inst_opcode) b.bb_instructions ++ done` by
        (irule dft_original_crossing_cut >>
         fs[dft_original_ordinary_environment_def] >> metis_tac[]) >>
      `MEM x b.bb_instructions /\ MEM y b.bb_instructions` by
        (drule dft_original_block_mem >>
         fs[dft_original_ordinary_environment_def] >> metis_tac[MEM_APPEND, MEM]) >>
      `inst_wf x /\ inst_wf y` by
        (fs[dft_original_block_def, dft_original_schedule_def, EVERY_MEM] >> metis_tac[]) >>
      `(!l. MEM (Label l) x.inst_operands ==> l IN FDOM s.vs_labels) /\
       (!l. MEM (Label l) y.inst_operands ==> l IN FDOM s.vs_labels)` by
        (irule dft_original_crossing_labels >>
         fs[dft_original_ordinary_environment_def] >> metis_tac[]) >>
      `!op. MEM op x.inst_operands ==> ?v. eval_operand op s = SOME v` by
        (drule dft_original_first_operands >>
         disch_then (qspecl_then [`x`, `y::post`,
           `FILTER (\i. is_pseudo i.inst_opcode) b.bb_instructions`, `done`] mp_tac) >>
         fs[dft_original_ordinary_environment_def, dft_ordinary_swap_pair_def,
            APPEND_ASSOC]) >>
      `!op. MEM op y.inst_operands ==> ?v. eval_operand op s = SOME v` by
        (rpt gen_tac >> disch_tac >> irule dft_original_before_operands >>
         fs[dft_original_ordinary_environment_def, dft_ordinary_swap_pair_def] >> metis_tac[]) >>
      `!sx. step_inst_base x s = OK sx ==> !op. MEM op y.inst_operands ==>
        ?v. eval_operand op (sx with vs_inst_idx := SUC s.vs_inst_idx) = SOME v` by
        (rpt strip_tac >> irule dft_original_after_operands >>
         fs[dft_original_ordinary_environment_def, dft_ordinary_swap_pair_def] >>
         metis_tac[is_pseudo_def]) >>
      irule dft_ordinary_pair_event_segment >>
      fs[dft_original_ordinary_environment_def] >> metis_tac[]) >>
  qexistsl_tac [`1`, `1`] >> simp[FUNPOW] >> conj_tac
  >- (simp[dft_ordinary_endpoint_def] >> disj1_tac >>
      irule dft_ordinary_sync_outside >>
      fs[dft_original_ordinary_environment_def, dft_ordinary_swap_pair_def] >>
      metis_tac[is_pseudo_def]) >>
  conj_tac
  >- (irule dft_ordinary_sync_outside_cover >> fs[dft_original_ordinary_environment_def]) >>
  irule dft_ordinary_sync_outside_gas_cover >>
  fs[dft_original_ordinary_environment_def] >> metis_tac[]
QED

Theorem dft_original_endpoint_event_segment:
  dft_original_ordinary_environment Corig C L q pre x y post /\
  dft_original_label_ready C L c /\ dft_ordinary_endpoint q pre x y post c d ==>
  ?k j. 0 < k /\ k <= 3 /\ 0 < j /\ j <= 3 /\
    dft_ordinary_endpoint q pre x y post
      (FUNPOW (dft_occ_oracle_next w C) k c)
      (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx q pre x y post C)) j d) /\
    dft_original_label_ready C L (FUNPOW (dft_occ_oracle_next w C) k c) /\
    dft_ordinary_prefix_cover (dft_gas_edit_fn q pre x y post) w C
      (dft_gas_edit_ctx q pre x y post C) c d k j /\
    dft_segment_gas_cover w C (dft_gas_edit_ctx q pre x y post C) c d k j
Proof
  strip_tac >>
  `dft_original_context Corig C` by fs[dft_original_ordinary_environment_def] >>
  `!k. dft_original_label_ready C L (FUNPOW (dft_occ_oracle_next w C) k c)` by
    metis_tac[dft_original_label_iter] >>
  fs[dft_ordinary_endpoint_def]
  >- (drule_all dft_original_sync_event_segment >> metis_tac[dft_ordinary_endpoint_def]) >>
  qexistsl_tac [`1`, `1`] >> simp[FUNPOW] >> conj_tac
  >- (disj2_tac >> irule dft_ordinary_stopped_next >> simp[]) >>
  conj_tac >- (irule dft_ordinary_stopped_cover >> simp[]) >>
  irule dft_ordinary_stopped_gas_cover >> simp[]
QED
