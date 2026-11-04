Theory dftGasEventTrace
Ancestors
  dftOccurrenceGasEditTrace dftOrdinaryEventTrace dftOccurrenceGasEdit
  dftOccurrenceOrdinaryClosure dftOccurrenceMachine dftOpenMachine
  dftOpenErase dftOccurrenceReplay venomExecSemantics venomState venomInst list arithmetic

Theorem dft_gas_pair_sync_segment:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode = GAS /\ y.inst_opcode = GAS /\
  x.inst_outputs = [u] /\ y.inst_outputs = [v] /\
  x.inst_operands = [] /\ y.inst_operands = [] /\ u <> v /\
  dft_ordinary_sync bb0 pre x y post c d /\
  dft_edit_before bb0 (LENGTH pre) c ==>
  dft_ordinary_sync bb0 pre x y post
    (FUNPOW (dft_occ_oracle_next w C) 2 c)
    (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C)) 2 d)
Proof
  simp[dft_ordinary_sync_def, FUNPOW] >> strip_tac >>
  drule_all dft_gas_edit_middle_safe_cut >> strip_tac >>
  simp[FUNPOW_2] >> irule dft_gas_edit_middle_join >> metis_tac[]
QED

Theorem dft_gas_pair_cross_events:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode = GAS /\ y.inst_opcode = GAS /\
  x.inst_outputs = [u] /\ y.inst_outputs = [v] /\
  x.inst_operands = [] /\ y.inst_operands = [] /\
  dft_ordinary_sync bb0 pre x y post c d /\
  dft_edit_before bb0 (LENGTH pre) c ==>
  (dft_occ_gas_event i a c <=> dft_occ_gas_event i a
    (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C) d)) /\
  (dft_occ_gas_event i a (dft_occ_oracle_next w C c) <=> dft_occ_gas_event i a d)
Proof
  simp[dft_ordinary_sync_def, dft_edit_before_def] >> rpt strip_tac >>
  Cases_on `c` >> gvs[] >> Cases_on `stack` >>
  gvs[dft_occ_gas_event_def, dft_occ_event_def,
       dft_edit_occ_def, dft_edit_core_def, dft_edit_control_def,
       dft_gas_edit_block_def, get_instruction_def, EL_APPEND_EQN,
       dft_occ_oracle_next_def, dft_occ_next_def, dft_occ_address_def,
       dft_next_inf_def, dft_fill_def, dft_fill_control_def, dft_erase_def,
       dft_open_next_def, dft_open_deliver_def, dft_open_continue_def,
       is_terminator_def, dft_occ_update_def, update_var_def, ADD1]
QED

Theorem dft_gas_pair_event_cover:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode = GAS /\ y.inst_opcode = GAS /\
  x.inst_outputs = [u] /\ y.inst_outputs = [v] /\
  x.inst_operands = [] /\ y.inst_operands = [] /\
  dft_ordinary_sync bb0 pre x y post c d /\
  dft_edit_before bb0 (LENGTH pre) c ==>
  dft_segment_gas_cover w C (dft_gas_edit_ctx bb0 pre x y post C) c d 2 2
Proof
  strip_tac >>
  `!i a. (dft_occ_gas_event i a c <=> dft_occ_gas_event i a
      (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C) d)) /\
    (dft_occ_gas_event i a (dft_occ_oracle_next w C c) <=> dft_occ_gas_event i a d)` by
    (rpt gen_tac >> irule dft_gas_pair_cross_events >> metis_tac[]) >>
  simp[dft_segment_gas_cover_def] >> conj_tac >>
  (map_every qx_gen_tac [`h`, `i`, `a`] >> strip_tac >>
   Cases_on `h = 0`
   >- (gvs[FUNPOW] >> qexists_tac `1` >> simp[FUNPOW]) >>
   `h = 1` by decide_tac >> gvs[FUNPOW] >>
   qexists_tac `0` >> simp[FUNPOW])
QED

Theorem dft_gas_sync_event_segment:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode = GAS /\ y.inst_opcode = GAS /\
  x.inst_outputs = [u] /\ y.inst_outputs = [v] /\
  x.inst_operands = [] /\ y.inst_operands = [] /\
  u <> v /\ x.inst_id <> y.inst_id /\
  dft_ordinary_sync bb0 pre x y post c d ==>
  ?k j. 0 < k /\ k <= 2 /\ 0 < j /\ j <= 2 /\
    dft_ordinary_sync bb0 pre x y post
      (FUNPOW (dft_occ_oracle_next w C) k c)
      (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C)) j d) /\
    dft_segment_gas_cover w C (dft_gas_edit_ctx bb0 pre x y post C) c d k j
Proof
  strip_tac >> Cases_on `dft_edit_before bb0 (LENGTH pre) c`
  >- (qexistsl_tac [`2`, `2`] >> simp[] >> conj_tac
      >- (irule dft_gas_pair_sync_segment >> metis_tac[]) >>
      irule dft_gas_pair_event_cover >> metis_tac[]) >>
  qexistsl_tac [`1`, `1`] >> simp[FUNPOW] >> conj_tac
  >- (irule dft_ordinary_sync_outside >> simp[] >> metis_tac[]) >>
  irule dft_ordinary_sync_outside_gas_cover >> metis_tac[]
QED

Theorem dft_gas_orbit_event_forward:
  !h c d i a.
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode = GAS /\ y.inst_opcode = GAS /\
  x.inst_outputs = [u] /\ y.inst_outputs = [v] /\
  x.inst_operands = [] /\ y.inst_operands = [] /\
  u <> v /\ x.inst_id <> y.inst_id /\
  dft_ordinary_sync bb0 pre x y post c d /\
  dft_occ_gas_event i a (FUNPOW (dft_occ_oracle_next w C) h c) ==>
  ?t. dft_occ_gas_event i a
    (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C)) t d)
Proof
  completeInduct_on `h` >> rpt strip_tac >>
  drule_all dft_gas_sync_event_segment >>
  disch_then (qspecl_then [`w`, `C`] strip_assume_tac) >>
  Cases_on `h < k`
  >- (fs[dft_segment_gas_cover_def] >> metis_tac[]) >>
  `h - k < h /\ h = (h - k) + k` by decide_tac >>
  first_x_assum (qspec_then `h - k` mp_tac) >> simp[] >>
  disch_then (qspecl_then
    [`FUNPOW (dft_occ_oracle_next w C) k c`,
     `FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C)) j d`,
     `i`, `a`] mp_tac) >>
  simp[GSYM FUNPOW_ADD] >> strip_tac >>
  qexists_tac `j + t` >> simp[]
QED

Theorem dft_gas_orbit_event_backward:
  !h c d i a.
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode = GAS /\ y.inst_opcode = GAS /\
  x.inst_outputs = [u] /\ y.inst_outputs = [v] /\
  x.inst_operands = [] /\ y.inst_operands = [] /\
  u <> v /\ x.inst_id <> y.inst_id /\
  dft_ordinary_sync bb0 pre x y post c d /\
  dft_occ_gas_event i a
    (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C)) h d) ==>
  ?t. dft_occ_gas_event i a (FUNPOW (dft_occ_oracle_next w C) t c)
Proof
  completeInduct_on `h` >> rpt strip_tac >>
  drule_all dft_gas_sync_event_segment >>
  disch_then (qspecl_then [`w`, `C`] strip_assume_tac) >>
  Cases_on `h < j`
  >- (fs[dft_segment_gas_cover_def] >> metis_tac[]) >>
  `h - j < h /\ h = (h - j) + j` by decide_tac >>
  first_x_assum (qspec_then `h - j` mp_tac) >> simp[] >>
  disch_then (qspecl_then
    [`FUNPOW (dft_occ_oracle_next w C) k c`,
     `FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C)) j d`,
     `i`, `a`] mp_tac) >>
  simp[GSYM FUNPOW_ADD] >> strip_tac >>
  qexists_tac `k + t` >> simp[]
QED

Theorem dft_gas_root_event_support:
  bb0.bb_instructions = pre ++ [x;y] ++ post /\
  x.inst_opcode = GAS /\ y.inst_opcode = GAS /\
  x.inst_outputs = [u] /\ y.inst_outputs = [v] /\
  x.inst_operands = [] /\ y.inst_operands = [] /\
  u <> v /\ x.inst_id <> y.inst_id ==>
  (!h i a. dft_occ_gas_event i a
    (FUNPOW (dft_occ_oracle_next w C) h
      (dft_occ_init (DftOpen (DftEnter fn 0 s) [] n))) ==>
    ?t. dft_occ_gas_event i a
      (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C)) t
        (dft_occ_init (DftOpen
          (DftEnter (dft_gas_edit_fn bb0 pre x y post fn) 0 s) [] n)))) /\
  (!h i a. dft_occ_gas_event i a
    (FUNPOW (dft_occ_oracle_next w (dft_gas_edit_ctx bb0 pre x y post C)) h
      (dft_occ_init (DftOpen
        (DftEnter (dft_gas_edit_fn bb0 pre x y post fn) 0 s) [] n))) ==>
    ?t. dft_occ_gas_event i a
      (FUNPOW (dft_occ_oracle_next w C) t
        (dft_occ_init (DftOpen (DftEnter fn 0 s) [] n))))
Proof
  strip_tac >> conj_tac
  >- (rpt strip_tac >> irule dft_gas_orbit_event_forward >>
      metis_tac[dft_ordinary_sync_init]) >>
  rpt strip_tac >> irule dft_gas_orbit_event_backward >>
  metis_tac[dft_ordinary_sync_init]
QED
