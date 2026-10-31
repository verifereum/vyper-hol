(* Read-footprint congruence, independent of encoder execution. *)
Theory abiEncoderOpenInputFrame
Ancestors
  abiEncoderOpenInput abiEncoderInputFrame abiEncoderInput
  valueEncoding valueEncodingProps contractABI words list arithmetic

Theorem abi_encoder_open_input_mem_agree:
  !ei at av sb cap mem. abi_encoder_open_input ei at av sb cap mem ==>
  !mem'. mem_bytes_at sb cap mem = mem_bytes_at sb cap mem' ==>
    abi_encoder_open_input ei at av sb cap mem'
Proof
  ho_match_mp_tac abi_encoder_open_input_ind >> rpt conj_tac
  >- (rpt strip_tac >> irule abiEncoderOpenInputTheory.word >> simp[] >>
      drule abi_encoder_window_slice >>
      disch_then (qspecl_then [`0`, `32`] mp_tac) >> simp[])
  >- (rpt strip_tac >> irule abiEncoderOpenInputTheory.copy >> simp[] >>
      drule abi_encoder_window_slice >>
      disch_then (qspecl_then [`0`, `sz`] mp_tac) >> simp[])
  >- (rpt strip_tac >> (irule abiEncoderOpenInputTheory.bytes >> simp[] >>
      conj_tac
      >- (drule abi_encoder_window_word >>
          disch_then (qspec_then `0` mp_tac) >> simp[]) >>
      drule abi_encoder_window_slice >>
      disch_then (qspecl_then [`32`, `LENGTH bs`] mp_tac) >> simp[]))
  >- (rpt strip_tac >>
      rename1 `32 + LENGTH avs * mem_sz <= capacity` >>
      irule abiEncoderOpenInputTheory.open_array >> simp[] >>
      reverse conj_tac
      >- (drule abi_encoder_window_word >>
          disch_then (qspec_then `0` mp_tac) >> simp[]) >>
      rpt strip_tac >> fs[AC ADD_COMM ADD_ASSOC, MULT_COMM] >>
      first_x_assum irule >> simp[] >>
      irule EQ_SYM >> irule abi_encoder_window_slice >>
      qexists_tac `capacity` >> simp[] >>
      `32 + i * mem_sz + mem_sz <= capacity` by
        (irule abi_encoder_array_slot_bound >>
         qexists_tac `LENGTH avs` >> simp[MULT_COMM]) >> decide_tac) >>
  rpt strip_tac >> irule abiEncoderOpenInputTheory.complex >> simp[] >>
  qexists_tac `ats` >> simp[] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`i`, `ei`, `abi_sz`, `mem_sz`, `dyn`] mp_tac) >>
  simp[] >> strip_tac >> simp[] >> first_x_assum irule >>
  irule EQ_SYM >> irule abi_encoder_window_slice >>
  qexists_tac `cap` >> simp[] >>
  `i < LENGTH infos` by simp[] >>
  drule_all abi_encoder_member_slot_bound >> decide_tac
QED

Theorem abi_encoder_open_input_empty_memory:
  abi_encoder_open_input ei at av sb 0 mem ==>
  abi_encoder_open_input ei at av sb 0 mem'
Proof
  strip_tac >> drule abi_encoder_open_input_mem_agree >>
  disch_then (qspec_then `mem'` mp_tac) >> simp[mem_bytes_at_def]
QED

Theorem abi_encoder_zero_aware_separation:
  venomMemDefs$regions_disjoint (sb,cap) (d,n) <=>
  cap = 0 \/ n = 0 \/ sb + cap <= d \/ d + n <= sb
Proof
  simp[venomMemDefsTheory.regions_disjoint_def] >> metis_tac[]
QED
