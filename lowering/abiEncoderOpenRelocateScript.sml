Theory abiEncoderOpenRelocate
Ancestors
  abiEncoderOpenInput abiEncoderOpenInputFrame abiEncoderInputFrame abiEncoderMemory abiEncoderInput
  abiStaticAggregateProps valueEncoding valueEncodingProps contractABI words list arithmetic

Theorem abi_encoder_open_input_relocate:
  !ei at av sb cap mem. abi_encoder_open_input ei at av sb cap mem ==>
  !db mem'. mem_bytes_at sb cap mem = mem_bytes_at db cap mem' ==>
    abi_encoder_open_input ei at av db cap mem'
Proof
  ho_match_mp_tac abi_encoder_open_input_ind >> rpt conj_tac
  >- (rpt strip_tac >> irule abiEncoderOpenInputTheory.word >> simp[] >>
      drule abi_encoder_window_slice >>
      disch_then (qspecl_then [`0`, `32`] mp_tac) >> simp[])
  >- (rpt strip_tac >> irule abiEncoderOpenInputTheory.copy >> simp[] >>
      drule abi_encoder_window_slice >>
      disch_then (qspecl_then [`0`, `sz`] mp_tac) >> simp[])
  >- (rpt strip_tac >>
      `32 <= cap` by decide_tac >>
      `mem_word_at db mem' = n2w (LENGTH bs)` by
        (mp_tac (Q.INST [`off` |-> `0`] abi_encoder_window_word) >>
         asm_simp_tac (srw_ss()) []) >>
      `mem_bytes_at (db+32) (LENGTH bs) mem' = bs` by
        (mp_tac (Q.INST [`off` |-> `32`, `len` |-> `LENGTH (bs:word8 list)`]
          abi_encoder_window_slice) >> asm_simp_tac bool_ss []) >>
      irule abiEncoderOpenInputTheory.bytes >> simp[])
  >- (rpt strip_tac >>
      rename1 `32+LENGTH avs*mem_sz <= capacity` >>
      `32 <= capacity` by decide_tac >>
      irule abiEncoderOpenInputTheory.open_array >> simp[] >>
      reverse conj_tac
      >- (drule abi_encoder_window_word >>
          disch_then (qspec_then `0` mp_tac) >> simp[]) >>
      rpt strip_tac >> first_x_assum irule >> simp[] >>
      irule EQ_SYM >>
      `32+i*mem_sz+mem_sz <= capacity` by
        (irule abi_encoder_array_slot_bound >> qexists_tac `LENGTH avs` >> simp[]) >>
      mp_tac (Q.INST [`cap` |-> `capacity`, `off` |-> `32+i*mem_sz`, `len` |-> `mem_sz`] abi_encoder_window_slice) >>
      asm_simp_tac (srw_ss()) [AC ADD_COMM ADD_ASSOC]) >>
  rpt strip_tac >> irule abiEncoderOpenInputTheory.complex >> simp[] >>
  qexists_tac `ats` >> simp[] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`i`, `ei`, `abi_sz`, `mem_sz`, `dyn`] mp_tac) >>
  simp[] >> strip_tac >> simp[] >> first_x_assum irule >>
  `i < LENGTH infos` by simp[] >>
  `abi_encoder_member_span (TAKE i infos)+mem_sz <= cap` by
    (drule_all abi_encoder_member_slot_bound >> decide_tac) >>
  irule EQ_SYM >>
  mp_tac (Q.INST [`off` |-> `abi_encoder_member_span (TAKE i infos)`, `len` |-> `mem_sz`]
    abi_encoder_window_slice) >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_open_input_relocate_capacity:
  abi_encoder_open_input ei at av sb cap mem /\ cap <= n /\
  mem_bytes_at sb cap mem = mem_bytes_at db cap mem' ==>
  abi_encoder_open_input ei at av db n mem'
Proof
  strip_tac >> drule_all abi_encoder_open_input_relocate >> strip_tac >>
  irule abi_encoder_open_input_capacity >> goal_assum (drule_at Any) >> simp[]
QED

Theorem abi_encoder_open_input_mcopy_prefix:
  abi_encoder_open_input ei at av sb cap s.vs_memory /\ cap <= n ==>
  abi_encoder_open_input ei at av db n (mcopy db sb n s).vs_memory
Proof
  strip_tac >> irule abi_encoder_open_input_relocate_capacity >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  irule EQ_SYM >>
  mp_tac (Q.INST [`cap` |-> `n`, `off` |-> `0`, `len` |-> `cap`,
    `mem` |-> `s.vs_memory`, `mem'` |-> `(mcopy db sb n s).vs_memory`]
    abi_encoder_window_slice) >> simp[mcopy_mem_bytes_at_same]
QED
