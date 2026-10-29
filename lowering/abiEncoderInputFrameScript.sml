(* Complete encoder sources depend only on their declared memory window. *)
Theory abiEncoderInputFrame
Ancestors
  abiEncoderInput abiEncoderMemory abiStaticPrimitiveProps abiDecoderFrame abiDecoderContract
  valueEncoding valueEncodingProps valueEncodingProofs venomState contractABI words list
  rich_list arithmetic

Theorem abi_encoder_window_slice:
  mem_bytes_at sb cap mem = mem_bytes_at db cap mem' /\ off+len <= cap ==>
  mem_bytes_at (db+off) len mem' = mem_bytes_at (sb+off) len mem
Proof
  strip_tac >> irule EQ_SYM >> irule mem_bytes_at_translated_window >>
  qexists_tac `cap` >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_window_word:
  mem_bytes_at sb cap mem = mem_bytes_at db cap mem' /\ off+32 <= cap ==>
  mem_word_at (db+off) mem' = mem_word_at (sb+off) mem
Proof
  strip_tac >> simp_tac bool_ss [mem_word_at_bytes] >>
  AP_TERM_TAC >> drule_all abi_encoder_window_slice >> simp[]
QED

Theorem abi_encoder_word_relocate:
  abi_encoder_input AbiPrimWord at av sb cap mem /\
  mem_bytes_at sb cap mem = mem_bytes_at db cap mem' ==>
  abi_encoder_input AbiPrimWord at av db cap mem'
Proof
  simp_tac bool_ss [abi_encoder_input_word_iff] >> strip_tac >>
  asm_simp_tac bool_ss [] >>
  mp_tac (Q.INST [`off` |-> `0`, `len` |-> `32`] abi_encoder_window_slice) >>
  asm_simp_tac (srw_ss()) []
QED

Theorem abi_encoder_copy_relocate:
  abi_encoder_input (AbiCopy sz) at av sb cap mem /\
  mem_bytes_at sb cap mem = mem_bytes_at db cap mem' ==>
  abi_encoder_input (AbiCopy sz) at av db cap mem'
Proof
  simp_tac bool_ss [abi_encoder_input_copy_iff] >> strip_tac >>
  asm_simp_tac bool_ss [] >>
  mp_tac (Q.INST [`off` |-> `0`, `len` |-> `sz`] abi_encoder_window_slice) >>
  asm_simp_tac (srw_ss()) []
QED

Theorem abi_encoder_bytes_relocate:
  abi_encoder_input (AbiBytestring maxlen) at av sb cap mem /\
  mem_bytes_at sb cap mem = mem_bytes_at db cap mem' ==>
  abi_encoder_input (AbiBytestring maxlen) at av db cap mem'
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_encoder_input _ _ _ _ _ _`
    (qx_choose_then `bs` (MAP_EVERY assume_tac o CONJUNCTS) o REWRITE_RULE [abi_encoder_input_bytes_iff]) >>
  `32 <= cap` by decide_tac >>
  `mem_word_at db mem' = n2w (LENGTH bs)` by
    (mp_tac (Q.INST [`off` |-> `0`] abi_encoder_window_word) >> asm_simp_tac (srw_ss()) []) >>
  `mem_bytes_at (db+32) (LENGTH bs) mem' = bs` by
    (mp_tac (Q.INST [`off` |-> `32`, `len` |-> `LENGTH (bs:word8 list)`]
      abi_encoder_window_slice) >> asm_simp_tac bool_ss []) >>
  simp_tac bool_ss [abi_encoder_input_bytes_iff] >> qexists_tac `bs` >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_array_relocate:
  has_type (Array NONE ct) (ListV avs) /\
  abi_sz = abi_member_head_size ct /\ dyn = is_dynamic ct /\
  32 + LENGTH avs * mem_sz <= cap /\ mem_word_at sb mem = n2w (LENGTH avs) /\
  (!i. i < LENGTH avs ==> !b m.
    mem_bytes_at (sb+32+i*mem_sz) mem_sz mem = mem_bytes_at b mem_sz m ==>
    abi_encoder_input ei ct (EL i avs) b mem_sz m) ==>
  !db mem'. mem_bytes_at sb cap mem = mem_bytes_at db cap mem' ==>
    abi_encoder_input (AbiDynArray ei abi_sz mem_sz dyn) (Array NONE ct) (ListV avs) db cap mem'
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> rpt gen_tac >> strip_tac >>
  `32 <= cap` by decide_tac >>
  `mem_word_at db mem' = n2w (LENGTH avs)` by
    (mp_tac (Q.INST [`off` |-> `0`] abi_encoder_window_word) >> asm_simp_tac (srw_ss()) []) >>
  irule abiEncoderInputTheory.array >> asm_simp_tac bool_ss [] >>
  qx_gen_tac `i` >> strip_tac >>
  `32+i*mem_sz+mem_sz <= cap` by
    (irule abi_encoder_array_slot_bound >> qexists_tac `LENGTH avs` >> asm_simp_tac bool_ss []) >>
  `mem_bytes_at (sb+32+i*mem_sz) mem_sz mem = mem_bytes_at (db+32+i*mem_sz) mem_sz mem'` by
    (mp_tac (Q.INST [`off` |-> `32+i*mem_sz`, `len` |-> `mem_sz`] abi_encoder_window_slice) >>
     asm_simp_tac (srw_ss()) [AC ADD_COMM ADD_ASSOC]) >>
  first_x_assum irule >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_complex_relocate:
  abi_encoder_tuple_type at ats /\ has_type at (ListV avs) /\
  LENGTH infos = LENGTH ats /\ LENGTH ats = LENGTH avs /\
  abi_encoder_member_span infos <= cap /\
  (!i ei abi_sz mem_sz dyn. i < LENGTH infos /\ EL i infos = (ei,abi_sz,mem_sz,dyn) ==>
    abi_sz = abi_member_head_size (EL i ats) /\ dyn = is_dynamic (EL i ats) /\
    (!b m. mem_bytes_at (sb+abi_encoder_member_span (TAKE i infos)) mem_sz mem =
      mem_bytes_at b mem_sz m ==> abi_encoder_input ei (EL i ats) (EL i avs) b mem_sz m)) ==>
  !db mem'. mem_bytes_at sb cap mem = mem_bytes_at db cap mem' ==>
    abi_encoder_input (AbiComplex infos) at (ListV avs) db cap mem'
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> rpt gen_tac >> strip_tac >>
  irule abiEncoderInputTheory.complex >> asm_simp_tac bool_ss [] >>
  qexists_tac `ats` >> asm_simp_tac bool_ss [] >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!i ei abi_sz mem_sz dyn. _`
    (qspecl_then [`i`, `ei`, `abi_sz`, `mem_sz`, `dyn`] mp_tac) >>
  asm_simp_tac bool_ss [] >> strip_tac >> asm_simp_tac bool_ss [] >>
  `i < LENGTH infos` by asm_simp_tac (srw_ss()) [] >>
  `abi_encoder_member_span (TAKE i infos)+mem_sz <= cap` by
    (drule_all abi_encoder_member_slot_bound >> decide_tac) >>
  `mem_bytes_at (sb+abi_encoder_member_span (TAKE i infos)) mem_sz mem =
    mem_bytes_at (db+abi_encoder_member_span (TAKE i infos)) mem_sz mem'` by
    (mp_tac (Q.INST [`off` |-> `abi_encoder_member_span (TAKE i infos)`, `len` |-> `mem_sz`]
      abi_encoder_window_slice) >> asm_simp_tac bool_ss []) >>
  first_x_assum irule >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_input_relocate:
  !ei at av sb cap mem. abi_encoder_input ei at av sb cap mem ==>
  !db mem'. mem_bytes_at sb cap mem = mem_bytes_at db cap mem' ==>
    abi_encoder_input ei at av db cap mem'
Proof
  ho_match_mp_tac abi_encoder_input_ind >> rpt conj_tac
  >- (rpt strip_tac >> irule abi_encoder_word_relocate >>
      qexistsl_tac [`mem`, `sb`] >> asm_simp_tac (srw_ss()) [abi_encoder_input_word_iff])
  >- (rpt strip_tac >> irule abi_encoder_copy_relocate >>
      qexistsl_tac [`mem`, `sb`] >> asm_simp_tac (srw_ss()) [abi_encoder_input_copy_iff])
  >- (rpt strip_tac >> irule abi_encoder_bytes_relocate >>
      qexistsl_tac [`mem`, `sb`] >> gvs[abi_encoder_input_bytes_iff, LET_THM])
  >- (rpt gen_tac >> strip_tac >>
      rename1 `has_type (Array NONE ct) (ListV avs)` >>
      rename1 `32+LENGTH avs*mem_sz <= capacity` >>
      mp_tac (Q.INST [`cap` |-> `capacity`] abi_encoder_array_relocate) >> asm_simp_tac bool_ss []) >>
  rpt gen_tac >> strip_tac >> mp_tac abi_encoder_complex_relocate >> fs[]
QED

Theorem abi_encoder_input_mem_agree:
  abi_encoder_input ei at av sb cap mem /\
  mem_bytes_at sb cap mem = mem_bytes_at sb cap mem' ==>
  abi_encoder_input ei at av sb cap mem'
Proof
  strip_tac >> drule abi_encoder_input_relocate >>
  disch_then (qspecl_then [`sb`, `mem'`] mp_tac) >> asm_simp_tac bool_ss []
QED

Theorem abi_encoder_input_frame:
  abi_encoder_input ei at av sb cap s.vs_memory /\
  abi_decode_footprint_frame fp s t /\ abi_footprint_disjoint sb cap fp ==>
  abi_encoder_input ei at av sb cap t.vs_memory
Proof
  strip_tac >>
  `mem_bytes_at sb cap s.vs_memory = mem_bytes_at sb cap t.vs_memory` by
    (drule_all abi_decode_footprint_frame_slice >> simp[EQ_SYM_EQ]) >>
  drule_all abi_encoder_input_mem_agree >> simp[]
QED

Theorem abi_encoder_input_mcopy:
  abi_encoder_input ei at av sb cap s.vs_memory ==>
  abi_encoder_input ei at av db cap (mcopy db sb cap s).vs_memory
Proof
  strip_tac >> drule abi_encoder_input_relocate >>
  disch_then (qspecl_then [`db`, `(mcopy db sb cap s).vs_memory`] mp_tac) >>
  simp[mcopy_mem_bytes_at_same]
QED
