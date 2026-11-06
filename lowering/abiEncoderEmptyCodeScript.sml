(* Structural boundary for zero-output encoder fragments. *)
Theory abiEncoderEmptyCode
Ancestors
  abiEncoderWindow abiEncoderOpenInput abiEncoderInput abiDecodeRanges
  abiEncoder contractABI valueEncoding valueEncodingProofs list rich_list words byte arithmetic

Definition abi_encoder_empty_def:
  abi_encoder_empty AbiPrimWord = F /\
  abi_encoder_empty (AbiCopy sz) = (sz = 0) /\
  abi_encoder_empty (AbiBytestring n) = F /\
  abi_encoder_empty (AbiDynArray ei asz msz dyn) = F /\
  abi_encoder_empty (AbiComplex infos) = abi_encoder_empty_members infos /\
  abi_encoder_empty_members [] = T /\
  abi_encoder_empty_members ((ei,asz,msz,dyn)::infos) =
    (abi_encoder_empty ei /\ asz = 0 /\ ~dyn /\ abi_encoder_empty_members infos)
End

Theorem abi_encoder_empty_members_every:
  !infos. abi_encoder_empty_members infos <=>
    EVERY (\(ei,asz,msz,dyn). abi_encoder_empty ei /\ asz = 0 /\ ~dyn) infos
Proof
  Induct >> simp[abi_encoder_empty_def] >>
  qx_gen_tac `info` >> PairCases_on `info` >> simp[abi_encoder_empty_def] >> metis_tac[]
QED

Theorem abi_encoder_empty_nested_probe:
  abi_encoder_empty (AbiComplex [(AbiComplex [(AbiCopy 0,0,19,F)],0,23,F)])
Proof
  simp[abi_encoder_empty_def]
QED

Theorem abi_encoder_window_empty:
  !ei at av sb cap mem. abi_encoder_window_input ei at av sb cap mem ==>
  LENGTH (enc at av) = 0 ==> abi_encoder_empty ei
Proof
  ho_match_mp_tac abi_encoder_window_input_strongind >> rpt conj_tac
  >- (rpt strip_tac >> drule (cj 1 enc_has_static_length) >> simp[])
  >- (rpt strip_tac >> drule (cj 1 enc_has_static_length) >>
      gvs[abi_encoder_empty_def])
  >- (rpt strip_tac >> gvs[enc_def] >>
      qpat_x_assum `word_to_bytes _ _ = []`
        (mp_tac o Q.AP_TERM `LENGTH`) >> simp[LENGTH_word_to_bytes])
  >- (rpt gen_tac >> strip_tac >> rename1 `abi_sz = abi_member_head_size ct` >>
      `LIST_REL abi_encoder_layout_valid (REPLICATE (LENGTH avs) ct) avs` by
        (simp[LIST_REL_EL_EQN] >> rpt strip_tac >>
         first_x_assum (qspec_then `n` mp_tac) >> simp[EL_REPLICATE] >>
         metis_tac[abi_encoder_window_input_valid, abi_encoder_structural_valid_layout]) >>
      drule abi_encoder_open_enc_tuple_length >>
      disch_then (qspecl_then [`head_lengths (REPLICATE (LENGTH avs) ct) 0`,
        `0`, `[word_to_bytes (n2w (LENGTH avs):bytes32) T]`, `[]`] mp_tac) >>
      simp[Once enc_def, LENGTH_word_to_bytes] >>
      rpt strip_tac >> gvs[]) >>
  rpt strip_tac >>
  `LIST_REL abi_encoder_layout_valid ats avs` by
    (simp[LIST_REL_EL_EQN] >> rpt strip_tac >>
     `n < LENGTH infos` by decide_tac >>
     Cases_on `EL n infos` >> rename1 `EL n infos = (child,rest)` >> PairCases_on `rest` >>
     first_x_assum (qspec_then `n` mp_tac) >> simp[] >>
     metis_tac[abi_encoder_window_input_valid, abi_encoder_structural_valid_layout]) >>
  `LENGTH (enc at (ListV avs)) = LENGTH (enc (Tuple ats) (ListV avs))` by
    (gvs[abi_encoder_tuple_type_def, enc_def]) >>
  `SUM (MAP abi_member_head_size ats) = 0` by
    (drule abi_encoder_open_tuple_length >> decide_tac) >>
  simp[abi_encoder_empty_def, abi_encoder_empty_members_every, EVERY_EL] >>
  qx_gen_tac `i` >> strip_tac >>
  Cases_on `EL i infos` >> rename1 `EL i infos = (child,rest)` >> PairCases_on `rest` >>
  first_x_assum (qspec_then `i` mp_tac) >> simp[] >> strip_tac >>
  `abi_member_head_size (EL i ats) = 0` by
    (gvs[SUM_eq_0, MEM_MAP] >> first_x_assum irule >>
     qexists_tac `EL i ats` >> simp[MEM_EL] >> metis_tac[]) >>
  Cases_on `is_dynamic (EL i ats)` >> gvs[abi_member_head_size_def] >>
  `LENGTH (enc (EL i ats) (EL i avs)) = 0` by
    (gvs[LIST_REL_EL_EQN, abi_encoder_layout_valid_def] >>
     metis_tac[LENGTH_NIL]) >>
  metis_tac[LENGTH_NIL]
QED
