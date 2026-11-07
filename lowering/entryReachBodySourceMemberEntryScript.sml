Theory entryReachBodySourceMemberEntry
Ancestors
  entryReachBodyMemberInputs entryReachBodySourceMemory entryReachBodySourceLayout
  entryReachBodyMemberSetup abiDecoderCoherence abiDecoderMembers
  abiCanonicalHeadSize abiDecoderMemberBody abiDecoderMemberSlice entryReachBodyLayoutWindows
  abiDecodeRanges contractABI list rich_list arithmetic words byte
  valueEncodingProps valueEncodingProofs valueEncoding

Definition entry_source_metadata_def:
  entry_source_metadata ce env sf ty tv di av v <=>
    entry_abi_support env ty /\ evaluate_type env ty = SOME tv /\
    value_has_type tv v /\ vyper_to_abi env ty v = SOME av /\
    di = type_to_abi_dec_info sf ce ty /\
    type_memory_size tv = type_memory_bytes ce ty
End

Definition entry_source_members_def:
  entry_source_members ce env sf [] [] [] [] = T /\
  entry_source_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) =
    (abi_decoder_coherent ce env sf ty tv /\
     entry_source_metadata ce env sf ty tv (type_to_abi_dec_info sf ce ty) av v /\
     entry_source_members ce env sf tys tvs avs vs) /\
  entry_source_members ce env sf _ _ _ _ = F
End

Theorem entry_source_members_layout[local]:
  !tys tvs avs vs. entry_source_members ce env sf tys tvs avs vs ==>
  LIST_REL abi_encoder_layout_valid (MAP (vyper_to_abi_type env) tys) avs /\
  LENGTH tys = LENGTH avs
Proof
  Induct >> Cases_on `tvs` >> Cases_on `avs` >> Cases_on `vs` >>
  simp[entry_source_members_def, entry_source_metadata_def] >>
  rpt strip_tac >> simp[] >>
  metis_tac[entry_source_conversion_layout]
QED

Theorem entry_layout_member_offset_load[local]:
  LIST_REL abi_encoder_layout_valid (pre ++ aty::post) (pvs ++ av::rest) /\
  LENGTH pre = LENGTH pvs /\ is_dynamic aty /\
  E = enc (Tuple (pre ++ aty::post)) (ListV (pvs ++ av::rest)) /\
  mem_bytes_at sb (LENGTH E) (abi_decode_source opc s) = E /\
  sb + LENGTH E < dimword (:256) ==>
  abi_decode_load opc
    (n2w (sb + SUM (MAP abi_member_head_size pre)) : 256 word) s =
    n2w (head_lengths (pre ++ aty::post) 0 +
         SUM (MAP2 abi_member_tail_size pre pvs))
Proof
  strip_tac >> drule_all entry_layout_member_head_window >>
  simp_tac bool_ss [LET_THM] >>
  asm_simp_tac bool_ss [abi_member_head_size_def] >> strip_tac >>
  `SUM (MAP abi_member_head_size pre) + 32 <= LENGTH E` by
    (qpat_x_assum `TAKE 32 _ = _` (mp_tac o AP_TERM ``LENGTH : word8 list -> num``) >>
     pure_rewrite_tac [LENGTH_TAKE_EQ, LENGTH_DROP] >>
     asm_simp_tac (srw_ss()) [Excl "enc_def"] >> decide_tac) >>
  `sb + SUM (MAP abi_member_head_size pre) < dimword (:256)` by decide_tac >>
  drule_all abi_decode_load_window >>
  disch_then (qspecl_then [`s`, `opc`] SUBST1_TAC) >>
  asm_rewrite_tac[] >>
  asm_simp_tac bool_ss [enc_number_def] >>
  irule word_of_bytes_word_to_bytes >> simp[dividesTheory.divides_def]
QED

Theorem entry_layout_member_inputs[local]:
  LIST_REL abi_encoder_layout_valid (pre ++ aty::post) (pvs ++ av::rest) /\
  LENGTH pre = LENGTH pvs /\
  E = enc (Tuple (pre ++ aty::post)) (ListV (pvs ++ av::rest)) /\
  mem_bytes_at sb (LENGTH E) (abi_decode_source CALLDATALOAD s) = E /\
  sb + LENGTH E < dimword (:256) /\
  off = abi_tuple_child_offset (pre ++ aty::post) (pvs ++ av::rest) (LENGTH pre) /\
  ao = SUM (MAP abi_member_head_size pre) ==>
  (is_dynamic aty ==>
    abi_decode_load CALLDATALOAD (n2w (sb+ao) : bytes32) s = n2w off /\
    sb+off < dimword (:256)) /\
  off = (if is_dynamic aty then head_lengths (pre ++ aty::post) 0 +
           SUM (MAP2 abi_member_tail_size pre pvs)
         else ao) /\
  mem_bytes_at (sb+off) (LENGTH (enc aty av)) (abi_decode_source CALLDATALOAD s) =
    enc aty av /\
  sb+off+LENGTH (enc aty av) < dimword (:256)
Proof
  strip_tac >>
  `TAKE (LENGTH pre) (pvs ++ av::rest) = pvs` by
    metis_tac[TAKE_LENGTH_APPEND] >>
  `off = (if is_dynamic aty then head_lengths (pre ++ aty::post) 0 +
            SUM (MAP2 abi_member_tail_size pre pvs) else ao)` by
    asm_simp_tac bool_ss [abi_tuple_child_offset_append] >>
  `mem_bytes_at (sb+off) (LENGTH (enc aty av)) (abi_decode_source CALLDATALOAD s) =
     enc aty av /\ sb+off+LENGTH (enc aty av) < dimword (:256)` by
    metis_tac[entry_layout_member_source] >>
  `sb+off < dimword (:256)` by decide_tac >>
  conj_tac
  >- (strip_tac >> drule_all entry_layout_member_offset_load >> metis_tac[]) >>
  asm_rewrite_tac[]
QED

Theorem entry_source_members_child_facts[local]:
  entry_source_members ce env sf pretys pretvs preavs prevs /\
  entry_source_members ce env sf (ty::tys) (tv::tvs) (av::avs) (v::vs) /\
  ats = MAP (vyper_to_abi_type env) (pretys ++ ty::tys) /\
  vals = preavs ++ av::avs /\
  vo = SUM (MAP (type_memory_bytes ce) pretys) /\
  outsz = SUM (MAP (type_memory_bytes ce) (pretys ++ ty::tys)) /\
  ei = type_to_abi_dec_info sf ce ty ==>
  LIST_REL abi_encoder_layout_valid ats vals /\
  LENGTH pretys = LENGTH preavs /\
  abi_decoder_coherent ce env sf ty tv /\
  entry_source_metadata ce env sf ty tv ei av v /\
  vo + type_memory_size tv <= outsz
Proof
  strip_tac >>
  drule_all entry_source_members_layout >> strip_tac >>
  qpat_assum `entry_source_members _ _ _ (ty::tys) _ _ _`
    (strip_assume_tac o REWRITE_RULE [entry_source_members_def]) >>
  drule_all entry_source_members_layout >> strip_tac >>
  `LIST_REL abi_encoder_layout_valid
      (MAP (vyper_to_abi_type env) pretys) preavs` by
    metis_tac[entry_source_members_layout] >>
  `LIST_REL abi_encoder_layout_valid
      (MAP (vyper_to_abi_type env) tys) avs` by
    metis_tac[entry_source_members_layout] >>
  `abi_encoder_layout_valid (vyper_to_abi_type env ty) av` by
    (fs[entry_source_metadata_def] >> metis_tac[entry_source_conversion_layout]) >>
  `type_memory_size tv = type_memory_bytes ce ty` by
    fs[entry_source_metadata_def] >>
  `LENGTH pretys = LENGTH preavs` by metis_tac[entry_source_members_layout] >>
  asm_simp_tac bool_ss [MAP_APPEND, MAP, LIST_REL_def] >>
  simp[SUM_APPEND, MAP_APPEND] >>
  simp[LIST_REL_APPEND_EQ, LIST_REL_def]
QED
