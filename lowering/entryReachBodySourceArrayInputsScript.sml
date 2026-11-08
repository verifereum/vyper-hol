Theory entryReachBodySourceArrayInputs
Ancestors
  entryReachBodySourceArrayBounds entryReachBodySourceMemberEntry
  entryReachBodySourceLayout entryReachBodyConversionSupport
  abiEncoderSourceTransport abiDecoderCoherence abiDecoderMembers
  vyperTyping vyperABI vyperValue vyperValueOperation
  contractABI abiEncoder list rich_list arithmetic words supportedTypes compileEnv
  abiCanonicalHeadSize abiCanonicalWindows abiDecodeRanges abiDecoderArraySlice abiDecoderTypedContract
  entryReachBodyMemberInputs entryReachBodyLayoutWindows byte

Theorem entry_source_dynamic_array_child_metadata:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  entry_source_metadata ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV avs) (ArrayV (DynArrayV xs)) /\ j < LENGTH xs ==>
  LENGTH xs = LENGTH avs /\ LENGTH xs <= maxn /\
  abi_decoder_coherent ce env sf ty tv /\
  entry_source_metadata ce env sf ty tv (type_to_abi_dec_info sf ce ty) (EL j avs) (EL j xs) /\
  LIST_REL abi_encoder_layout_valid (REPLICATE (LENGTH avs) (vyper_to_abi_type env ty)) avs /\
  abi_embedded_static_size ce.ce_struct_fields ty = abi_member_head_size (vyper_to_abi_type env ty) /\
  type_memory_bytes ce (ArrayT ty (Dynamic maxn)) = 32 + maxn * type_memory_bytes ce ty
Proof
  strip_tac >>
  `LENGTH xs = LENGTH avs /\ LENGTH xs <= maxn` by
    (irule entry_source_dynamic_array_alignment >>
     gvs[entry_source_metadata_def, Excl "enc_def"] >> metis_tac[]) >>
  gvs[abi_decoder_coherent_array_iff, entry_source_metadata_def, Excl "enc_def"] >>
  `abi_decoder_header ce env ty tv` by metis_tac[abi_decoder_coherent_header] >>
  gvs[Once entry_abi_support_cases, supported_scalar_type_def, supported_word_type_def,
      supported_string_type_def, Excl "enc_def"] >>
  gvs[value_has_type_def, AllCaseEqs(), Excl "enc_def"] >>
  drule abi_encoder_same_conversion >> strip_tac >>
  qpat_x_assum `LENGTH avs = LENGTH xs` kall_tac >>
  `!i. i < LENGTH avs ==> abi_encoder_layout_valid (vyper_to_abi_type env ty) (EL i avs)` by
    (rpt strip_tac >> irule entry_source_conversion_layout >>
     qpat_x_assum `all_have_type _ _` (mp_tac o REWRITE_RULE [all_have_type_EVERY, EVERY_EL]) >>
     qpat_x_assum `abi_decoder_header ce env ty tv` (mp_tac o REWRITE_RULE [abi_decoder_header_def]) >>
     metis_tac[]) >>
  qpat_x_assum `all_have_type _ _` (mp_tac o REWRITE_RULE [all_have_type_EVERY, EVERY_EL]) >>
  qpat_x_assum `abi_decoder_header ce env ty tv` (mp_tac o REWRITE_RULE [abi_decoder_header_def]) >>
  rpt strip_tac >>
  simp[LIST_REL_EL_EQN, EL_REPLICATE, Once type_memory_bytes_def, Excl "enc_def"]
QED

Theorem source_array_tuple_window[local]:
  LIST_REL abi_encoder_layout_valid (REPLICATE (LENGTH avs) aty) avs /\
  mem_bytes_at sb (LENGTH (enc (Array NONE aty) (ListV avs))) mem =
    enc (Array NONE aty) (ListV avs) /\
  sb + LENGTH (enc (Array NONE aty) (ListV avs)) < dimword (:256) ==>
  mem_bytes_at (sb+32) (LENGTH (enc (Tuple (REPLICATE (LENGTH avs) aty)) (ListV avs))) mem =
    enc (Tuple (REPLICATE (LENGTH avs) aty)) (ListV avs) /\
  sb+32+LENGTH (enc (Tuple (REPLICATE (LENGTH avs) aty)) (ListV avs)) < dimword (:256)
Proof
  simp_tac bool_ss [canonical_array_tuple] >> strip_tac >>
  `LENGTH (enc_number (Uint 256) (NumV (LENGTH avs))) = 32` by
    simp[enc_number_def, LENGTH_word_to_bytes] >>
  conj_tac
  >- (qpat_x_assum `LENGTH (enc_number _ _) = 32` (fn th => once_rewrite_tac[GSYM th]) >>
      irule abi_decoder_source_subwindow >> qexists `[]` >> simp[Excl "enc_def"]) >>
  gvs[LENGTH_APPEND, Excl "enc_def"]
QED

Theorem source_array_member_source[local]:
  LIST_REL abi_encoder_layout_valid (REPLICATE (LENGTH (pre++av::post)) aty) (pre++av::post) /\
  mem_bytes_at sb (LENGTH (enc (Array NONE aty) (ListV (pre++av::post)))) mem =
    enc (Array NONE aty) (ListV (pre++av::post)) /\
  sb + LENGTH (enc (Array NONE aty) (ListV (pre++av::post))) < dimword (:256) ==>
  mem_bytes_at (sb + abi_array_child_offset NONE aty (pre++av::post) (LENGTH pre))
    (LENGTH (enc aty av)) mem = enc aty av /\
  sb + abi_array_child_offset NONE aty (pre++av::post) (LENGTH pre) + LENGTH (enc aty av) < dimword (:256)
Proof
  strip_tac >> drule_all source_array_tuple_window >> strip_tac >>
  `REPLICATE (LENGTH (pre++av::post)) aty =
    REPLICATE (LENGTH pre) aty ++ aty::REPLICATE (LENGTH post) aty` by
    simp_tac bool_ss [LENGTH_APPEND, LENGTH, GSYM REPLICATE, REPLICATE_APPEND] >>
  `SUM (MAP abi_member_head_size (REPLICATE (LENGTH pre) aty)) = LENGTH pre * abi_member_head_size aty /\
   head_lengths (REPLICATE (LENGTH (pre++av::post)) aty) 0 = LENGTH (pre++av::post) * abi_member_head_size aty /\
   SUM (MAP2 abi_member_tail_size (REPLICATE (LENGTH pre) aty) pre) =
     SUM (MAP (abi_member_tail_size aty) pre)` by
    simp[uniform_member_sizes, head_lengths_acc] >>
  qpat_x_assum `LIST_REL _ _ _` mp_tac >>
  qpat_assum `REPLICATE _ _ = _` (fn th => pure_rewrite_tac[th]) >> strip_tac >>
  drule entry_layout_member_source >>
  disch_then (qspec_then `sb+32` mp_tac) >>
  qpat_x_assum `REPLICATE _ _ = _` (fn th =>
    asm_simp_tac bool_ss [GSYM th, LENGTH_REPLICATE, uniform_member_sizes]) >>
  disch_then (qspec_then `mem` mp_tac o SIMP_RULE bool_ss [GSYM AND_IMP_INTRO]) >>
  asm_simp_tac bool_ss [] >> Cases_on `is_dynamic aty` >>
  asm_simp_tac bool_ss [abi_array_child_offset_append, ADD_ASSOC]
QED

Theorem entry_source_dynamic_array_child_window:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  entry_source_metadata ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV avs) (ArrayV (DynArrayV xs)) /\ j < LENGTH xs /\
  mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env (ArrayT ty (Dynamic maxn))) (ListV avs)))
    (abi_decode_source CALLDATALOAD s) = enc (vyper_to_abi_type env (ArrayT ty (Dynamic maxn))) (ListV avs) /\
  sb + LENGTH (enc (vyper_to_abi_type env (ArrayT ty (Dynamic maxn))) (ListV avs)) < dimword (:256) /\
  d + type_memory_bytes ce (ArrayT ty (Dynamic maxn)) < dimword (:256) ==>
  let off = abi_array_child_offset NONE (vyper_to_abi_type env ty) avs j;
      cell = d+32+j*type_memory_bytes ce ty in
  LENGTH xs = LENGTH avs /\ LENGTH xs <= maxn /\ LENGTH avs < dimword (:256) /\
  abi_decoder_coherent ce env sf ty tv /\
  entry_source_metadata ce env sf ty tv (type_to_abi_dec_info sf ce ty) (EL j avs) (EL j xs) /\
  mem_bytes_at (sb+off) (LENGTH (enc (vyper_to_abi_type env ty) (EL j avs)))
    (abi_decode_source CALLDATALOAD s) = enc (vyper_to_abi_type env ty) (EL j avs) /\
  sb+off+LENGTH (enc (vyper_to_abi_type env ty) (EL j avs)) < dimword (:256) /\
  cell < dimword (:256) /\
  cell+type_memory_bytes ce ty <= d+type_memory_bytes ce (ArrayT ty (Dynamic maxn))
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all entry_source_dynamic_array_child_metadata >> strip_tac >>
  `LENGTH avs < dimword (:256)` by
    (irule entry_source_array_count_word_bound >>
     qexistsl [`Dynamic maxn`, `env`, `sb`, `ArrayTV tv (Dynamic maxn)`, `ty`, `ArrayV (DynArrayV xs)`] >>
     fs[entry_source_metadata_def, Excl "enc_def"]) >>
  `j < LENGTH avs` by decide_tac >>
  `TAKE j avs ++ EL j avs::DROP (SUC j) avs = avs` by
    (qspec_then `j` (qspec_then `avs` mp_tac) TAKE_DROP_SUC >>
     asm_simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND]) >>
  `LENGTH (TAKE j avs) = j` by simp[LENGTH_TAKE] >>
  mp_tac (Q.INST [`pre` |-> `TAKE j avs`, `av` |-> `EL j avs`,
    `post` |-> `DROP (SUC j) avs`] (Q.GENL [`aty`, `mem`] source_array_member_source)) >>
  disch_then (qspecl_then [`vyper_to_abi_type env ty`, `abi_decode_source CALLDATALOAD s`] mp_tac) >>
  asm_simp_tac bool_ss [] >>
  impl_tac
  >- (qpat_x_assum `mem_bytes_at sb _ _ = _` mp_tac >>
      qpat_x_assum `sb + _ < _` mp_tac >>
      simp_tac bool_ss [vyper_to_abi_type_def]) >>
  strip_tac >> asm_simp_tac bool_ss [] >>
  irule abi_decoder_array_cell_window >>
  asm_simp_tac bool_ss [] >> decide_tac
QED

Theorem source_array_dynamic_head[local]:
  LIST_REL abi_encoder_layout_valid (REPLICATE (LENGTH (pre++av::post)) aty) (pre++av::post) /\
  is_dynamic aty ==>
  TAKE 32 (DROP (LENGTH pre * abi_member_head_size aty)
    (enc (Tuple (REPLICATE (LENGTH (pre++av::post)) aty)) (ListV (pre++av::post)))) =
  enc_number (Uint 256) (NumV
    (LENGTH (pre++av::post) * abi_member_head_size aty + SUM (MAP (abi_member_tail_size aty) pre)))
Proof
  strip_tac >>
  `REPLICATE (LENGTH (pre++av::post)) aty =
    REPLICATE (LENGTH pre) aty ++ aty::REPLICATE (LENGTH post) aty` by
    simp_tac bool_ss [LENGTH_APPEND, LENGTH, GSYM REPLICATE, REPLICATE_APPEND] >>
  qpat_x_assum `LIST_REL _ _ _` mp_tac >>
  qpat_assum `REPLICATE _ _ = _` (fn th => pure_rewrite_tac[th]) >> strip_tac >>
  drule entry_layout_member_head_window >>
  asm_simp_tac bool_ss [LET_THM, LENGTH_REPLICATE] >>
  qpat_x_assum `REPLICATE _ _ = _` (fn th =>
    asm_simp_tac bool_ss [GSYM th, uniform_member_sizes, head_lengths_acc, abi_member_head_size_def, ADD_CLAUSES])
QED

Theorem source_array_dynamic_offset_load[local]:
  LIST_REL abi_encoder_layout_valid (REPLICATE (LENGTH (pre++av::post)) aty) (pre++av::post) /\
  is_dynamic aty /\
  mem_bytes_at sb (LENGTH (enc (Array NONE aty) (ListV (pre++av::post))))
    (abi_decode_source CALLDATALOAD s) = enc (Array NONE aty) (ListV (pre++av::post)) /\
  sb + LENGTH (enc (Array NONE aty) (ListV (pre++av::post))) < dimword (:256) ==>
  abi_decode_load CALLDATALOAD
    (n2w (sb+32+LENGTH pre * abi_member_head_size aty) : bytes32) s =
  n2w (LENGTH (pre++av::post) * abi_member_head_size aty + SUM (MAP (abi_member_tail_size aty) pre))
Proof
  strip_tac >> drule_all source_array_tuple_window >> strip_tac >>
  drule_all source_array_dynamic_head >> strip_tac >>
  qmatch_asmsub_abbrev_tac `TAKE 32 (DROP ao bs)` >>
  `ao+32 <= LENGTH bs` by
    (qpat_x_assum `TAKE 32 _ = _` (mp_tac o AP_TERM ``LENGTH : word8 list -> num``) >>
     simp_tac (srw_ss()) [LENGTH_TAKE_EQ, LENGTH_DROP, enc_number_def, LENGTH_word_to_bytes] >>
     decide_tac) >>
  `sb+32+ao < dimword (:256)` by (fs[Abbr `bs`, Excl "enc_def"] >> decide_tac) >>
  drule_all abi_decode_load_window >>
  disch_then (qspecl_then [`s`, `CALLDATALOAD`] mp_tac) >>
  asm_simp_tac bool_ss [Abbr `bs`, Abbr `ao`] >>
  disch_then SUBST1_TAC >> asm_rewrite_tac[enc_number_def] >>
  irule word_of_bytes_word_to_bytes >> simp[dividesTheory.divides_def]
QED

Theorem entry_layout_dynamic_array_offset_inputs:
  LIST_REL abi_encoder_layout_valid (REPLICATE (LENGTH avs) aty) avs /\
  j < LENGTH avs /\
  mem_bytes_at sb (LENGTH (enc (Array NONE aty) (ListV avs)))
    (abi_decode_source CALLDATALOAD s) = enc (Array NONE aty) (ListV avs) /\
  sb + LENGTH (enc (Array NONE aty) (ListV avs)) < dimword (:256) ==>
  (is_dynamic aty ==>
    abi_decode_load CALLDATALOAD (n2w (sb+32+j*abi_member_head_size aty) : bytes32) s =
      n2w (abi_array_child_offset NONE aty avs j - 32)) /\
  (~is_dynamic aty ==> abi_array_child_offset NONE aty avs j = 32+j*abi_member_head_size aty)
Proof
  strip_tac >>
  `TAKE j avs ++ EL j avs::DROP (SUC j) avs = avs` by
    (qspec_then `j` (qspec_then `avs` mp_tac) TAKE_DROP_SUC >>
     asm_simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND]) >>
  `LENGTH (TAKE j avs) = j` by simp[LENGTH_TAKE] >>
  `abi_array_child_offset NONE aty avs j =
    32 + (if is_dynamic aty then LENGTH avs * abi_member_head_size aty +
      SUM (MAP (abi_member_tail_size aty) (TAKE j avs)) else j*abi_member_head_size aty)` by
    (Cases_on `is_dynamic aty` >> simp[abi_array_child_offset_def]) >>
  reverse conj_tac >- simp[] >> strip_tac >>
  mp_tac (Q.INST [`pre` |-> `TAKE j avs`, `av` |-> `EL j avs`,
    `post` |-> `DROP (SUC j) avs`] source_array_dynamic_offset_load) >>
  asm_simp_tac bool_ss [] >> simp[]
QED

Theorem entry_source_dynamic_array_offset_inputs:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  entry_source_metadata ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV avs) (ArrayV (DynArrayV xs)) /\ j < LENGTH xs /\
  mem_bytes_at sb (LENGTH (enc (vyper_to_abi_type env (ArrayT ty (Dynamic maxn))) (ListV avs)))
    (abi_decode_source CALLDATALOAD s) = enc (vyper_to_abi_type env (ArrayT ty (Dynamic maxn))) (ListV avs) /\
  sb + LENGTH (enc (vyper_to_abi_type env (ArrayT ty (Dynamic maxn))) (ListV avs)) < dimword (:256) ==>
  let aty = vyper_to_abi_type env ty in
  (is_dynamic aty ==>
    abi_decode_load CALLDATALOAD (n2w (sb+32+j*abi_member_head_size aty) : bytes32) s =
      n2w (abi_array_child_offset NONE aty avs j - 32)) /\
  (~is_dynamic aty ==> abi_array_child_offset NONE aty avs j = 32+j*abi_member_head_size aty)
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all entry_source_dynamic_array_child_metadata >> strip_tac >>
  irule entry_layout_dynamic_array_offset_inputs >>
  qpat_x_assum `mem_bytes_at sb _ _ = _` mp_tac >>
  qpat_x_assum `sb + _ < _` mp_tac >>
  asm_simp_tac bool_ss [vyper_to_abi_type_def] >> rpt strip_tac >> decide_tac
QED
