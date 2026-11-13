Theory abiEncoderWindowArrayLayout
Ancestors
  abiEncoderWindow abiEncoderOpenInput abiEncoderSharedArrayInitFrame
  abiEncoderArrayPrefix abiEncoderTuple abiDecodeRanges valueEncodingProps words list rich_list arithmetic

Theorem window_array_live_child:
  abi_encoder_window_input (AbiDynArray ei asz msz active)
    (Array NONE ty) (ListV avs) sb cap mem /\ j < LENGTH avs ==>
  ?child_cap. child_cap <= msz /\ 32+j*msz+child_cap <= cap /\
    abi_encoder_window_input ei ty (EL j avs)
      (sb+32+j*msz) child_cap mem
Proof
  strip_tac >> drule_all abi_encoder_window_array_child >> strip_tac >>
  qexists_tac `child_cap` >> asm_rewrite_tac[] >> decide_tac
QED

Theorem window_array_member_layout:
  abi_encoder_window_input (AbiDynArray ei asz msz active)
    (Array NONE ty) (ListV avs) sb cap mem ==>
  LIST_REL abi_encoder_layout_valid (REPLICATE (LENGTH avs) ty) avs
Proof
  strip_tac >> simp[LIST_REL_EL_EQN, EL_REPLICATE] >> rpt strip_tac >>
  drule_all window_array_live_child >> strip_tac >>
  metis_tac[abi_encoder_window_input_valid, abi_encoder_structural_valid_layout]
QED

Theorem window_array_layout:
  abi_encoder_window_input (AbiDynArray ei asz msz active)
    (Array NONE ty) (ListV avs) sb cap mem ==>
  LENGTH (enc (Array NONE ty) (ListV avs)) =
    32 + LENGTH avs * abi_member_head_size ty +
      SUM (MAP (abi_member_tail_size ty) avs)
Proof
  strip_tac >> drule window_array_member_layout >>
  metis_tac[abi_encoder_open_array_length]
QED

Theorem window_array_prefix_complete:
  abi_encoder_window_input (AbiDynArray ei asz msz active)
    (Array NONE ty) (ListV avs) sb cap source /\
  abi_encoder_array_prefix ty avs (LENGTH avs) d mem ==>
  mem_bytes_at d (LENGTH (enc (Array NONE ty) (ListV avs))) mem =
    enc (Array NONE ty) (ListV avs)
Proof
  strip_tac >> drule window_array_member_layout >>
  metis_tac[abi_encoder_open_array_prefix_complete]
QED

Theorem window_array_prefix_step_geometry:
  abi_encoder_window_input (AbiDynArray ei asz msz active)
    (Array NONE ty) (ListV avs) sb cap source /\ j < LENGTH avs ==>
  (is_dynamic ty ==>
    j * abi_member_head_size ty + 32 <= LENGTH avs * abi_member_head_size ty /\
    32 + LENGTH avs * abi_member_head_size ty +
      SUM (MAP (abi_member_tail_size ty) (TAKE j avs)) +
      LENGTH (enc ty (EL j avs)) <= LENGTH (enc (Array NONE ty) (ListV avs))) /\
  (~is_dynamic ty ==>
    j * abi_member_head_size ty + LENGTH (enc ty (EL j avs)) <=
      LENGTH avs * abi_member_head_size ty)
Proof
  strip_tac >> drule window_array_member_layout >> strip_tac >>
  drule_all window_array_live_child >> strip_tac >>
  `abi_encoder_layout_valid ty (EL j avs)` by
    metis_tac[abi_encoder_window_input_valid, abi_encoder_structural_valid_layout] >>
  `SUM (MAP (abi_member_tail_size ty) (TAKE j avs)) +
      abi_member_tail_size ty (EL j avs) <= SUM (MAP (abi_member_tail_size ty) avs)` by
    (irule abiEncoderInputTheory.abi_encoder_prefix_sum_bound >> asm_rewrite_tac[]) >>
  `j * abi_member_head_size ty + abi_member_head_size ty <=
    LENGTH avs * abi_member_head_size ty` by
    (`SUC j * abi_member_head_size ty <= LENGTH avs * abi_member_head_size ty` by simp[] >>
     pop_assum (mp_tac o REWRITE_RULE [MULT_CLAUSES]) >> decide_tac) >>
  drule window_array_layout >>
  Cases_on `is_dynamic ty` >>
  gvs[abi_member_head_size_def, abi_member_tail_size_def, abi_encoder_layout_valid_def] >>
  decide_tac
QED
