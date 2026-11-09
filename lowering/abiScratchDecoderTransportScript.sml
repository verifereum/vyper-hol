(* Source bytes and physical buffer separation survive recursive decoder effects. *)
Theory abiScratchDecoderTransport
Ancestors
  abiScratchDecoderContract abiScratchEncoderContract abiScratchEffect abiScratchFootprint
  abiDecoderFootprint abiDecoderAllocation abiDecoderFrame abiDecoderContract abiDecoderReentry
  abiDecoderTypedContract abiDecoderCoherence compileEnv valueEncoding vyperABI contractABI
  venomState words list arithmetic

Theorem abi_decode_source_footprint_frame:
  abi_decode_source_opcode opc /\
  (opc = MLOAD ==> abi_footprint_disjoint sb len fp) /\
  abi_decode_footprint_frame fp s t ==>
  mem_bytes_at sb len (abi_decode_source opc t) = mem_bytes_at sb len (abi_decode_source opc s)
Proof
  rw[abi_decode_source_opcode_def, abi_decode_source_def, abi_decode_footprint_frame_def] >>
  first_x_assum irule >> first_assum ACCEPT_TAC
QED

Theorem abi_scratch_decoder_source_effect:
  abi_scratch_decoder_ranges opc base_op hi_op src dst B sb len d sz first last b cap initial /\
  abi_scratch_effect first last lo hi_id next limit_st d sz b cap initial actual /\
  first <= lo /\ hi_id <= last ==>
  mem_bytes_at (B + sb) len (abi_decode_source opc actual) =
    mem_bytes_at (B + sb) len (abi_decode_source opc initial)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_scratch_effect_frame >> strip_tac >>
  qpat_assum `abi_scratch_decoder_ranges _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_ranges_def]) >>
  irule abi_decode_source_footprint_frame >> asm_simp_tac bool_ss [] >>
  qexists_tac `(d,sz)::abi_decoder_child_scratch (abi_decoder_ids first last) b cap initial` >>
  asm_simp_tac bool_ss []
QED

Theorem abi_scratch_decoder_ranges_effect:
  abi_scratch_decoder_ranges opc base_op hi_op src dst B sb len d sz first last b cap initial /\
  abi_scratch_effect first last lo hi_id next limit_st d sz b cap initial actual /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
  abi_decoder_operand_live next hi_op /\ abi_decoder_operand_live next base_op ==>
  abi_scratch_decoder_ranges opc base_op hi_op src dst B sb len d sz first last b cap actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_scratch_decoder_ranges _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_ranges_def]) >>
  `abi_scratch_evolution (abi_decoder_ids first last) b cap initial actual` by
    fs[abi_scratch_effect_def] >>
  `eval_operand src actual = SOME (n2w sb) /\ eval_operand dst actual = SOME (n2w d) /\
    eval_operand base_op actual = SOME (n2w B)` by
    (imp_res_tac abi_scratch_effect_operand >> asm_simp_tac bool_ss []) >>
  `abi_footprint_disjoint d sz
    (abi_decoder_child_scratch (abi_decoder_ids first last) b cap actual)` by
    (irule abi_scratch_disjoint_advance >> simp[] >> qexists_tac `initial` >> simp[]) >>
  asm_simp_tac bool_ss [abi_scratch_decoder_ranges_def] >> conj_tac
  >- (Cases_on `hi_op = Lit 0w` >- simp[] >>
      qpat_x_assum `hi_op = Lit 0w \/ _` mp_tac >> asm_simp_tac bool_ss [] >>
      disch_then (qx_choose_then `h` (MAP_EVERY assume_tac o CONJUNCTS)) >>
      qexists_tac `h` >> imp_res_tac abi_scratch_effect_operand >> asm_simp_tac bool_ss []) >>
  strip_tac >>
  qpat_x_assum `opc = MLOAD ==> _` (fn th => drule_all th) >>
  simp_tac bool_ss [abi_scratch_disjoint_cons] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  asm_simp_tac bool_ss [abi_scratch_disjoint_cons] >>
  irule abi_scratch_disjoint_advance >> simp[] >> qexists_tac `initial` >> simp[]
QED

Theorem abi_scratch_decoder_input_mono:
  abi_scratch_decoder_input ce env sf ty tv bs v st src dst opc base_op hi B sb d first last b cap s /\
  st.cs_next_var <= prepared.cs_next_var ==>
  abi_scratch_decoder_input ce env sf ty tv bs v prepared src dst opc base_op hi B sb d first last b cap s
Proof
  simp_tac bool_ss [abi_scratch_decoder_input_def] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> asm_simp_tac bool_ss [] >>
  rpt conj_tac >> irule abi_decoder_operand_live_mono >>
  qexists_tac `st.cs_next_var` >> asm_simp_tac bool_ss []
QED

Theorem abi_scratch_decoder_input_effect:
  abi_scratch_decoder_input ce env sf ty tv bs v st src dst opc base_op hi_op B sb d first last b cap initial /\
  abi_scratch_effect first last lo hi_id next limit_st d (type_memory_bytes ce ty) b cap initial actual /\
  first <= lo /\ hi_id <= last /\ st.cs_next_var <= next ==>
  abi_scratch_decoder_input ce env sf ty tv bs v st src dst opc base_op hi_op B sb d first last b cap actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_scratch_decoder_input ce env sf ty tv bs v st src dst opc base_op hi_op B sb d first last b cap initial`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_input_def]) >>
  `abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
    abi_decoder_operand_live next hi_op /\ abi_decoder_operand_live next base_op` by
    (rpt conj_tac >> irule abi_decoder_operand_live_mono >>
     qexists_tac `st.cs_next_var` >> asm_simp_tac bool_ss []) >>
  drule_all abi_scratch_decoder_ranges_effect >> strip_tac >>
  drule_all abi_scratch_decoder_source_effect >> strip_tac >>
  asm_simp_tac bool_ss [abi_scratch_decoder_input_def]
QED

Theorem abi_scratch_decoder_input_effect_frame:
  abi_scratch_decoder_input ce env sf ty tv bs v st src dst opc base_op hi_op B sb d first last b cap initial /\
  abi_scratch_effect first last lo hi_id next limit_st d (type_memory_bytes ce ty) b cap initial actual /\
  st.cs_next_var <= next /\
  abi_decode_footprint_frame
    ((d,type_memory_bytes ce ty)::abi_decoder_child_scratch (abi_decoder_ids first last) b cap actual)
    initial actual ==>
  abi_scratch_decoder_input ce env sf ty tv bs v st src dst opc base_op hi_op B sb d first last b cap actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qhdtm_assum `abi_scratch_decoder_input`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_scratch_decoder_input_def]) >>
  `abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
   abi_decoder_operand_live next hi_op /\ abi_decoder_operand_live next base_op` by
    (rpt conj_tac >> irule abi_decoder_operand_live_mono >>
     qexists_tac `st.cs_next_var` >> asm_simp_tac bool_ss []) >>
  drule_all abi_scratch_decoder_ranges_effect >> strip_tac >>
  `mem_bytes_at (B + sb) (LENGTH bs) (abi_decode_source opc actual) =
   mem_bytes_at (B + sb) (LENGTH bs) (abi_decode_source opc initial)` by
    (irule abi_decode_source_footprint_frame >>
     conj_tac >- fs[abi_scratch_decoder_ranges_def] >>
     qexists_tac `(d,type_memory_bytes ce ty)::abi_decoder_child_scratch (abi_decoder_ids first last) b cap actual` >>
     qpat_x_assum `abi_scratch_decoder_ranges _ _ _ _ _ _ _ _ _ _ _ _ _ _ actual` mp_tac >>
     simp[abi_scratch_decoder_ranges_def]) >>
  asm_simp_tac bool_ss [abi_scratch_decoder_input_def]
QED
