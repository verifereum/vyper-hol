(* Straight-line instruction shape of a decoder that has not closed a block. *)
Theory bodyFullAbiDecodeCutStraightSlice
Ancestors
  abiDecoderAppend abiDecoderArrayInit abiDecoderArrayLoopInit abiDecoderBulk
  abiDecoderBytesPhases abiDecoderClampedWord abiDecoderLoopCode abiDecoderLoopEmit
  abiDecoderArraySetupCode abiDecoderArraySetupInputs
  abiDecoderRecursiveLoopLayout abiDecoderRange exprSimAbiDecodeCompositePrefix
  exprSimAbiDecodeSiteCoverage exprSimAbiGasBridge fragExec emitHelperProps
  exprLoweringProps abiEncoder abiDecoderContract compileEnv emitHelper venomInst
  pair list rich_list arithmetic

val no_terms = ``\a b. EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts a b)``;

Theorem cut_history_length[local]:
  cs_extends a b ==> LENGTH a.cs_blocks <= LENGTH b.cs_blocks
Proof
  rw[cs_extends_def] >> simp[]
QED

Theorem cut_history_between[local]:
  cs_extends a b /\ cs_extends b c /\ c.cs_blocks = a.cs_blocks ==>
  b.cs_blocks = a.cs_blocks /\ c.cs_blocks = b.cs_blocks
Proof
  simp[cs_extends_def] >> rpt strip_tac >> gvs[]
QED

Theorem cut_straight_append[local]:
  cs_extends a b /\ cs_extends b c /\ c.cs_blocks = a.cs_blocks /\
  (^no_terms) a b /\ (^no_terms) b c ==> (^no_terms) a c
Proof
  BETA_TAC >> strip_tac >>
  drule_all cut_history_between >> strip_tac >>
  drule_all abi_decode_frag_code_compose >>
  fs[frag_code_same_blocks, GSYM emitted_insts_def, EVERY_MEM] >> metis_tac[]
QED

Theorem cut_emit_add[local]:
  emit_op ADD ops a = (x,b) ==>
  cs_extends a b /\ (^no_terms) a b
Proof
  BETA_TAC >> strip_tac >>
  conj_tac >- metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  drule emitted_insts_emit_op >> simp[mk_inst_def, is_terminator_def]
QED

Theorem cut_loop_closes[local]:
  compile_abi_decode_dyn_loop dst src MLOAD base_op hi ei asz msz ip cnt a = ((),b) ==>
  b.cs_blocks <> a.cs_blocks
Proof
  strip_tac >> drule abi_decode_dyn_loop_trace >> strip_tac >>
  drule abi_decoder_array_setup_head >> strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  drule_all abi_decode_array_element_setup_shape >> strip_tac >>
  drule cs_extends_abi_decode >> strip_tac >>
  drule abi_decoder_loop_prefix_facts >> strip_tac >>
  gvs[] >> drule abi_decoder_loop_suffix_extends >> strip_tac >>
  `LENGTH st0.cs_blocks <= LENGTH b.cs_blocks` by
    (irule cut_history_length >>
     `cs_extends st0 middle` by (irule cs_extends_same_block >> simp[]) >>
     metis_tac[cs_extends_trans]) >>
  strip_tac >> fs[]
  >> (gvs[])
QED

Theorem cut_array_straight[local]:
  compile_abi_decode_to_buf dst src MLOAD base_op hi (DecDynArray ei asz msz dyn maxn) a = ((),b) /\
  b.cs_blocks = a.cs_blocks ==> (^no_terms) a b
Proof
  BETA_TAC >> strip_tac >>
  `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
  Cases_on `dyn \/ dec_info_needs_clamp ei`
  >- (drule_all abi_decode_loop_array_trace >> strip_tac >>
      drule_all abi_decode_array_loop_init_shape >> strip_tac >>
      drule cut_loop_closes >> simp[]) >>
  `dyn = F` by fs[] >> gvs[] >>
  drule_all abi_decoder_bulk_shape >> simp[EVERY_MEM]
QED

Theorem cut_before_straight_mutual[local]:
  (!dst src opc base hi info a b.
    opc = MLOAD /\ compile_abi_decode_to_buf dst src opc base hi info a = ((),b) /\
    b.cs_blocks = a.cs_blocks ==> (^no_terms) a b) /\
  (!dst src opc base hi elems ao vo a b.
    opc = MLOAD /\ compile_abi_decode_complex_elems dst src opc base hi elems ao vo a = ((),b) /\
    b.cs_blocks = a.cs_blocks ==> (^no_terms) a b) /\
  (!dst src opc base hi ei asz msz ip cnt a b.
    opc = MLOAD /\ compile_abi_decode_dyn_loop dst src opc base hi ei asz msz ip cnt a = ((),b) /\
    b.cs_blocks = a.cs_blocks ==> (^no_terms) a b)
Proof
  BETA_TAC >> ho_match_mp_tac compile_abi_decode_to_buf_ind >> rpt conj_tac
  >- (rpt strip_tac >> gvs[] >>
      `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
      drule_all abi_decoder_clamped_word_shape >> simp[EVERY_MEM])
  >- (rpt strip_tac >> gvs[] >>
      `abi_decode_source_opcode MLOAD` by simp[abi_decode_source_opcode_def] >>
      drule_all abi_decode_bytes_position_shape >> simp[EVERY_MEM])
  >- (rpt strip_tac >> gvs[] >> metis_tac[cut_array_straight, BETA_THM])
  >- suspend "complex"
  >- (simp[Once compile_abi_decode_to_buf_def, comp_return_def, emitted_insts_refl])
  >- suspend "cons"
  >> (rpt strip_tac >> gvs[] >> drule cut_loop_closes >> simp[])
QED

Resume cut_before_straight_mutual[complex]:
  rpt gen_tac >> disch_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `hi = Lit 0w`
  >- (gvs[compile_abi_decode_to_buf_def] >> metis_tac[]) >>
  gvs[compile_abi_decode_to_buf_def, comp_bind_def, comp_ignore_bind_def] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op ADD _ a = (_,p)` >>
  rename1 `compile_abi_decode_range_check _ _ _ p = ((),q)` >>
  drule (BETA_RULE cut_emit_add) >> strip_tac >>
  drule compile_abi_decode_range_check_fragment_shape >> strip_tac >>
  `cs_extends p q` by
    (irule cs_extends_same_block >> gvs[inst_extends_def, IS_PREFIX_APPEND]) >>
  `cs_extends q b` by
    metis_tac[CONJUNCT1 (CONJUNCT2 cs_appends_abi_decode_mutual), cs_appends_def] >>
  `cs_extends a q` by metis_tac[cs_extends_trans] >>
  `q.cs_blocks = a.cs_blocks` by metis_tac[cut_history_between] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts a q)` by
    (irule (BETA_RULE cut_straight_append) >> simp[] >> qexists_tac `p` >> fs[EVERY_MEM]) >>
  irule (BETA_RULE cut_straight_append) >> simp[] >> qexists_tac `q` >>
  metis_tac[]
QED

Resume cut_before_straight_mutual[cons]:
  rpt gen_tac >> disch_tac >> rpt gen_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `compile_abi_decode_complex_elems _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_abi_decode_to_buf_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  rename1 `compile_getelemptr_abi _ _ _ _ _ _ a = (_,p)` >>
  rename1 `emit_op ADD _ p = (_,q)` >>
  rename1 `compile_abi_decode_to_buf _ _ _ _ _ _ q = ((),r)` >>
  drule abi_decode_member_pointer_prefix_shape >> strip_tac >>
  drule (BETA_RULE cut_emit_add) >> strip_tac >>
  `cs_extends a p` by
    (irule cs_extends_same_block >> gvs[inst_extends_def, IS_PREFIX_APPEND]) >>
  drule cs_extends_abi_decode >> strip_tac >>
  `cs_extends r b` by
    metis_tac[CONJUNCT1 (CONJUNCT2 cs_appends_abi_decode_mutual), cs_appends_def] >>
  `cs_extends a q` by metis_tac[cs_extends_trans] >>
  `cs_extends q b` by metis_tac[cs_extends_trans] >>
  `q.cs_blocks = a.cs_blocks /\ r.cs_blocks = q.cs_blocks /\ b.cs_blocks = r.cs_blocks` by
    metis_tac[cut_history_between] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts a q)` by
    (irule (BETA_RULE cut_straight_append) >> simp[] >> qexists_tac `p` >> fs[EVERY_MEM]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts q b)` by
    (irule (BETA_RULE cut_straight_append) >> simp[] >> qexists_tac `r` >> metis_tac[]) >>
  metis_tac[BETA_RULE cut_straight_append]
QED

Finalise cut_before_straight_mutual

Theorem abi_decode_cut_before_slice_straight:
  hi <> Lit 0w /\
  ((?dst src input info.
      compile_abi_decode_to_buf dst src MLOAD (Var input) hi info a = ((),b)) \/
   (?dst src input elems ao vo.
      compile_abi_decode_complex_elems dst src MLOAD (Var input) hi elems ao vo a = ((),b)) \/
   (?dst src input ei asz msz ip cnt.
      compile_abi_decode_dyn_loop dst src MLOAD (Var input) hi ei asz msz ip cnt a = ((),b))) /\
  cs_extends start a /\ cs_extends a b /\ cs_extends b final /\
  frag_ops_free start final /\ a.cs_blocks = start.cs_blocks /\ b.cs_blocks = a.cs_blocks ==>
  EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> PHI /\
             ~is_terminator i.inst_opcode) (emitted_insts a b)
Proof
  strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts a b)` by
    metis_tac[BETA_RULE cut_before_straight_mutual] >>
  `cs_extends start b` by metis_tac[cs_extends_trans] >>
  `frag_code a b = emitted_insts a b` by
    simp[frag_code_same_blocks, emitted_insts_def] >>
  fs[frag_ops_free_def, EVERY_MEM] >> rpt strip_tac >>
  `MEM i (frag_code start b)` by
    metis_tac[abi_decode_frag_code_right_inclusion] >>
  `MEM i (frag_code start final)` by
    metis_tac[abi_decode_frag_code_left_inclusion] >>
  metis_tac[]
QED
