(* Semantic sensitivity excludes unused bytestring capacity. *)
Theory abiDecodePtrFlatValue
Ancestors
  exprPtrCleanBufferPost exprSimProps valueEncoding valueEncodingProps
  bodyPtrDefs venomState words list arithmetic vfmConstants
  abiDecodePtrMemberFrame exprSimBufferStore contractABI vyperTypeABI
  abiDecodePtrFootprint abiDecoderMemberInfos abiDecoderCoherence supportedTypes
  abiEncoder loweringPosts compileEnv vyperValue exprLowering abiDecodePtrFlatRun

Theorem clean_footprint_value_robust:
  val_in_memory tv v off mem /\ val_wf tv v /\
  (!i. off <= i /\ i < off+val_footprint tv v ==> i NOTIN dirty) ==>
  !mem'. mem_agree_outside dirty mem mem' ==> val_in_memory tv v off mem'
Proof
  rpt strip_tac >> irule val_in_memory_footprint_agree >>
  simp[] >> qexists_tac `mem` >> simp[] >>
  irule clean_window_memory_agree >> qexists_tac `dirty` >> simp[]
QED

(* Member robustness composes without requiring tuple padding to be clean. *)
Theorem abi_decode_tuple_robust_cons:
  (!mem'. mem_agree_outside dirty mem mem' ==> val_in_memory tv v off mem') /\
  (!mem'. mem_agree_outside dirty mem mem' ==>
    tuple_in_memory vs tvs (off+type_memory_size tv) mem') ==>
  !mem'. mem_agree_outside dirty mem mem' ==>
    tuple_in_memory (v::vs) (tv::tvs) off mem'
Proof
  simp[Once val_in_memory_def]
QED

Theorem abi_decode_window_value_robust:
  abi_decode_ptr_window G tn s root b m /\
  val_in_memory tv v (w2n b) s.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= m ==>
  !mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    val_in_memory tv v (w2n b) mem'
Proof
  rpt strip_tac >> irule clean_footprint_value_robust >> simp[] >>
  qexistsl_tac [`tn.t_mem`, `s.vs_memory`] >> simp[] >>
  fs[abi_decode_ptr_window_def] >> rpt strip_tac >>
  first_x_assum irule >> decide_tac
QED

(* The runtime header determines the sensitive size, not the declared cap. *)
Theorem abi_decode_bytestring_value_footprint:
  is_bytestring_type ty /\ evaluate_type env ty = SOME tv /\
  value_has_type tv v /\ val_in_memory tv v p s.vs_memory /\
  val_wf tv v /\ type_memory_size tv < dimword(:256) ==>
  val_footprint tv v <= 32+contractABI$ceil32 (w2n (mload p s))
Proof
  strip_tac >> drule_all buffer_typed_bytestring_header >> strip_tac >>
  `val_store_size tv v <= type_memory_size tv /\
   val_footprint tv v <= val_store_size tv v` by
    metis_tac[val_store_size_le, val_footprint_le_store_size] >>
  `len <= 32 * word_size len` by simp[le_word_size_mul] >>
  `len < dimword(:256)` by decide_tac >>
  simp[w2n_n2w, contractABITheory.ceil32_def, word_size_def] >>
  fs[word_size_def]
QED

Theorem abi_decode_supported_value_footprint:
  supported_scalar_type ty /\ evaluate_type env ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\ val_in_memory tv v p s.vs_memory /\
  type_memory_size tv < dimword(:256) ==>
  val_footprint tv v <=
    abi_decode_runtime_footprint (type_to_abi_dec_info sf ce ty) p s
Proof
  strip_tac >>
  `is_bytestring_type ty ==> val_footprint tv v <=
    32+contractABI$ceil32 (w2n (mload p s))` by
    (strip_tac >> irule abi_decode_bytestring_value_footprint >> metis_tac[]) >>
  Cases_on `ty` >> fs[supported_scalar_type_def, supported_word_type_def,
    supported_string_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  fs[supported_word_type_def, supported_string_type_def,
    type_to_abi_dec_info_def, abi_decode_runtime_footprint_def] >>
  TRY (rename1 `BytesT bd` >> Cases_on `bd` >>
    fs[supported_word_type_def, supported_string_type_def,
      type_to_abi_dec_info_def, abi_decode_runtime_footprint_def]) >>
  gvs[evaluate_type_def, is_bytestring_type_def, type_memory_size_def] >>
  Cases_on `v` >> simp[val_footprint_def, type_memory_size_def]
QED

Theorem abi_decode_clean_flat_tuple_robust:
  !tys tvs vs p.
  EVERY supported_scalar_type tys /\
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
  LIST_REL value_has_type tvs vs /\ LIST_REL val_wf tvs vs /\
  EVERY (\tv. type_memory_size tv < dimword(:256)) tvs /\
  tuple_in_memory vs tvs p s.vs_memory /\
  abi_decode_clean_flat (abi_decoder_member_infos sf ce tys) p tn s ==>
  !mem'. mem_agree_outside tn.t_mem s.vs_memory mem' ==>
    tuple_in_memory vs tvs p mem'
Proof
  Induct >- (Cases_on `tvs` >> Cases_on `vs` >>
    simp[Once val_in_memory_def] >> simp[Once val_in_memory_def]) >>
  qx_gen_tac `ty` >> Cases_on `tvs` >> Cases_on `vs` >>
  simp[Once val_in_memory_def, abi_decoder_member_infos_def,
    abi_decode_clean_flat_def] >> rpt strip_tac >>
  rename1 `abi_decoder_coherent ce env sf ty tv` >>
  drule abi_decoder_coherent_header >>
  simp[abi_decoder_header_def] >> strip_tac >>
  rename1 `val_wf tv v` >>
  irule abi_decode_tuple_robust_cons >>
  qexistsl_tac [`tn.t_mem`, `s.vs_memory`] >> simp[] >> conj_tac
  >- (rpt strip_tac >> first_x_assum irule >>
      simp[abi_decoder_member_infos_def] >> metis_tac[]) >>
  rpt strip_tac >> irule clean_footprint_value_robust >> simp[] >>
  qexistsl_tac [`tn.t_mem`, `s.vs_memory`] >> simp[] >>
  `val_footprint tv v <= abi_decode_runtime_footprint
    (type_to_abi_dec_info sf ce ty) p s` by
    (irule abi_decode_supported_value_footprint >> metis_tac[]) >>
  rpt strip_tac >> gvs[]
QED

Theorem abi_decode_flat_success_robust:
  abi_decode_member_live ret ctx func cenv cx es src b h dst d cap pos z hi sa G tn s /\
  abi_decode_flat_layout (abi_decoder_member_infos sf ce tys) off q z h cap /\
  compile_abi_decode_complex_elems (Var dst) pos MLOAD (Var src) hi
    (abi_decoder_member_infos sf ce tys) off q sa = ((),sb) /\
  fn_has_code sa sb func /\ run_inst_seq (emitted_insts sa sb) s = OK u /\
  EVERY supported_scalar_type tys /\
  LIST_REL (abi_decoder_coherent ce env sf) tys tvs /\
  LIST_REL value_has_type tvs vs /\ LIST_REL val_wf tvs vs /\
  EVERY (\tv. type_memory_size tv < dimword(:256)) tvs /\
  tuple_in_memory vs tvs (w2n d+q) u.vs_memory ==>
  ?H tf. inst_seq_ptr D 0 ctx func PG G tn (emitted_insts sa sb) s H tf /\
    abi_decode_member_live ret ctx func cenv cx es src b h dst d cap pos z hi sb H tf
      (u with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    abi_decode_member_frame sa G tn s H tf
      (u with vs_inst_idx := LENGTH sb.cs_current_insts)
      (w2n d+q) (SUM (MAP (SND o SND) (abi_decoder_member_infos sf ce tys))) /\
    (!mem'. mem_agree_outside tf.t_mem u.vs_memory mem' ==>
      tuple_in_memory vs tvs (w2n d+q) mem')
Proof
  strip_tac >> drule_all abi_decode_flat_success >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`H`, `tf`] >> simp[] >> rpt strip_tac >>
  irule abi_decode_clean_flat_tuple_robust >> simp[] >>
  qexistsl_tac [`ce`, `env`,
    `u with vs_inst_idx := LENGTH sb.cs_current_insts`, `sf`, `tf`, `tys`] >> fs[ADD_COMM]
QED
