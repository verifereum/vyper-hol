Theory abiDecoderBulk
Ancestors
  abiDecoderDynarrayBound abiDecoderBytesBound abiDecoderCopy abiDecoderComposition
  abiDecoderContract abiDecoderGuards emitHelperProps exprLoweringProps compileEnv emitHelper
  valueEncoding venomExecSemantics venomState words abiDecoderArrayHeader abiDecoderFrameCompose
  arithmetic abiDecoderDynarrayPrefix abiDecoderGuard abiEncoder venomMemProps
  abiStaticDynarrayLayout abiCanonicalArrays abiStaticAggregateProps abiStaticLayoutProps
  abiStaticPrimitiveProps vyperABI vyperTyping contractABI byte list rich_list
  abiDecoderCoherence abiDecoderLayout exprLowering vyperValue abiDecodeRanges
  abiDecoderTypedContract abiCanonicalArrayLoad abiDecoderFrame abiDecoderBytesTyped fragExec
  venomInst

(* ===== Payload ===== *)

(* The actual static-element dynamic-array payload-copy block. *)

Definition abi_decode_bulk_payload_def:
  abi_decode_bulk_payload dst src cnt mem_sz opc =
    do copy_sz <- emit_op MUL [cnt; Lit (n2w mem_sz)];
       src_data <- emit_op ADD [src; Lit 32w];
       dst_data <- emit_op ADD [dst; Lit 32w];
       emit_void (abi_decode_copy_opcode opc) [dst_data;src_data;copy_sz]
    od
End

Theorem abi_decode_bulk_payload_sequence:
  abi_decode_bulk_payload dst src cnt mem_sz opc st = ((),st') /\
  abi_decode_source_opcode opc /\ eval_operand src s = SOME (n2w sb) /\
  eval_operand dst s = SOME (n2w d) /\ eval_operand cnt s = SOME (n2w n) /\
  sb + 32 < dimword (:256) /\ d + 32 < dimword (:256) /\
  n * mem_sz < dimword (:256) /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    mem_bytes_at (d + 32) (n * mem_sz) t.vs_memory =
      mem_bytes_at (sb + 32) (n * mem_sz) (abi_decode_source opc s) /\
    abi_decode_frame (d + 32) (n * mem_sz) s t /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    inst_extends st st'
Proof
  simp[abi_decode_bulk_payload_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  pairarg_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op MUL [cnt; Lit (n2w mem_sz)] st = (sz_op,c1)` >>
  rename1 `emit_op ADD [src; Lit 32w] c1 = (src_data,c2)` >>
  rename1 `emit_op ADD [dst; Lit 32w] c2 = (dst_data,c3)` >>
  `eval_operand (Lit (n2w mem_sz)) s = SOME (n2w mem_sz)` by simp[eval_operand_def] >>
  drule_all abi_decode_mul_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >> gvs[word_mul_n2w] >>
  `eval_operand src s1 = SOME (n2w sb)` by metis_tac[] >>
  `eval_operand (Lit 32w) s1 = SOME 32w` by simp[eval_operand_def] >>
  drule_all abi_decode_add_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `eval_operand dst s2 = SOME (n2w d)` by metis_tac[] >>
  qspecl_then [`dst`, `Lit 32w`, `n2w d`, `32w`, `c2`, `dst_data`, `c3`, `s2`]
    mp_tac abi_decode_add_sequence >>
  impl_tac >- simp[eval_operand_def] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 c3) s2 = OK s3` >>
  `eval_operand sz_op s3 = SOME (n2w (n * mem_sz)) /\
   eval_operand src_data s3 = SOME ((n2w sb : bytes32) + 32w)` by
    (ONCE_REWRITE_TAC [arithmeticTheory.MULT_COMM] >> metis_tac[]) >>
  drule_all abi_decode_copy_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c3 st') s3 = OK t` >>
  `fresh_vars_wrt st' t` by (drule_all abi_decode_copy_fresh >> simp[]) >>
  drule inst_extends_emit_void >> strip_tac >>
  `run_inst_seq (emitted_insts c2 st') s2 = OK t /\ inst_extends c2 st'` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s3`, `c3`] >> simp[]) >>
  `run_inst_seq (emitted_insts c1 st') s1 = OK t /\ inst_extends c1 st'` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s2`, `c2`] >> simp[]) >>
  `run_inst_seq (emitted_insts st st') s = OK t /\ inst_extends st st'` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`, `c1`] >> simp[]) >>
  qexists_tac `t` >> gvs[word_add_n2w, w2n_n2w, abi_decode_copy_bytes_def,
    mem_bytes_at_def, abi_decode_source_def, abi_decode_frame_def] >> metis_tac[]
QED

(* ===== Body ===== *)

(* Count/header and payload writes in the static-element dynamic-array path. *)

Definition abi_decode_bulk_body_def:
  abi_decode_bulk_body dst src opc mem_sz =
    do cnt <- abi_decode_array_header dst src opc;
       abi_decode_bulk_payload dst src cnt mem_sz opc
    od
End

Theorem abi_decode_bulk_body_sequence:
  abi_decode_bulk_body dst src opc mem_sz st = ((),st') /\
  abi_decode_source_opcode opc /\ eval_operand src s = SOME (n2w sb) /\
  eval_operand dst s = SOME (n2w d) /\
  abi_decode_load opc (n2w sb : bytes32) s = n2w n /\
  sb + 32 < dimword (:256) /\ d + 32 < dimword (:256) /\
  n * mem_sz < dimword (:256) /\
  (opc = MLOAD ==> sb + 32 + n * mem_sz <= d \/ d + 32 <= sb + 32) /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    mem_word_at d t.vs_memory = n2w n /\
    mem_bytes_at (d + 32) (n * mem_sz) t.vs_memory =
      mem_bytes_at (sb + 32) (n * mem_sz) (abi_decode_source opc s) /\
    abi_decode_frame d (32 + n * mem_sz) s t /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    inst_extends st st'
Proof
  simp_tac bool_ss [abi_decode_bulk_body_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `abi_decode_array_header dst src opc st = (cnt,c1)` >>
  `d < dimword (:256)` by decide_tac >>
  drule_all abi_decode_array_header_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand src s1 = SOME (n2w sb) /\
   eval_operand dst s1 = SOME (n2w d)` by metis_tac[] >>
  mp_tac (Q.INST [`st` |-> `c1`, `s` |-> `s1`]
    abi_decode_bulk_payload_sequence) >> impl_tac >- simp[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 st') s1 = OK t` >>
  `mem_word_at d t.vs_memory = mem_word_at d s1.vs_memory` by
    (irule abi_decode_frame_mem_word >>
     qexistsl_tac [`d + 32`, `n * mem_sz`] >> simp[]) >>
  `mem_bytes_at (sb + 32) (n * mem_sz) (abi_decode_source opc s1) =
   mem_bytes_at (sb + 32) (n * mem_sz) (abi_decode_source opc s)` by
    (irule abi_decode_frame_source_window >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`d`, `32`] >> simp[]) >>
  `abi_decode_frame d (32 + n * mem_sz) s t` by
    (irule abi_decode_frame_adjacent >> qexists_tac `s1` >> simp[]) >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  qexists_tac `t` >> gvs[] >> metis_tac[]
QED

(* ===== Decoder Bulk ===== *)

(* Successful execution of the emitted static-element dynamic-array decoder. *)

Theorem abi_decode_bulk_phases:
  abi_decode_source_opcode opc /\ ~dec_info_needs_clamp ei ==>
  compile_abi_decode_to_buf dst src opc hi
    (DecDynArray ei abi_sz mem_sz F maxn) =
    do abi_decode_dynarray_prefix src opc hi maxn abi_sz;
       abi_decode_bulk_body dst src opc mem_sz
    od
Proof
  strip_tac >> gvs[abi_decode_source_opcode_def] >> Cases_on `hi = Lit 0w` >>
  simp[FUN_EQ_THM, compile_abi_decode_to_buf_def,
       abi_decode_dynarray_prefix_def, abi_decode_count_guard_def,
       abi_decode_dynarray_end_guard_def, abi_decode_dynarray_end_def,
       abi_decode_le_guard_def, abi_decode_bulk_body_def,
       abi_decode_array_header_def, abi_decode_bulk_payload_def,
       abi_decode_copy_opcode_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >> rpt gen_tac >> rpt (pairarg_tac >> gvs[])
QED

Theorem abi_decode_bulk_sequence:
  compile_abi_decode_to_buf dst src opc hi
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),st') /\
  ~dec_info_needs_clamp ei /\ abi_decode_source_opcode opc /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  abi_decode_load opc (n2w sb : bytes32) s = n2w n /\
  n <= maxn /\ maxn < dimword (:256) /\
  sb + 32 < dimword (:256) /\ d + 32 < dimword (:256) /\
  n * mem_sz < dimword (:256) /\
  (opc = MLOAD ==> sb + 32 + n * mem_sz <= d \/ d + 32 <= sb + 32) /\
  (hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\
                     sb + 32 + n * abi_sz <= h /\ h < dimword (:256)) /\
  fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    mem_word_at d t.vs_memory = n2w n /\
    mem_bytes_at (d + 32) (n * mem_sz) t.vs_memory =
      mem_bytes_at (sb + 32) (n * mem_sz) (abi_decode_source opc s) /\
    abi_decode_frame d (32 + n * mem_sz) s t /\ fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    inst_extends st st'
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac bool_ss [abi_decode_bulk_phases, comp_ignore_bind_def,
                       comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >>
  rename1 `abi_decode_dynarray_prefix src opc hi maxn abi_sz st = (prefix_result,c1)` >>
  Cases_on `prefix_result` >>
  mp_tac (Q.INST [`st'` |-> `c1`] abi_decode_dynarray_prefix_sequence) >>
  impl_tac >- simp[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand src s1 = SOME (n2w sb) /\
   eval_operand dst s1 = SOME (n2w d)` by metis_tac[] >>
  `abi_decode_load opc (n2w sb : bytes32) s1 = n2w n` by
    gvs[abi_decode_load_def, abi_decode_source_def, mload_def] >>
  `abi_decode_bulk_body dst src opc mem_sz c1 = ((),st')` by
    (qpat_x_assum `_ = ((),st')` mp_tac >>
     asm_simp_tac bool_ss [pairTheory.UNCURRY_DEF]) >>
  drule_all abi_decode_bulk_body_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 st') s1 = OK t` >>
  drule_all abi_decode_sequence_chain >> strip_tac >> qexists_tac `t` >>
  gvs[abi_decode_frame_def, abi_decode_source_def] >> metis_tac[]
QED

(* ===== Contract ===== *)

(* Canonical source and post-copy layout for static-element dynamic arrays. *)

Theorem static_dynarray_encoding:
  ~is_dynamic ty ==>
  enc (Array NONE ty) (ListV avs) =
    word_to_bytes (n2w (LENGTH avs) : bytes32) T ++ FLAT (MAP (enc ty) avs)
Proof
  strip_tac >>
  `enc (Array NONE ty) (ListV avs) = enc_number (Uint 256) (NumV (LENGTH avs)) ++
    enc (Array (SOME (LENGTH avs)) ty) (ListV avs)` by
    (pure_rewrite_tac[canonical_array_tuple] >> simp[]) >>
  asm_simp_tac bool_ss [enc_static_array, enc_number_def]
QED

Theorem static_dynarray_source_windows:
  static_layout_compatible ce env ty tv /\ all_have_type tv vs /\
  vyper_to_abi_same env ty vs = SOME avs /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs))) source =
    enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) ==>
  mem_word_at sb source = n2w (LENGTH vs) /\
  mem_bytes_at (sb + 32) (LENGTH vs * type_memory_size tv) source =
    FLAT (MAP (enc (vyper_to_abi_type env ty)) avs)
Proof
  strip_tac >> drule static_layout_compatible_properties >> strip_tac >>
  drule_all static_same_canonical_layout >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_x_assum `mem_bytes_at sb _ source = _` mp_tac >>
  asm_simp_tac bool_ss [static_dynarray_encoding] >> strip_tac >>
  drule mem_bytes_at_append_parts >> strip_tac >>
  gvs[mem_word_at_bytes, word_of_bytes_word_to_bytes,
      dividesTheory.divides_def, Excl "enc_def"]
QED

Theorem static_dynarray_copied_layout:
  static_layout_compatible ce env ty tv /\ all_have_type tv vs /\
  vyper_to_abi_same env ty vs = SOME avs /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs))) source =
    enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  mem_word_at d mem = n2w (LENGTH vs) /\
  mem_bytes_at (d + 32) (LENGTH vs * type_memory_size tv) mem =
    mem_bytes_at (sb + 32) (LENGTH vs * type_memory_size tv) source ==>
  val_in_memory (ArrayTV tv (Dynamic n)) (ArrayV (DynArrayV vs)) d mem
Proof
  strip_tac >> drule_all static_dynarray_source_windows >> strip_tac >>
  `mem_bytes_at (d + 32) (LENGTH vs * type_memory_size tv) mem =
    FLAT (MAP (enc (vyper_to_abi_type env ty)) avs)` by asm_rewrite_tac[] >>
  mp_tac static_dynarray_canonical_layout >> asm_simp_tac bool_ss []
QED

(* ===== Metadata ===== *)

(* Static dynamic-array descriptor sizes derived from recursive coherence. *)

Theorem abi_decoder_bulk_metadata:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  DecDynArray ei abi_sz mem_sz F maxn =
    type_to_abi_dec_info sf ce (ArrayT ty (Dynamic maxn)) /\
  ~dec_info_needs_clamp ei ==>
  static_layout_compatible ce env ty tv /\
  ei = type_to_abi_dec_info sf ce ty /\
  abi_sz = type_memory_size tv /\ mem_sz = type_memory_size tv /\
  maxn < dimword (:256) /\
  type_memory_bytes ce (ArrayT ty (Dynamic maxn)) = 32 + maxn * mem_sz
Proof
  strip_tac >>
  qpat_x_assum `DecDynArray _ _ _ _ _ = _` mp_tac >>
  simp[Once type_to_abi_dec_info_def] >> strip_tac >>
  `abi_decoder_coherent ce env sf ty tv` by
    gvs[abi_decoder_coherent_array_iff] >>
  `static_layout_compatible ce env ty tv` by
    (drule_all abi_decoder_unclamped_static_layout >> simp[]) >>
  drule static_layout_compatible_properties >> strip_tac >>
  `abi_decoder_header ce env ty tv` by
    (drule abi_decoder_coherent_header >> simp[]) >>
  `evaluate_type env (ArrayT ty (Dynamic maxn)) =
   SOME (ArrayTV tv (Dynamic maxn))` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  mp_tac (Q.SPECL [`env`, `ArrayT ty (Dynamic maxn)`, `ArrayTV tv (Dynamic maxn)`]
    (cj 1 evaluate_type_well_formed)) >>
  simp[well_formed_type_value_def] >> strip_tac >>
  gvs[abi_decoder_header_def, abi_member_head_size_def, type_memory_bytes_def]
QED

(* ===== Typed ===== *)

(* Typed bulk dynamic-array decoding from canonical ABI source bytes. *)

Theorem abi_decoder_bulk_pre_facts:
  ~dec_info_needs_clamp ei /\
  abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn))
    (ArrayTV tv (Dynamic maxn)) (DecDynArray ei abi_sz mem_sz F maxn)
    (ListV avs) (ArrayV (DynArrayV vs)) st last src dst opc hi sb d b cap s ==>
  static_layout_compatible ce env ty tv /\ all_have_type tv vs /\
  vyper_to_abi_same env ty vs = SOME avs /\
  abi_sz = mem_sz /\ mem_sz = type_memory_size tv /\
  LENGTH vs <= maxn /\ maxn < dimword (:256) /\
  abi_decode_source_opcode opc /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  fresh_vars_wrt st s /\
  abi_decode_load opc (n2w sb : bytes32) s = n2w (LENGTH vs) /\
  sb + 32 < dimword (:256) /\ d + 32 < dimword (:256) /\
  LENGTH vs * mem_sz < dimword (:256) /\
  (opc = MLOAD ==> sb + 32 + LENGTH vs * mem_sz <= d \/ d + 32 <= sb + 32) /\
  (hi = Lit 0w \/ ?h. eval_operand hi s = SOME (n2w h) /\
                     sb + 32 + LENGTH vs * abi_sz <= h /\ h < dimword (:256)) /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    (abi_decode_source opc s) = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs) /\
  32 + LENGTH vs * mem_sz <= type_memory_bytes ce (ArrayT ty (Dynamic maxn))
Proof
  pure_rewrite_tac[abi_decoder_recursive_pre_def, abi_decoder_pre_def,
                   abi_decoder_metadata_def, abi_decoder_ranges_def] >> strip_tac >>
  drule_all abi_decoder_bulk_metadata >> strip_tac >>
  drule_all abi_decoder_typed_conversion >> strip_tac >>
  `vyper_to_abi_same env ty vs = SOME avs` by
    (qpat_x_assum `vyper_to_abi env (ArrayT _ _) _ = _` mp_tac >>
     simp[Once vyper_to_abi_def, AllCaseEqs()]) >>
  `all_have_type tv vs /\ LENGTH vs <= maxn` by fs[Once value_has_type_def] >>
  drule_all static_same_canonical_layout >> strip_tac >>
  drule static_layout_compatible_properties >> strip_tac >>
  `LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)) =
   32 + LENGTH vs * type_memory_size tv` by
    simp[static_dynarray_encoding, LENGTH_word_to_bytes, Excl "enc_def"] >>
  `mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
     (abi_decode_source opc s) = enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)` by
    fs[vyper_to_abi_type_def] >>
  `abi_decode_load opc (n2w sb : bytes32) s = n2w (LENGTH avs)` by
    (irule canonical_dynamic_array_count_load >>
     qexists_tac `vyper_to_abi_type env ty` >> fs[vyper_to_abi_type_def]) >>
  `LENGTH vs * mem_sz <= maxn * mem_sz` by simp[LE_MULT_RCANCEL] >>
  gvs[vyper_to_abi_type_def, abi_footprint_disjoint_def, type_memory_bytes_def,
      DISJ_IMP_THM, FORALL_AND_THM, Excl "enc_def"] >>
  rpt strip_tac >> gvs[Excl "enc_def"] >> TRY decide_tac >>
  disj2_tac >> rename1 `eval_operand hi s = SOME (n2w hb)` >>
  qexists_tac `hb` >> simp[] >> decide_tac
QED

(* ===== Fragment ===== *)

(* Typed execution and straight-line fragments for bulk dynamic-array decoding. *)

Theorem abi_decoder_typed_bulk_sequence:
  compile_abi_decode_to_buf dst src opc hi
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),st') /\
  ~dec_info_needs_clamp ei /\
  abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn))
    (ArrayTV tv (Dynamic maxn)) (DecDynArray ei abi_sz mem_sz F maxn)
    (ListV avs) (ArrayV (DynArrayV vs)) st last src dst opc hi sb d b cap s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    abi_decoder_post (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs))
      st' d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap s t
Proof
  strip_tac >> drule_all abi_decoder_bulk_pre_facts >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decode_bulk_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') s = OK t` >>
  `val_in_memory (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs)) d t.vs_memory` by
    (qpat_assum `mem_sz = type_memory_size tv`
       (fn th => RULE_ASSUM_TAC (PURE_REWRITE_RULE [th])) >>
     mp_tac (Q.INST [`n` |-> `maxn`, `mem` |-> `t.vs_memory`,
       `source` |-> `abi_decode_source opc s`] static_dynarray_copied_layout) >>
     asm_simp_tac bool_ss []) >>
  qexists_tac `t` >> simp[abi_decoder_post_def] >>
  irule abi_decoder_frame_from_output >> irule abi_decode_frame_widen >>
  qexistsl_tac [`d`, `32 + LENGTH vs * mem_sz`] >> simp[]
QED

Theorem abi_decoder_bulk_shape:
  compile_abi_decode_to_buf dst src opc hi
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),st') /\
  abi_decode_source_opcode opc /\ ~dec_info_needs_clamp ei ==>
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts st'.cs_current_insts /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts st st')
Proof
  strip_tac >> gvs[abi_decode_source_opcode_def] >> Cases_on `hi = Lit 0w` >>
  gvs[compile_abi_decode_to_buf_def, comp_bind_def, comp_ignore_bind_def,
      comp_return_def, emit_op_def, emit_void_def, fresh_var_def,
      fresh_id_def, emit_def, emitted_insts_def, IS_PREFIX_APPEND] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
  gvs[DROP_LENGTH_APPEND, is_terminator_def, mk_inst_def]
QED

Theorem abi_decoder_typed_bulk_fragment:
  compile_abi_decode_to_buf dst src opc hi
    (DecDynArray ei abi_sz mem_sz F maxn) st = ((),st') /\
  ~dec_info_needs_clamp ei ==>
  frag_exec ctx st st'
    (abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn))
       (ArrayTV tv (Dynamic maxn)) (DecDynArray ei abi_sz mem_sz F maxn)
       (ListV avs) (ArrayV (DynArrayV vs)) st last src dst opc hi sb d b cap)
    (\t. ?s. abi_decoder_recursive_pre ce env sf (ArrayT ty (Dynamic maxn))
       (ArrayTV tv (Dynamic maxn)) (DecDynArray ei abi_sz mem_sz F maxn)
       (ListV avs) (ArrayV (DynArrayV vs)) st last src dst opc hi sb d b cap s /\
       abi_decoder_post (ArrayTV tv (Dynamic maxn)) (ArrayV (DynArrayV vs))
         st' d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap s t)
    (K F)
Proof
  reverse (Cases_on `abi_decode_source_opcode opc`)
  >- simp[frag_exec_def, abi_decoder_recursive_pre_def,
          abi_decoder_pre_def, abi_decoder_ranges_def] >>
  strip_tac >> drule_all abi_decoder_bulk_shape >> strip_tac >>
  irule frag_exec_run_inst_seq >> simp[] >> rpt strip_tac >>
  drule_all abi_decoder_typed_bulk_sequence >> strip_tac >>
  qexists_tac `t` >> simp[abi_decoder_post_inst_idx] >> qexists_tac `s` >> simp[]
QED
