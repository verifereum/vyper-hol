(* Budget-free semantic transport for the scalar member execution. *)
Theory stmtSimLogScalarMembers
Ancestors
  abiDecoderRange
  stmtSimLogEncodeLayout abiEncoder emitHelper compileEnv abiEncoderInputFrame abiEncoderMembersStep
  abiEncoderTuple abiEncoderOpenPrefix abiDecoderFrame abiDecoderFrameCompose abiDecoderContract
  abiEncoderInput abiDecodeRanges valueEncoding valueEncodingDefs valueEncodingProps contractABI list arithmetic
  abiEncoderChildCode abiEncoderMemberCode abiEncoderReentryLeaves abiEncoderLeaves
  abiEncoderChildPrefix abiEncoderChildSuffix abiEncoderBytes abiEncoderCounters abiEncoderResultLive
  abiBuiltinPrefix abiDecoderReentry abiDecoderDynamicLoopSetup abiDecoderReentryAddress
  abiDecoderLoop abiDecoderGuards emitHelperProps exprLoweringProps venomState venomInst words

Theorem log_members_layout_frame:
  log_members_layout infos tys avs pre pvs sb so ho d hl outcap initial.vs_memory /\
  abi_decode_footprint_frame fp initial actual /\
  abi_footprint_disjoint (sb+so) (abi_encoder_member_span infos) fp /\
  abi_footprint_disjoint d (LENGTH (FLAT (abi_tuple_heads hl 0 pre pvs))) fp /\
  abi_footprint_disjoint (d+hl) (LENGTH (FLAT (abi_tuple_tails pre pvs))) fp ==>
  log_members_layout infos tys avs pre pvs sb so ho d hl outcap actual.vs_memory
Proof
  simp_tac bool_ss [log_members_layout_def] >> strip_tac >>
  drule_all abi_encoder_input_frame >> strip_tac >>
  drule_all abi_encoder_tuple_prefix_frame >> simp[]
QED

Theorem log_members_layout_advance:
  log_members_layout ((ei,asz,mz,dyn)::infos) (ty::tys) (av::avs)
    pre pvs sb so ho d hl outcap initial.vs_memory /\
  abi_decode_footprint_frame fp initial actual /\
  abi_footprint_disjoint (sb+so+mz) (abi_encoder_member_span infos) fp /\
  abi_encoder_tuple_prefix hl (pre++[ty]) (pvs++[av]) d actual.vs_memory ==>
  log_members_layout infos tys avs (pre++[ty]) (pvs++[av])
    sb (so+mz) (ho+asz) d hl outcap actual.vs_memory
Proof
  strip_tac >> drule log_members_layout_cons_input >> strip_tac >>
  drule_all abi_encoder_input_frame >> strip_tac >>
  qpat_x_assum `log_members_layout _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [log_members_layout_def, EVERY_DEF, pairTheory.pair_case_thm] >>
  strip_tac >> drule_all abi_encoder_members_prefix_advance >> strip_tac >>
  simp_tac bool_ss [log_members_layout_def, EVERY_DEF, pairTheory.pair_case_thm,
    GSYM APPEND_ASSOC, APPEND, ADD_ASSOC] >>
  fs[Excl "enc_def"]
QED

(* Expose the exact written head/tail bounds without a runtime budget. *)
Theorem log_members_layout_bounds:
  log_members_layout ((ei,asz,mz,dyn)::infos) (ty::tys) (av::avs)
    pre pvs sb so ho d hl outcap mem ==>
  LENGTH pre = LENGTH pvs /\
  ho = LENGTH (FLAT (abi_tuple_heads hl 0 pre pvs)) /\
  ho+asz <= hl /\ hl+LENGTH (FLAT (abi_tuple_tails pre pvs)) <= outcap /\
  (~dyn ==> ho+LENGTH (enc ty av) <= hl) /\
  (dyn ==> ho+32 <= hl /\
    hl+LENGTH (FLAT (abi_tuple_tails pre pvs))+LENGTH (enc ty av) <= outcap)
Proof
  strip_tac >> drule log_members_layout_cons_input >> strip_tac >>
  qpat_x_assum `log_members_layout _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [log_members_layout_def] >> strip_tac >>
  `LENGTH pre = LENGTH pvs` by (irule has_types_length >> simp[]) >>
  `has_types tys avs` by
    (drule abi_encoder_input_typed >> simp[Once has_type_def]) >>
  `has_types (pre++ty::tys) (pvs++av::avs)` by
    simp[has_types_append, has_type_def] >>
  mp_tac (Q.INST [`heads` |-> `ho:num`,
    `tails` |-> `SUM (MAP2 abi_member_tail_size pre pvs)`,
    `output_size` |-> `outcap:num`]
    abi_encoder_members_layout) >>
  (impl_tac >- asm_simp_tac bool_ss []) >> strip_tac >>
  gvs[Excl "enc_def"]
QED

Theorem log_members_layout_static_step:
  log_members_layout ((ei,asz,mz,F)::infos) (ty::tys) (av::avs)
    pre pvs sb so ho d hl outcap initial.vs_memory /\
  (sb+so+mz+abi_encoder_member_span infos <= d \/
    d+outcap <= sb+so+mz) /\
  abi_decode_footprint_frame [(d+ho,LENGTH (enc ty av))] initial actual /\
  mem_bytes_at (d+ho) (LENGTH (enc ty av)) actual.vs_memory = enc ty av ==>
  log_members_layout infos tys avs (pre++[ty]) (pvs++[av])
    sb (so+mz) (ho+asz) d hl outcap actual.vs_memory
Proof
  strip_tac >> drule log_members_layout_cons_input >> strip_tac >>
  drule log_members_layout_bounds >> strip_tac >>
  fs[Excl "enc_def"] >>
  `abi_encoder_tuple_prefix hl pre pvs d initial.vs_memory` by
    fs[log_members_layout_def, Excl "enc_def"] >>
  `abi_encoder_tuple_prefix hl pre pvs d actual.vs_memory` by
    (irule abi_encoder_tuple_prefix_frame >>
     qexistsl_tac [`[(d+ho,LENGTH (enc ty av))]`, `initial`] >>
     simp[abi_footprint_disjoint_def, Excl "enc_def"] >> decide_tac) >>
  `abi_encoder_tuple_prefix hl (pre++[ty]) (pvs++[av]) d actual.vs_memory` by
    (irule abi_encoder_tuple_prefix_append >>
     asm_simp_tac bool_ss [] >>
     fs[Excl "enc_def", mem_bytes_at_def]) >>
  drule log_members_layout_advance >>
  disch_then (qspecl_then [`[(d+ho,LENGTH (enc ty av))]`, `actual`] mp_tac) >>
  (impl_tac >- (simp[abi_footprint_disjoint_def, Excl "enc_def"] >> decide_tac)) >>
  `so+mz = mz+so` by decide_tac >> asm_simp_tac bool_ss []
QED

(* Static scalar child: one address ADD followed by the allocation-free copy. *)
Theorem log_scalar_copy_child_run:
  compile_abi_encode_child dst src (AbiCopy 32) F ho dp st = (out,end_st) /\
  abi_encoder_input (AbiCopy 32) ty av sb cap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\
  eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  sb < dimword (:256) /\ d+ho < dimword (:256) /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st end_st) initial = OK actual /\
    inst_extends st end_st /\ fresh_vars_wrt limit_st actual /\
    mem_bytes_at (d+ho) (LENGTH (enc ty av)) actual.vs_memory = enc ty av /\
    eval_operand out actual = SOME (n2w (LENGTH (enc ty av))) /\
    abi_decode_frame (d+ho) (LENGTH (enc ty av)) initial actual /\
    actual.vs_allocas = initial.vs_allocas /\
    actual.vs_alloca_next = initial.vs_alloca_next /\
    actual.vs_halted = initial.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w)
Proof
  strip_tac >> drule abi_encode_static_child_trace >> strip_tac >>
  drule abi_encode_copy_code >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  `prepared.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  `eval_operand (Lit (n2w ho)) initial = SOME (n2w ho)` by simp[eval_operand_def] >>
  drule_all abi_builtin_emit_add >> strip_tac >>
  rename1 `abi_builtin_prefix st prepared limit_st initial ready` >>
  qpat_x_assum `abi_builtin_prefix _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [abi_builtin_prefix_def, abi_decoder_address_frame_def] >> strip_tac >>
  `eval_operand src ready = SOME (n2w sb)` by (first_x_assum irule >> simp[]) >>
  `abi_encoder_input (AbiCopy 32) ty av sb cap ready.vs_memory` by gvs[] >>
  `eval_operand head ready = SOME (n2w (d+ho))` by fs[word_add_n2w] >>
  `32 < dimword (:256)` by simp[dimword_def] >>
  drule_all abi_encoder_copy_input_reentry >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts prepared end_st) ready = OK actual` >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  qexists_tac `actual` >>
  asm_simp_tac bool_ss [] >> gvs[abi_decode_frame_def] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem log_members_layout_static_child:
  compile_abi_encode_child dst src (AbiCopy 32) F ho dp st = (out,end_st) /\
  log_members_layout ((AbiCopy 32,asz,mz,F)::infos) (ty::tys) (av::avs)
    pre pvs sb so ho d hl outcap initial.vs_memory /\
  eval_operand src initial = SOME (n2w (sb+so)) /\
  eval_operand dst initial = SOME (n2w d) /\
  abi_decoder_operand_live st.cs_next_var src /\
  sb+so < dimword (:256) /\ d+ho < dimword (:256) /\
  (sb+so+mz+abi_encoder_member_span infos <= d \/ d+outcap <= sb+so+mz) /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st end_st) initial = OK actual /\
    inst_extends st end_st /\ fresh_vars_wrt limit_st actual /\
    log_members_layout infos tys avs (pre++[ty]) (pvs++[av])
      sb (so+mz) (ho+asz) d hl outcap actual.vs_memory /\
    eval_operand out actual = SOME (n2w (LENGTH (enc ty av))) /\
    abi_decode_frame (d+ho) (LENGTH (enc ty av)) initial actual /\
    actual.vs_allocas = initial.vs_allocas /\
    actual.vs_alloca_next = initial.vs_alloca_next /\
    actual.vs_halted = initial.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule log_members_layout_cons_input >> strip_tac >>
  drule_all log_scalar_copy_child_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st end_st) initial = OK actual` >>
  `abi_decode_footprint_frame [(d+ho,LENGTH (enc ty av))] initial actual` by
    (fs[abi_decode_frame_def, abi_decode_footprint_frame_def, abi_footprint_disjoint_def] >>
     rpt strip_tac >> first_x_assum irule >> simp[]) >>
  drule_all log_members_layout_static_step >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

(* Address setup followed by an allocation-free bytes child. *)
Theorem log_scalar_bytes_body_run:
  abi_encode_child_prefix dst ho dp st = (ops,prepared) /\
  compile_abi_encode_to_buf (SND (SND ops)) src (AbiBytestring mx) prepared = (len,child_end) /\
  abi_encoder_input (AbiBytestring mx) ty av sb cap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\
  eval_operand dst initial = SOME (n2w d) /\ eval_operand dp initial = SOME (n2w p) /\
  mload p initial = n2w off /\ p < dimword (:256) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\ abi_decoder_operand_live st.cs_next_var dp /\
  sb < dimword (:256) /\ d+off+LENGTH (enc ty av) < dimword (:256) /\
  (sb+cap <= d+off \/ d+off+LENGTH (enc ty av) <= sb) /\
  child_end.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?ready actual. abi_builtin_prefix st prepared limit_st initial ready /\
    run_inst_seq (emitted_insts prepared child_end) ready = OK actual /\
    inst_extends prepared child_end /\ fresh_vars_wrt limit_st actual /\
    eval_operand (FST ops) actual = SOME (n2w (d+ho)) /\
    eval_operand (FST (SND ops)) actual = SOME (n2w off) /\
    eval_operand len actual = SOME (n2w (LENGTH (enc ty av))) /\
    abi_decoder_operand_live child_end.cs_next_var len /\
    mem_bytes_at (d+off) (LENGTH (enc ty av)) actual.vs_memory = enc ty av /\
    abi_decode_frame (d+off) (LENGTH (enc ty av)) ready actual /\
    actual.vs_allocas = ready.vs_allocas /\ actual.vs_alloca_next = ready.vs_alloca_next /\
    actual.vs_halted = ready.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encoder_counters >> strip_tac >>
  drule abi_encode_result_live >> strip_tac >>
  drule abi_encode_child_prefix_shape >> strip_tac >>
  `prepared.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all abi_encode_child_prefix_sequence >> strip_tac >>
  rename1 `abi_builtin_prefix st prepared limit_st initial ready` >>
  qpat_assum `abi_builtin_prefix _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_prefix_def]) >>
  qpat_assum `abi_decoder_address_frame _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
  `eval_operand src ready = SOME (n2w sb)` by (first_x_assum irule >> simp[]) >>
  `abi_decoder_operand_live prepared.cs_next_var src` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  `abi_encoder_input (AbiBytestring mx) ty av sb cap ready.vs_memory` by gvs[] >>
  drule_all abi_encoder_bytes_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts prepared child_end) ready = OK actual` >>
  qexistsl_tac [`ready`, `actual`] >> asm_simp_tac bool_ss [] >>
  rpt strip_tac >>
  `abi_decoder_operand_live prepared.cs_next_var op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  `eval_operand op ready = SOME w` by (first_x_assum irule >> simp[]) >>
  first_x_assum irule >> simp[]
QED

Theorem log_scalar_bytes_child_run:
  compile_abi_encode_child dst src (AbiBytestring mx) T ho dp st = (out,end_st) /\
  abi_encoder_input (AbiBytestring mx) ty av sb cap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w d) /\
  eval_operand dp initial = SOME (n2w p) /\ mload p initial = n2w off /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\ abi_decoder_operand_live st.cs_next_var dp /\
  p < dimword (:256) /\ d+ho < dimword (:256) /\ sb < dimword (:256) /\
  d+off+LENGTH (enc ty av) < dimword (:256) /\
  (sb+cap <= d+off \/ d+off+LENGTH (enc ty av) <= sb) /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?ready encoded actual.
    run_inst_seq (emitted_insts st end_st) initial = OK actual /\
    inst_extends st end_st /\ fresh_vars_wrt limit_st actual /\
    ready.vs_memory = initial.vs_memory /\
    ready.vs_call_ctx = initial.vs_call_ctx /\ ready.vs_data_section = initial.vs_data_section /\
    mem_bytes_at (d+off) (LENGTH (enc ty av)) encoded.vs_memory = enc ty av /\
    abi_decode_frame (d+off) (LENGTH (enc ty av)) ready encoded /\
    actual.vs_memory =
      (mstore p (n2w (off+LENGTH (enc ty av))) (mstore (d+ho) (n2w off) encoded)).vs_memory /\
    abi_decode_footprint_frame [(d+ho,32);(p,32)] encoded actual /\
    eval_operand out actual = SOME (n2w (LENGTH (enc ty av))) /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    actual.vs_halted = initial.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_encode_dynamic_child_trace >> strip_tac >>
  drule abi_encode_child_suffix_shape >> strip_tac >>
  drule abi_encoder_counters >> strip_tac >>
  `child_end.cs_next_var <= limit_st.cs_next_var` by decide_tac >>
  drule_all log_scalar_bytes_body_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts prepared child_end) ready = OK encoded` >>
  `eval_operand dp encoded = SOME (n2w p)` by (first_x_assum irule >> simp[]) >>
  `abi_decoder_operand_live child_end.cs_next_var dp` by
    (drule abi_encode_child_prefix_shape >> strip_tac >>
     irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >> simp[]) >>
  drule_all abi_encode_child_suffix_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts child_end end_st) encoded = OK actual` >>
  qpat_assum `abi_builtin_prefix _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_prefix_def]) >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  qexistsl_tac [`ready`, `encoded`, `actual`] >>
  asm_simp_tac bool_ss [] >> gvs[abi_decoder_address_frame_def] >>
  rpt strip_tac >>
  `abi_decoder_operand_live child_end.cs_next_var op` by
    (irule abi_decoder_operand_live_mono >> qexists_tac `st.cs_next_var` >>
     drule abi_encode_child_prefix_shape >> strip_tac >> simp[]) >>
  `eval_operand op encoded = SOME w` by (first_x_assum irule >> simp[]) >>
  first_x_assum irule >> simp[]
QED

Theorem log_members_layout_dynamic_step:
  log_members_layout ((ei,asz,mz,T)::infos) (ty::tys) (av::avs)
    pre pvs sb so ho d hl outcap initial.vs_memory /\
  off = hl+LENGTH (FLAT (abi_tuple_tails pre pvs)) /\
  (d+outcap <= p \/ p+32 <= d) /\
  (sb+so+mz+abi_encoder_member_span infos <= d \/ d+outcap <= sb+so+mz) /\
  (sb+so+mz+abi_encoder_member_span infos <= p \/ p+32 <= sb+so+mz) /\
  abi_decode_footprint_frame [(d+ho,32);(d+off,LENGTH (enc ty av));(p,32)] initial actual /\
  mem_word_at (d+ho) actual.vs_memory = n2w off /\
  mem_bytes_at (d+off) (LENGTH (enc ty av)) actual.vs_memory = enc ty av ==>
  log_members_layout infos tys avs (pre++[ty]) (pvs++[av])
    sb (so+mz) (ho+asz) d hl outcap actual.vs_memory
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule log_members_layout_cons_input >> strip_tac >>
  drule log_members_layout_bounds >> strip_tac >>
  `abi_encoder_tuple_prefix hl pre pvs d initial.vs_memory` by
    fs[log_members_layout_def, Excl "enc_def"] >>
  `is_dynamic ty` by fs[Excl "enc_def"] >>
  `ho+32 <= hl /\ off+LENGTH (enc ty av) <= outcap` by fs[] >>
  `abi_encoder_tuple_prefix hl (pre++[ty]) (pvs++[av]) d actual.vs_memory` by
    (drule_at (Pat `abi_decode_footprint_frame _ _ _`) abi_encoder_tuple_dynamic_step >>
     simp_tac bool_ss [] >> disch_then irule >> simp[] >>
     qexists_tac `outcap` >> simp[] >> decide_tac) >>
  drule log_members_layout_advance >>
  disch_then (qspecl_then [`[(d+ho,32);(d+off,LENGTH (enc ty av));(p,32)]`, `actual`] mp_tac) >>
  (impl_tac >- (simp[abi_footprint_disjoint_def, Excl "enc_def"] >> decide_tac)) >>
  `so+mz = mz+so` by decide_tac >> asm_simp_tac bool_ss []
QED


Theorem log_footprint_prefix_transport:
  ready.vs_memory = initial.vs_memory /\
  ready.vs_call_ctx = initial.vs_call_ctx /\
  ready.vs_data_section = initial.vs_data_section /\
  abi_decode_footprint_frame fp ready actual ==>
  abi_decode_footprint_frame fp initial actual
Proof
  simp_tac bool_ss [abi_decode_footprint_frame_def] >>
  strip_tac >> asm_simp_tac bool_ss []
QED

Theorem log_bytes_phase_frame:
  ready.vs_memory = initial.vs_memory /\
  ready.vs_call_ctx = initial.vs_call_ctx /\
  ready.vs_data_section = initial.vs_data_section /\
  abi_decode_frame q n ready encoded /\
  abi_decode_footprint_frame [(h,32);(p,32)] encoded actual ==>
  abi_decode_footprint_frame [(h,32);(q,n);(p,32)] initial actual
Proof
  strip_tac >> drule (iffLR abi_decode_frame_footprint) >> strip_tac >>
  drule_all log_footprint_prefix_transport >> strip_tac >>
  irule abi_decode_footprint_frame_trans >> qexists_tac `encoded` >> conj_tac
  >- (irule abi_decode_footprint_frame_weaken >>
      qexists_tac `[(q,n)]` >> simp[] >>
      rpt strip_tac >> qexistsl_tac [`q`, `n`] >> simp[]) >>
  irule abi_decode_footprint_frame_weaken >>
  qexists_tac `[(h,32);(p,32)]` >> simp[] >>
  rpt strip_tac >> qexistsl_tac [`d`, `sz`] >> simp[]
QED

Theorem log_bytes_phase_contents:
  actual.vs_memory = (mstore p next (mstore h off encoded)).vs_memory /\
  mem_bytes_at q n encoded.vs_memory = bs /\
  (h+32 <= p \/ p+32 <= h) /\
  (q+n <= h \/ h+32 <= q) /\ (q+n <= p \/ p+32 <= q) ==>
  mem_word_at h actual.vs_memory = off /\
  mem_word_at p actual.vs_memory = next /\
  mem_bytes_at q n actual.vs_memory = bs
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_encoder_child_suffix_words >> strip_tac >>
  `mem_bytes_at q n (mstore p next (mstore h off encoded)).vs_memory =
    mem_bytes_at q n encoded.vs_memory` by
    (irule abi_encoder_child_suffix_preserves_tail >> asm_simp_tac bool_ss []) >>
  asm_simp_tac bool_ss []
QED

Theorem log_members_layout_dynamic_child:
  compile_abi_encode_child dst src (AbiBytestring mx) T ho dp st = (out,end_st) /\
  log_members_layout ((AbiBytestring mx,asz,mz,T)::infos) (ty::tys) (av::avs)
    pre pvs sb so ho d hl outcap initial.vs_memory /\
  off = hl+LENGTH (FLAT (abi_tuple_tails pre pvs)) /\
  eval_operand src initial = SOME (n2w (sb+so)) /\ eval_operand dst initial = SOME (n2w d) /\
  eval_operand dp initial = SOME (n2w p) /\ mload p initial = n2w off /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\ abi_decoder_operand_live st.cs_next_var dp /\
  p < dimword (:256) /\ d+ho < dimword (:256) /\ sb+so < dimword (:256) /\
  d+outcap < dimword (:256) /\
  (sb+so+mz <= d \/ d+outcap <= sb+so) /\
  (d+outcap <= p \/ p+32 <= d) /\
  (sb+so+mz+abi_encoder_member_span infos <= d \/ d+outcap <= sb+so+mz) /\
  (sb+so+mz+abi_encoder_member_span infos <= p \/ p+32 <= sb+so+mz) /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st end_st) initial = OK actual /\
    inst_extends st end_st /\ fresh_vars_wrt limit_st actual /\
    log_members_layout infos tys avs (pre++[ty]) (pvs++[av])
      sb (so+mz) (ho+asz) d hl outcap actual.vs_memory /\
    eval_operand out actual = SOME (n2w (LENGTH (enc ty av))) /\
    mload p actual = n2w (off+LENGTH (enc ty av)) /\
    abi_decode_footprint_frame [(d+ho,32);(d+off,LENGTH (enc ty av));(p,32)] initial actual /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    actual.vs_halted = initial.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule log_members_layout_cons_input >> strip_tac >>
  drule log_members_layout_bounds >> strip_tac >>
  `ho+32 <= off /\ off+LENGTH (enc ty av) <= outcap` by fs[] >>
  `d+off+LENGTH (enc ty av) < dimword (:256)` by decide_tac >>
  Q.SUBGOAL_THEN `sb+so+mz <= d+off \/ d+off+LENGTH (enc ty av) <= sb+so`
    assume_tac >- decide_tac >>
  drule_all log_scalar_bytes_child_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st end_st) initial = OK actual` >>
  drule_all log_bytes_phase_frame >> strip_tac >>
  (Q.SUBGOAL_THEN `d+ho+32 <= p \/ p+32 <= d+ho` assume_tac >- decide_tac) >>
  (Q.SUBGOAL_THEN `d+off+LENGTH (enc ty av) <= p \/ p+32 <= d+off` assume_tac >- decide_tac) >>
  (Q.SUBGOAL_THEN `d+off+LENGTH (enc ty av) <= d+ho \/ d+ho+32 <= d+off` assume_tac >- decide_tac) >>
  drule_all log_bytes_phase_contents >> strip_tac >>
  drule_all log_members_layout_dynamic_step >> strip_tac >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >>
  qpat_x_assum `mem_word_at p actual.vs_memory = _` mp_tac >>
  simp[mem_word_at_eq_mload]
QED

(* One member, with the common tuple-output/cursor footprint. *)
Theorem log_scalar_member_child_run:
  compile_abi_encode_child dst src ei dyn ho dp st = (out,end_st) /\
  log_members_layout ((ei,asz,mz,dyn)::infos) (ty::tys) (av::avs)
    pre pvs sb so ho d hl outcap initial.vs_memory /\
  eval_operand src initial = SOME (n2w (sb+so)) /\
  eval_operand dst initial = SOME (n2w d) /\ eval_operand dp initial = SOME (n2w p) /\
  mload p initial = n2w (hl+LENGTH (FLAT (abi_tuple_tails pre pvs))) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\ abi_decoder_operand_live st.cs_next_var dp /\
  sb+so < dimword (:256) /\ d+outcap < dimword (:256) /\ p < dimword (:256) /\
  (sb+so+mz+abi_encoder_member_span infos <= d \/ d+outcap <= sb+so) /\
  (sb+so+mz+abi_encoder_member_span infos <= p \/ p+32 <= sb+so) /\
  (d+outcap <= p \/ p+32 <= d) /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st end_st) initial = OK actual /\
    inst_extends st end_st /\ fresh_vars_wrt limit_st actual /\
    log_members_layout infos tys avs (pre++[ty]) (pvs++[av])
      sb (so+mz) (ho+asz) d hl outcap actual.vs_memory /\
    mload p actual = n2w (hl+LENGTH (FLAT (abi_tuple_tails (pre++[ty]) (pvs++[av])))) /\
    abi_decode_footprint_frame [(d,outcap);(p,32)] initial actual /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    actual.vs_halted = initial.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule log_members_layout_cons_input >> strip_tac >>
  drule log_members_layout_bounds >> strip_tac >>
  drule log_members_layout_offsets >> strip_tac >>
  `d+ho < dimword (:256)` by decide_tac >>
  qpat_x_assum `log_scalar_enc_info ei` mp_tac >>
  simp_tac bool_ss [log_scalar_enc_info_def] >> strip_tac
  >- suspend "static"
  >> suspend "dynamic"
QED

Resume log_scalar_member_child_run[static]:
  qpat_x_assum `ei = AbiCopy 32` SUBST_ALL_TAC >>
  `dyn = F` by
    (qpat_x_assum `abi_encoder_input (AbiCopy 32) _ _ _ _ _` mp_tac >>
     simp[abi_encoder_input_copy_iff]) >>
  qpat_x_assum `dyn = F` SUBST_ALL_TAC >>
  `ho+LENGTH (enc ty av) <= outcap` by fs[Excl "enc_def"] >>
  Q.SUBGOAL_THEN `sb+so+mz+abi_encoder_member_span infos <= d \/ d+outcap <= sb+so+mz`
    assume_tac >- decide_tac >>
  drule_all log_members_layout_static_child >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st end_st) initial = OK actual` >>
  `abi_decode_footprint_frame [(d+ho,LENGTH (enc ty av))] initial actual` by
    (irule (iffLR abi_decode_frame_footprint) >> asm_simp_tac bool_ss []) >>
  `mload p actual = mload p initial` by
    (irule abi_decode_footprint_frame_mload >>
     qexists_tac `[(d+ho,LENGTH (enc ty av))]` >>
     simp[abi_footprint_disjoint_def] >> decide_tac) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [] >> simp[] >>
  irule abi_decode_footprint_frame_weaken >>
  qexists_tac `[(d+ho,LENGTH (enc ty av))]` >> simp[] >>
  qexistsl_tac [`d`, `outcap`] >> simp[]
QED

Resume log_scalar_member_child_run[dynamic]:
  qpat_x_assum `ei = AbiBytestring n` SUBST_ALL_TAC >>
  `dyn = T` by
    (qpat_x_assum `abi_encoder_input (AbiBytestring _) _ _ _ _ _` mp_tac >>
     simp[abi_encoder_input_bytes_iff, is_dynamic_def] >> rpt strip_tac >> simp[is_dynamic_def]) >>
  qpat_x_assum `dyn = T` SUBST_ALL_TAC >>
  (Q.SUBGOAL_THEN `sb+so+mz <= d \/ d+outcap <= sb+so` assume_tac >- decide_tac) >>
  (Q.SUBGOAL_THEN `sb+so+mz+abi_encoder_member_span infos <= d \/ d+outcap <= sb+so+mz`
    assume_tac >- decide_tac) >>
  (Q.SUBGOAL_THEN `sb+so+mz+abi_encoder_member_span infos <= p \/ p+32 <= sb+so+mz`
    assume_tac >- decide_tac) >>
  drule_all (SIMP_RULE bool_ss [] (Q.INST
    [`off` |-> `hl+LENGTH (FLAT (abi_tuple_tails pre pvs))`]
    log_members_layout_dynamic_child)) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st end_st) initial = OK actual` >>
  qexists_tac `actual` >> asm_simp_tac bool_ss [ADD_ASSOC] >>
  irule abi_decode_footprint_frame_weaken >>
  qexists_tac `[(d+ho,32);(d+(hl+LENGTH (FLAT (abi_tuple_tails pre pvs))),LENGTH (enc ty av));(p,32)]` >>
  simp_tac bool_ss [] >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  simp_tac std_ss [MEM, pairTheory.PAIR_EQ, DISJ_IMP_THM, FORALL_AND_THM] >>
  conj_tac >- (qexistsl_tac [`d`, `outcap`] >> simp[] >> fs[Excl "enc_def"]) >>
  conj_tac >- (qexistsl_tac [`d`, `outcap`] >> simp[] >> fs[Excl "enc_def"]) >>
  qexistsl_tac [`p`, `32`] >> simp[]
QED

Finalise log_scalar_member_child_run

Theorem log_members_layout_lengths:
  log_members_layout infos tys avs pre pvs sb so ho d hl outcap mem ==>
  LENGTH infos = LENGTH tys /\ LENGTH tys = LENGTH avs
Proof
  simp_tac bool_ss [log_members_layout_def] >> strip_tac >>
  qpat_x_assum `abi_encoder_input _ _ _ _ _ _` mp_tac >>
  simp[abi_encoder_complex_input_iff, abi_encoder_tuple_type_def] >>
  rpt strip_tac >> gvs[]
QED

