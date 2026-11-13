Theory exprSimAbiEncodeTupleOpen
Ancestors
  abiEncoderOpenRelocate abiEncoderOpenInput abiEncoderWrites abiEncoderBytes
  abiDecoderContract abiDecoderReentry abiTupleEncodeSlot
  context exprLowering emitHelper emitHelperProps exprLoweringProps
  valueEncoding valueEncodingDefs valueEncodingProps compileEnv venomState venomInst venomMemDefs
  contractABI words list abiEncoderOpenInputFrame abiDecoderFrameCompose
  abiTupleEncodeInput abiTupleEncodeMemory abiTupleProps arithmetic
  abiBuiltinPrefix abiDecoderDynamicLoopSetup abiDecoderGuards abiDecoderRange abiTupleEncodePrepare

(* Only the meaningful prefix is owned. MCOPY may snapshot unused source
   padding that overlaps the destination, without affecting this result. *)
Theorem abi_encode_open_copy_write:
  compile_copy_memory dst src n st = ((),final) /\
  eval_operand dst s = SOME (n2w d) /\ d < dimword (:256) /\
  eval_operand src s = SOME (n2w sb) /\ sb < dimword (:256) /\
  n < dimword (:256) /\ fresh_vars_wrt limit_st s /\
  abi_encoder_open_input ei at av sb cap s.vs_memory /\ cap <= n ==>
  ?actual. run_inst_seq (emitted_insts st final) s = OK actual /\
    inst_extends st final /\
    abi_encoder_open_input ei at av d n actual.vs_memory /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame d n s actual /\
    actual.vs_allocas = s.vs_allocas /\ actual.vs_alloca_next = s.vs_alloca_next /\
    actual.vs_halted = s.vs_halted /\
    (!op. eval_operand op actual = eval_operand op s)
Proof
  strip_tac >> Cases_on `n = 0`
  >- (gvs[compile_copy_memory_def, comp_return_def] >>
      `abi_encoder_open_input ei at av d 0 s.vs_memory` by
        (irule abi_encoder_open_input_relocate_capacity >>
         goal_assum (drule_at Any) >> simp[mem_bytes_at_def]) >>
      qexists_tac `s` >>
      simp[emitted_insts_def, run_inst_seq_def, inst_extends_def,
           abi_decode_frame_def]) >>
  `emit_void MCOPY [dst;src;Lit (n2w n)] st = ((),final)` by
    (Cases_on `n` >> gvs[compile_copy_memory_def]) >>
  `eval_operand (Lit (n2w n)) s = SOME (n2w n)` by simp[eval_operand_def] >>
  drule_all abi_encoder_emit_copy >> strip_tac >>
  `abi_decode_frame d n s (mcopy d sb n s)` by
    (simp_tac bool_ss [abi_decode_frame_def] >> conj_tac
     >- (rpt strip_tac >> irule mcopy_mem_bytes_at_disjoint >> simp[]) >> simp[]) >>
  drule_all abi_encoder_open_input_mcopy_prefix >>
  disch_then (qspec_then `d` assume_tac) >>
  qexists_tac `mcopy d sb n s` >> simp[abi_encoder_copy_eval]
QED

Theorem abi_encode_open_bytes_copy:
  compile_copy_memory dst src n st = ((),final) /\
  eval_operand dst s = SOME (n2w d) /\ d < dimword (:256) /\
  eval_operand src s = SOME (n2w sb) /\ sb < dimword (:256) /\
  n < dimword (:256) /\ fresh_vars_wrt limit_st s /\
  (at = Bytes NONE \/ at = String) /\ has_type at (BytesV bs) /\
  LENGTH bs <= maxlen /\ 32 + LENGTH bs <= n /\
  mem_word_at sb s.vs_memory = n2w (LENGTH bs) /\
  mem_bytes_at (sb+32) (LENGTH bs) s.vs_memory = bs ==>
  ?actual. run_inst_seq (emitted_insts st final) s = OK actual /\
    abi_encoder_open_input (AbiBytestring maxlen) at (BytesV bs)
      d n actual.vs_memory /\ abi_decode_frame d n s actual
Proof
  strip_tac >>
  `abi_encoder_open_input (AbiBytestring maxlen) at (BytesV bs)
     sb (32+LENGTH bs) s.vs_memory` by
    (irule abiEncoderOpenInputTheory.bytes >> simp[]) >>
  drule_all abi_encode_open_copy_write >> metis_tac[]
QED

(* The destination starts precisely where the meaningful prefix ends,
   inside the unused half of the declared source capacity. *)
Theorem abi_encode_open_copy_padding_overlap:
  abi_encoder_open_input (AbiBytestring 32) (Bytes NONE) (BytesV [])
    0 32 s.vs_memory ==>
  abi_encoder_open_input (AbiBytestring 32) (Bytes NONE) (BytesV [])
    32 64 (mcopy 32 0 64 s).vs_memory /\
  venomMemDefs$regions_disjoint (0,32) (32,64) /\
  ~venomMemDefs$regions_disjoint (0,64) (32,64)
Proof
  strip_tac >> reverse conj_tac
  >- simp[venomMemDefsTheory.regions_disjoint_def] >>
  irule abi_encoder_open_input_mcopy_prefix >>
  goal_assum (drule_at Any) >> simp[]
QED

Definition abi_tuple_open_input_def:
  abi_tuple_open_input sf ce ty at av op next lo hi s <=>
    abi_decoder_operand_live next op /\ type_memory_bytes ce ty < dimword (:256) /\
    if is_word_type ty then
      ?w. eval_operand op s = SOME w /\ has_type at av /\ ~is_dynamic at /\
        static_length at = 32 /\ word_to_bytes w T = enc at av
    else
      ?sb cap. eval_operand op s = SOME (n2w sb) /\ sb < dimword (:256) /\
        cap <= type_memory_bytes ce ty /\
        abi_encoder_open_input (type_to_abi_enc_info sf ce ty) at av sb cap s.vs_memory /\
        (sb+cap <= lo \/ hi <= sb)
End

Definition abi_tuple_open_inputs_def:
  abi_tuple_open_inputs sf ce [] ats avs next lo hi s = (ats = [] /\ avs = []) /\
  abi_tuple_open_inputs sf ce ((op,ty)::xs) ats avs next lo hi s =
    ?at ts av vs. ats = at::ts /\ avs = av::vs /\
      abi_tuple_open_input sf ce ty at av op next lo hi s /\
      abi_tuple_open_inputs sf ce xs ts vs next lo hi s
End

Definition abi_tuple_open_memory_def:
  abi_tuple_open_memory sf ce [] ats avs d mem = (ats = [] /\ avs = []) /\
  abi_tuple_open_memory sf ce ((op,ty)::xs) ats avs d mem =
    ?at ts av vs. ats = at::ts /\ avs = av::vs /\
      abi_encoder_open_input (type_to_abi_enc_info sf ce ty) at av d
        (type_memory_bytes ce ty) mem /\
      abi_tuple_open_memory sf ce xs ts vs (d+type_memory_bytes ce ty) mem
End

Definition abi_tuple_open_result_def:
  abi_tuple_open_result sf ce xs ats avs st final limit_st d s t <=>
    run_inst_seq (emitted_insts st final) s = OK t /\ inst_extends st final /\
    abi_tuple_open_memory sf ce xs ats avs d t.vs_memory /\
    fresh_vars_wrt limit_st t /\ abi_decode_frame d (abi_tuple_bytes ce xs) s t /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_halted = s.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\ eval_operand op s = SOME w ==>
      eval_operand op t = SOME w)
End

Theorem abi_tuple_open_input_transport:
  abi_tuple_open_input sf ce ty at av op next lo hi s /\ next <= later /\ lo <= hi /\
  (!op w. abi_decoder_operand_live next op /\ eval_operand op s = SOME w ==>
    eval_operand op t = SOME w) /\ abi_decode_frame lo (hi-lo) s t ==>
  abi_tuple_open_input sf ce ty at av op later lo hi t
Proof
  simp_tac bool_ss [abi_tuple_open_input_def] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_decoder_operand_live later op` by
    (irule abi_decoder_operand_live_mono >> goal_assum (drule_at Any) >> simp[]) >>
  Cases_on `is_word_type ty` >> gvs[]
  >- (qexists_tac `w` >> simp[] >> first_x_assum irule >> simp[]) >>
  qexistsl_tac [`sb`, `cap`] >> simp[] >>
  irule abi_encoder_open_input_mem_agree >> goal_assum (drule_at Any) >>
  irule EQ_SYM >>
  qpat_x_assum `abi_decode_frame _ _ _ _`
    (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_decode_frame_def]) >>
  disch_then irule >> decide_tac
QED

Theorem abi_tuple_open_inputs_transport:
  !xs ats avs next later lo hi s t.
  abi_tuple_open_inputs sf ce xs ats avs next lo hi s /\ next <= later /\ lo <= hi /\
  (!op w. abi_decoder_operand_live next op /\ eval_operand op s = SOME w ==>
    eval_operand op t = SOME w) /\ abi_decode_frame lo (hi-lo) s t ==>
  abi_tuple_open_inputs sf ce xs ats avs later lo hi t
Proof
  Induct >- simp[abi_tuple_open_inputs_def] >> gen_tac >> PairCases_on `h` >>
  simp[abi_tuple_open_inputs_def] >> rpt gen_tac >> strip_tac >> gvs[] >> conj_tac
  >- (drule_all abi_tuple_open_input_transport >> simp[]) >>
  first_x_assum drule_all >> simp[]
QED

Theorem abi_tuple_open_write:
  (if is_word_type ty then emit_void MSTORE [dst;op]
   else compile_copy_memory dst op (type_memory_bytes ce ty)) st = ((),final) /\
  eval_operand dst s = SOME (n2w d) /\ d < dimword (:256) /\
  fresh_vars_wrt limit_st s /\
  abi_tuple_open_input sf ce ty at av op next lo hi s ==>
  ?actual. run_inst_seq (emitted_insts st final) s = OK actual /\ inst_extends st final /\
    abi_encoder_open_input (type_to_abi_enc_info sf ce ty) at av d
      (type_memory_bytes ce ty) actual.vs_memory /\
    fresh_vars_wrt limit_st actual /\ abi_decode_frame d (type_memory_bytes ce ty) s actual /\
    actual.vs_allocas = s.vs_allocas /\ actual.vs_alloca_next = s.vs_alloca_next /\
    actual.vs_halted = s.vs_halted /\ (!op. eval_operand op actual = eval_operand op s)
Proof
  strip_tac >> Cases_on `is_word_type ty`
  >- (`abi_tuple_encode_input sf ce ty at av op next lo hi s` by
        gvs[abi_tuple_open_input_def, abi_tuple_encode_input_def] >>
      gvs[] >> drule_all abi_tuple_encode_word_write >> strip_tac >>
      drule abi_encoder_input_open >> metis_tac[]) >>
  gvs[abi_tuple_open_input_def] >> drule_all abi_encode_open_copy_write >> metis_tac[]
QED

Theorem abi_tuple_open_result_slot:
  compile_abi_tuple_slot ce buf off op ty st = ((),final) /\
  eval_operand buf s = SOME (n2w baddr) /\ baddr+off < dimword (:256) /\ lo <= hi /\
  abi_tuple_open_input sf ce ty at av op st.cs_next_var lo hi s /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?actual. abi_tuple_open_result sf ce [(op,ty)] [at] [av]
    st final limit_st (baddr+off) s actual
Proof
  strip_tac >> drule abi_tuple_encode_slot_shape >> strip_tac >>
  qpat_x_assum `compile_abi_tuple_slot _ _ _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [compile_abi_tuple_slot_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >>
  rename1 `emit_op ADD [buf;Lit (n2w off)] st = (dst,address_st)` >>
  gvs[] >> drule emitted_insts_emit_op >> strip_tac >>
  `address_st.cs_next_var <= limit_st.cs_next_var /\
   st.cs_next_var <= address_st.cs_next_var` by decide_tac >>
  `eval_operand (Lit (n2w off)) s = SOME (n2w off)` by simp[eval_operand_def] >>
  drule_all abi_builtin_emit_add >> strip_tac >>
  rename1 `abi_builtin_prefix st address_st limit_st s addressed` >>
  qpat_assum `abi_builtin_prefix _ _ _ _ _`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_prefix_def]) >>
  qpat_assum `abi_decoder_address_frame _ _ _`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_address_frame_def]) >>
  `eval_operand dst addressed = SOME (n2w (baddr+off))` by fs[word_add_n2w] >>
  `abi_decode_frame lo (hi-lo) s addressed` by simp[abi_decode_frame_def] >>
  `abi_tuple_open_input sf ce ty at av op address_st.cs_next_var lo hi addressed` by
    (irule abi_tuple_open_input_transport >> conj_tac >- simp[] >>
     qexistsl_tac [`st.cs_next_var`, `s`] >> simp[]) >>
  drule_all abi_tuple_open_write >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts address_st final) addressed = OK actual` >>
  `run_inst_seq (emitted_insts st final) s = OK actual /\ inst_extends st final` by
    (irule abi_decode_sequence_chain >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `abi_decode_frame (baddr+off) (type_memory_bytes ce ty) s actual` by
    (irule abi_decode_frame_trans >> qexists_tac `addressed` >> simp[abi_decode_frame_def]) >>
  qexists_tac `actual` >>
  simp[abi_tuple_open_result_def, abi_tuple_open_memory_def, abi_tuple_bytes_def] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem abi_tuple_open_result_cons:
  abi_tuple_open_result sf ce [(op,ty)] [at] [av] st middle limit_st d s t /\
  abi_tuple_open_result sf ce xs ats avs middle final limit_st
    (d+type_memory_bytes ce ty) t u /\
  st.cs_next_var <= middle.cs_next_var ==>
  abi_tuple_open_result sf ce ((op,ty)::xs) (at::ats) (av::avs)
    st final limit_st d s u
Proof
  simp_tac (srw_ss()) [abi_tuple_open_result_def, abi_tuple_open_memory_def,
    abi_tuple_bytes_def] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `abi_encoder_open_input (type_to_abi_enc_info sf ce ty) at av d
     (type_memory_bytes ce ty) u.vs_memory` by
    (irule abi_encoder_open_input_mem_agree >> qexists_tac `t.vs_memory` >> simp[] >>
     irule EQ_SYM >> qpat_x_assum `abi_decode_frame (d+_) _ _ _`
       (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [abi_decode_frame_def]) >>
     disch_then irule >> simp[]) >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  drule_all abi_decode_frame_adjacent >> strip_tac >> simp[] >>
  qx_genl_tac [`older`, `older_word`] >> strip_tac >>
  `eval_operand older t = SOME older_word` by (first_x_assum irule >> simp[]) >>
  qpat_x_assum `!op w. abi_decoder_operand_live middle.cs_next_var op /\ _ ==> _` irule >>
  simp[] >> irule abi_decoder_operand_live_mono >>
  qexists_tac `st.cs_next_var` >> simp[]
QED

Theorem abi_tuple_open_tail_inputs:
  abi_tuple_open_result sf ce [(op,ty)] [at] [av] st middle limit_st d s t /\
  abi_tuple_open_inputs sf ce xs ats avs st.cs_next_var lo hi s /\
  st.cs_next_var <= middle.cs_next_var /\ lo <= d /\ d+type_memory_bytes ce ty <= hi ==>
  abi_tuple_open_inputs sf ce xs ats avs middle.cs_next_var lo hi t
Proof
  strip_tac >>
  qpat_x_assum `abi_tuple_open_result _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[abi_tuple_open_result_def, abi_tuple_bytes_def] >> strip_tac >>
  `lo <= hi` by decide_tac >>
  `abi_decode_frame lo (hi-lo) s t` by
    (irule abi_decode_frame_widen >>
     qexistsl_tac [`d`, `type_memory_bytes ce ty`] >> simp[] >> decide_tac) >>
  drule_all abi_tuple_open_inputs_transport >> simp[]
QED

Theorem abi_tuple_open_sequence:
  !xs ce buf off st final s baddr ats avs lo hi.
  compile_store_abi_tuple ce buf off xs st = ((),final) /\
  eval_operand buf s = SOME (n2w baddr) /\ abi_decoder_operand_live st.cs_next_var buf /\
  lo <= baddr+off /\ baddr+off+abi_tuple_bytes ce xs <= hi /\ hi < dimword (:256) /\
  abi_tuple_open_inputs sf ce xs ats avs st.cs_next_var lo hi s /\
  final.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?actual. abi_tuple_open_result sf ce xs ats avs st final limit_st (baddr+off) s actual
Proof
  Induct
  >- (simp[compile_store_abi_tuple_def, comp_return_def, abi_tuple_open_inputs_def] >>
      rpt strip_tac >> gvs[] >> qexists_tac `s` >>
      simp[abi_tuple_open_result_def, emitted_insts_def, run_inst_seq_def,
        inst_extends_refl, abi_tuple_open_memory_def, abi_tuple_bytes_def,
        abi_decode_frame_def]) >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  simp_tac bool_ss [abi_tuple_encode_store_cons, comp_ignore_bind_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[abi_tuple_open_inputs_def] >>
  rename1 `compile_abi_tuple_slot ce buf off h0 h1 st = ((),middle)` >>
  rename1 `abi_tuple_open_input sf ce h1 head_at head_av h0 st.cs_next_var lo hi s` >>
  rename1 `abi_tuple_open_inputs sf ce xs tail_ats tail_avs st.cs_next_var lo hi s` >>
  drule abi_tuple_encode_slot_shape >> strip_tac >>
  drule abi_tuple_encode_store_shape >> strip_tac >>
  `middle.cs_next_var <= limit_st.cs_next_var /\ st.cs_next_var <= middle.cs_next_var /\
   baddr+off < dimword (:256) /\ lo <= hi /\ baddr+off+type_memory_bytes ce h1 <= hi /\
   lo <= baddr+(off+type_memory_bytes ce h1) /\
   baddr+(off+type_memory_bytes ce h1)+abi_tuple_bytes ce xs <= hi` by
    (fs[abi_tuple_bytes_def] >> decide_tac) >>
  drule_all abi_tuple_open_result_slot >> strip_tac >>
  rename1 `abi_tuple_open_result sf ce [(h0,h1)] [head_at] [head_av]
    st middle limit_st (baddr+off) s written` >>
  drule_all abi_tuple_open_tail_inputs >> strip_tac >>
  `eval_operand buf written = SOME (n2w baddr) /\ fresh_vars_wrt limit_st written` by
    (fs[abi_tuple_open_result_def] >> metis_tac[]) >>
  `abi_decoder_operand_live middle.cs_next_var buf` by
    (irule abi_decoder_operand_live_mono >> goal_assum (drule_at Any) >> simp[]) >>
  `?actual. abi_tuple_open_result sf ce xs tail_ats tail_avs middle final limit_st
    (baddr+(off+type_memory_bytes ce h1)) written actual` by
    (first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >>
     conj_tac >- (qexists_tac `buf` >> gvs[]) >>
     qexistsl_tac [`hi`, `lo`] >> gvs[] >> decide_tac) >>
  qexists_tac `actual` >> irule abi_tuple_open_result_cons >>
  qexistsl_tac [`middle`, `written`] >>
  asm_simp_tac bool_ss [ADD_ASSOC] >>
  qpat_x_assum `abi_tuple_open_result _ _ xs _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac bool_ss [ADD_ASSOC]
QED
