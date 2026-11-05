(* Budget-free semantic transport for the scalar member execution. *)
Theory stmtSimLogScalarMembers
Ancestors
  stmtSimLogEncodeLayout abiEncoder emitHelper compileEnv abiEncoderInputFrame abiEncoderMembersStep
  abiEncoderTuple abiEncoderOpenPrefix abiDecoderFrame abiDecoderFrameCompose abiDecoderContract
  abiEncoderInput abiDecodeRanges valueEncoding valueEncodingProps contractABI list arithmetic
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
  cheat
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
  cheat
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
  cheat
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
  cheat
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
  cheat
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
  cheat
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
  cheat
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
  cheat
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
  cheat
QED


Theorem log_footprint_prefix_transport:
  ready.vs_memory = initial.vs_memory /\
  ready.vs_call_ctx = initial.vs_call_ctx /\
  ready.vs_data_section = initial.vs_data_section /\
  abi_decode_footprint_frame fp ready actual ==>
  abi_decode_footprint_frame fp initial actual
Proof
  cheat
QED

Theorem log_bytes_phase_frame:
  ready.vs_memory = initial.vs_memory /\
  ready.vs_call_ctx = initial.vs_call_ctx /\
  ready.vs_data_section = initial.vs_data_section /\
  abi_decode_frame q n ready encoded /\
  abi_decode_footprint_frame [(h,32);(p,32)] encoded actual ==>
  abi_decode_footprint_frame [(h,32);(q,n);(p,32)] initial actual
Proof
  cheat
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
  cheat
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
  cheat
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
  cheat
QED




Theorem log_members_layout_lengths:
  log_members_layout infos tys avs pre pvs sb so ho d hl outcap mem ==>
  LENGTH infos = LENGTH tys /\ LENGTH tys = LENGTH avs
Proof
  cheat
QED

