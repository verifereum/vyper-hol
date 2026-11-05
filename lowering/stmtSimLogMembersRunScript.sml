(* Compact proof-only interfaces for the allocation-free scalar tuple loop. *)
Theory stmtSimLogMembersRun
Ancestors
  stmtSimLogScalarMembers abiEncoderInput abiDecoderGuards exprLoweringProps
  abiEncoderMemberCode abiEncoderCounters abiBuiltinPrefix abiEncoderAddressReach
  abiDecoderDynamicLoopSetup abiDecoderReentry abiDecoderFrame abiDecoderLoop
  emitHelperProps compileEnv emitHelper abiEncoder venomState venomInst
  stmtSimLogEncodeLayout contractABI words list arithmetic

Definition log_members_run_pre_def:
  log_members_run_pre infos tys avs pre pvs sb so ho d hl outcap st limit_st src dst dp p s <=>
    log_members_layout infos tys avs pre pvs sb so ho d hl outcap s.vs_memory /\
    eval_operand src s = SOME (n2w sb) /\
    eval_operand dst s = SOME (n2w d) /\ eval_operand dp s = SOME (n2w p) /\
    mload p s = n2w (hl+LENGTH (FLAT (abi_tuple_tails pre pvs))) /\
    abi_decoder_operand_live st.cs_next_var src /\
    abi_decoder_operand_live st.cs_next_var dst /\ abi_decoder_operand_live st.cs_next_var dp /\
    sb+so+abi_encoder_member_span infos < dimword (:256) /\
    d+outcap < dimword (:256) /\ p < dimword (:256) /\
    (sb+so+abi_encoder_member_span infos <= d \/ d+outcap <= sb+so) /\
    (sb+so+abi_encoder_member_span infos <= p \/ p+32 <= sb+so) /\
    (d+outcap <= p \/ p+32 <= d) /\ fresh_vars_wrt limit_st s
End

Definition log_members_run_post_def:
  log_members_run_post st end_st limit_st d outcap p initial actual <=>
    run_inst_seq (emitted_insts st end_st) initial = OK actual /\
    inst_extends st end_st /\ fresh_vars_wrt limit_st actual /\
    abi_decode_footprint_frame [(d,outcap);(p,32)] initial actual /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    actual.vs_halted = initial.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w)
End

Theorem log_members_span_cons[local]:
  abi_encoder_member_span ((ei,asz,mz,dyn)::infos) = mz+abi_encoder_member_span infos
Proof
  cheat
QED

Theorem log_members_run_post_refl:
  fresh_vars_wrt limit_st s ==> log_members_run_post st st limit_st d outcap p s s
Proof
  cheat
QED

Theorem log_members_run_post_trans:
  log_members_run_post st middle limit_st d outcap p s t /\
  log_members_run_post middle final limit_st d outcap p t u /\
  st.cs_next_var <= middle.cs_next_var ==>
  log_members_run_post st final limit_st d outcap p s u
Proof
  cheat
QED

Theorem log_members_run_pre_address:
  log_members_run_pre infos tys avs pre pvs sb so ho d hl outcap st limit_st src dst dp p s /\
  abi_decoder_address_frame st.cs_next_var s t /\ fresh_vars_wrt limit_st t /\
  st.cs_next_var <= next.cs_next_var ==>
  log_members_run_pre infos tys avs pre pvs sb so ho d hl outcap next limit_st src dst dp p t
Proof
  cheat
QED

Theorem log_members_run_post_prefix:
  abi_builtin_prefix st next limit_st s t ==>
  log_members_run_post st next limit_st d outcap p s t
Proof
  cheat
QED

Theorem log_members_run_source_add:
  emit_op ADD [src;Lit (n2w so)] st = (elem_src,next) /\
  log_members_run_pre infos tys avs pre pvs sb so ho d hl outcap
    st limit_st src dst dp p s /\
  next.cs_next_var <= limit_st.cs_next_var ==>
  ?t. log_members_run_pre infos tys avs pre pvs sb so ho d hl outcap
        next limit_st src dst dp p t /\
    eval_operand elem_src t = SOME (n2w (sb+so)) /\
    abi_decoder_operand_live next.cs_next_var elem_src /\
    log_members_run_post st next limit_st d outcap p s t
Proof
  cheat
QED

Theorem log_members_run_child:
  compile_abi_encode_child dst elem_src ei dyn ho dp st = (out,end_st) /\
  log_members_run_pre ((ei,asz,mz,dyn)::infos) (ty::tys) (av::avs)
    pre pvs sb so ho d hl outcap st limit_st src dst dp p s /\
  eval_operand elem_src s = SOME (n2w (sb+so)) /\
  abi_decoder_operand_live st.cs_next_var elem_src /\
  end_st.cs_next_var <= limit_st.cs_next_var ==>
  ?t. log_members_run_pre infos tys avs (pre++[ty]) (pvs++[av])
        sb (so+mz) (ho+asz) d hl outcap end_st limit_st src dst dp p t /\
    log_members_run_post st end_st limit_st d outcap p s t
Proof
  cheat
QED

Theorem log_members_run_cons:
  emit_op ADD [src;Lit (n2w so)] st = (elem_src,prepared) /\
  compile_abi_encode_child dst elem_src ei dyn ho dp prepared = (out,child_end) /\
  log_members_run_pre ((ei,asz,mz,dyn)::infos) (ty::tys) (av::avs)
    pre pvs sb so ho d hl outcap st limit_st src dst dp p s /\
  child_end.cs_next_var <= limit_st.cs_next_var ==>
  ?t. log_members_run_pre infos tys avs (pre++[ty]) (pvs++[av])
        sb (so+mz) (ho+asz) d hl outcap child_end limit_st src dst dp p t /\
    log_members_run_post st child_end limit_st d outcap p s t
Proof
  cheat
QED

Theorem log_members_run_pre_lengths:
  log_members_run_pre infos tys avs pre pvs sb so ho d hl outcap st limit_st src dst dp p s ==>
  LENGTH infos = LENGTH tys /\ LENGTH tys = LENGTH avs
Proof
  cheat
QED

Theorem log_members_run_pre_fresh:
  log_members_run_pre infos tys avs pre pvs sb so ho d hl outcap st limit_st src dst dp p s ==>
  fresh_vars_wrt limit_st s
Proof
  cheat
QED

Theorem log_members_run_list:
  !infos dst src so ho dp st out final tys avs pre pvs sb d hl outcap limit_st p s.
  compile_abi_encode_complex_elems dst src infos so ho dp st = (out,final) /\
  log_members_run_pre infos tys avs pre pvs sb so ho d hl outcap st limit_st src dst dp p s /\
  final.cs_next_var <= limit_st.cs_next_var ==>
  ?t. log_members_run_pre [] [] [] (pre++tys) (pvs++avs)
        sb (so+abi_encoder_member_span infos)
        (ho+SUM (MAP (\(_,asz,_,_). asz) infos)) d hl outcap
        final limit_st src dst dp p t /\
    log_members_run_post st final limit_st d outcap p s t
Proof
  cheat
QED



(* Public unbundled endpoint; no interval allocation budget is required. *)
Theorem log_scalar_members_run:
  compile_abi_encode_complex_elems dst src infos so ho dp st = (out,final) /\
  log_members_layout infos tys avs pre pvs sb so ho d hl outcap initial.vs_memory /\
  eval_operand src initial = SOME (n2w sb) /\
  eval_operand dst initial = SOME (n2w d) /\ eval_operand dp initial = SOME (n2w p) /\
  mload p initial = n2w (hl+LENGTH (FLAT (abi_tuple_tails pre pvs))) /\
  abi_decoder_operand_live st.cs_next_var src /\
  abi_decoder_operand_live st.cs_next_var dst /\ abi_decoder_operand_live st.cs_next_var dp /\
  sb+so+abi_encoder_member_span infos < dimword (:256) /\
  d+outcap < dimword (:256) /\ p < dimword (:256) /\
  (sb+so+abi_encoder_member_span infos <= d \/ d+outcap <= sb+so) /\
  (sb+so+abi_encoder_member_span infos <= p \/ p+32 <= sb+so) /\
  (d+outcap <= p \/ p+32 <= d) /\ fresh_vars_wrt limit_st initial /\
  final.cs_next_var <= limit_st.cs_next_var ==>
  ?actual. run_inst_seq (emitted_insts st final) initial = OK actual /\
    inst_extends st final /\ fresh_vars_wrt limit_st actual /\
    log_members_layout [] [] [] (pre++tys) (pvs++avs)
      sb (so+abi_encoder_member_span infos)
      (ho+SUM (MAP (\(_,asz,_,_). asz) infos)) d hl outcap actual.vs_memory /\
    mload p actual = n2w (hl+LENGTH (FLAT (abi_tuple_tails (pre++tys) (pvs++avs)))) /\
    abi_decode_footprint_frame [(d,outcap);(p,32)] initial actual /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    actual.vs_halted = initial.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w)
Proof
  cheat
QED
