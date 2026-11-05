(* Selected-shape scalar tuple encoding; static tuples need no cursor. *)
Theory stmtSimLogScalarEncode
Ancestors
  stmtSimLogMembersRun stmtSimLogScalarPrefix stmtSimLogScalarMembers
  stmtSimLogEncodeLayout abiEncoderReentryLeaves abiEncoderInputFrame abiEncoderInput
  abiEncoderComplexCode abiEncoderComplexPrefix abiEncoderMemberCode abiBuiltinPrefix
  abiEncoderComplexDynamic abiEncoderMembersInput abiEncoderTuple abiEncoderOpenInput
  abiBuiltinAllocation abiDecoderReentry abiDecoderFrame abiDecoderFrameCompose abiDecoderDynamicLoopSetup
  abiDecoderGuards exprLoweringProps emitHelperProps compileEnv emitHelper abiEncoder
  abiCanonicalWindows valueEncoding contractABI venomState venomInst words list arithmetic finite_map

Theorem log_scalar_tuple_copy_run[local]:
  compile_abi_encode_to_buf dst src (AbiCopy n) st = (out,end_st) /\
  abi_encoder_input (AbiCopy n) (Tuple ats) (ListV avs) sb cap initial.vs_memory /\
  n < dimword (:256) /\ LENGTH (enc (Tuple ats) (ListV avs)) <= outcap /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w db) /\
  sb+cap < dimword (:256) /\ db+outcap < dimword (:256) /\
  fresh_vars_wrt limit_st initial ==>
  ?actual. run_inst_seq (emitted_insts st end_st) initial = OK actual /\
    inst_extends st end_st /\ fresh_vars_wrt limit_st actual /\
    mem_bytes_at db (LENGTH (enc (Tuple ats) (ListV avs))) actual.vs_memory =
      enc (Tuple ats) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Tuple ats) (ListV avs)))) /\
    abi_decode_footprint_frame [(db,outcap)] initial actual /\
    actual.vs_allocas = initial.vs_allocas /\ actual.vs_alloca_next = initial.vs_alloca_next /\
    actual.vs_halted = initial.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w)
Proof
  cheat
QED

Theorem log_scalar_tuple_members_run[local]:
  compile_abi_encode_complex_elems dst src infos 0 0 dp st = (out,end_st) /\
  log_members_run_pre infos ats avs [] [] sb 0 0 db hl outcap st limit_st src dst dp p initial /\
  end_st.cs_next_var <= limit_st.cs_next_var ==>
  ?actual. log_members_run_post st end_st limit_st db outcap p initial actual /\
    mem_bytes_at db (LENGTH (enc (Tuple ats) (ListV avs))) actual.vs_memory =
      enc (Tuple ats) (ListV avs) /\
    mload p actual = n2w (LENGTH (enc (Tuple ats) (ListV avs)))
Proof
  cheat
QED

Theorem log_scalar_tuple_load[local]:
  emit_op MLOAD [dp] st = (out,end_st) /\
  eval_operand dp initial = SOME (n2w p) /\ p < dimword (:256) /\
  mload p initial = n2w len /\ fresh_vars_wrt limit_st initial /\
  end_st.cs_next_var <= limit_st.cs_next_var ==>
  ?actual. log_members_run_post st end_st limit_st db outcap p initial actual /\
    eval_operand out actual = SOME (n2w len) /\ actual.vs_memory = initial.vs_memory
Proof
  cheat
QED

Theorem log_scalar_tuple_layout_frame[local]:
  abi_encoder_input (AbiComplex infos) (Tuple ats) (ListV avs) sb cap initial.vs_memory /\
  EVERY (\(child,asz,mz,dyn). log_scalar_enc_info child) infos /\
  LENGTH (enc (Tuple ats) (ListV avs)) <= outcap /\
  abi_decode_frame p 32 initial ready /\ (sb+cap <= p \/ p+32 <= sb) ==>
  log_members_layout infos ats avs [] [] sb 0 0 db (head_lengths ats 0) outcap ready.vs_memory /\
  abi_encoder_member_span infos <= cap /\
  SUM (MAP (\(_,asz,_,_). asz) infos) = head_lengths ats 0
Proof
  cheat
QED

Theorem log_scalar_tuple_dynamic_run[local]:
  compile_abi_encode_to_buf dst src (AbiComplex infos) st = (out,end_st) /\
  EXISTS (\(_,_,_,dyn). dyn) infos /\
  EVERY (\(child,asz,mz,dyn). log_scalar_enc_info child) infos /\
  abi_encoder_input (AbiComplex infos) (Tuple ats) (ListV avs) sb cap initial.vs_memory /\
  LENGTH (enc (Tuple ats) (ListV avs)) <= outcap /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w db) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  sb+cap < dimword (:256) /\ db+outcap < dimword (:256) /\
  (sb+cap <= db \/ db+outcap <= sb) /\
  ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
    FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,32)) /\
  p < dimword (:256) /\ (sb+cap <= p \/ p+32 <= sb) /\
  (db+outcap <= p \/ p+32 <= db) /\
  fresh_vars_wrt limit_st initial /\ end_st.cs_next_var <= limit_st.cs_next_var ==>
  ?actual. run_inst_seq (emitted_insts st end_st) initial = OK actual /\
    inst_extends st end_st /\ fresh_vars_wrt limit_st actual /\
    mem_bytes_at db (LENGTH (enc (Tuple ats) (ListV avs))) actual.vs_memory =
      enc (Tuple ats) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Tuple ats) (ListV avs)))) /\
    abi_decode_footprint_frame [(db,outcap);(p,32)] initial actual /\
    actual.vs_allocas = (abi_builtin_allocate_state st.cs_next_id 32 initial).vs_allocas /\
    actual.vs_alloca_next = (abi_builtin_allocate_state st.cs_next_id 32 initial).vs_alloca_next /\
    actual.vs_halted = initial.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w)
Proof
  cheat
QED






Theorem log_scalar_tuple_run:
  compile_abi_encode_to_buf dst src ei st = (out,end_st) /\
  abi_encoder_input ei (Tuple ats) (ListV avs) sb cap initial.vs_memory /\
  ((?n. ei = AbiCopy n /\ n < dimword (:256)) \/
   (?infos. ei = AbiComplex infos /\ EXISTS (\(_,_,_,dyn). dyn) infos /\
     EVERY (\(child,asz,mz,dyn). log_scalar_enc_info child) infos)) /\
  LENGTH (enc (Tuple ats) (ListV avs)) <= outcap /\
  eval_operand src initial = SOME (n2w sb) /\ eval_operand dst initial = SOME (n2w db) /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  sb+cap < dimword (:256) /\ db+outcap < dimword (:256) /\
  (sb+cap <= db \/ db+outcap <= sb) /\
  fresh_vars_wrt limit_st initial /\ end_st.cs_next_var <= limit_st.cs_next_var /\
  ((?infos. ei = AbiComplex infos) ==>
    ((FLOOKUP initial.vs_allocas st.cs_next_id = NONE /\ p = initial.vs_alloca_next) \/
      FLOOKUP initial.vs_allocas st.cs_next_id = SOME (p,32)) /\
    p < dimword (:256) /\ (sb+cap <= p \/ p+32 <= sb) /\
    (db+outcap <= p \/ p+32 <= db)) ==>
  ?actual. run_inst_seq (emitted_insts st end_st) initial = OK actual /\
    inst_extends st end_st /\ fresh_vars_wrt limit_st actual /\
    mem_bytes_at db (LENGTH (enc (Tuple ats) (ListV avs))) actual.vs_memory =
      enc (Tuple ats) (ListV avs) /\
    eval_operand out actual = SOME (n2w (LENGTH (enc (Tuple ats) (ListV avs)))) /\
    abi_decode_footprint_frame
      ((db,outcap)::(if (?infos. ei = AbiComplex infos) then [(p,32)] else [])) initial actual /\
    actual.vs_allocas =
      (if (?infos. ei = AbiComplex infos) then abi_builtin_allocate_state st.cs_next_id 32 initial
       else initial).vs_allocas /\
    actual.vs_alloca_next =
      (if (?infos. ei = AbiComplex infos) then abi_builtin_allocate_state st.cs_next_id 32 initial
       else initial).vs_alloca_next /\
    actual.vs_halted = initial.vs_halted /\
    (!op w. abi_decoder_operand_live st.cs_next_var op /\
      eval_operand op initial = SOME w ==> eval_operand op actual = SOME w)
Proof
  cheat
QED
