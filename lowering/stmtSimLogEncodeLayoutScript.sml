Theory stmtSimLogEncodeLayout
Ancestors
  stmtSimLogDataInput abiBuiltinEncodeWord supportedTypes exprLowering
  compileEnv list typedCopyMetadata abiEncoderMembersInput abiEncoderTuple
  abiEncoderMembersDefs abiEncoderOpenPrefix abiCanonicalWindows abiDecodeRanges contractABI

Definition log_scalar_enc_info_def:
  log_scalar_enc_info ei <=> (ei = AbiCopy 32 \/ ?n. ei = AbiBytestring n)
End

Theorem log_scalar_enc_info_selected:
  supported_scalar_type ty ==>
  log_scalar_enc_info (type_to_abi_enc_info sf ce ty)
Proof
  cheat
QED

Theorem log_tuple_enc_info_selected:
  type_to_abi_enc_info sf ce (TupleT tys) =
    if ~is_abi_dynamic ce.ce_struct_fields (TupleT tys) then
      AbiCopy (SUM (MAP (type_memory_bytes ce) tys))
    else
      AbiComplex (MAP (\t. (type_to_abi_enc_info sf ce t,
                            abi_embedded_static_size ce.ce_struct_fields t,
                            type_memory_bytes ce t,
                            is_abi_dynamic ce.ce_struct_fields t)) tys)
Proof
  cheat
QED

Theorem log_tuple_enc_members_scalar:
  EVERY supported_scalar_type tys ==>
  EVERY (\(ei,asz,mz,dyn). log_scalar_enc_info ei)
    (MAP (\t. (type_to_abi_enc_info sf ce t,
               abi_embedded_static_size ce.ce_struct_fields t,
               type_memory_bytes ce t,
               is_abi_dynamic ce.ce_struct_fields t)) tys)
Proof
  cheat
QED

(* Semantic layout only: no compiler interval or allocation budget. *)
Definition log_members_layout_def:
  log_members_layout infos tys avs pre pvs sb so ho d hl outcap mem <=>
    EVERY (\(ei,asz,mz,dyn). log_scalar_enc_info ei) infos /\
    abi_encoder_input (AbiComplex infos) (Tuple tys) (ListV avs)
      (sb+so) (abi_encoder_member_span infos) mem /\
    has_types pre pvs /\ hl = head_lengths (pre++tys) 0 /\
    ho = SUM (MAP abi_member_head_size pre) /\
    LENGTH (enc (Tuple (pre++tys)) (ListV (pvs++avs))) <= outcap /\
    abi_encoder_tuple_prefix hl pre pvs d mem
End

Theorem log_members_layout_initial:
  EVERY (\(ei,asz,mz,dyn). log_scalar_enc_info ei) infos /\
  abi_encoder_input (AbiComplex infos) (Tuple tys) (ListV avs) sb cap mem /\
  LENGTH (enc (Tuple tys) (ListV avs)) <= outcap ==>
  log_members_layout infos tys avs [] [] sb 0 0 d (head_lengths tys 0) outcap mem
Proof
  cheat
QED

Theorem log_members_layout_cons_input:
  log_members_layout ((ei,asz,mz,dyn)::infos) (ty::tys) (av::avs)
    pre pvs sb so ho d hl outcap mem ==>
  log_scalar_enc_info ei /\ has_type ty av /\
  asz = abi_member_head_size ty /\ dyn = is_dynamic ty /\
  abi_encoder_input ei ty av (sb+so) mz mem /\
  abi_encoder_input (AbiComplex infos) (Tuple tys) (ListV avs)
    (sb+so+mz) (abi_encoder_member_span infos) mem /\
  mz+abi_encoder_member_span infos <=
    abi_encoder_member_span ((ei,asz,mz,dyn)::infos)
Proof
  cheat
QED

Theorem log_members_layout_complete:
  log_members_layout [] [] [] pre pvs sb so ho d hl outcap mem ==>
  mem_bytes_at d (LENGTH (enc (Tuple pre) (ListV pvs))) mem =
    enc (Tuple pre) (ListV pvs)
Proof
  cheat
QED

Theorem log_members_layout_final_length:
  log_members_layout [] [] [] pre pvs sb so ho d hl outcap mem ==>
  LENGTH (enc (Tuple pre) (ListV pvs)) =
    hl + LENGTH (FLAT (abi_tuple_tails pre pvs))
Proof
  cheat
QED

Theorem log_members_layout_offsets:
  log_members_layout infos tys avs pre pvs sb so ho d hl outcap mem ==>
  SUM (MAP abi_member_head_size (pre++[ty])) = ho+abi_member_head_size ty /\
  LENGTH (FLAT (abi_tuple_tails (pre++[ty]) (pvs++[av]))) =
    LENGTH (FLAT (abi_tuple_tails pre pvs)) +
      (if is_dynamic ty then LENGTH (enc ty av) else 0)
Proof
  cheat
QED
