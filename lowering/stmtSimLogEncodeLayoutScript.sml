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
  strip_tac >> Cases_on `supported_word_type ty`
  >- (drule supported_word_type_is_word >> strip_tac >>
      drule abi_builtin_encode_word_info >>
      simp[log_scalar_enc_info_def]) >>
  `supported_string_type ty` by gvs[supported_scalar_type_def] >>
  Cases_on `ty` >> gvs[supported_string_type_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[supported_string_type_def, type_to_abi_enc_info_def,
      log_scalar_enc_info_def] >>
  rename1 `BytesT bound` >> Cases_on `bound` >>
  gvs[supported_string_type_def, type_to_abi_enc_info_def,
      log_scalar_enc_info_def]
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
  simp[Once type_to_abi_enc_info_def, Once type_memory_bytes_def, SF ETA_ss]
QED

Theorem log_tuple_enc_members_scalar:
  EVERY supported_scalar_type tys ==>
  EVERY (\(ei,asz,mz,dyn). log_scalar_enc_info ei)
    (MAP (\t. (type_to_abi_enc_info sf ce t,
               abi_embedded_static_size ce.ce_struct_fields t,
               type_memory_bytes ce t,
               is_abi_dynamic ce.ce_struct_fields t)) tys)
Proof
  simp[EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
  irule log_scalar_enc_info_selected >> first_x_assum irule >> simp[]
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
  rpt strip_tac >> drule abi_encoder_complex_input_span >> strip_tac >>
  simp[log_members_layout_def, has_type_def, Excl "enc_def"]
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
  simp_tac bool_ss [log_members_layout_def, EVERY_DEF, pairTheory.pair_case_thm] >>
  strip_tac >> drule abi_encoder_members_input_cons >> strip_tac >>
  gvs[]
QED

Theorem log_members_layout_complete:
  log_members_layout [] [] [] pre pvs sb so ho d hl outcap mem ==>
  mem_bytes_at d (LENGTH (enc (Tuple pre) (ListV pvs))) mem =
    enc (Tuple pre) (ListV pvs)
Proof
  simp_tac bool_ss [log_members_layout_def, APPEND_NIL] >> strip_tac >>
  gvs[Excl "enc_def"] >> irule abi_encoder_tuple_prefix_complete >> simp[]
QED

Theorem log_members_layout_final_length:
  log_members_layout [] [] [] pre pvs sb so ho d hl outcap mem ==>
  LENGTH (enc (Tuple pre) (ListV pvs)) =
    hl + LENGTH (FLAT (abi_tuple_tails pre pvs))
Proof
  simp_tac bool_ss [log_members_layout_def, APPEND_NIL] >> strip_tac >>
  simp[Once enc_def, enc_tuple_parts, LET_THM,
       abi_tuple_heads_length, head_lengths_acc]
QED

Theorem log_members_layout_offsets:
  log_members_layout infos tys avs pre pvs sb so ho d hl outcap mem ==>
  SUM (MAP abi_member_head_size (pre++[ty])) = ho+abi_member_head_size ty /\
  LENGTH (FLAT (abi_tuple_tails (pre++[ty]) (pvs++[av]))) =
    LENGTH (FLAT (abi_tuple_tails pre pvs)) +
      (if is_dynamic ty then LENGTH (enc ty av) else 0)
Proof
  simp_tac bool_ss [log_members_layout_def] >> strip_tac >>
  conj_tac >- simp[abi_encoder_open_prefix_head_advance] >>
  irule abi_encoder_open_prefix_tail_advance >>
  irule has_types_length >> first_assum ACCEPT_TAC
QED
