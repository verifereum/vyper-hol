(* Open child sources in the contiguous tuple staging layout. *)
Theory abiTupleEncodeOpenMemory
Ancestors
  abiTupleEncodeMemory abiTupleProps abiEncoderOpenInput abiEncoderOpenInputFrame
  abiEncoderMemory compileEnv exprLowering valueEncoding contractABI
  words list rich_list arithmetic

Definition abi_tuple_encode_open_memory_def:
  abi_tuple_encode_open_memory sf ce [] ats avs d mem = (ats = [] /\ avs = []) /\
  abi_tuple_encode_open_memory sf ce ((op,ty)::xs) ats avs d mem =
    (?at ts av vs. ats = at::ts /\ avs = av::vs /\
      abi_encoder_open_input (type_to_abi_enc_info sf ce ty) at av d (type_memory_bytes ce ty) mem /\
      abi_tuple_encode_open_memory sf ce xs ts vs (d+type_memory_bytes ce ty) mem)
End

Theorem abi_tuple_encode_open_memory_lengths:
  !xs ats avs d mem. abi_tuple_encode_open_memory sf ce xs ats avs d mem ==>
    LENGTH xs = LENGTH ats /\ LENGTH ats = LENGTH avs
Proof
  Induct >- simp[abi_tuple_encode_open_memory_def] >> gen_tac >> PairCases_on `h` >>
  simp[abi_tuple_encode_open_memory_def] >> rpt strip_tac >> gvs[] >> first_x_assum drule >> simp[]
QED

Theorem abi_tuple_encode_memory_open:
  !xs ats avs d mem. abi_tuple_encode_memory sf ce xs ats avs d mem ==>
    abi_tuple_encode_open_memory sf ce xs ats avs d mem
Proof
  Induct >- simp[abi_tuple_encode_memory_def, abi_tuple_encode_open_memory_def] >>
  gen_tac >> PairCases_on `h` >>
  simp[abi_tuple_encode_memory_def, abi_tuple_encode_open_memory_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[abi_encoder_input_open]
QED

Theorem abi_tuple_encode_open_memory_el:
  !xs ats avs d mem i. abi_tuple_encode_open_memory sf ce xs ats avs d mem /\ i < LENGTH xs ==>
    abi_encoder_open_input (type_to_abi_enc_info sf ce (SND (EL i xs)))
      (EL i ats) (EL i avs) (d + abi_tuple_bytes ce (TAKE i xs))
      (type_memory_bytes ce (SND (EL i xs))) mem
Proof
  Induct >- simp[abi_tuple_encode_open_memory_def] >> gen_tac >> PairCases_on `h` >>
  simp[abi_tuple_encode_open_memory_def] >> rpt gen_tac >> strip_tac >> gvs[] >>
  Cases_on `i` >> simp[abi_tuple_bytes_def] >>
  first_x_assum drule >> disch_then (qspec_then `n` mp_tac) >>
  simp_tac (srw_ss()) [abi_tuple_bytes_def, AC ADD_COMM ADD_ASSOC] >>
  disch_then irule >> decide_tac
QED
