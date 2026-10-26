(* Assemble complete static or dynamic tuple input from actual staged children. *)
Theory abiTupleEncodeAssembly
Ancestors
  abiTupleEncodeMemory abiTupleEncodeLayout abiTupleProps abiEncoderInput abiEncoderInputLayout
  abiEncoderMemory abiStaticAggregateProps compileEnv exprLowering
  valueEncoding contractABI words list rich_list arithmetic pair combin

Definition abi_tuple_encode_infos_def:
  abi_tuple_encode_infos sf ce (xs:(operand # type) list) =
    MAP (\(op,ty). (type_to_abi_enc_info sf ce ty,
      abi_embedded_static_size ce.ce_struct_fields ty, type_memory_bytes ce ty,
      is_abi_dynamic ce.ce_struct_fields ty)) xs
End

Theorem abi_tuple_encode_infos_shape:
  LENGTH (abi_tuple_encode_infos sf ce xs) = LENGTH xs /\
  abi_encoder_member_span (abi_tuple_encode_infos sf ce xs) = abi_tuple_bytes ce xs /\
  TAKE i (abi_tuple_encode_infos sf ce xs) = abi_tuple_encode_infos sf ce (TAKE i xs)
Proof
  simp[abi_tuple_encode_infos_def, abi_encoder_member_span_def, abi_tuple_bytes_def,
    MAP_MAP_o, o_DEF, LAMBDA_PROD, GSYM MAP_TAKE]
QED

Theorem abi_tuple_encode_infos_el:
  i < LENGTH xs ==>
  EL i (abi_tuple_encode_infos sf ce xs) =
    (type_to_abi_enc_info sf ce (SND (EL i xs)),
      abi_embedded_static_size ce.ce_struct_fields (SND (EL i xs)),
      type_memory_bytes ce (SND (EL i xs)), is_abi_dynamic ce.ce_struct_fields (SND (EL i xs)))
Proof
  strip_tac >> simp[abi_tuple_encode_infos_def, EL_MAP] >> Cases_on `EL i xs` >> simp[]
QED

Theorem abi_tuple_encode_layout_el:
  abi_tuple_encode_layout ce xs ats /\ i < LENGTH xs ==>
  abi_embedded_static_size ce.ce_struct_fields (SND (EL i xs)) = abi_member_head_size (EL i ats) /\
  is_abi_dynamic ce.ce_struct_fields (SND (EL i xs)) = is_dynamic (EL i ats)
Proof
  simp_tac bool_ss [abi_tuple_encode_layout_def, LIST_REL_EL_EQN] >> strip_tac >>
  first_x_assum (qspec_then `i` mp_tac) >> asm_simp_tac bool_ss [] >>
  Cases_on `EL i xs` >> simp[]
QED

Theorem abi_tuple_encode_memory_el:
  !xs ats avs d mem i. abi_tuple_encode_memory sf ce xs ats avs d mem /\ i < LENGTH xs ==>
  abi_encoder_input (type_to_abi_enc_info sf ce (SND (EL i xs))) (EL i ats) (EL i avs)
    (d+abi_tuple_bytes ce (TAKE i xs)) (type_memory_bytes ce (SND (EL i xs))) mem
Proof
  Induct >- simp[abi_tuple_encode_memory_def] >> gen_tac >> PairCases_on `h` >>
  rpt gen_tac >> simp[abi_tuple_encode_memory_def] >> strip_tac >> gvs[] >> Cases_on `i`
  >- simp[abi_tuple_bytes_def] >>
  gvs[] >>
  qpat_x_assum `!ats avs d mem i. _` drule_all >>
  simp_tac bool_ss [abi_tuple_bytes_def, MAP, SUM, o_THM, SND, ADD_ASSOC]
QED

Theorem abi_tuple_encode_complex_input:
  abi_tuple_encode_memory sf ce xs ats avs d mem /\ abi_tuple_encode_layout ce xs ats /\
  has_type (Tuple ats) (ListV avs) ==>
  abi_encoder_input (AbiComplex (abi_tuple_encode_infos sf ce xs)) (Tuple ats) (ListV avs)
    d (abi_tuple_bytes ce xs) mem
Proof
  strip_tac >> drule abi_tuple_encode_memory_lengths >> strip_tac >>
  irule abiEncoderInputTheory.complex >> simp[abi_encoder_tuple_type_def, abi_tuple_encode_infos_shape] >>
  qx_genl_tac [`i`, `ei`, `abi_sz`, `mem_sz`, `dyn`] >> strip_tac >>
  `i < LENGTH xs` by fs[abi_tuple_encode_infos_shape] >>
  drule_all abi_tuple_encode_infos_el >> strip_tac >>
  drule_all abi_tuple_encode_layout_el >> strip_tac >>
  drule_all abi_tuple_encode_memory_el >> strip_tac >>
  gvs[abi_tuple_encode_infos_shape]
QED

Theorem abi_tuple_encode_input:
  abi_tuple_encode_memory sf ce xs ats avs d mem /\ abi_tuple_encode_layout ce xs ats /\
  has_type (Tuple ats) (ListV avs) ==>
  abi_encoder_input (type_to_abi_enc_info sf ce (TupleT (MAP SND xs))) (Tuple ats) (ListV avs)
    d (abi_tuple_bytes ce xs) mem
Proof
  strip_tac >> drule abi_tuple_encode_layout_dynamic >> strip_tac >>
  Cases_on `any_dynamic ats`
  >- (drule_all abi_tuple_encode_complex_input >>
      asm_simp_tac (srw_ss()) [Once type_to_abi_enc_info_def, abi_tuple_encode_infos_def,
        MAP_MAP_o, o_DEF, LAMBDA_PROD]) >>
  drule_all abi_tuple_encode_static_window >> strip_tac >>
  drule_all abi_tuple_encode_layout_static_length >> strip_tac >>
  drule abi_tuple_encode_memory_lengths >> strip_tac >>
  asm_simp_tac (srw_ss()) [Once type_to_abi_enc_info_def, type_memory_bytes_def,
    abi_tuple_bytes_def, MAP_MAP_o, o_DEF, abi_encoder_input_copy_iff, is_dynamic_def,
    enc_static_tuple] >>
  qpat_x_assum `mem_bytes_at d (abi_tuple_bytes ce xs) mem = _` mp_tac >>
  simp_tac bool_ss [abi_tuple_bytes_def, o_DEF]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_TUPLE_ENCODE_ASSEMBLY_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI tuple encoder input assembly not kernel closed: " ^ n)
  end) (DB.thms "abiTupleEncodeAssembly");
