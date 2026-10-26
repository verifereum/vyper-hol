(* Complete child encoder inputs in the contiguous tuple memory layout. *)
Theory abiTupleEncodeMemory
Ancestors
  abiTupleProps abiEncoderInput abiEncoderInputLayout abiEncoderMemory
  abiEncoderInputFrame compileEnv exprLowering valueEncoding contractABI
  words list rich_list arithmetic

Definition abi_tuple_encode_memory_def:
  abi_tuple_encode_memory sf ce [] ats avs d mem = (ats = [] /\ avs = []) /\
  abi_tuple_encode_memory sf ce ((op,ty)::xs) ats avs d mem =
    (?at ts av vs. ats = at::ts /\ avs = av::vs /\
      abi_encoder_input (type_to_abi_enc_info sf ce ty) at av d (type_memory_bytes ce ty) mem /\
      abi_tuple_encode_memory sf ce xs ts vs (d+type_memory_bytes ce ty) mem)
End

Theorem abi_tuple_encode_memory_lengths:
  !xs ats avs d mem. abi_tuple_encode_memory sf ce xs ats avs d mem ==>
    LENGTH xs = LENGTH ats /\ LENGTH ats = LENGTH avs
Proof
  Induct >- simp[abi_tuple_encode_memory_def] >> gen_tac >> PairCases_on `h` >>
  simp[abi_tuple_encode_memory_def] >> rpt strip_tac >> gvs[] >> first_x_assum drule >> simp[]
QED

Theorem abi_tuple_encode_memory_typed:
  !xs ats avs d mem. abi_tuple_encode_memory sf ce xs ats avs d mem ==> has_types ats avs
Proof
  Induct >- simp[abi_tuple_encode_memory_def, has_type_def] >> gen_tac >> PairCases_on `h` >>
  simp[abi_tuple_encode_memory_def] >> rpt strip_tac >> gvs[] >>
  drule abi_encoder_input_typed >> strip_tac >> first_x_assum drule >> simp[has_type_def]
QED

Theorem abi_tuple_encode_bytes_zip:
  !ops tys. LENGTH ops = LENGTH tys ==>
    abi_tuple_bytes ce (ZIP (ops,tys)) = type_memory_bytes ce (TupleT tys)
Proof
  Induct >- simp[abi_tuple_bytes_def, type_memory_bytes_def] >>
  Cases_on `tys` >> simp[abi_tuple_bytes_def, type_memory_bytes_def] >>
  rpt strip_tac >> first_x_assum drule >> simp[abi_tuple_bytes_def, type_memory_bytes_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_TUPLE_ENCODE_MEMORY_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI tuple encoder memory not kernel closed: " ^ n)
  end) (DB.thms "abiTupleEncodeMemory");
