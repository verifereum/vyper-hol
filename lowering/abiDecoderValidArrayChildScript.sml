(* Select a typed actual-source child at an arbitrary dynamic-array index. *)
Theory abiDecoderValidArrayChild
Ancestors
  abiDecoderValidArrayWindows abiDecoderValidArrayValues abiDecoderArrayChild
  abiDecoderArrayInvariant abiDecoderCoherence abiDecoderTypedContract abiDecoderContract
  abiValidMembers abiDecodeRanges compileEnv valueEncoding vyperABI vyperValue
  contractABI venomState words list rich_list arithmetic

Theorem abi_decode_array_member_EL:
  !n j at base hds. j < n ==>
  EL j (abi_decode_members (REPLICATE n at) base hds) =
    dec at (abi_decode_member_bytes at base (DROP (j * abi_member_head_size at) hds))
Proof
  rpt strip_tac >>
  mp_tac (Q.ISPECL [`n:num`, `j:num`, `at:abi_type`] abi_decoder_replicate_member) >>
  impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
  asm_simp_tac (srw_ss()) [abi_decode_members_append, abi_decode_members_def,
    EL_APPEND_EQN, map_replicate, SUM_REPLICATE,
    Excl "enc_def", Excl "dec_def", Excl "valid_enc_def"]
QED

Theorem abi_decoder_valid_array_metadata_child:
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) di
    (ListV avs) (ArrayV (DynArrayV vs)) /\ j < LENGTH vs ==>
  abi_decoder_coherent ce env sf ty tv /\
  abi_decoder_metadata ce env ty tv (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (EL j avs) (EL j vs)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_dynarray_values >> strip_tac >>
  `j < LENGTH avs` by decide_tac >>
  `TAKE j avs ++ EL j avs::DROP (SUC j) avs = avs` by
    (mp_tac (Q.ISPEC `avs:abi_value list` (Q.SPEC `j:num` TAKE_DROP_SUC)) >>
     asm_simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND]) >>
  `TAKE j vs ++ EL j vs::DROP (SUC j) vs = vs` by
    (mp_tac (Q.ISPEC `vs:vyperValue$value list` (Q.SPEC `j:num` TAKE_DROP_SUC)) >>
     asm_simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND]) >>
  `LENGTH (TAKE j avs) = j /\ LENGTH (TAKE j vs) = j` by simp[LENGTH_TAKE, MIN_DEF] >>
  mp_tac (Q.INST [`parent_di` |-> `di:abi_dec_info`,
    `pre` |-> `TAKE j (avs:abi_value list)`, `av` |-> `EL j (avs:abi_value list)`,
    `post` |-> `DROP (SUC j) (avs:abi_value list)`, `vpre` |-> `TAKE j (vs:vyperValue$value list)`,
    `v` |-> `EL j (vs:vyperValue$value list)`, `vpost` |-> `DROP (SUC j) (vs:vyperValue$value list)`]
    abi_decoder_dynarray_metadata_child) >>
  asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_VALID_ARRAY_CHILD_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI valid array child selection not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderValidArrayChild");
