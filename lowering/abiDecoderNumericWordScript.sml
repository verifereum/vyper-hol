(* Canonical unsigned, address, Boolean and flag words satisfy their clamps. *)
Theory abiDecoderNumericWord
Ancestors
  abiDecoderClamp abiDecoderCoherence abiDecoderTypedContract abiDecoderContract
  abiCanonicalLoad abiDecoderWordTyped exprLowering compileEnv vyperABI
  contractABI valueEncoding venomState words arithmetic byte finite_map

Theorem abi_numeric_dimindex[simp,local]: dimindex (:256) = 256
Proof
  CONV_TAC fcpLib.INDEX_CONV
QED

Theorem abi_decoder_n2w_unsigned_bound:
  k < 2 ** bits ==> w2n (n2w k : bytes32) < 2 ** bits
Proof
  strip_tac >> simp[w2n_n2w] >> irule LESS_EQ_LESS_TRANS >>
  qexists_tac `k` >> simp[MOD_LESS_EQ]
QED

Theorem abi_decoder_canonical_word_load:
  sb < dimword (:256) /\
  mem_bytes_at sb 32 (abi_decode_source opc s) = word_to_bytes (w:bytes32) T ==>
  abi_decode_load opc (n2w sb : bytes32) s = w
Proof
  strip_tac >> asm_simp_tac bool_ss [abi_decode_load_bytes] >>
  asm_rewrite_tac[] >> irule word_of_bytes_word_to_bytes >>
  simp[dividesTheory.divides_def]
QED

Theorem abi_decoder_canonical_uint_clamp:
  has_type (Uint bits) av /\ sb < dimword (:256) /\
  mem_bytes_at sb 32 (abi_decode_source opc s) = enc (Uint bits) av ==>
  abi_decoder_clamp_valid (type_to_abi_clamp (BaseT (UintT bits)))
    (abi_decode_load opc (n2w sb : bytes32) s)
Proof
  Cases_on `av` >> simp[has_type_def, valid_int_bound_def] >> rpt strip_tac >>
  rename1 `k < 2 ** bits` >>
  `abi_decode_load opc (n2w sb : bytes32) s = n2w k` by
    (irule abi_decoder_canonical_word_load >> gvs[enc_def, enc_number_def]) >>
  Cases_on `bits = 256` >> gvs[type_to_abi_clamp_def, abi_decoder_clamp_valid_def] >>
  drule_all abi_decoder_n2w_unsigned_bound >> simp[]
QED

Theorem abi_decoder_canonical_address_clamp:
  has_type Address av /\ sb < dimword (:256) /\
  mem_bytes_at sb 32 (abi_decode_source opc s) = enc Address av ==>
  abi_decoder_clamp_valid (IntClamp 160 F) (abi_decode_load opc (n2w sb : bytes32) s)
Proof
  Cases_on `av` >> simp_tac bool_ss [has_type_def] >> rpt strip_tac >>
  rename1 `k < 2 ** 160` >>
  `abi_decode_load opc (n2w sb : bytes32) s = n2w k` by
    (irule abi_decoder_canonical_word_load >> gvs[enc_def, enc_number_def]) >>
  simp[abi_decoder_clamp_valid_def] >>
  drule_all abi_decoder_n2w_unsigned_bound >> simp[]
QED

Theorem abi_decoder_canonical_bool_clamp:
  has_type Bool av /\ sb < dimword (:256) /\
  mem_bytes_at sb 32 (abi_decode_source opc s) = enc Bool av ==>
  abi_decoder_clamp_valid BoolClamp (abi_decode_load opc (n2w sb : bytes32) s)
Proof
  Cases_on `av` >> simp[has_type_def] >> rpt strip_tac >> rename1 `k < 2` >>
  `abi_decode_load opc (n2w sb : bytes32) s = n2w k` by
    (irule abi_decoder_canonical_word_load >> gvs[enc_def, enc_number_def]) >>
  simp[abi_decoder_clamp_valid_def] >>
  irule (SIMP_RULE (srw_ss()) []
    (Q.INST [`bits` |-> `1`] abi_decoder_n2w_unsigned_bound)) >> simp[]
QED

Theorem abi_decoder_canonical_flag_clamp:
  abi_decoder_coherent ce env sf (FlagT nsid) tv /\
  abi_decoder_metadata ce env (FlagT nsid) tv root_di av v /\
  sb < dimword (:256) /\
  mem_bytes_at sb 32 (abi_decode_source opc s) =
    enc (vyper_to_abi_type env (FlagT nsid)) av ==>
  abi_decoder_clamp_valid
    (if ce.ce_flag_n_members (nsid_to_string nsid) = 256 then NoClamp
     else IntClamp (ce.ce_flag_n_members (nsid_to_string nsid)) F)
    (abi_decode_load opc (n2w sb : bytes32) s)
Proof
  simp[abi_decoder_coherent_flag_iff, abi_decoder_metadata_def] >>
  rpt strip_tac >> Cases_on `av` >>
  gvs[has_type_def, abi_to_vyper_def, AllCaseEqs()] >>
  rename1 `mem_bytes_at sb 32 (abi_decode_source opc s) =
    word_to_bytes (n2w k : bytes32) T` >>
  `abi_decode_load opc (n2w sb : bytes32) s = n2w k` by
    (irule abi_decoder_canonical_word_load >> gvs[enc_def, enc_number_def]) >>
  Cases_on `ce.ce_flag_n_members (nsid_to_string nsid) = 256` >>
  gvs[abi_decoder_clamp_valid_def] >>
  drule_all abi_decoder_n2w_unsigned_bound >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_NUMERIC_WORD_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI canonical numeric word not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderNumericWord");
