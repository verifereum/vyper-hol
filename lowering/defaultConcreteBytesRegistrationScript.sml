(* Exact modular calldata address used by a dynamic registration head. *)
Theory defaultConcreteBytesRegistration
Ancestors defaultConcreteRegistrationDefs defaultConcreteRegistrationInit
  defaultBytesRegistration vyperCalldata abiDecoderContract words list

Theorem default_registration_dynamic_decode:
  4 <= off /\ off < dimword (:256) /\ tv_abi_dynamic tv /\
  calldata_decode_args s.vs_call_ctx.cc_calldata [tv] (off-4) = SOME [x] ==>
  4 <= w2n ((4w + abi_decode_load CALLDATALOAD
    ((4w+n2w(off-4)):bytes32) s):bytes32) /\
  cd_decode F s.vs_call_ctx.cc_calldata tv
    (w2n ((4w + abi_decode_load CALLDATALOAD
      ((4w+n2w(off-4)):bytes32) s):bytes32)) = SOME x
Proof
  strip_tac >>
  `4 + (off-4) = off` by decide_tac >>
  `((4w + n2w (off-4)):bytes32) = n2w off` by
    (simp[word_add_n2w]) >>
  gvs[calldata_decode_args_def, AllCaseEqs()] >>
  gvs[abi_decode_load_def, abi_decode_source_def, cd_word_def,
       cd_bytes_def, word_add_def, w2n_n2w]
QED
