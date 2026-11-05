(* Pure ABI/Vyper conversion boundary. ABI shape alone loses Vyper bounds. *)
Theory abiVyperAdmissible
Ancestors
  vyperABI contractABI finite_map words list

(* A rounded global byte cap cannot replace the per-value Vyper bound.
   This is not a counterexample to the extcall simulation theorem. *)
Theorem abi_dynamic_bytes_erased_bound_probe:
  let ty = BaseT (BytesT (Dynamic 1)) in
  let av = contractABI$BytesV [0w;0w] in
  let at = vyper_to_abi_type FEMPTY ty in
  let bs = enc at av in
    vyper_decode_valid_enc at bs /\
    static_length at <= LENGTH bs /\
    LENGTH bs <= vyper_abi_size_bound FEMPTY ty /\
    abi_to_vyper FEMPTY ty av = NONE /\
    dec at bs = av /\
    evaluate_abi_decode_returndata FEMPTY ty bs = INR "abi_decode conversion"
Proof
  EVAL_TAC >>
  CONV_TAC (DEPTH_CONV wordsLib.WORD_EVAL_CONV) >>
  EVAL_TAC
QED
