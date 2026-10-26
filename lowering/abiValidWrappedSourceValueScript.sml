(* A singleton source decode supplies the child conversion without requiring
   the child's suffix to pass another global size-window check. *)
Theory abiValidWrappedSourceValue
Ancestors
  abiValidSingletonArray vyperABI vyperValue contractABI words list

Theorem abi_valid_dynamic_singleton_source:
  is_dynamic (vyper_to_abi_type env ty) /\
  evaluate_abi_decode env (TupleT [ty]) bs = INL (ArrayV (TupleV [v])) ==>
  valid_enc (Tuple [vyper_to_abi_type env ty]) bs /\
  abi_to_vyper env ty
    (dec (vyper_to_abi_type env ty) (DROP (abi_head_word bs) bs)) = SOME v
Proof
  strip_tac >>
  gvs[evaluate_abi_decode_def, decode_abi_value_def, vyper_valid_enc_def,
    vyper_to_abi_type_def, abi_dynamic_singleton_value, abi_to_vyper_def, AllCaseEqs(),
    Excl "valid_enc_def", Excl "dec_def"]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_VALID_WRAPPED_SOURCE_VALUE_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI valid wrapped source conversion not kernel closed: " ^ n)
  end) (DB.thms "abiValidWrappedSourceValue");
