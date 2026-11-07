(* Constructor checks relevant to original-argument ABI typing. *)
Theory entryArgumentAbiFacts
Ancestors entryArgumentCastFacts vyperValueOperation vyperABI list pair

Theorem entry_fixed_cast_rejects_dynamic_constructor[local]:
  safe_cast (ArrayTV tv (Fixed n)) (ArrayV (DynArrayV vs)) = NONE
Proof
  simp[Once safe_cast_def]
QED

Theorem entry_struct_cast_requires_names[local]:
  MAP FST fields <> MAP FST types ==>
  safe_cast (StructTV types) (StructV fields) = NONE
Proof
  simp[Once safe_cast_def]
QED

(* ABI TYPING INTERFACE AUDIT:
   bind_arguments_source_values supplies evaluate_type and value_has_type in
   original source order, and safe_cast_some_eq makes each bound value the
   corresponding original argument. The two checks above rule out the apparent
   Fixed/DynArray and struct-field-name mismatches permitted by the broader ABI
   conversion definition alone.

   No general forward typed-conversion theorem was located in generated .sig
   files, lowering or semantics sources. vyperTypeABI.vyper_to_abi_total needs
   typed input but exports only existence of conversion, NOT ABI has_type.
   abiDecoderLayout.abi_decoder_typed_conversion consumes has_type and cannot
   be used to produce it. stmtSimLogDataInput.log_word_abi_type is an inherited
   admission and only covers supported_word_type, not arbitrary entry types.

   Missing reusable semantic boundary (NOT an assertion in this theory):
     evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\
     vyper_to_abi tenv ty v = SOME av ==>
       has_type (vyper_to_abi_type tenv ty) av.
   Its validity and necessary well-formed-type/namespace premises must be
   checked before launching a general induction. Base type widths, flag limits,
   sparse fixed arrays, tuples and namespace-deleted struct field environments
   all occur in that induction; conversion existence alone is insufficient.
   A mutual list version would give has_types (vyper_to_abi_types tenv tys) avs.

   Frozen-source premise origins for a future list adapter:
   - bind_arguments_source_values gives evaluated tv and original input typing;
   - valid_vyper_call gives LENGTH vals=LENGTH args and calldata_encodes;
   - calldata_encodes gives vyper_to_abi_list on TAKE(LENGTH vals)(MAP SND args)
     and exact encoded tuple bytes; equal lengths remove TAKE;
   - source_typing_ok plus selected declared-function checking supplies
     params_ok / assignability (currently local source_typing_ok_params_ok);
   - source_typing_ok's check_contract supplies contract_namespaces_ok if the
     general semantic boundary needs a namespace premise.
   No package coherence/resource/provenance claim is made by this audit.
*)
