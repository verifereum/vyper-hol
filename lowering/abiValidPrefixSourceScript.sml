(* Source validity establishes canonical prefixes for static values and dynamic
   arrays of static elements, including nested structs/tuples/fixed arrays. *)
Theory abiValidPrefixSource
Ancestors
  abiValidStatic abiBuiltinPrefixInput abiBuiltinSource abiDecoderCoherence
  abiDecoderTypedContract abiDecoderContract vyperABIValid vyperABI contractABI valueEncoding
  compileEnv venomState words list rich_list

Theorem abi_valid_prefix_types:
  (~is_dynamic at \/ ?elem. at = Array NONE elem /\ ~is_dynamic elem) /\
  valid_enc at bs /\ static_length at <= LENGTH bs ==>
  LENGTH (enc at (dec at bs)) <= LENGTH bs /\
  TAKE (LENGTH (enc at (dec at bs))) bs = enc at (dec at bs)
Proof
  strip_tac >> gvs[Excl "enc_def", Excl "dec_def", Excl "valid_enc_def"] >>
  FIRST
  [drule_all abi_valid_static_array_prefix >> simp[],
   drule abi_static_prefix_static >> simp_tac bool_ss [abi_static_prefix_def] >>
     disch_then (qspec_then `bs` mp_tac) >>
     impl_tac >- asm_simp_tac bool_ss [] >> strip_tac >>
     asm_simp_tac (srw_ss()) [LENGTH_TAKE_EQ, TAKE_TAKE_MIN]]
QED

Theorem abi_valid_prefix_source:
  evaluate_abi_decode env ty bs = INL v /\
  (~is_dynamic (vyper_to_abi_type env ty) \/
    ?elem. vyper_to_abi_type env ty = Array NONE elem /\ ~is_dynamic elem) ==>
  LENGTH (enc (vyper_to_abi_type env ty) (dec (vyper_to_abi_type env ty) bs)) <= LENGTH bs /\
  TAKE (LENGTH (enc (vyper_to_abi_type env ty) (dec (vyper_to_abi_type env ty) bs))) bs =
    enc (vyper_to_abi_type env ty) (dec (vyper_to_abi_type env ty) bs)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule evaluate_abi_decode_vyper_valid_enc >> strip_tac >>
  qpat_assum `vyper_valid_enc _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [vyper_valid_enc_window]) >>
  irule abi_valid_prefix_types >> asm_simp_tac bool_ss []
QED

Theorem abi_builtin_prefix_pre_valid_source:
  abi_decoder_coherent ce env sf ty tv /\ evaluate_abi_decode env ty bs = INL v /\
  (~is_dynamic (vyper_to_abi_type env ty) \/
    ?elem. vyper_to_abi_type env ty = Array NONE elem /\ ~is_dynamic elem) /\
  val_in_memory (BaseTV (BytesT (Dynamic input_bound))) (vyperValue$BytesV bs) p s.vs_memory /\
  eval_operand data s = SOME (n2w p) /\ abi_decoder_operand_live st.cs_next_var data /\
  abi_builtin_decode_resources st first last min_size max_size (type_memory_bytes ce ty)
    (LENGTH bs) p d b cap s ==>
  abi_builtin_prefix_pre ce env sf ty tv bs (dec (vyper_to_abi_type env ty) bs) v st
    first last data min_size max_size p d b cap s
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_valid_prefix_source >> strip_tac >>
  drule_all abi_builtin_prefix_pre_from_source >> simp[]
QED
