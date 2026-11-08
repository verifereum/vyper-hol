Theory entryReachBodyZeroSlotProbes
Ancestors
  entryReachBodySourceSupport vyperValue vyperABI contractABI supportedTypes
  vyperContext vyperTyping finite_map list rich_list words entryReachBodyEncodingSizes

Theorem entry_empty_struct_zero_encoding:
  supported_place_type [StructDecl "Empty" []] (StructT (NONE,"Empty")) /\
  evaluate_type (type_env [StructDecl "Empty" []]) (StructT (NONE,"Empty")) =
    SOME (StructTV []) /\
  type_slot_size (StructTV []) = 0 /\
  vyper_to_abi (type_env [StructDecl "Empty" []]) (StructT (NONE,"Empty"))
    (StructV []) = SOME (ListV []) /\
  enc (vyper_to_abi_type (type_env [StructDecl "Empty" []])
    (StructT (NONE,"Empty"))) (ListV []) = []
Proof
  EVAL_TAC
QED

Theorem entry_empty_tuple_zero_encoding:
  evaluate_type FEMPTY (TupleT []) = SOME (TupleTV []) /\
  type_slot_size (TupleTV []) = 0 /\
  vyper_to_abi FEMPTY (TupleT []) (ArrayV (TupleV [])) = SOME (ListV []) /\
  enc (vyper_to_abi_type FEMPTY (TupleT [])) (ListV []) = []
Proof
  EVAL_TAC
QED

Theorem entry_empty_struct_array_evaluation_fails:
  evaluate_type (type_env [StructDecl "Empty" []])
    (ArrayT (StructT (NONE,"Empty")) (Fixed 1)) = NONE /\
  evaluate_type (type_env [StructDecl "Empty" []])
    (ArrayT (StructT (NONE,"Empty")) (Dynamic 1)) = NONE
Proof
  EVAL_TAC
QED

Theorem entry_probe_tuple_type[local]:
  has_type (Tuple tys) (ListV avs) ==> LENGTH avs < dimword (:256)
Proof
  simp[Once has_type_def, valid_length_def]
QED

