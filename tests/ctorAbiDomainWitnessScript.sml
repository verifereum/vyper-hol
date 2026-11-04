Theory ctorAbiDomainWitness
Ancestors
  vyperTypeContract vyperInterpreter vyperABI contractABI
  vyperValue finite_map list

Theorem constructor_bytes0_metadata_boundary:
  params_ok (type_env []) [("x", BaseT (BytesT (Fixed 0)))] /\
  IS_SOME (bind_arguments (type_env [])
    [("x", BaseT (BytesT (Fixed 0)))] [vyperValue$BytesV []]) /\
  vyper_to_abi_list (type_env []) [BaseT (BytesT (Fixed 0))]
    [vyperValue$BytesV []] = SOME [contractABI$BytesV []] /\
  ~has_types [Bytes (SOME 0)] [contractABI$BytesV []]
Proof
  EVAL_TAC
QED
