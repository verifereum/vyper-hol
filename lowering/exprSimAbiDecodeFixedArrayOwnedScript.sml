Theory exprSimAbiDecodeFixedArrayOwned
Ancestors
  exprSimAbiDecodeConstructorOutcome exprSimAbiDecodeArrayMembers
  exprSimAbiDecodeArrayBulk exprSimAbiDecodeComplexOutcome
  exprSimAbiDecodeMemberExecute vyperTypeABI
  exprSimAbiDecodeTupleAssembly abiDecoderFixedMemory
  exprSimAbiDecodeTupleOutcome
  abiValidAggregateHeads abiValidMembers vyperABIValid vyperABI contractABI
  vyperValue words list rich_list arithmetic

Theorem abi_decode_fixed_array_sparse_length_probe:
  abi_decode_source_accepts FEMPTY (ArrayT (BaseT BoolT) (Fixed 1))
    (REPLICATE 32 (0w:byte))
    (ArrayV (make_array_value (BaseTV BoolT) (Fixed 1) []))
Proof
  EVAL_TAC >> simp[dimword_def, wordsTheory.word_0_n2w] >> EVAL_TAC
QED

Theorem abi_decode_fixed_array_members_source:
  evaluate_type env ty = SOME tv /\
  n * abi_member_head_size (vyper_to_abi_type env ty) <= LENGTH bs /\
  n < dimword (:256) ==>
  (abi_decode_source_accepts env (ArrayT ty (Fixed n)) bs v <=>
   ?vs. LENGTH vs = n /\
   (!k. k < n ==> abi_decode_source_accepts env ty
     (abi_decode_member_bytes (vyper_to_abi_type env ty) bs
       (DROP (k * abi_member_head_size (vyper_to_abi_type env ty)) bs)) (EL k vs)) /\
   v = ArrayV (make_array_value tv (Fixed n) vs))
Proof
  strip_tac >>
  `!vs. (vyper_decode_valid_enc_tuple (REPLICATE n (vyper_to_abi_type env ty)) bs bs /\
     abi_to_vyper_list env (REPLICATE n ty)
       (abi_decode_members (REPLICATE n (vyper_to_abi_type env ty)) bs bs) = SOME vs) <=>
    LENGTH vs = n /\ (!k. k < n ==> abi_decode_source_accepts env ty
      (abi_decode_member_bytes (vyper_to_abi_type env ty) bs
        (DROP (k * abi_member_head_size (vyper_to_abi_type env ty)) bs)) (EL k vs))` by
    (gen_tac >> mp_tac (Q.SPECL [`n`, `env`, `ty`, `bs`, `0`, `vs`]
      abi_array_members_source) >> simp[]) >>
  pop_assum mp_tac >>
  simp_tac std_ss [abi_decode_source_accepts_def, vyper_to_abi_type_def,
    Once vyper_decode_valid_enc_def, Once dec_def, LET_THM,
    abi_decode_array_members, abi_decode_members_value,
    abi_to_vyper_def, abi_decode_members_length, LENGTH_REPLICATE,
    REVERSE_DEF, APPEND, compatible_bound_def,
    GSYM vyper_decode_valid_enc_tuple_REPLICATE] >>
  asm_simp_tac (srw_ss()) [DROP_0, make_array_value_def, AllCaseEqs(),
    Excl "dec_def", Excl "vyper_decode_valid_enc_def"] >>
  metis_tac[]
QED

Theorem abi_decode_fixed_array_source_intro:
  evaluate_type env ty = SOME tv /\
  n * abi_member_head_size (vyper_to_abi_type env ty) <= LENGTH bs /\
  n < dimword (:256) /\ LENGTH vs = n /\
  (!k. k < n ==> abi_decode_source_accepts env ty
    (abi_decode_member_bytes (vyper_to_abi_type env ty) bs
      (DROP (k * abi_member_head_size (vyper_to_abi_type env ty)) bs)) (EL k vs)) ==>
  abi_decode_source_accepts env (ArrayT ty (Fixed n)) bs
    (ArrayV (make_array_value tv (Fixed n) vs))
Proof
  strip_tac >> drule_all abi_decode_fixed_array_members_source >> metis_tac[]
QED

Theorem abi_decode_fixed_array_member_reject:
  evaluate_type env ty = SOME tv /\
  n * abi_member_head_size (vyper_to_abi_type env ty) <= LENGTH bs /\
  n < dimword (:256) /\ k < n /\
  ~(?v. abi_decode_source_accepts env ty
    (abi_decode_member_bytes (vyper_to_abi_type env ty) bs
      (DROP (k * abi_member_head_size (vyper_to_abi_type env ty)) bs)) v) ==>
  ~(?v. abi_decode_source_accepts env (ArrayT ty (Fixed n)) bs v)
Proof
  strip_tac >> drule_all abi_decode_fixed_array_members_source >> metis_tac[]
QED

Theorem abi_decode_fixed_rows_source:
  abi_tuple_rows_schema ce env (REPLICATE n (ei,ty,tv,asz,msz)) /\
  evaluate_type env ty = SOME tv /\
  asz = abi_member_head_size (vyper_to_abi_type env ty) /\
  n * asz <= LENGTH bs /\ n < dimword (:256) ==>
  (abi_decode_source_accepts env (ArrayT ty (Fixed n)) bs v <=>
   ?vs. abi_tuple_rows_accept env bs 0 (REPLICATE n (ei,ty,tv,asz,msz)) vs /\
     v = ArrayV (make_array_value tv (Fixed n) vs))
Proof
  strip_tac >>
  drule abi_tuple_rows_accept_source >>
  disch_then (qspecl_then [`bs`, `0`] mp_tac) >>
  simp[map_replicate, SUM_REPLICATE, abi_tuple_row_abi_width_def] >>
  strip_tac >>
  simp_tac std_ss [abi_decode_source_accepts_def, vyper_to_abi_type_def,
    Once vyper_decode_valid_enc_def, Once dec_def, LET_THM,
    abi_decode_array_members, abi_decode_members_value,
    abi_to_vyper_def, abi_decode_members_length, LENGTH_REPLICATE,
    REVERSE_DEF, APPEND, compatible_bound_def,
    GSYM vyper_decode_valid_enc_tuple_REPLICATE] >>
  asm_simp_tac (srw_ss()) [DROP_0, AllCaseEqs(), Excl "dec_def",
    Excl "vyper_decode_valid_enc_def"] >> metis_tac[]
QED

Theorem abi_decode_fixed_rows_memory:
  abi_tuple_rows_schema ce env (REPLICATE n (ei,ty,tv,asz,msz)) /\
  abi_tuple_rows_values env bs 0 0 d (REPLICATE n (ei,ty,tv,asz,msz)) vs s ==>
  val_in_memory (ArrayTV tv (Fixed n))
    (ArrayV (make_array_value tv (Fixed n) vs)) d s.vs_memory
Proof
  strip_tac >> drule_all abi_tuple_rows_values_memory >>
  simp[map_replicate] >> strip_tac >>
  simp_tac bool_ss [make_array_value_def] >>
  irule abi_decoder_fixed_array_memory >>
  drule abi_tuple_rows_values_length >> simp[]
QED
