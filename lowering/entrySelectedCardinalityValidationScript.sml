Theory entrySelectedCardinalityValidation
Ancestors
  arithmetic combin list rich_list words finite_map vyperAST vyperValue vyperTypeSystem
  vyperABI contractABI abiCanonicalWindows byte

Theorem scalar_tuple_evaluations[local]:
  !n acc. evaluate_types tenv (REPLICATE n (BaseT (UintT 256))) acc =
    SOME (REVERSE acc ++ REPLICATE n (BaseTV (UintT 256)))
Proof
  Induct >> simp[REPLICATE, Once evaluate_type_def] >>
  simp[evaluate_type_def, REVERSE_DEF, REPLICATE, REPLICATE_APPEND, APPEND_ASSOC]
QED

Theorem scalar_tuple_slot_sum[local]:
  !n. type_slot_size_list (REPLICATE n (BaseTV (UintT 256))) = n
Proof
  Induct >> simp[REPLICATE, type_slot_size_def]
QED

Theorem scalar_tuple_evaluation:
  n <= dimword (:256) ==>
  evaluate_type tenv (TupleT (REPLICATE n (BaseT (UintT 256)))) =
    SOME (TupleTV (REPLICATE n (BaseTV (UintT 256))))
Proof
  simp[Once evaluate_type_def, scalar_tuple_evaluations,
       type_slot_size_def, scalar_tuple_slot_sum]
QED

Theorem scalar_tuple_assignability:
  assignable_type tenv
    (TupleT (REPLICATE (dimword (:256)) (BaseT (UintT 256))))
Proof
  simp[Once assignable_type_def, well_formed_type_def, scalar_tuple_evaluation,
       assignable_type_def, evaluate_type_def, dimword_def]
QED

Theorem scalar_tuple_array_rejected:
  !bd. ~assignable_type tenv
    (ArrayT (TupleT (REPLICATE (dimword (:256)) (BaseT (UintT 256)))) bd)
Proof
  gen_tac >> simp[Once assignable_type_def, well_formed_type_def] >>
  simp[Once evaluate_type_def, scalar_tuple_evaluation] >>
  Cases_on `bd` >>
  simp[type_slot_size_def, scalar_tuple_slot_sum, bound_length_def,
       dimword_def] >>
  Cases_on `n` >> simp[ADD_CLAUSES, MULT_CLAUSES] >> decide_tac
QED

Theorem scalar_tuple_public_validity_rejected:
  ~vyper_decode_valid_enc (Tuple (REPLICATE (dimword (:256)) (Uint 256))) bs
Proof
  simp[Once vyper_decode_valid_enc_def]
QED

Theorem scalar_tuple_encoding_length:
  !n hl tl.
  LENGTH (FLAT (abi_tuple_heads hl tl
    (REPLICATE n (Uint 256)) (REPLICATE n (NumV 0)))) = 32 * n
Proof
  Induct >> simp[REPLICATE, abi_tuple_heads_def, is_dynamic_def,
    enc_def, enc_number_def, LENGTH_word_to_bytes, MULT_CLAUSES]
QED

Theorem scalar_tuple_encoding_exceeds_cap:
  ~(LENGTH (enc (Tuple (REPLICATE (dimword (:256)) (Uint 256)))
          (ListV (REPLICATE (dimword (:256)) (NumV 0)))) < dimword (:256))
Proof
  simp[Once enc_def, enc_tuple_parts, scalar_tuple_encoding_length] >>
  decide_tac
QED

Theorem empty_array_abi_typing:
  has_type (Array NONE elem) (ListV [])
Proof
  simp[has_type_def, dimword_def]
QED

(* Premise ledger:
   - initial_venom_state_calldata_length already derives the strict calldata
     cap from source_typing_ok and initial_venom_state_rel. Reuse it.
   - A direct equality-sized scalar tuple is source-assignable, but its
     canonical encoding exceeds that cap and public tuple validity rejects it.
   - scalar_tuple_array_rejected covers Dynamic 0, Dynamic 1, and Fixed 0
     (indeed every bound). Thus the empty-value array cannot hide THIS tuple
     from source array well-formedness, despite vacuous ABI value recursion.
   - Public validity recurses only into actual array elements, not absent
     descendants. entry_fixed_zero_array_suffix_valid already checks that
     zero-element fixed ABI arrays accept arbitrary suffixes.
   - Still needed: a hereditary source-slot/ABI-encoding interface. Above an
     array, strict source slot bounds may exclude equality; along tuple and
     struct paths, actual encoding length must exclude it. These probes do
     not establish that general induction or original-argument ABI typing. *)
