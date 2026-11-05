(* Finite canonical sparse-array tests; the forward layout fact already exists. *)
Theory externalReturnStaticSemanticProbe
Ancestors
  externalReturnSemanticProbe valueEncodingProofs vyperTyping vyperTypeDefaults
  vyperABI contractABI finite_map abiEncoderWindow valueEncoding

Theorem return_sparse_bool_conversion:
  evaluate_type FEMPTY (ArrayT (BaseT BoolT) (Fixed 2)) =
    SOME (ArrayTV (BaseTV BoolT) (Fixed 2)) /\
  vyper_to_abi FEMPTY (ArrayT (BaseT BoolT) (Fixed 2))
    (ArrayV (SArrayV [(1,BoolV T)])) = SOME (ListV [NumV 0;NumV 1]) /\
  value_has_type (ArrayTV (BaseTV BoolT) (Fixed 2))
    (ArrayV (SArrayV [(1,BoolV T)]))
Proof
  CONV_TAC EVAL >> simp[wordsTheory.dimword_def]
QED

Theorem return_sparse_bool_window:
  val_in_memory (ArrayTV (BaseTV BoolT) (Fixed 2))
    (ArrayV (SArrayV [(1,BoolV T)])) sb mem ==>
  abi_encoder_window_input (AbiCopy 64) (Array (SOME 2) Bool)
    (ListV [NumV 0;NumV 1]) sb 64 mem
Proof
  strip_tac >>
  `mem_bytes_at sb 64 mem = enc (Array (SOME 2) Bool) (ListV [NumV 0;NumV 1])` by
    (mp_tac (Q.SPECL [`FEMPTY`, `ArrayT (BaseT BoolT) (Fixed 2)`]
       val_in_memory_static_abi_proof) >>
     simp[return_sparse_bool_conversion, vyper_to_abi_type_def,
          is_dynamic_def, type_memory_size_def] >>
     disch_then (qspecl_then [`ArrayV (SArrayV [(1,BoolV T)])`,
       `ListV [NumV 0;NumV 1]`, `sb`, `mem`] mp_tac) >>
     simp[return_sparse_bool_conversion]) >>
  irule window_copy >>
  simp[has_type_def, is_dynamic_def, static_length_def, wordsTheory.dimword_def]
QED

(* Zero-slot element arrays are rejected by evaluate_type. This is a
   failed probe schema, not a counterexample to external_frame_ret_ok. *)
Theorem return_sparse_empty_type_rejected:
  evaluate_type FEMPTY (ArrayT (TupleT []) (Fixed 2)) = NONE
Proof
  CONV_TAC EVAL
QED

Theorem return_sparse_empty_window:
  val_in_memory (ArrayTV (TupleTV []) (Fixed 2))
    (ArrayV (SArrayV [])) sb mem ==>
  abi_encoder_window_input (AbiCopy 0) (Array (SOME 2) (Tuple []))
    (ListV [ListV [];ListV []]) sb 0 mem
Proof
  strip_tac >> irule window_copy >>
  simp[has_type_def, is_dynamic_def, static_length_def, mem_bytes_at_def,
       enc_def] >> CONV_TAC EVAL >> simp[wordsTheory.dimword_def]
QED
