(* Concrete gate for recursive positional widening and aggregate MCOPY. *)
Theory exprExtRequestLayoutProbe
Ancestors
  exprExtRequestTupleStore vyperTypeSystem compileEnv valueEncoding
  venomExecSemantics venomState
Libs
  wordsLib

Definition request_layout_small_def:
  request_layout_small =
    TupleT [BaseT (BytesT (Dynamic 1)); BaseT (UintT 256)]
End

Definition request_layout_large_def:
  request_layout_large =
    TupleT [BaseT (BytesT (Dynamic 64)); BaseT (UintT 256)]
End

Theorem request_layout_compatible:
  arg_type_fits request_layout_small request_layout_large /\
  well_formed_type FEMPTY request_layout_small /\
  well_formed_type FEMPTY request_layout_large /\
  assignable_type FEMPTY request_layout_large /\
  abi_decode_bytes_widths FEMPTY request_layout_large
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def] >> EVAL_TAC
QED

Theorem request_layout_sizes:
  type_memory_bytes cenv request_layout_small = 96 /\
  type_memory_bytes cenv request_layout_large = 128 /\
  type_memory_bytes cenv (BaseT (BytesT (Dynamic 1))) = 64 /\
  type_memory_bytes cenv (BaseT (BytesT (Dynamic 64))) = 96
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def] >> EVAL_TAC
QED

Definition request_layout_value_def:
  request_layout_value = ArrayV (TupleV [BytesV []; IntV 7])
End

Theorem request_layout_copy_mismatch:
  let s = mstore 64 7w (seed with vs_memory := []) in
  val_in_memory
    (TupleTV [BaseTV (BytesT (Dynamic 1)); BaseTV (UintT 256)])
    request_layout_value 0 s.vs_memory /\
  ~val_in_memory
    (TupleTV [BaseTV (BytesT (Dynamic 64)); BaseTV (UintT 256)])
    request_layout_value 256 (mcopy 256 0 128 s).vs_memory /\
  mem_word_at (256 + 64) (mcopy 256 0 128 s).vs_memory = 7w /\
  mem_word_at (256 + 96) (mcopy 256 0 128 s).vs_memory = 0w
Proof
  EVAL_TAC >> simp[]
QED

(* The candidate mismatch is NOT reached by compile_call: the call tuple
   uses lowered operand types (exprLoweringScript.sml:2679,2698-2700),
   not the widened interface signature. *)
Theorem request_layout_actual_call_type:
  MAP (lowered_value_type cenv) [Name request_layout_small "x"] =
    [request_layout_small] /\
  MAP (lowered_value_type cenv) [Name request_layout_small "x"] <>
    [request_layout_large]
Proof
  EVAL_TAC
QED
