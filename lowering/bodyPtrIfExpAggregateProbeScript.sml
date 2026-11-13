Theory bodyPtrIfExpAggregateProbe
Ancestors
  bodyPtrIfExpSourceTyping bodyPtrIfExpMemoryTransport bodyPtrIfExpNoCopy context compileEnv

(* A diagnostic for the generic candidate, not a counterexample to an
   actual IfExp frame: double typing does not identify byte alignment. *)
Theorem ifexp_tuple_alignment_probe:
  value_has_type (TupleTV [BaseTV AddressT])
    (ArrayV (TupleV [BytesV (REPLICATE 20 (1w:word8))])) /\
  value_has_type (TupleTV [BaseTV (BytesT (Fixed 20))])
    (ArrayV (TupleV [BytesV (REPLICATE 20 (1w:word8))])) /\
  val_in_memory (TupleTV [BaseTV AddressT])
    (ArrayV (TupleV [BytesV (REPLICATE 20 (1w:word8))])) 0
    (REPLICATE 12 0w ++ REPLICATE 20 (1w:word8)) /\
  ~val_in_memory (TupleTV [BaseTV (BytesT (Fixed 20))])
    (ArrayV (TupleV [BytesV (REPLICATE 20 (1w:word8))])) 0
    (REPLICATE 12 0w ++ REPLICATE 20 (1w:word8))
Proof
  EVAL_TAC >> simp[wordsTheory.word_0_n2w, wordsTheory.word_1_n2w, wordsTheory.dimword_def] >> EVAL_TAC
QED

Theorem ifexp_tuple_alignment_layout_probe:
  !ce. same_memory_layout ce (TupleT [BaseT AddressT])
    (TupleT [BaseT (BytesT (Fixed 20))])
Proof
  simp[same_memory_layout_def, punnable_def, type_memory_bytes_def]
QED

(* Actual internal-call annotation compatibility excludes the diagnostic
   pair: layout plus double typing alone omitted this separate premise. *)
Theorem ifexp_tuple_alignment_not_widening:
  !tenv. ~type_widens_to tenv (TupleT [BaseT AddressT])
    (TupleT [BaseT (BytesT (Fixed 20))])
Proof
  simp[vyperTypeSystemTheory.type_widens_to_def,
       vyperTypeSystemTheory.arg_type_fits_def]
QED
