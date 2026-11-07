(* Static source types encode every word of their storage region. *)
Theory vyperStorageCoverage
Ancestors
  vyperABI vyperStorage vyperTyping vyperValue list

Theorem encode_value_live_written:
  !tenv ty tv v writes i.
    evaluate_type tenv ty = SOME tv /\ ~vyper_is_dynamic tenv ty /\
    value_has_type tv v /\ encode_value tv v = SOME writes /\
    i < type_slot_size tv ==>
    MEM i (MAP FST writes)
Proof
  FAIL_TAC "Encoding coverage proof pending"
QED
