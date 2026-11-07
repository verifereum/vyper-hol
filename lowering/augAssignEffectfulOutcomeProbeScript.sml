(* A bounded diagnostic, not a counterexample to stmt_frag.  A shortened
   array's region invariant imposes no canonicality on its dead payload. *)
Theory augAssignEffectfulOutcomeProbe
Ancestors
  augAssignEffectfulRead vyperLookupStorage vyperStorage vfmState

Theorem empty_outer_array_noncanonical_payload:
  slots_in_range (update_storage 1w 256w (\k. 0w)) 0
    (ArrayTV (ArrayTV (BaseTV (UintT 8)) (Fixed 1)) (Dynamic 1)) /\
  lookup_storage 1w (update_storage 1w 256w (\k. 0w)) = 256w /\
  decode_base_from_slot
    (lookup_storage 1w (update_storage 1w 256w (\k. 0w)))
    (BaseTV (UintT 8)) = IntV 0 /\
  ~word_slot_canonical
    (lookup_storage 1w (update_storage 1w 256w (\k. 0w)))
    (BaseTV (UintT 8))
Proof
  EVAL_TAC >> simp[SF wordsLib.SIZES_ss] >> EVAL_TAC
QED
