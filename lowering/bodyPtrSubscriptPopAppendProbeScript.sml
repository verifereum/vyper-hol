(* Owner changes under the source's actual mutations, not arbitrary rebinding. *)
Theory bodyPtrSubscriptPopAppendProbe
Ancestors
  vyperState bodyPtrSubscriptMutableProbe

Theorem second_root_pop_keeps_captured_row:
  FST (bind (pop_place cx (MemoryPlace "x" []))
    (\p. bind (pop_place cx (MemoryPlace "x" []))
      (\q. read_place cx (MemoryPlace "x"
        [ValueSubscript (IntV 1); ValueSubscript (IntV 0)])))
    (es with scopes := [FEMPTY |+ ("x",
      <|assignable := T;
        type := ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 2)) (Dynamic 2);
        value := ArrayV (DynArrayV [ArrayV (DynArrayV [IntV 7; IntV 8]);
          ArrayV (DynArrayV [IntV 9; IntV 10])]); popped := []|>)])) = INL (IntV 9)
Proof
  EVAL_TAC >> simp[return_def, lookup_scopes_def] >> EVAL_TAC >> simp[return_def]
QED

Theorem root_append_changes_captured_row:
  FST (bind (pop_place cx (MemoryPlace "x" []))
    (\p. bind (append_place cx (MemoryPlace "x" [])
      (ArrayV (DynArrayV [IntV 11; IntV 12])))
      (\q. read_place cx (MemoryPlace "x"
        [ValueSubscript (IntV 1); ValueSubscript (IntV 0)])))
    (es with scopes := [FEMPTY |+ ("x",
      <|assignable := T;
        type := ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 2)) (Dynamic 2);
        value := ArrayV (DynArrayV [ArrayV (DynArrayV [IntV 7; IntV 8]);
          ArrayV (DynArrayV [IntV 9; IntV 10])]); popped := []|>)])) = INL (IntV 11)
Proof
  EVAL_TAC >> simp[return_def, lookup_scopes_def] >> EVAL_TAC >> simp[return_def]
QED

Theorem historical_row_pop_reads:
  FST (bind (pop_place cx (MemoryPlace "x" []))
    (\p. bind (pop_place cx (MemoryPlace "x" [ValueSubscript (IntV 1)]))
      (\q. bind (read_result cx q)
        (\v. bind (read_place cx (MemoryPlace "x"
          [ValueSubscript (IntV 1); ValueSubscript (IntV 0)]))
          (\w. return (v,w)))))
    (es with scopes := [FEMPTY |+ ("x",
      <|assignable := T;
        type := ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 2)) (Dynamic 2);
        value := ArrayV (DynArrayV [ArrayV (DynArrayV [IntV 7; IntV 8]);
          ArrayV (DynArrayV [IntV 9; IntV 10])]); popped := []|>)])) =
    INL (IntV 10,IntV 9)
Proof
  EVAL_TAC >> simp[return_def, lookup_scopes_def] >>
  EVAL_TAC >> simp[return_def, subscript_type_def] >> EVAL_TAC >>
  simp[return_def, lookup_scopes_def] >> EVAL_TAC >> simp[return_def]
QED

Theorem second_root_pop_history:
  OPTION_MAP (\entry. entry.popped)
    (lookup_scopes "x" (SND (bind (pop_place cx (MemoryPlace "x" []))
      (\p. pop_place cx (MemoryPlace "x" []))
      (es with scopes := [FEMPTY |+ ("x",
        <|assignable := T;
          type := ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 2)) (Dynamic 2);
          value := ArrayV (DynArrayV [ArrayV (DynArrayV [IntV 7; IntV 8]);
            ArrayV (DynArrayV [IntV 9; IntV 10])]); popped := []|>)]))).scopes) =
  SOME [([ValueSubscript (IntV 0)], ArrayV (DynArrayV [IntV 7; IntV 8]));
        ([ValueSubscript (IntV 1)], ArrayV (DynArrayV [IntV 9; IntV 10]))]
Proof
  EVAL_TAC >> simp[return_def, lookup_scopes_def] >> EVAL_TAC >>
  simp[return_def, lookup_scopes_def] >> EVAL_TAC
QED

Theorem root_append_clears_history:
  OPTION_MAP (\entry. entry.popped)
    (lookup_scopes "x" (SND (bind (pop_place cx (MemoryPlace "x" []))
      (\p. append_place cx (MemoryPlace "x" [])
        (ArrayV (DynArrayV [IntV 11; IntV 12])))
      (es with scopes := [FEMPTY |+ ("x",
        <|assignable := T;
          type := ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 2)) (Dynamic 2);
          value := ArrayV (DynArrayV [ArrayV (DynArrayV [IntV 7; IntV 8]);
            ArrayV (DynArrayV [IntV 9; IntV 10])]); popped := []|>)]))).scopes) = SOME []
Proof
  EVAL_TAC >> simp[return_def, lookup_scopes_def] >> EVAL_TAC >>
  simp[return_def, lookup_scopes_def] >> EVAL_TAC
QED

Theorem historical_row_pop_history:
  OPTION_MAP (\entry. entry.popped)
    (lookup_scopes "x" (SND (bind (pop_place cx (MemoryPlace "x" []))
      (\p. pop_place cx (MemoryPlace "x" [ValueSubscript (IntV 1)]))
      (es with scopes := [FEMPTY |+ ("x",
        <|assignable := T;
          type := ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 2)) (Dynamic 2);
          value := ArrayV (DynArrayV [ArrayV (DynArrayV [IntV 7; IntV 8]);
            ArrayV (DynArrayV [IntV 9; IntV 10])]); popped := []|>)]))).scopes) =
  SOME [([ValueSubscript (IntV 1); ValueSubscript (IntV 1)], IntV 10);
        ([ValueSubscript (IntV 1)], ArrayV (DynArrayV [IntV 9]))]
Proof
  EVAL_TAC >> simp[return_def, lookup_scopes_def] >> EVAL_TAC >>
  simp[return_def, lookup_scopes_def] >> EVAL_TAC
QED

(* evaluate_def: Pop is an expression (1586), so (a) and (c) can be nested
   in an index's expression/argument computation subject to typing. Append
   is a statement (1463), not an expression. An isolated internal callee's
   Append affects its argument copy, not a caller local (PopScopeProbe).
   Therefore (b) is an owner-transition interface test, not a reachable local
   append index counterexample. A viable retained-memory contract must relate
   bytes at the address of the CURRENT-first / HISTORY-fallback owner selected
   by read_memory_path at the consumer endpoint. It must describe shortened
   historical parents and newer child history records, not immutable values.
   Clearing all history on a live Append is benign for newly-live captured
   slots but needs separate treatment for deeper paths not made live. *)
