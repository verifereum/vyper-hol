(* Bounded temporal experiment: a fixed local contains a mutable dynamic
   array. The retained element address is stable, but its value is not. *)
Theory bodyPtrSubscriptMutableProbe
Ancestors
  vyperState loweringPosts exprLowering

Theorem nested_dynamic_pop_observation:
  FST (bind
    (pop_place cx (MemoryPlace "x" [ValueSubscript (IntV 0)]))
    (\pv. read_place cx (MemoryPlace "x" [ValueSubscript (IntV 0)]))
    (es with scopes := [FEMPTY |+ ("x",
      <|assignable := T;
        type := ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 2)) (Fixed 1);
        value := ArrayV (SArrayV [(0, ArrayV (DynArrayV [IntV 0; IntV 1]))]);
        popped := []|>)])) = INL (ArrayV (DynArrayV [IntV 0]))
Proof
  EVAL_TAC >> simp[return_def, lookup_scopes_def] >> EVAL_TAC >> simp[return_def]
QED
