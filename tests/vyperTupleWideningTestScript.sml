(* The tuple target used to require exact element types, rejecting the
   recursive bound widening accepted for the corresponding base targets. *)
Theory vyperTupleWideningTest
Ancestors
  finite_map vyperTypeSystem
Libs
  wordsLib

Theorem tuple_target_nested_bound_widening:
  atarget_accepts
    (env with
       <| var_types := FEMPTY |+
            ("x", ArrayT (BaseT (BytesT (Dynamic 64))) (Dynamic 4)) |+
            ("y", ArrayT (ArrayT (BaseT (StringT 64)) (Dynamic 4)) (Fixed 2));
          var_assignable := FEMPTY |+ ("x",T) |+ ("y",T);
          type_defs := FEMPTY |>)
    (TupleTarget [BaseTarget (NameTarget "x"); BaseTarget (NameTarget "y")])
    (TupleT [ArrayT (BaseT (BytesT (Dynamic 32))) (Dynamic 2);
             ArrayT (ArrayT (BaseT (StringT 8)) (Dynamic 2)) (Fixed 2)])
Proof
  simp[atarget_accepts_def] >> EVAL_TAC >>
  simp[wordsTheory.dimword_def, EVAL ``dimindex(:256)``,
       vyperValueTheory.type_slot_size_def] >> EVAL_TAC
QED
