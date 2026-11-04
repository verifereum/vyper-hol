Theory sourceConstValueStructuredTest
Ancestors
  sourceConstValueStructuredProps sourceConstValueStructured sourceConstEval
  sourceConstAST sourceConstValue vyperAST vyperValue vyperTyping
  vyperValueOperation vyperTypeSystem vyperInterpreter vyperState finite_map
Libs
  wordsLib intLib

(* Audit the entire new proof API, not just computation-test conclusions. *)
val () = List.app (fn thy =>
  List.app (fn (name,th) =>
    let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
    in
      if null (Thm.hyp th) andalso null axioms andalso
         List.all (fn s => s = "DISK_THM") oracles then ()
      else raise Fail ("structured value kernel audit: " ^ thy ^ "." ^ name)
    end) (DB.thms thy))
  ["sourceConstValueStructured", "sourceConstValueTypeMono",
   "sourceConstValueAggregateLib", "sourceConstValueStructuredProps"];

Theorem structured_static_sparse:
  sourceConstValueStructured$source_const_reify FEMPTY FEMPTY
    (ArrayT (BaseT (UintT 8)) (Fixed 3))
    (SCV_List [SCV_Int 0; SCV_Int 7; SCV_Int 0]) =
  SOME (Builtin (ArrayT (BaseT (UintT 8)) (Fixed 3))
    (MakeArray (SOME (BaseT (UintT 8))) (Fixed 3))
    [Literal (BaseT (UintT 8)) (IntL 0);
     Literal (BaseT (UintT 8)) (IntL 7);
     Literal (BaseT (UintT 8)) (IntL 0)]) /\
  make_array_value (BaseTV (UintT 8)) (Fixed 3) [IntV 0;IntV 7;IntV 0] =
    SArrayV [(1,IntV 7)]
Proof
  EVAL_TAC
QED

Theorem structured_sparse_logical_length:
  source_const_structured_represents FEMPTY
    (SCV_List [SCV_Int 0;SCV_Int 0;SCV_Int 0]) (ArrayV (SArrayV [])) /\
  array_length (ArrayTV (BaseTV (UintT 8)) (Fixed 3)) (SArrayV []) = 3
Proof
  conj_tac
  >- (simp[source_const_structured_represents_def] >>
      qexistsl_tac [`BaseTV (UintT 8)`,`Fixed 3`,`[IntV 0;IntV 0;IntV 0]`] >>
      EVAL_TAC >> simp[]) >>
  EVAL_TAC
QED

Theorem structured_nested_tuple_array:
  sourceConstValueStructured$source_const_reify FEMPTY FEMPTY
    (TupleT [BaseT BoolT; ArrayT (BaseT (UintT 8)) (Dynamic 2)])
    (SCV_Tuple [SCV_Bool T; SCV_List [SCV_Int 0;SCV_Int 1]]) =
  SOME (Builtin (TupleT [BaseT BoolT;ArrayT (BaseT (UintT 8)) (Dynamic 2)])
    (MakeArray NONE (Fixed 2))
    [Literal (BaseT BoolT) (BoolL T);
     Builtin (ArrayT (BaseT (UintT 8)) (Dynamic 2))
       (MakeArray (SOME (BaseT (UintT 8))) (Dynamic 2))
       [Literal (BaseT (UintT 8)) (IntL 0);Literal (BaseT (UintT 8)) (IntL 1)]])
Proof
  EVAL_TAC
QED

Theorem structured_rejection_bound_arity_child_descriptor:
  sourceConstValueStructured$source_const_reify FEMPTY FEMPTY
    (ArrayT (BaseT BoolT) (Fixed 2)) (SCV_List [SCV_Bool T]) = NONE /\
  sourceConstValueStructured$source_const_reify FEMPTY FEMPTY
    (ArrayT (BaseT BoolT) (Dynamic 0)) (SCV_List [SCV_Bool T]) = NONE /\
  sourceConstValueStructured$source_const_reify FEMPTY FEMPTY
    (TupleT [BaseT BoolT;BaseT BoolT]) (SCV_Tuple [SCV_Bool T]) = NONE /\
  sourceConstValueStructured$source_const_reify FEMPTY FEMPTY
    (ArrayT (BaseT (UintT 8)) (Dynamic 2)) (SCV_List [SCV_Int 256]) = NONE /\
  sourceConstValueStructured$source_const_reify FEMPTY FEMPTY
    (BaseT (BytesT (Dynamic 32))) (SCV_BytesType F 32) = NONE
Proof
  EVAL_TAC
QED

(* The resolved identity deliberately differs from the source path spelling. *)
Theorem structured_nominal_identity:
  sourceConstValueStructured$source_const_reify
    (FEMPTY |+ (["pkg";"Alias"],(SOME 4,"Internal")))
    (FEMPTY |+ ((SOME 4,"Internal"),StructArgs [("x",BaseT BoolT)]))
    (StructT (SOME 4,"Internal"))
    (SCV_Struct ["pkg";"Alias"] [("x",SCV_Bool T)]) =
    SOME (StructLit (StructT (SOME 4,"Internal")) (SOME 4,"Internal")
      [("x",Literal (BaseT BoolT) (BoolL T))]) /\
  sourceConstValueStructured$source_const_reify FEMPTY
    (FEMPTY |+ ((NONE,"S"),StructArgs [("x",BaseT BoolT)]))
    (StructT (NONE,"S")) (SCV_Struct ["S"] [("x",SCV_Bool T)]) = NONE /\
  sourceConstValueStructured$source_const_reify
    (FEMPTY |+ (["S"],(SOME 1,"S")))
    (FEMPTY |+ ((NONE,"S"),StructArgs [("x",BaseT BoolT)]))
    (StructT (NONE,"S")) (SCV_Struct ["S"] [("x",SCV_Bool T)]) = NONE
Proof
  EVAL_TAC
QED

Theorem structured_struct_fields_rejected:
  sourceConstValueStructured$source_const_reify
    (FEMPTY |+ (["S"],(NONE,"S")))
    (FEMPTY |+ ((NONE,"S"),StructArgs [("x",BaseT BoolT);("y",BaseT BoolT)]))
    (StructT (NONE,"S"))
    (SCV_Struct ["S"] [("y",SCV_Bool T);("x",SCV_Bool F)]) = NONE /\
  sourceConstValueStructured$source_const_reify
    (FEMPTY |+ (["S"],(NONE,"S")))
    (FEMPTY |+ ((NONE,"S"),StructArgs [("x",BaseT BoolT);("y",BaseT BoolT)]))
    (StructT (NONE,"S"))
    (SCV_Struct ["S"] [("x",SCV_Bool T);("x",SCV_Bool F)]) = NONE /\
  sourceConstValueStructured$source_const_reify
    (FEMPTY |+ (["S"],(NONE,"S"))) FEMPTY (StructT (NONE,"S"))
    (SCV_Struct ["S"] [("x",SCV_Bool T)]) = NONE
Proof
  EVAL_TAC
QED
