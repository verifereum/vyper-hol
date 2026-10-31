(* #551 blocker: Python's late staging aliases complex memory arguments,
   whereas the runtime interpreter materialises each argument before the next.
   This witness must not be hidden by a frontend-only correctness claim. *)
Theory abiAliasRegression
Ancestors
  vyperInterpreter vyperContext vyperState vyperAST vyperTypeSystem
  finite_map

val () = computeLib.add_funs
  [wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``];

Theorem raw_encode_alias_accepted:
  FLOOKUP env.var_types "a" = SOME (ArrayT (BaseT BoolT) (Dynamic 2)) /\
  FLOOKUP env.var_assignable "a" = SOME T ==>
  well_typed_expr env
    (TypeBuiltin (BaseT (BytesT (Dynamic 160))) (AbiEncode F NONE)
      (TupleT [ArrayT (BaseT BoolT) (Dynamic 2); BaseT BoolT])
      [Name (ArrayT (BaseT BoolT) (Dynamic 2)) "a";
       Pop (BaseT BoolT) (NameTarget "a")])
Proof
  EVAL_TAC >> simp[]
QED

Definition abi_alias_state_def:
  abi_alias_state = empty_state with scopes :=
    [FEMPTY |+ ("a", <| assignable := T;
      type := ArrayTV (BaseTV BoolT) (Dynamic 2);
      value := ArrayV (DynArrayV [BoolV T; BoolV F]); popped := [] |>)]
End

Theorem interpreter_arguments_snapshot_before_pop:
  FST (eval_exprs empty_evaluation_context
    [Name (ArrayT (BaseT BoolT) (Dynamic 2)) "a";
     Pop (BaseT BoolT) (NameTarget "a")] abi_alias_state) =
  INL [ArrayV (DynArrayV [BoolV T; BoolV F]); BoolV F]
Proof
  EVAL_TAC >> simp[return_def]
QED
