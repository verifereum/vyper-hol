(* Regressions for the ABI-aware pure equations. No readiness or typing
   premise is used by either correspondence theorem. *)
Theory vyperPureAbiTest
Ancestors
  vyperEvalPureExpr vyperPureExpr vyperAbiAliasTest vyperInterpreter
  vyperAbiOperand vyperContext vyperState vyperAST vyperValue vyperStorage
  finite_map list
Libs
  wordsLib intLib

val () = computeLib.add_funs
  [wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``];

Definition malformed_abi_state_def:
  malformed_abi_state = empty_state with scopes :=
    [FEMPTY |+ ("a", <| assignable := T;
      type := ArrayTV (BaseTV BoolT) (Dynamic 2);
      value := BoolV T |>)]
End

Definition scalar_abi_expr_def:
  scalar_abi_expr = TypeBuiltin (BaseT (BytesT (Dynamic 32)))
    (AbiEncode F NONE) (TupleT [BaseT BoolT]) [Name (BaseT BoolT) "a"]
End

(* Former counterexample: eager materialisation ignored the local entry's
   array representation. Capturing that malformed array must now fail. *)
Theorem malformed_abi_is_pure:
  pure_expr scalar_abi_expr
Proof
  EVAL_TAC
QED

Theorem malformed_abi_pure_none:
  eval_pure_expr empty_evaluation_context malformed_abi_state scalar_abi_expr = NONE
Proof
  EVAL_TAC
QED

Theorem malformed_abi_original_error:
  eval_expr empty_evaluation_context scalar_abi_expr malformed_abi_state =
    (INR (Error (TypeError "ABI memory encoding")), malformed_abi_state)
Proof
  EVAL_TAC
QED

Theorem wellformed_scalar_abi:
  eval_pure_expr empty_evaluation_context
    (empty_state with scopes :=
      [FEMPTY |+ ("a", <| assignable := T; type := BaseTV BoolT;
        value := BoolV T |>)]) scalar_abi_expr =
    SOME (Value (BytesV (REPLICATE 31 0w ++ [1w])))
Proof
  EVAL_TAC
QED

Definition array_abi_expr_def:
  array_abi_expr = TypeBuiltin (BaseT (BytesT (Dynamic 128)))
    (AbiEncode T NONE) (TupleT [alias_array_type])
    [Name alias_array_type "a"]
End

Theorem wellformed_array_abi:
  eval_pure_expr empty_evaluation_context alias_state array_abi_expr =
    SOME (Value (BytesV (REPLICATE 31 0w ++ [32w] ++
      REPLICATE 31 0w ++ [2w] ++ REPLICATE 31 0w ++ [1w] ++ REPLICATE 32 0w)))
Proof
  EVAL_TAC
QED

(* Conditional selection unwraps the selected operand; the untaken missing
   name is not evaluated. The projection then loads the false element. *)
Theorem wellformed_conditional_projection_abi:
  eval_pure_expr empty_evaluation_context alias_state
    (TypeBuiltin (BaseT (BytesT (Dynamic 32))) (AbiEncode F NONE)
      (TupleT [BaseT BoolT])
      [Subscript (BaseT BoolT)
        (IfExp alias_array_type (Literal (BaseT BoolT) (BoolL T))
          (Name alias_array_type "a") (Name alias_array_type "missing"))
        (Literal (BaseT (UintT 256)) (IntL 1))]) =
    SOME (Value (BytesV (REPLICATE 32 0w)))
Proof
  EVAL_TAC
QED

Theorem wellformed_attribute_abi:
  eval_pure_expr empty_evaluation_context struct_alias_state
    (TypeBuiltin (BaseT (BytesT (Dynamic 128))) (AbiEncode T NONE)
      (TupleT [alias_array_type])
      [Attribute alias_array_type (Name (StructT (NONE,"S")) "s") "xs"]) =
    eval_pure_expr empty_evaluation_context alias_state array_abi_expr
Proof
  EVAL_TAC
QED

Theorem wellformed_storage_abi:
  eval_pure_expr (storage_alias_context F) (storage_alias_state F)
    (TypeBuiltin (BaseT (BytesT (Dynamic 128))) (AbiEncode T NONE)
      (TupleT [alias_array_type])
      [TopLevelName alias_array_type (NONE,"a")]) =
    eval_pure_expr empty_evaluation_context alias_state array_abi_expr
Proof
  EVAL_TAC
QED

(* A nested ordinary fallback (a builtin with no location) is a snapshot. *)
Theorem wellformed_fallback_abi:
  eval_pure_expr empty_evaluation_context empty_state
    (TypeBuiltin (BaseT (BytesT (Dynamic 32))) (AbiEncode F NONE)
      (TupleT [BaseT (UintT 256)])
      [Builtin (BaseT (UintT 256)) (Bop Add)
        [Literal (BaseT (UintT 256)) (IntL 1);
         Literal (BaseT (UintT 256)) (IntL 2)]]) =
    SOME (Value (BytesV (REPLICATE 31 0w ++ [3w])))
Proof
  EVAL_TAC
QED

Theorem pure_array_abi_original_and_cleanup:
  eval_expr empty_evaluation_context array_abi_expr alias_state =
    (INL (Value (BytesV (REPLICATE 31 0w ++ [32w] ++
      REPLICATE 31 0w ++ [2w] ++ REPLICATE 31 0w ++ [1w] ++ REPLICATE 32 0w))),
     alias_state)
Proof
  irule eval_pure_expr_to_eval_expr_some >>
  ACCEPT_TAC wellformed_array_abi
QED

Definition immutable_abi_context_def:
  immutable_abi_context = empty_evaluation_context with sources :=
    [(0w,[(NONE,[VariableDecl Private Immutable "a" alias_array_type NONE])])]
End

Definition immutable_abi_state_def:
  immutable_abi_state = empty_state with immutables :=
    [(0w,[(NONE,FEMPTY |+
      ("a",(alias_array_tv,ArrayV (DynArrayV [BoolV T; BoolV F]))))])]
End

Theorem wellformed_immutable_abi:
  eval_pure_expr immutable_abi_context immutable_abi_state
    (TypeBuiltin (BaseT (BytesT (Dynamic 128))) (AbiEncode T NONE)
      (TupleT [alias_array_type])
      [TopLevelName alias_array_type (NONE,"a")]) =
    eval_pure_expr empty_evaluation_context alias_state array_abi_expr
Proof
  EVAL_TAC
QED

(* The nested encoding releases only its own suffix; the first outer operand
   must still be live when staging resumes. *)
Definition nested_pure_abi_expr_def:
  nested_pure_abi_expr =
    TypeBuiltin (BaseT (BytesT (Dynamic 224))) (AbiEncode T NONE)
      (TupleT [alias_array_type; BaseT (BytesT (Dynamic 32))])
      [Name alias_array_type "a";
       TypeBuiltin (BaseT (BytesT (Dynamic 32))) (AbiEncode F NONE)
         (TupleT [BaseT BoolT]) [Literal (BaseT BoolT) (BoolL T)]]
End

Theorem nested_pure_abi:
  eval_pure_expr empty_evaluation_context alias_state nested_pure_abi_expr =
    SOME (Value (BytesV (REPLICATE 31 0w ++ [64w] ++
      REPLICATE 31 0w ++ [160w] ++ REPLICATE 31 0w ++ [2w] ++
      REPLICATE 31 0w ++ [1w] ++ REPLICATE 32 0w ++
      REPLICATE 31 0w ++ [32w] ++ REPLICATE 31 0w ++ [1w])))
Proof
  EVAL_TAC
QED

Definition prefixed_abi_state_def:
  prefixed_abi_state = alias_state with <|
    abi_memory := [(([],"outer"),empty_storage)];
    abi_immutables := [((0w,(NONE,"outer")),empty_storage)] |>
End

Theorem pure_abi_preserves_existing_capture_prefixes:
  eval_pure_expr empty_evaluation_context prefixed_abi_state array_abi_expr =
    eval_pure_expr empty_evaluation_context alias_state array_abi_expr ∧
  eval_expr empty_evaluation_context array_abi_expr prefixed_abi_state =
    (INL (Value (BytesV (REPLICATE 31 0w ++ [32w] ++
      REPLICATE 31 0w ++ [2w] ++ REPLICATE 31 0w ++ [1w] ++ REPLICATE 32 0w))),
     prefixed_abi_state)
Proof
  conj_tac >- EVAL_TAC >>
  irule eval_pure_expr_to_eval_expr_some >> EVAL_TAC
QED
