(* Executable regressions for cd74ce4f57e3771aeeab8f061fa3be45bfe8a29c.
   The first test is actual eval_expr, not a synthetic list of ABI values. *)
Theory vyperAbiAliasTest
Ancestors
  vyperInterpreter vyperAbiOperand vyperContext vyperState vyperAST
  vyperValue vyperStorage vfmState words finite_map list
Libs
  monadsyntax wordsLib intLib

val () = computeLib.add_funs
  [wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``];

(* Local memory uses the slot codec's word offsets and left-aligned fixed
   bytes. Keep its concrete roundtrip with the delayed ABI memory regressions. *)
Theorem memory_fixed_bytes_roundtrip:
  encode_value (BaseTV (BytesT (Fixed 2))) (BytesV [18w;52w]) =
    SOME [(0, (0x1234w:256 word) << 240)] ∧
  decode_value
    (apply_writes 0w [(0, (0x1234w:256 word) << 240)] empty_storage)
    0 (BaseTV (BytesT (Fixed 2))) = SOME (BytesV [18w;52w])
Proof
  EVAL_TAC
QED

Definition alias_array_type_def:
  alias_array_type = ArrayT (BaseT BoolT) (Dynamic 2)
End

Definition alias_array_tv_def:
  alias_array_tv = ArrayTV (BaseTV BoolT) (Dynamic 2)
End

Definition alias_state_def:
  alias_state = empty_state with scopes :=
    [FEMPTY |+ ("a", <| assignable := T; type := alias_array_tv;
      value := ArrayV (DynArrayV [BoolV T; BoolV F]) |>)]
End

Definition alias_expr_def:
  alias_expr = TypeBuiltin (BaseT (BytesT (Dynamic 160))) (AbiEncode F NONE)
    (TupleT [alias_array_type; BaseT BoolT])
    [Name alias_array_type "a"; Pop (BaseT BoolT) (NameTarget "a")]
End

(* Pinned runtime output: tuple offset 64, false, array length 1, true. *)
Theorem eval_expr_alias_matches_pinned:
  FST (eval_expr empty_evaluation_context alias_expr alias_state) =
  INL (Value (BytesV
    (REPLICATE 31 0w ++ [64w] ++ REPLICATE 32 0w ++
     REPLICATE 31 0w ++ [1w] ++ REPLICATE 31 0w ++ [1w])))
Proof
  EVAL_TAC
QED

Theorem abi_operand_lifetime_is_scoped:
  (SND (eval_expr empty_evaluation_context alias_expr alias_state)).abi_memory = []
Proof
  EVAL_TAC
QED

Theorem abi_operand_lifetime_ends_on_error:
  (SND (eval_expr empty_evaluation_context
    (TypeBuiltin (BaseT (BytesT (Dynamic 160))) (AbiEncode F NONE)
      (TupleT [alias_array_type; alias_array_type])
      [Name alias_array_type "a"; Name alias_array_type "missing"])
    alias_state)).abi_memory = []
Proof
  EVAL_TAC
QED

(* General eval_exprs deliberately retains its old snapshot contract. *)
Theorem unrelated_exprs_still_snapshot:
  FST (eval_exprs empty_evaluation_context
    [Name alias_array_type "a"; Pop (BaseT BoolT) (NameTarget "a")] alias_state) =
  INL [ArrayV (DynArrayV [BoolV T; BoolV F]); BoolV F]
Proof
  EVAL_TAC
QED

Theorem nested_abi_cleanup_preserves_outer_alias_updates:
  FST ((do
    args <- eval_abi_exprs empty_evaluation_context
      [Name alias_array_type "a"; alias_expr];
    stage_abi_operands empty_evaluation_context args
  od) alias_state) =
  INL [ArrayV (DynArrayV [BoolV T]);
       BytesV (REPLICATE 31 0w ++ [64w] ++ REPLICATE 32 0w ++
         REPLICATE 31 0w ++ [1w] ++ REPLICATE 31 0w ++ [1w])]
Proof
  EVAL_TAC
QED

Definition indexed_alias_state_def:
  indexed_alias_state = empty_state with scopes :=
    [FEMPTY |+ ("a", <| assignable := T;
      type := ArrayTV alias_array_tv (Dynamic 2);
      value := ArrayV (DynArrayV
        [ArrayV (DynArrayV [BoolV T; BoolV F]);
         ArrayV (DynArrayV [BoolV F; BoolV T])]) |>)
     |+ ("i", <| assignable := T;
       type := ArrayTV (BaseTV (UintT 256)) (Dynamic 1);
       value := ArrayV (DynArrayV [IntV 1]) |>)]
End

(* An effectful index is captured once.  Replaying the AST would pop an empty
   index array; taking an early snapshot would retain the second true element. *)
Theorem index_is_evaluated_once_before_later_effect:
  FST ((do
    args <- eval_abi_exprs empty_evaluation_context
      [Subscript alias_array_type
         (Name (ArrayT alias_array_type (Dynamic 2)) "a")
         (Pop (BaseT (UintT 256)) (NameTarget "i"));
       Pop (BaseT BoolT)
         (SubscriptTarget (NameTarget "a") (Literal (BaseT (UintT 256)) (IntL 1)))];
    stage_abi_operands empty_evaluation_context args
  od) indexed_alias_state) =
  INL [ArrayV (DynArrayV [BoolV F]); BoolV T]
Proof
  EVAL_TAC
QED

Definition conditional_alias_state_def:
  conditional_alias_state = alias_state with scopes :=
    [FEMPTY |+ ("a", <| assignable := T; type := alias_array_tv;
      value := ArrayV (DynArrayV [BoolV T; BoolV F]) |>)
     |+ ("cond", <| assignable := T;
       type := ArrayTV (BaseTV BoolT) (Dynamic 1);
       value := ArrayV (DynArrayV [BoolV T]) |>)]
End

Theorem condition_is_evaluated_once_and_keeps_memory_alias:
  FST ((do
    args <- eval_abi_exprs empty_evaluation_context
      [IfExp alias_array_type (Pop (BaseT BoolT) (NameTarget "cond"))
         (Name alias_array_type "a") (Name alias_array_type "missing");
       Pop (BaseT BoolT) (NameTarget "a")];
    stage_abi_operands empty_evaluation_context args
  od) conditional_alias_state) =
  INL [ArrayV (DynArrayV [BoolV T]); BoolV F]
Proof
  EVAL_TAC
QED

Definition struct_alias_state_def:
  struct_alias_state = empty_state with scopes :=
    [FEMPTY |+ ("s", <| assignable := T;
      type := StructTV [("xs",alias_array_tv)];
      value := StructV [("xs", ArrayV (DynArrayV [BoolV T; BoolV F]))] |>)]
End

Theorem attribute_keeps_memory_alias:
  FST ((do
    args <- eval_abi_exprs empty_evaluation_context
      [Attribute alias_array_type (Name (StructT (NONE,"S")) "s") "xs";
       Pop (BaseT BoolT) (AttributeTarget (NameTarget "s") "xs")];
    stage_abi_operands empty_evaluation_context args
  od) struct_alias_state) =
  INL [ArrayV (DynArrayV [BoolV T]); BoolV F]
Proof
  EVAL_TAC
QED

(* Pointers to popped complex elements remain valid: pop changes only length,
   not backing cells.  This cannot be implemented as a late logical subscript. *)
Theorem complex_pop_retains_backing_cells:
  FST ((do
    args <- eval_abi_exprs empty_evaluation_context
      [Subscript alias_array_type
         (Name (ArrayT alias_array_type (Dynamic 2)) "a")
         (Literal (BaseT (UintT 256)) (IntL 1));
       Pop alias_array_type (NameTarget "a")];
    stage_abi_operands empty_evaluation_context args
  od) indexed_alias_state) =
  INL [ArrayV (DynArrayV [BoolV F; BoolV T]);
       ArrayV (DynArrayV [BoolV F; BoolV T])]
Proof
  EVAL_TAC
QED

(* Primitive projection loads at unwrap, before a later write to that cell. *)
Theorem primitive_unwrap_is_eager:
  FST ((do
    arg <- eval_abi_expr empty_evaluation_context
      (Subscript (BaseT BoolT) (Name alias_array_type "a")
        (Literal (BaseT (UintT 256)) (IntL 1)));
    arg <- unwrap_abi_operand empty_evaluation_context arg;
    assign_target empty_evaluation_context
      (BaseTargetV (ScopedVar "a") [ValueSubscript (IntV 1)]) (Replace (BoolV T));
    read_abi_operand empty_evaluation_context arg
  od) alias_state) = INL (BoolV F)
Proof
  EVAL_TAC
QED

Definition storage_alias_context_def:
  storage_alias_context tr = empty_evaluation_context with
    <| sources := [(empty_evaluation_context.txn.target,
         [(NONE,[VariableDecl Private (if tr then Transient else Storage)
           "a" alias_array_type NONE])])];
       layouts := [(empty_evaluation_context.txn.target,
         ([((NONE,"a"),0)],[((NONE,"a"),0)]))] |>
End

Definition storage_alias_state_def:
  storage_alias_state tr = SND (write_storage_slot (storage_alias_context tr) tr 0w
    alias_array_tv (ArrayV (DynArrayV [BoolV T; BoolV F])) empty_state)
End

Theorem storage_and_transient_unwrap_copy_before_later_effect:
  ∀tr. FST ((do
    args <- eval_abi_exprs (storage_alias_context tr)
      [TopLevelName alias_array_type (NONE,"a");
       Pop (BaseT BoolT) (TopLevelNameTarget (NONE,"a"))];
    stage_abi_operands (storage_alias_context tr) args
  od) (storage_alias_state tr)) =
  INL [ArrayV (DynArrayV [BoolV T; BoolV F]); BoolV F]
Proof
  Cases >> EVAL_TAC
QED
