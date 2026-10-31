(* Pin cd74ce4f: constructor projections pass source checking. Legacy executes
   projected pop; Venom panics at builder.load(IMMUTABLES), NOT a source error.
   Constructor projected assignment executes in both backends. Runtime source
   mutation is rejected in both. See immutable-projection-execute-pin.py/log.
   These tests distinguish immutable copy-on-unwrap from local memory aliasing. *)
Theory vyperAbiImmutableProjectionTest
Ancestors
  vyperAbiAliasTest vyperInterpreter vyperAbiOperand vyperContext vyperState
  vyperAST vyperValue vyperStorage finite_map list
Libs
  monadsyntax wordsLib intLib

val () = computeLib.add_funs
  [wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``];

Definition immutable_nested_type_def:
  immutable_nested_type = ArrayT alias_array_type (Dynamic 2)
End

Definition immutable_projection_context_def:
  immutable_projection_context = empty_evaluation_context with <|
    in_deploy := T;
    sources := [(0w,[(NONE,[VariableDecl Private Immutable "a"
      immutable_nested_type NONE])])]
  |>
End

Definition immutable_projection_state_def:
  immutable_projection_state = empty_state with <|
    scopes := [FEMPTY
      |+ ("indices", <| assignable := T;
          type := ArrayTV (BaseTV (UintT 256)) (Dynamic 1);
          value := ArrayV (DynArrayV [IntV 0]); popped := [] |>)] ;
    immutables := [(0w,[(NONE,FEMPTY |+ ("a",
      (ArrayTV alias_array_tv (Dynamic 2),
       ArrayV (DynArrayV [ArrayV (DynArrayV [BoolV T;BoolV F])]))))])]
  |>
End

Definition immutable_projection_expr_def:
  immutable_projection_expr = Subscript alias_array_type
    (TopLevelName immutable_nested_type (NONE,"a"))
    (Literal (BaseT (UintT 256)) (IntL 0))
End

Definition immutable_projection_target_def:
  immutable_projection_target = SubscriptTarget
    (TopLevelNameTarget (NONE,"a"))
    (Literal (BaseT (UintT 256)) (IntL 0))
End

(* Executed legacy pin: ((true,false),false), not ((true),false).
   The second mutation must not update the already-unwrapped first argument. *)
Theorem immutable_complex_unwrap_is_copy_not_local_alias:
  FST ((do
    args <- eval_abi_exprs immutable_projection_context
      [immutable_projection_expr;
       Pop (BaseT BoolT) immutable_projection_target];
    stage_abi_operands immutable_projection_context args
  od) immutable_projection_state) =
  INL [ArrayV (DynArrayV [BoolV T;BoolV F]); BoolV F]
Proof
  EVAL_TAC
QED

(* The pop pointer still reads the old last cell after decrementing length.
   Re-encoding only the new logical immutable value would erase that cell. *)
Definition immutable_true_last_state_def:
  immutable_true_last_state = immutable_projection_state with immutables :=
    [(0w,[(NONE,FEMPTY |+ ("a",
      (ArrayTV alias_array_tv (Dynamic 2),
       ArrayV (DynArrayV [ArrayV (DynArrayV [BoolV F;BoolV T])]))))])]
End

Theorem immutable_pop_pointer_retains_old_element_cell:
  FST ((do
    arg <- abi_target_operand immutable_projection_context
      (ImmutableVar NONE "a") [ValueSubscript (IntV 0)];
    ptr <- abi_pop_pointer immutable_projection_context arg;
    pop_place immutable_projection_context
      (ImmutablePlace NONE "a" [ValueSubscript (IntV 0)]);
    read_abi_operand immutable_projection_context ptr
  od) immutable_true_last_state) = INL (BoolV T)
Proof
  EVAL_TAC
QED

Definition immutable_indexed_pop_result_def:
  immutable_indexed_pop_result = (do
    args <- eval_abi_exprs immutable_projection_context
      [Pop (BaseT BoolT)
        (SubscriptTarget (TopLevelNameTarget (NONE,"a"))
          (Pop (BaseT (UintT 256)) (NameTarget "indices")));
       immutable_projection_expr];
    stage_abi_operands immutable_projection_context args
  od) immutable_projection_state
End

Theorem immutable_pop_captures_effectful_index_once:
  FST immutable_indexed_pop_result =
    INL [BoolV F; ArrayV (DynArrayV [BoolV T])] /\
  lookup_scopes_val "indices" (SND immutable_indexed_pop_result).scopes =
    SOME (ArrayV (DynArrayV []))
Proof
  EVAL_TAC
QED

(* Executed in both backends; re-evaluating indices.pop() would fail. *)
Theorem immutable_assignment_captures_effectful_index_once:
  FST (eval_stmts immutable_projection_context
    [Assign (BaseTarget (SubscriptTarget
       (SubscriptTarget (TopLevelNameTarget (NONE,"a"))
         (Pop (BaseT (UintT 256)) (NameTarget "indices")))
       (Literal (BaseT (UintT 256)) (IntL 0))))
       (Literal (BaseT BoolT) (BoolL F));
     Return (SOME immutable_projection_expr)]
    immutable_projection_state) =
  INR (ReturnException (ArrayV (DynArrayV [BoolV F;BoolV F])))
Proof
  EVAL_TAC
QED

Theorem immutable_lowered_location_observes_assignment_before_unwrap:
  FST ((do
    arg <- eval_abi_expr immutable_projection_context immutable_projection_expr;
    write_place immutable_projection_context
      (ImmutablePlace NONE "a" [ValueSubscript (IntV 0);ValueSubscript (IntV 0)])
      (BoolV F);
    unwrap_abi_operand immutable_projection_context arg
  od) immutable_projection_state) =
  INL (AbiSnapshot (ArrayV (DynArrayV [BoolV F;BoolV F])))
Proof
  EVAL_TAC
QED

(* ABI cleanup must not free constructor immutable backing. It belongs to the
   evaluation frame, unlike scratch snapshots for local-memory operands. *)
Theorem immutable_backing_outlives_nested_abi_cleanup:
  FST ((do
    arg <- eval_abi_expr immutable_projection_context immutable_projection_expr;
    mark <- mark_abi_memory;
    release_abi_memory mark;
    pop_place immutable_projection_context
      (ImmutablePlace NONE "a" [ValueSubscript (IntV 0)]);
    read_abi_operand immutable_projection_context arg
  od) immutable_projection_state) = INL (ArrayV (DynArrayV [BoolV T]))
Proof
  EVAL_TAC
QED

Definition immutable_complex_pop_state_def:
  immutable_complex_pop_state = immutable_projection_state with immutables :=
    [(0w,[(NONE,FEMPTY |+ ("a",
      (ArrayTV (ArrayTV alias_array_tv (Dynamic 2)) (Dynamic 2),
       ArrayV (DynArrayV [ArrayV (DynArrayV
         [ArrayV (DynArrayV [BoolV T;BoolV F]);
          ArrayV (DynArrayV [BoolV F;BoolV T])])]))))])]
End

(* Legacy executable result: the old second child survives the pop and is
   copied on unwrap, while the first ABI argument keeps both children. *)
Theorem immutable_complex_popped_child_is_copied_from_stale_capacity:
  FST ((do
    args <- eval_abi_exprs immutable_projection_context
      [Subscript immutable_nested_type
         (TopLevelName (ArrayT immutable_nested_type (Dynamic 2)) (NONE,"a"))
         (Literal (BaseT (UintT 256)) (IntL 0));
       Pop alias_array_type immutable_projection_target];
    stage_abi_operands immutable_projection_context args
  od) immutable_complex_pop_state) =
  INL [ArrayV (DynArrayV [ArrayV (DynArrayV [BoolV T;BoolV F]);
                         ArrayV (DynArrayV [BoolV F;BoolV T])]);
       ArrayV (DynArrayV [BoolV F;BoolV T])]
Proof
  EVAL_TAC
QED

Theorem immutable_arena_is_reset_at_new_evaluation_frame:
  (initial_state am scs).abi_immutables = []
Proof
  simp[initial_state_def]
QED
