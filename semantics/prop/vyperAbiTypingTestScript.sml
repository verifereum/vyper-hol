(* Executable typing checks at the real interpreter boundary, including raw
   pointers to complex cells after their enclosing array has been popped. *)
Theory vyperAbiTypingTest
Ancestors
  vyperAbiAliasTest vyperAbiOperandTyping vyperAbiReadTyping
  vyperAbiOperand vyperInterpreter
  vyperContext vyperState vyperAST vyperValue vyperTyping list option
Libs
  wordsLib intLib

val () = computeLib.add_funs
  [wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``];

Definition popped_complex_args_def:
  popped_complex_args =
    [Subscript alias_array_type
       (Name (ArrayT alias_array_type (Dynamic 2)) "a")
       (Literal (BaseT (UintT 256)) (IntL 1));
     Pop alias_array_type (NameTarget "a")]
End

(* Both operands still designate the old second cell, though the current
   logical array has only one element. In particular the typing premise is
   not a late evaluation of the original subscript AST. *)
Theorem actual_complex_pop_raw_cells_typed:
  let (res,rt) = eval_abi_exprs empty_evaluation_context
    popped_complex_args indexed_alias_state in
  res = INL [AbiMemory 0 4 alias_array_tv; AbiMemory 1 4 alias_array_tv] /\
  LIST_REL (abi_operand_typed empty_evaluation_context rt)
    [alias_array_tv; alias_array_tv]
    [AbiMemory 0 4 alias_array_tv; AbiMemory 1 4 alias_array_tv] /\
  (?entry. lookup_scopes "a" rt.scopes = SOME entry /\
    entry.value = ArrayV (DynArrayV [ArrayV (DynArrayV [BoolV T; BoolV F])]))
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[value_has_type_def]
QED

Theorem actual_alias_result_typed_and_released:
  case eval_expr empty_evaluation_context alias_expr alias_state of
  | (INL (Value v),rt) =>
      value_has_type (BaseTV (BytesT (Dynamic 160))) v /\ rt.abi_memory = []
  | _ => F
Proof
  EVAL_TAC
QED

(* A captured token is valid without assuming its later cell is readable.
   The actual failed decode remains a RuntimeError, preserving source typing. *)
Theorem delayed_bad_length_is_runtime_error:
  let tv = ArrayTV (BaseTV BoolT) (Dynamic 2) in
  let st = empty_state with abi_memory :=
    [(([],"a"), K (3w:bytes32))] in
  let arg = AbiMemory 0 0 tv in
  abi_operand_valid st tv arg /\
  read_abi_operand empty_evaluation_context arg st =
    (INR (Error (RuntimeError "ABI memory read")),st)
Proof
  EVAL_TAC >> simp[]
QED

Theorem actual_storage_unwrap_typed:
  !tr.
  let (res,rt) = eval_abi_exprs (storage_alias_context tr)
    [TopLevelName alias_array_type (NONE,"a");
     Pop (BaseT BoolT) (TopLevelNameTarget (NONE,"a"))]
    (storage_alias_state tr) in
  ?args. res = INL args /\
    LIST_REL (abi_operand_typed (storage_alias_context tr) rt)
      [alias_array_tv; BaseTV BoolT] args
Proof
  Cases >> EVAL_TAC >> simp[] >> EVAL_TAC >> simp[value_has_type_def]
QED
