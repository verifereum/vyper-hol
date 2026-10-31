(* Immutable typing regressions at the pinned, separate-arena boundary.
   No delayed-read readiness or current logical-index bound is assumed. *)
Theory vyperAbiImmutableTypingTest
Ancestors
  vyperAbiTypingTest vyperAbiBoundsTypingTest vyperAbiImmutableProjectionTest
  vyperAbiOperandTyping vyperAbiStateTyping vyperAbiReadTyping
  vyperAbiDecodeTyping vyperAbiExprTyping vyperAbiProjectionTyping
  vyperAbiWriteTyping vyperAbiOperand vyperInterpreter vyperContext vyperState
  vyperAST vyperValue vyperTyping list option
Libs
  wordsLib intLib monadsyntax

val () = computeLib.add_funs
  [wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``];

Theorem immutable_valid_without_readiness:
  let tv = ArrayTV (BaseTV BoolT) (Dynamic 2) in
  let st = empty_state with abi_immutables :=
    [((0w,(NONE,"a")), K (3w:bytes32))] in
  let arg = AbiImmutable 0 0 tv in
  abi_operand_valid st tv arg /\
  read_abi_operand empty_evaluation_context arg st =
    (INR (Error (RuntimeError "ABI immutable read")),st)
Proof
  EVAL_TAC >> simp[]
QED

Theorem immutable_token_is_not_a_local_token:
  let st = empty_state with abi_memory :=
    [(([],"a"), K (0w:bytes32))] in
  ~abi_operand_valid st (BaseTV BoolT) (AbiImmutable 0 0 (BaseTV BoolT))
Proof
  EVAL_TAC
QED

Theorem immutable_complex_unwrap_valid_and_typed:
  let (res,rt) = eval_abi_exprs immutable_projection_context
    [immutable_projection_expr;
     Pop (BaseT BoolT) immutable_projection_target]
    immutable_projection_state in
  res = INL [AbiSnapshot (ArrayV (DynArrayV [BoolV T;BoolV F]));
             AbiSnapshot (BoolV F)] /\
  LIST_REL (abi_operand_valid rt) [alias_array_tv;BaseTV BoolT]
    [AbiSnapshot (ArrayV (DynArrayV [BoolV T;BoolV F]));
     AbiSnapshot (BoolV F)] /\
  LIST_REL (abi_operand_typed immutable_projection_context rt)
    [alias_array_tv;BaseTV BoolT]
    [AbiSnapshot (ArrayV (DynArrayV [BoolV T;BoolV F]));
     AbiSnapshot (BoolV F)] /\
  rt.abi_memory = [] /\ LENGTH rt.abi_immutables = 2
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[value_has_type_def]
QED

(* A projected pop retains a typed complex cell beyond the new length. *)
Theorem immutable_popped_complex_raw_cell_typed:
  let (res,rt) = (do
    arg <- abi_target_operand immutable_projection_context
      (ImmutableVar NONE "a") [ValueSubscript (IntV 0)];
    ptr <- abi_pop_pointer immutable_projection_context arg;
    pop_place immutable_projection_context
      (ImmutablePlace NONE "a" [ValueSubscript (IntV 0)]);
    return ptr
  od) immutable_complex_pop_state in
  res = INL (AbiImmutable 0 5 alias_array_tv) /\
  abi_operand_valid rt alias_array_tv (AbiImmutable 0 5 alias_array_tv) /\
  abi_operand_typed immutable_projection_context rt alias_array_tv
    (AbiImmutable 0 5 alias_array_tv) /\
  read_abi_operand immutable_projection_context (AbiImmutable 0 5 alias_array_tv) rt =
    (INL (ArrayV (DynArrayV [BoolV F;BoolV T])),rt)
Proof
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[value_has_type_def]
QED

Theorem immutable_write_source_key_is_separate:
  let st = empty_state with abi_immutables :=
    [((0w,(NONE,"a")), K (1w:bytes32))] in
  write_abi_immutables empty_evaluation_context (SOME 1) "a"
    (BaseTV BoolT) (BoolV F) [] (Replace (BoolV F)) st = (INL (),st)
Proof
  EVAL_TAC
QED

Theorem immutable_valid_after_local_release:
  abi_operand_valid st tv (AbiImmutable token off tv) ==>
  abi_operand_valid (SND (release_abi_memory mark st)) tv
    (AbiImmutable token off tv)
Proof
  ACCEPT_TAC abi_immutable_valid_release
QED

Theorem immutable_successful_read_needs_only_validity:
  abi_operand_valid st tv (AbiImmutable token off tv) /\
  read_abi_operand cx (AbiImmutable token off tv) st = (INL v,rt) ==>
  rt = st /\ value_has_type tv v
Proof
  metis_tac[read_abi_operand_valid_typed]
QED

Theorem immutable_logical_length_runtime_error:
  FST (project_abi_operand empty_evaluation_context
    (AbiImmutable 0 0 alias_array_tv) (ValueSubscript (IntV 1))
    (SND (capture_abi_immutable empty_evaluation_context NONE "a" alias_array_tv
      (ArrayV (DynArrayV [BoolV T])) empty_state))) =
    INR (Error (RuntimeError "ABI subscript dynamic bounds"))
Proof
  EVAL_TAC
QED

Theorem immutable_malformed_projection_still_type_error:
  project_abi_operand cx (AbiImmutable token off (ArrayTV tv bd))
    (ValueSubscript (BoolV T)) st =
    (INR (Error (TypeError "ABI immutable projection")),st)
Proof
  Cases_on `bd` >>
  simp[project_abi_operand_def, check_abi_projection_def,
       abi_subscript_offset_def, ignore_bind_def, bind_def,
       lift_option_type_def, return_def, raise_def]
QED

Theorem immutable_capacity_runtime_error:
  project_abi_operand cx (AbiImmutable token off (ArrayTV tv bd))
    (ValueSubscript (IntV (-1))) st =
    (INR (Error (RuntimeError "ABI subscript bounds")),st)
Proof
  Cases_on `bd` >>
  simp[project_abi_operand_def, check_abi_projection_def,
       ignore_bind_def, bind_def, check_def, assert_def]
QED
