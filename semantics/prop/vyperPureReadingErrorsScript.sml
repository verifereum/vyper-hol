Theory vyperPureReadingErrors
Ancestors
  vyperAST vyperValue vyperValueOperation vyperABI vyperContext
  vyperState vyperInterpreter

(* These pure producers feed lift_sum or lift_sum_runtime.  They cannot emit
   either diagnostic reserved for the corresponding stateful primitive. *)
val missing_msg = ``"msg.gas: no gas reading"``;
val overflow_msg = ``"transfer_value recipient overflow"``;
val reserved_msg = ``msg = ^missing_msg \/ msg = ^overflow_msg``;
val RESERVED_MSG_CASES = gen_tac >> disch_then (DISJ_CASES_THEN SUBST1_TAC);

Theorem range_error_exclusion[local]:
  !msg. ^reserved_msg ==> !v1 v2. get_range_limits v1 v2 <> INR (RuntimeError msg)
Proof
  RESERVED_MSG_CASES >> simp[oneline get_range_limits_def, AllCaseEqs()]
QED

Theorem binop_error_exclusion[local]:
  !msg. ^reserved_msg ==>
    !u tv bop v1 v2. evaluate_binop u tv bop v1 v2 <> INR (RuntimeError msg)
Proof
  RESERVED_MSG_CASES >> rpt gen_tac >> Cases_on `bop` >>
  simp[evaluate_binop_def, binop_negate_def, bounded_int_op_def,
       bounded_decimal_op_def, wrapped_int_op_def, AllCaseEqs()] >>
  simp[oneline binop_negate_def, AllCaseEqs()]
QED

Theorem concat_loop_error_exclusion[local]:
  !msg. ^reserved_msg ==>
    !n v sa ba vs. evaluate_concat_loop n v sa ba vs <> INR (RuntimeError msg)
Proof
  RESERVED_MSG_CASES >> recInduct evaluate_concat_loop_ind >> rpt strip_tac >>
  gvs[evaluate_concat_loop_def, AllCaseEqs()]
QED

Theorem builtin_delegate_error_exclusions[local]:
  !msg. ^reserved_msg ==>
    (!n vs. evaluate_concat n vs <> INR (RuntimeError msg)) /\
    (!v sv lv n. evaluate_slice v sv lv n <> INR (RuntimeError msg)) /\
    (!dn v. evaluate_as_wei_value dn v <> INR (RuntimeError msg)) /\
    (!tx n. evaluate_block_hash tx n <> INR (RuntimeError msg)) /\
    (!vs. evaluate_ecrecover vs <> INR (RuntimeError msg)) /\
    (!vs. evaluate_ecadd vs <> INR (RuntimeError msg)) /\
    (!vs. evaluate_ecmul vs <> INR (RuntimeError msg))
Proof
  RESERVED_MSG_CASES >> rpt conj_tac >>
  simp[evaluate_concat_def, concat_loop_error_exclusion, evaluate_slice_def,
       evaluate_as_wei_value_def, evaluate_block_hash_def,
       oneline evaluate_ecrecover_def, oneline evaluate_ecadd_def,
       oneline evaluate_ecmul_def, AllCaseEqs()]
QED

Theorem builtin_error_exclusion[local]:
  !msg. ^reserved_msg ==>
    !cx acc ty bt tys vs. evaluate_builtin cx acc ty bt tys vs <>
      INR (RuntimeError msg)
Proof
  RESERVED_MSG_CASES >> rpt gen_tac >> Cases_on `bt` >>
  simp[evaluate_builtin_def, evaluate_calldata_slice_def,
       builtin_delegate_error_exclusions, binop_error_exclusion,
       bounded_int_op_def, bounded_decimal_op_def, AllCaseEqs()]
QED

Theorem code_source_error_exclusion[local]:
  !msg. ^reserved_msg ==>
    !cx acc self cty aty vs. evaluate_code_source cx acc self cty aty vs <>
      INR (RuntimeError msg)
Proof
  RESERVED_MSG_CASES >> simp[evaluate_code_source_def, builtin_error_exclusion,
                             AllCaseEqs()]
QED

Theorem convert_error_exclusion[local]:
  !msg. ^reserved_msg ==>
    !env v ty. evaluate_convert env v ty <> INR (RuntimeError msg)
Proof
  RESERVED_MSG_CASES >>
  simp[oneline evaluate_convert_def, bounded_decimal_op_def, AllCaseEqs()]
QED

Theorem conversion_delegate_error_exclusions[local]:
  !msg. ^reserved_msg ==>
    (!env from_ty v ty. evaluate_convert_from env from_ty v ty <> INR (RuntimeError msg)) /\
    (!bs n bt. evaluate_extract32 bs n bt <> INR (RuntimeError msg))
Proof
  RESERVED_MSG_CASES >>
  simp[evaluate_convert_from_def, evaluate_extract32_def,
       convert_error_exclusion, AllCaseEqs()]
QED

Theorem abi_error_exclusions[local]:
  !msg. ^reserved_msg ==>
    (!env ty bs. evaluate_abi_decode env ty bs <> INR msg) /\
    (!env ty bs. evaluate_abi_decode_returndata env ty bs <> INR msg)
Proof
  RESERVED_MSG_CASES >>
  simp[evaluate_abi_decode_def, evaluate_abi_decode_returndata_def,
       decode_abi_value_def, AllCaseEqs()]
QED

Theorem abi_return_error_exclusion[local]:
  !msg. ^reserved_msg ==>
    !env ty bs. evaluate_abi_decode_return env ty bs <> INR msg
Proof
  RESERVED_MSG_CASES >>
  simp[evaluate_abi_decode_return_def, abi_error_exclusions, AllCaseEqs()]
QED

val type_builtin_eq = oneline evaluate_type_builtin_def;

Theorem type_builtin_error_exclusion[local]:
  !msg. ^reserved_msg ==>
    !cx tb typ tys vs. evaluate_type_builtin cx tb typ tys vs <>
      INR (RuntimeError msg)
Proof
  RESERVED_MSG_CASES >>
  (rpt gen_tac >> Cases_on `tb`
   >>> SPLIT_LT 1 (ALLGOALS (simp[type_builtin_eq,
         conversion_delegate_error_exclusions, oneline evaluate_max_value_def,
         oneline evaluate_min_value_def, AllCaseEqs()]), ALL_LT)
   >>> SPLIT_LT 1 (ALLGOALS (simp[type_builtin_eq,
         conversion_delegate_error_exclusions, oneline evaluate_max_value_def,
         oneline evaluate_min_value_def, AllCaseEqs()]), ALL_LT)
   >>> SPLIT_LT 1 (ALLGOALS (simp[type_builtin_eq,
         conversion_delegate_error_exclusions, oneline evaluate_max_value_def,
         oneline evaluate_min_value_def, AllCaseEqs()]), ALL_LT)
   >>> SPLIT_LT 1 (ALLGOALS (simp[type_builtin_eq,
         conversion_delegate_error_exclusions, oneline evaluate_max_value_def,
         oneline evaluate_min_value_def, AllCaseEqs()]), ALL_LT)
   >>> SPLIT_LT 1 (ALLGOALS (simp[type_builtin_eq,
         conversion_delegate_error_exclusions, oneline evaluate_max_value_def,
         oneline evaluate_min_value_def, AllCaseEqs()]), ALL_LT)
   >>> SPLIT_LT 1 (ALLGOALS (simp[type_builtin_eq,
         conversion_delegate_error_exclusions, oneline evaluate_max_value_def,
         oneline evaluate_min_value_def, AllCaseEqs()]), ALL_LT)
   >>> SPLIT_LT 1 (ALLGOALS (simp[type_builtin_eq, abi_error_exclusions,
         AllCaseEqs()]), ALL_LT) >>
   simp[type_builtin_eq, evaluate_abi_encode_bytes_def, AllCaseEqs()])
QED

(* Pure reads and mutations of places also feed lift_sum. *)
Theorem array_mutation_error_exclusions[local]:
  !msg. ^reserved_msg ==>
    (!tv av i v. array_set_index tv av i v <> INR (RuntimeError msg)) /\
    (!tv a v. append_element tv a v <> INR (RuntimeError msg)) /\
    (!a. pop_element a <> INR (RuntimeError msg)) /\
    (!a. popped_value a <> INR (RuntimeError msg))
Proof
  RESERVED_MSG_CASES >>
  simp[array_set_index_def, oneline append_element_def,
       oneline pop_element_def, oneline popped_value_def, AllCaseEqs()]
QED

Theorem subscript_read_error_exclusions[local]:
  !msg. ^reserved_msg ==>
    (!tv v path. evaluate_subscripts tv v path <> INR (RuntimeError msg)) /\
    (!entry path. read_memory_path entry path <> INR (RuntimeError msg))
Proof
  RESERVED_MSG_CASES >>
  (conj_tac >> rpt strip_tac
   >- (drule evaluate_subscripts_error_shape >> simp[]) >>
   drule read_memory_path_error_shape >> simp[])
QED

Theorem subscript_write_error_exclusion[local]:
  !msg. ^reserved_msg ==>
    !tv a path ao. assign_subscripts tv a path ao <> INR (RuntimeError msg)
Proof
  RESERVED_MSG_CASES >> recInduct assign_subscripts_ind >> rpt strip_tac >>
  gvs[assign_subscripts_def, array_mutation_error_exclusions, AllCaseEqs()] >>
  metis_tac[]
QED

Theorem replace_memory_error_exclusion[local]:
  !msg. ^reserved_msg ==>
    !entry path v. replace_memory_entry entry path v <> INR (RuntimeError msg)
Proof
  RESERVED_MSG_CASES >>
  simp[replace_memory_entry_def, subscript_write_error_exclusion, AllCaseEqs()]
QED

Theorem pure_reading_error_exclusions:
  ((!v1 v2. get_range_limits v1 v2 <> INR (RuntimeError ^missing_msg)) /\
    (!u tv bop v1 v2. evaluate_binop u tv bop v1 v2 <> INR (RuntimeError ^missing_msg)) /\
    (!cx acc self cty aty vs. evaluate_code_source cx acc self cty aty vs <>
      INR (RuntimeError ^missing_msg)) /\
    (!cx acc ty bt tys vs. evaluate_builtin cx acc ty bt tys vs <> INR (RuntimeError ^missing_msg)) /\
    (!cx tb typ tys vs. evaluate_type_builtin cx tb typ tys vs <> INR (RuntimeError ^missing_msg)) /\
    (!env ty bs. evaluate_abi_decode_return env ty bs <> INR ^missing_msg) /\
    (!tv v path. evaluate_subscripts tv v path <> INR (RuntimeError ^missing_msg)) /\
    (!entry path. read_memory_path entry path <> INR (RuntimeError ^missing_msg)) /\
    (!tv a path ao. assign_subscripts tv a path ao <> INR (RuntimeError ^missing_msg)) /\
    (!entry path v. replace_memory_entry entry path v <> INR (RuntimeError ^missing_msg)) /\
    (!tv a v. append_element tv a v <> INR (RuntimeError ^missing_msg)) /\
    (!a. pop_element a <> INR (RuntimeError ^missing_msg)) /\
    (!a. popped_value a <> INR (RuntimeError ^missing_msg)))
Proof
  simp[range_error_exclusion, binop_error_exclusion, code_source_error_exclusion,
       builtin_error_exclusion, type_builtin_error_exclusion, abi_return_error_exclusion,
       subscript_read_error_exclusions, subscript_write_error_exclusion,
       replace_memory_error_exclusion, array_mutation_error_exclusions]
QED

Theorem pure_overflow_error_exclusions:
  ((!v1 v2. get_range_limits v1 v2 <> INR (RuntimeError ^overflow_msg)) /\
    (!u tv bop v1 v2. evaluate_binop u tv bop v1 v2 <> INR (RuntimeError ^overflow_msg)) /\
    (!cx acc self cty aty vs. evaluate_code_source cx acc self cty aty vs <>
      INR (RuntimeError ^overflow_msg)) /\
    (!cx acc ty bt tys vs. evaluate_builtin cx acc ty bt tys vs <> INR (RuntimeError ^overflow_msg)) /\
    (!cx tb typ tys vs. evaluate_type_builtin cx tb typ tys vs <> INR (RuntimeError ^overflow_msg)) /\
    (!env ty bs. evaluate_abi_decode_return env ty bs <> INR ^overflow_msg) /\
    (!tv v path. evaluate_subscripts tv v path <> INR (RuntimeError ^overflow_msg)) /\
    (!entry path. read_memory_path entry path <> INR (RuntimeError ^overflow_msg)) /\
    (!tv a path ao. assign_subscripts tv a path ao <> INR (RuntimeError ^overflow_msg)) /\
    (!entry path v. replace_memory_entry entry path v <> INR (RuntimeError ^overflow_msg)) /\
    (!tv a v. append_element tv a v <> INR (RuntimeError ^overflow_msg)) /\
    (!a. pop_element a <> INR (RuntimeError ^overflow_msg)) /\
    (!a. popped_value a <> INR (RuntimeError ^overflow_msg)))
Proof
  simp[range_error_exclusion, binop_error_exclusion, code_source_error_exclusion,
       builtin_error_exclusion, type_builtin_error_exclusion, abi_return_error_exclusion,
       subscript_read_error_exclusions, subscript_write_error_exclusion,
       replace_memory_error_exclusion, array_mutation_error_exclusions]
QED
