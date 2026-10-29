(* Projection shape is determined by source typing, independently of runtime
   array bounds. Bounds failures stay RuntimeError and never require readiness.
   AbiMemory and AbiImmutable preserve their respective arena token; projection
   checks the live dynamic length only while forming the pointer. *)
Theory vyperAbiProjectionTyping
Ancestors
  list rich_list option pair arithmetic integer alist
  vyperAST vyperValue vyperState vyperMisc vyperAbiOperand
  vyperAbiReadTyping vyperTypeExprSoundness vyperStorageBackend
Libs
  intLib

Definition abi_projection_shape_def:
  abi_projection_shape (ArrayTV tv bd) (ValueSubscript (IntV i)) child =
    (child = tv) /\
  abi_projection_shape (TupleTV tvs) (ValueSubscript (IntV i)) child =
    (0 <= i /\ oEL (Num i) tvs = SOME child) /\
  abi_projection_shape (StructTV fields) (AttrSubscript id) child =
    (ALOOKUP fields id = SOME child) /\
  abi_projection_shape _ _ _ = F
End

Theorem abi_field_offset_lookup:
  !fields id tv. ALOOKUP fields id = SOME tv ==>
  ?off. abi_field_offset id fields = SOME (off,tv)
Proof
  Induct >> simp[abi_field_offset_def] >>
  gen_tac >> PairCases_on `h` >> rw[abi_field_offset_def] >> res_tac >> simp[]
QED

Theorem abi_array_projection_valid:
  well_formed_type_value tv /\
  abi_operand_valid st (ArrayTV tv bd) arg /\
  (~?v. arg = AbiSnapshot v) /\
  project_abi_operand cx arg (ValueSubscript (IntV i)) st = (res,rt) ==>
  rt = st /\ no_type_error_result res /\
  case res of INL child => abi_operand_valid rt tv child | INR _ => T
Proof
  Cases_on `arg` >> Cases_on `bd` >>
  rw[abi_operand_valid_def, project_abi_operand_def,
     check_abi_projection_def, abi_subscript_offset_def,
     bound_length_def, check_def, assert_def, ignore_bind_def, bind_def,
     lift_option_type_def, return_def, raise_def,
     get_storage_backend_def, get_accounts_def, get_transient_storage_def,
     no_type_error_result_def, AllCaseEqs()] >>
  gvs[oEL_THM, AllCaseEqs(), return_def, raise_def, bind_def,
      no_type_error_result_def, abi_operand_valid_def,
      check_abi_projection_def, abi_subscript_offset_def,
      bound_length_def, check_def, assert_def, ignore_bind_def,
      lift_option_type_def, get_storage_backend_def,
      get_accounts_def, get_transient_storage_def] >>
  imp_res_tac get_storage_backend_state >> gvs[no_type_error_result_def,
    abi_operand_valid_def, get_storage_backend_eq]
QED

Theorem abi_tuple_projection_valid:
  well_formed_type_value tv /\ 0 <= i /\ oEL (Num i) tvs = SOME tv /\
  abi_operand_valid st (TupleTV tvs) arg /\
  (~?v. arg = AbiSnapshot v) /\
  project_abi_operand cx arg (ValueSubscript (IntV i)) st = (res,rt) ==>
  rt = st /\ no_type_error_result res /\
  case res of INL child => abi_operand_valid rt tv child | INR _ => T
Proof
  Cases_on `arg` >>
  rw[abi_operand_valid_def, project_abi_operand_def,
     check_abi_projection_def, abi_subscript_offset_def,
     bind_def, lift_option_type_def, return_def,
     no_type_error_result_def, abi_operand_valid_def] >>
  gvs[project_abi_operand_def, check_abi_projection_def,
      abi_subscript_offset_def, bind_def, ignore_bind_def, lift_option_type_def,
      return_def, no_type_error_result_def, abi_operand_valid_def]
QED

Theorem abi_struct_projection_valid:
  well_formed_type_value tv /\ ALOOKUP fields id = SOME tv /\
  abi_operand_valid st (StructTV fields) arg /\
  (~?v. arg = AbiSnapshot v) /\
  project_abi_operand cx arg (AttrSubscript id) st = (res,rt) ==>
  rt = st /\ no_type_error_result res /\
  case res of INL child => abi_operand_valid rt tv child | INR _ => T
Proof
  strip_tac >> drule abi_field_offset_lookup >> strip_tac >>
  Cases_on `arg` >>
  gvs[abi_operand_valid_def, project_abi_operand_def,
      check_abi_projection_def, abi_subscript_offset_def,
      bind_def, ignore_bind_def, lift_option_type_def, return_def,
      no_type_error_result_def, abi_operand_valid_def]
QED

Theorem abi_projection_valid:
  well_formed_type_value tv /\ abi_projection_shape parent sub tv /\
  abi_operand_valid st parent arg /\ (~?v. arg = AbiSnapshot v) /\
  project_abi_operand cx arg sub st = (res,rt) ==>
  rt = st /\ no_type_error_result res /\
  case res of INL child => abi_operand_valid rt tv child | INR _ => T
Proof
  Cases_on `parent` >> Cases_on `sub` >>
  TRY (qmatch_goalsub_rename_tac `ValueSubscript index` >> Cases_on `index`) >>
  simp[abi_projection_shape_def] >> rpt gen_tac >> strip_tac >>
  metis_tac[abi_array_projection_valid, abi_tuple_projection_valid,
            abi_struct_projection_valid]
QED
