(* Delayed ABI reads are partial: a failed decode is a RuntimeError, not a
   source TypeError. Validity records the captured token and type, not an
   assumed readiness/success fact about a future cell read. Successful reads,
   unwraps and staged lists are typed using decode_value_well_typed.
   Strong cell preservation is separately provided by
   vyperAbiOperandTyping. *)
Theory vyperAbiReadTyping
Ancestors
  list rich_list option pair arithmetic vyperAST vyperValue vyperState
  vyperMisc vyperAbiOperand vyperStorageBackend vyperTyping vyperTypeExprSoundness
  vyperAbiOperandTyping vyperAbiDecodeTyping vyperAbiStateTyping

Definition abi_operand_valid_def:
  abi_operand_valid st tv (AbiSnapshot v) =
    (well_formed_type_value tv /\ value_has_type tv v) /\
  abi_operand_valid st tv (AbiMemory token off t) =
    (well_formed_type_value tv /\ t = tv /\ token < LENGTH st.abi_memory) /\
  abi_operand_valid st tv (AbiImmutable token off t) =
    (well_formed_type_value tv /\ t = tv /\ token < LENGTH st.abi_immutables) /\
  abi_operand_valid st tv (AbiStorage tr slot t) =
    (well_formed_type_value tv /\ t = tv) /\
  abi_operand_valid st tv (AbiMapping tr slot kt vt) = F
End

Theorem abi_operand_valid_memory_frame:
  LENGTH st.abi_memory <= LENGTH rt.abi_memory /\
  LENGTH st.abi_immutables <= LENGTH rt.abi_immutables /\
  abi_operand_valid st tv arg ==>
  abi_operand_valid rt tv arg
Proof
  Cases_on `arg` >> simp[abi_operand_valid_def] >> decide_tac
QED

Theorem abi_operand_valid_capture_memory:
  abi_operand_valid st tv arg /\
  capture_abi_memory cx id t v st = (res,rt) ==>
  abi_operand_valid rt tv arg
Proof
  strip_tac >> drule capture_abi_memory_length >> strip_tac >>
  drule capture_abi_memory_typing_frame >> strip_tac >>
  irule abi_operand_valid_memory_frame >> qexists_tac `st` >> simp[]
QED

Theorem abi_operand_valid_capture_immutable:
  abi_operand_valid st tv arg /\
  capture_abi_immutable cx src id t v st = (res,rt) ==>
  abi_operand_valid rt tv arg
Proof
  strip_tac >> drule capture_abi_immutable_length >> strip_tac >>
  drule capture_abi_immutable_typing_frame >> strip_tac >>
  irule abi_operand_valid_memory_frame >> qexists_tac `st` >> simp[]
QED

Theorem abi_operand_valid_write_memory:
  abi_operand_valid st tv arg /\
  write_abi_memory cx id t v subs ao st = (res,rt) ==>
  abi_operand_valid rt tv arg
Proof
  strip_tac >> drule write_abi_memory_length >> strip_tac >>
  drule write_abi_memory_immutables >> strip_tac >>
  irule abi_operand_valid_memory_frame >> qexists_tac `st` >> simp[]
QED

Theorem abi_operand_valid_write_immutables:
  abi_operand_valid st tv arg /\
  write_abi_immutables cx src id t v subs ao st = (res,rt) ==>
  abi_operand_valid rt tv arg
Proof
  strip_tac >> drule write_abi_immutables_length >> strip_tac >>
  drule write_abi_immutables_typing_frame >> strip_tac >>
  irule abi_operand_valid_memory_frame >> qexists_tac `st` >> simp[]
QED

Theorem abi_immutable_valid_release:
  abi_operand_valid st tv (AbiImmutable token off tv) ==>
  abi_operand_valid (SND (release_abi_memory mark st)) tv
    (AbiImmutable token off tv)
Proof
  simp[abi_operand_valid_def, release_abi_memory_def, return_def]
QED

Theorem read_abi_operand_valid:
  abi_operand_valid st tv arg /\
  read_abi_operand cx arg st = (res,rt) ==>
  rt = st /\ no_type_error_result res
Proof
  Cases_on `arg` >>
  rw[abi_operand_valid_def, read_abi_operand_def,
     read_storage_slot_eq, lift_option_def, return_def, raise_def,
     no_type_error_result_def, AllCaseEqs()] >>
  gvs[oEL_THM, option_CASE_rator, AllCaseEqs(), return_def, raise_def,
      no_type_error_result_def]
QED

(* The successful read exposes a genuine decode, rather than a postulated
   ready cell. The storage can be the later, actually written backing store. *)
Theorem read_abi_operand_valid_success:
  abi_operand_valid st tv arg /\
  read_abi_operand cx arg st = (INL v,rt) ==>
  rt = st /\ well_formed_type_value tv /\
  (value_has_type tv v \/ ?mem off. decode_value mem off tv = SOME v)
Proof
  Cases_on `arg` >>
  rw[abi_operand_valid_def, read_abi_operand_def,
     read_storage_slot_eq, lift_option_def, return_def, raise_def,
     AllCaseEqs()] >>
  gvs[oEL_THM, option_CASE_rator, AllCaseEqs(), return_def, raise_def] >>
  metis_tac[]
QED

Theorem read_abi_operand_valid_typed:
  abi_operand_valid st tv arg /\
  read_abi_operand cx arg st = (INL v,rt) ==>
  rt = st /\ value_has_type tv v
Proof
  strip_tac >> drule_all read_abi_operand_valid_success >> strip_tac >>
  fs[] >> drule_all (cj 1 decode_value_well_typed) >> simp[]
QED

Theorem unwrap_abi_operand_valid_no_type_error:
  abi_operand_valid st tv arg /\
  unwrap_abi_operand cx arg st = (res,rt) ==>
  rt = st /\ no_type_error_result res
Proof
  Cases_on `arg` >>
  rw[abi_operand_valid_def, unwrap_abi_operand_def, bind_def,
     return_def, raise_def, AllCaseEqs(), no_type_error_result_def] >>
  gvs[read_abi_operand_def, read_storage_slot_eq, lift_option_def,
      return_def, raise_def, AllCaseEqs(), no_type_error_result_def,
      oEL_THM, option_CASE_rator] >>
  gvs[return_def, raise_def, AllCaseEqs(), no_type_error_result_def]
QED

Theorem unwrap_abi_operand_valid_success:
  abi_operand_valid st tv arg /\
  unwrap_abi_operand cx arg st = (INL out,rt) ==>
  rt = st /\ abi_operand_valid st tv out
Proof
  Cases_on `arg` >>
  rw[abi_operand_valid_def, unwrap_abi_operand_def, bind_def,
     return_def, raise_def, AllCaseEqs()] >>
  gvs[read_abi_operand_def, read_storage_slot_eq, lift_option_def,
      return_def, raise_def, AllCaseEqs(), oEL_THM, option_CASE_rator] >>
  gvs[return_def, raise_def, AllCaseEqs(), abi_operand_valid_def] >>
  drule_all (cj 1 decode_value_well_typed) >> simp[]
QED

(* Immutable unwrap always freezes a value, even for complex types. *)
Theorem unwrap_abi_immutable_valid_snapshot:
  abi_operand_valid st tv (AbiImmutable token off tv) /\
  unwrap_abi_operand cx (AbiImmutable token off tv) st = (INL out,rt) ==>
  rt = st /\ ?v. out = AbiSnapshot v /\ value_has_type tv v
Proof
  rw[unwrap_abi_operand_def, bind_def, return_def, AllCaseEqs()] >>
  drule_all read_abi_operand_valid_typed >> simp[]
QED

Theorem stage_abi_operands_valid_no_type_error:
  !args tvs cx st res rt.
  LIST_REL (abi_operand_valid st) tvs args /\
  stage_abi_operands cx args st = (res,rt) ==>
  rt = st /\ no_type_error_result res
Proof
  Induct >> Cases_on `tvs` >>
  simp[stage_abi_operands_def, return_def, no_type_error_result_def] >>
  rpt gen_tac >> strip_tac >>
  rename1 `abi_operand_valid st tv arg` >>
  Cases_on `read_abi_operand cx arg st` >>
  rename1 `read_abi_operand cx arg st = (head_res,head_st)` >>
  drule_all read_abi_operand_valid >> strip_tac >> gvs[] >>
  Cases_on `head_res` >>
  gvs[stage_abi_operands_def, bind_def, return_def,
      no_type_error_result_def, AllCaseEqs()] >>
  first_x_assum drule_all >> simp[]
QED

Theorem stage_abi_operands_valid_typed:
  !args tvs cx st vs rt.
  LIST_REL (abi_operand_valid st) tvs args /\
  stage_abi_operands cx args st = (INL vs,rt) ==>
  rt = st /\ LIST_REL value_has_type tvs vs
Proof
  Induct >> Cases_on `tvs` >>
  simp[stage_abi_operands_def, return_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[stage_abi_operands_def, bind_def, return_def, AllCaseEqs()] >>
  drule_all read_abi_operand_valid_typed >> strip_tac >> gvs[] >>
  first_x_assum drule_all >> simp[]
QED
