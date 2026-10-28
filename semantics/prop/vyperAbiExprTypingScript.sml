(* Consumer interface for the ABI-expression induction predicates. Delayed
   operands carry a type tag and live token, never a future-read hypothesis. *)
Theory vyperAbiExprTyping
Ancestors
  list rich_list option pair arithmetic vyperAST vyperState vyperInterpreter
  vyperMisc vyperTyping vyperAbiOperand vyperAbiReadTyping vyperAbiStateTyping
  vyperTypeSystem vyperTypeInvariants vyperTypeEnv vyperTypeValues
  vyperTypeExprResult vyperTypeExprSoundness

Definition abi_expr_result_valid_def:
  abi_expr_result_valid env st e arg <=>
    ?tv. evaluate_type env.type_defs (expr_type e) = SOME tv /\
         abi_operand_valid st tv arg
End

Definition abi_place_result_valid_def:
  abi_place_result_valid env st arg vt <=>
    case vt of
    | Type ty => ?tv. evaluate_type env.type_defs ty = SOME tv /\
                     abi_operand_valid st tv arg
    | HashMapT kt vt' => ?tr slot. arg = AbiMapping tr slot kt vt'
End

Definition abi_exprs_result_valid_def:
  abi_exprs_result_valid env st es args <=>
    ?tvs. LIST_REL (\e tv. evaluate_type env.type_defs (expr_type e) = SOME tv) es tvs /\
          LIST_REL (abi_operand_valid st) tvs args
End

Theorem abi_expr_result_valid_memory_frame:
  LENGTH st.abi_memory <= LENGTH rt.abi_memory /\
  LENGTH st.abi_immutables <= LENGTH rt.abi_immutables /\
  abi_expr_result_valid env st e arg ==>
  abi_expr_result_valid env rt e arg
Proof
  rw[abi_expr_result_valid_def] >> goal_assum drule >>
  drule_all abi_operand_valid_memory_frame >> simp[]
QED

Theorem abi_place_result_valid_memory_frame:
  LENGTH st.abi_memory <= LENGTH rt.abi_memory /\
  LENGTH st.abi_immutables <= LENGTH rt.abi_immutables /\
  abi_place_result_valid env st arg vt ==>
  abi_place_result_valid env rt arg vt
Proof
  Cases_on `vt` >> rw[abi_place_result_valid_def] >>
  goal_assum drule >> drule_all abi_operand_valid_memory_frame >> simp[]
QED

Theorem abi_exprs_result_valid_memory_frame:
  LENGTH st.abi_memory <= LENGTH rt.abi_memory /\
  LENGTH st.abi_immutables <= LENGTH rt.abi_immutables /\
  abi_exprs_result_valid env st es args ==>
  abi_exprs_result_valid env rt es args
Proof
  rw[abi_exprs_result_valid_def] >> goal_assum drule >>
  irule LIST_REL_mono >> qexists_tac `abi_operand_valid st` >> simp[] >>
  rpt strip_tac >> drule_all abi_operand_valid_memory_frame >> simp[]
QED

Theorem abi_exprs_result_valid_nil[simp]:
  abi_exprs_result_valid env st [] []
Proof
  simp[abi_exprs_result_valid_def]
QED

Theorem abi_exprs_result_valid_cons:
  abi_expr_result_valid env st e arg /\
  abi_exprs_result_valid env st es args ==>
  abi_exprs_result_valid env st (e::es) (arg::args)
Proof
  rw[abi_expr_result_valid_def, abi_exprs_result_valid_def] >>
  qexists_tac `tv::tvs` >> simp[]
QED

Theorem abi_expr_result_valid_unwrap:
  abi_expr_result_valid env st e arg /\
  unwrap_abi_operand cx arg st = (INL out,rt) ==>
  rt = st /\ abi_expr_result_valid env rt e out
Proof
  rw[abi_expr_result_valid_def] >>
  drule_all unwrap_abi_operand_valid_success >> strip_tac >> gvs[] >>
  goal_assum drule >> simp[]
QED

Theorem abi_expr_result_valid_unwrap_no_type_error:
  abi_expr_result_valid env st e arg /\
  unwrap_abi_operand cx arg st = (res,rt) ==>
  rt = st /\ no_type_error_result res
Proof
  rw[abi_expr_result_valid_def] >>
  drule_all unwrap_abi_operand_valid_no_type_error >> simp[]
QED

Theorem abi_exprs_result_valid_stage:
  abi_exprs_result_valid env st es args /\
  stage_abi_operands cx args st = (INL vs,rt) ==>
  rt = st /\ exprs_runtime_typed env es vs
Proof
  rw[abi_exprs_result_valid_def] >>
  drule_all stage_abi_operands_valid_typed >> strip_tac >>
  simp[exprs_runtime_typed_def] >> goal_assum drule >> simp[]
QED

Theorem abi_exprs_result_valid_stage_no_type_error:
  abi_exprs_result_valid env st es args /\
  stage_abi_operands cx args st = (res,rt) ==>
  rt = st /\ no_type_error_result res
Proof
  rw[abi_exprs_result_valid_def] >>
  drule_all stage_abi_operands_valid_no_type_error >> simp[]
QED

Theorem capture_abi_memory_valid:
  well_formed_type_value tv /\ value_has_type tv v ==>
  ?rt. capture_abi_memory cx id tv v st = (INL (LENGTH st.abi_memory),rt) /\
       abi_operand_valid rt tv (AbiMemory (LENGTH st.abi_memory) 0 tv)
Proof
  strip_tac >>
  `?writes. encode_value tv v = SOME writes` by
    metis_tac[value_has_type_equiv, IS_SOME_EXISTS] >>
  simp[capture_abi_memory_def, return_def, abi_operand_valid_def]
QED

Theorem capture_abi_immutable_valid:
  well_formed_type_value tv /\ value_has_type tv v ==>
  ?rt. capture_abi_immutable cx src id tv v st =
         (INL (LENGTH st.abi_immutables),rt) /\
       abi_operand_valid rt tv (AbiImmutable (LENGTH st.abi_immutables) 0 tv)
Proof
  strip_tac >>
  `?writes. encode_value tv v = SOME writes` by
    metis_tac[value_has_type_equiv, IS_SOME_EXISTS] >>
  simp[capture_abi_immutable_def, return_def, abi_operand_valid_def]
QED

(* The source/global-lookup proof supplies the typed immutable entry. This
   boundary does not assume that any later location decode will succeed. *)
Theorem lookup_abi_immutable_valid:
  get_immutables cx src st = (INL imms,st) /\
  FLOOKUP imms id = SOME (tv,v) /\
  well_formed_type_value tv /\ value_has_type tv v ==>
  ?arg rt. lookup_abi_immutable cx src id st = (INL arg,rt) /\
    abi_operand_valid rt tv arg /\ rt.abi_memory = st.abi_memory /\
    LENGTH st.abi_immutables <= LENGTH rt.abi_immutables /\
    (state_well_typed rt <=> state_well_typed st) /\
    (!env cx'. env_consistent env cx' rt <=> env_consistent env cx' st) /\
    rt.accounts = st.accounts
Proof
  strip_tac >> Cases_on `abi_primitive tv`
  >- (simp[lookup_abi_immutable_def, lift_option_type_def, bind_def,
           return_def, abi_operand_valid_def]) >>
  `?captured. capture_abi_immutable cx src id tv v st =
      (INL (LENGTH st.abi_immutables),captured) /\
      abi_operand_valid captured tv (AbiImmutable (LENGTH st.abi_immutables) 0 tv)` by
    (irule capture_abi_immutable_valid >> simp[]) >>
  pop_assum strip_assume_tac >>
  drule capture_abi_immutable_typing_frame >> strip_tac >>
  drule capture_abi_immutable_length >> strip_tac >>
  simp[lookup_abi_immutable_def, lift_option_type_def, bind_def, return_def]
QED

Theorem lookup_abi_local_sound:
  well_typed_expr env (Name ty id) /\ env_consistent env cx st /\
  state_well_typed st /\ lookup_abi_local cx id st = (res,rt) ==>
  state_well_typed rt /\ env_consistent env cx rt /\
  rt.accounts = st.accounts /\ LENGTH st.abi_memory <= LENGTH rt.abi_memory /\
  rt.abi_immutables = st.abi_immutables /\
  no_type_error_result res /\
  case res of INL arg => abi_expr_result_valid env rt (Name ty id) arg
            | INR exn => T
Proof
  strip_tac >> drule_all well_typed_Name_lookup >> strip_tac >>
  `well_formed_type_value tv` by
    metis_tac[evaluate_type_well_formed_type_value] >>
  Cases_on `abi_primitive tv`
  >- gvs[lookup_abi_local_def, get_scopes_def, lift_option_type_def,
         bind_def, return_def, abi_expr_result_valid_def,
         abi_operand_valid_def, no_type_error_result_def, expr_type_def] >>
  `?captured. capture_abi_memory cx id tv entry.value st =
      (INL (LENGTH st.abi_memory),captured) /\
      abi_operand_valid captured tv (AbiMemory (LENGTH st.abi_memory) 0 tv)` by
    (irule capture_abi_memory_valid >> simp[]) >>
  pop_assum strip_assume_tac >>
  gvs[lookup_abi_local_def, get_scopes_def, lift_option_type_def,
      bind_def, return_def] >>
  drule capture_abi_memory_typing_frame >> strip_tac >>
  drule capture_abi_memory_length >> strip_tac >>
  simp[no_type_error_result_def, abi_expr_result_valid_def, expr_type_def] >>
  goal_assum drule >> simp[]
QED
