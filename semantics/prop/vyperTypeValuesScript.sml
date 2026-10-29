(*
 * Runtime value/type bridge lemmas for the fresh Vyper type system.
 *)

Theory vyperTypeValues
Ancestors
  list rich_list pred_set prim_rec arithmetic finite_map option pair
  vyperAST vyperValue vyperValueOperation vyperMisc vyperABI
  vyperState vyperContext vyperStorage vyperInterpreter
  vyperTyping vyperEncodeDecode vyperArith vyperTypeSystem vyperTypeInvariants
Libs
  wordsLib

(* ===== Basic evaluate_type / value_has_type bridge ===== *)

Theorem evaluate_type_well_formed_type_value:
  evaluate_type tenv ty = SOME tv ==> well_formed_type_value tv
Proof
  metis_tac[evaluate_type_well_formed]
QED

Theorem value_has_type_NoneTV[simp]:
  value_has_type NoneTV v <=> v = NoneV
Proof
  Cases_on `v` >> simp[value_has_type_def]
QED

Theorem value_has_type_BoolTV:
  value_has_type (BaseTV BoolT) v ==> ?b. v = BoolV b
Proof
  Cases_on `v` >> simp[value_has_type_def]
QED

Theorem value_has_type_StringTV:
  value_has_type (BaseTV (StringT n)) v ==> ?s. v = StringV s
Proof
  Cases_on `v` >> simp[value_has_type_def]
QED

Theorem evaluate_type_NoneT[simp]:
  evaluate_type tenv NoneT = SOME NoneTV
Proof
  simp[evaluate_type_def]
QED

Theorem evaluate_type_NoneTV_imp_NoneT:
  evaluate_type tenv ty = SOME NoneTV ==> ty = NoneT
Proof
  Cases_on `ty` >> gvs[evaluate_type_def, AllCaseEqs()]
QED

Theorem evaluate_type_not_NoneT_imp_not_NoneTV:
  evaluate_type tenv ty = SOME tyv /\ ty <> NoneT ==> tyv <> NoneTV
Proof
  metis_tac[evaluate_type_NoneTV_imp_NoneT]
QED

Theorem evaluate_type_BaseT_cases:
  evaluate_type tenv (BaseT bt) = SOME tv ==>
  ?btv. tv = BaseTV btv
Proof
  Cases_on `bt` >> rw[evaluate_type_def, AllCaseEqs(), LET_THM]
QED

Theorem evaluate_type_not_ArrayT_imp_not_ArrayTV:
  evaluate_type tenv ty = SOME tyv /\ (!t bd. ty <> ArrayT t bd) ==>
  !t b. tyv <> ArrayTV t b
Proof
  Cases_on `ty` >> rpt strip_tac >>
  gvs[evaluate_type_def, AllCaseEqs(), LET_THM]
QED

Theorem evaluate_type_ArrayT_cases:
  evaluate_type tenv (ArrayT elem bd) = SOME tv ==>
  ?elem_tv. tv = ArrayTV elem_tv bd /\ evaluate_type tenv elem = SOME elem_tv
Proof
  rw[evaluate_type_def, AllCaseEqs(), LET_THM]
QED

Theorem evaluate_type_TupleT_cases:
  evaluate_type tenv (TupleT tys) = SOME tv ==>
  ?tvs. tv = TupleTV tvs /\ LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) tys tvs
Proof
  rw[evaluate_type_def, AllCaseEqs(), LET_THM]
  >> gvs[evaluate_types_OPT_MMAP, OPT_MMAP_SOME_IFF]
  >> gvs[LIST_REL_EL_EQN, EVERY_EL, EL_MAP, IS_SOME_EXISTS]
  >> rw[] >> first_x_assum drule >> rw[]
  >> rw[]
QED

(* ===== Literal soundness ===== *)

Theorem well_typed_literal_sound:
  well_typed_literal ty lit /\ evaluate_type tenv ty = SOME tv ==>
  value_has_type tv (evaluate_literal lit)
Proof
  Cases_on `ty` >> Cases_on `lit` >> rw[] >>
  gvs[well_typed_literal_def, evaluate_type_def, evaluate_literal_def,
      value_has_type_def, AllCaseEqs(), LET_THM, within_int_bound_def] >>
  gvs[evaluate_type_def, value_has_type_def, compatible_bound_def]
QED

Theorem literal_value_result_typed:
  well_typed_literal ty lit /\ evaluate_type tenv ty = SOME tv ==>
  value_result_typed (Value (evaluate_literal lit)) tv
Proof
  rw[value_result_typed_def] >> drule_all well_typed_literal_sound >> simp[]
QED

(* ===== Lists ===== *)

(* ===== Top-level values ===== *)

Theorem value_result_typed_Value:
  value_result_typed (Value v) tv <=> value_has_type tv v
Proof
  simp[value_result_typed_def]
QED

Theorem value_result_is_value:
  value_result_typed res tv ==> ?v. res = Value v
Proof
  rw[value_result_typed_def] >> metis_tac[]
QED
