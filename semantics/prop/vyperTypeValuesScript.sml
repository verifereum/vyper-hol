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

Theorem well_formed_type_evaluate_type_well_formed:
  well_formed_type tenv ty /\ evaluate_type tenv ty = SOME tv ==>
  well_formed_type_value tv
Proof
  rw[well_formed_type_def] >> drule evaluate_type_well_formed_type_value >> simp[]
QED

Theorem value_has_type_well_formed_dest:
  value_has_type tv v /\ well_formed_type_value tv ==> value_has_type tv v
Proof
  simp[]
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

Theorem toplevel_value_typed_BoolTV:
  toplevel_value_typed tv (BaseTV BoolT) ==> ?b. tv = Value (BoolV b)
Proof
  Cases_on `tv` >> simp[toplevel_value_typed_def] >>
  metis_tac[value_has_type_BoolTV]
QED

Theorem value_has_type_StringTV:
  value_has_type (BaseTV (StringT n)) v ==> ?s. v = StringV s
Proof
  Cases_on `v` >> simp[value_has_type_def]
QED

Theorem toplevel_value_typed_StringTV:
  toplevel_value_typed tv (BaseTV (StringT n)) ==> ?s. tv = Value (StringV s)
Proof
  Cases_on `tv` >> simp[toplevel_value_typed_def] >>
  metis_tac[value_has_type_StringTV]
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

Theorem evaluate_type_BaseT_imp_not_ArrayTV:
  evaluate_type tenv (BaseT bt) = SOME tyv ==> !t b. tyv <> ArrayTV t b
Proof
  strip_tac >> drule evaluate_type_BaseT_cases >> strip_tac >> gvs[]
QED

Theorem evaluate_type_FlagT_imp_not_ArrayTV:
  evaluate_type tenv (FlagT fid) = SOME tyv ==> !t b. tyv <> ArrayTV t b
Proof
  rpt strip_tac >> gvs[evaluate_type_def, AllCaseEqs()]
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

Theorem value_has_type_evaluate_type_well_formed:
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v ==>
  well_formed_type_value tv
Proof
  metis_tac[evaluate_type_well_formed_type_value]
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

Theorem literal_toplevel_value_typed:
  well_typed_literal ty lit /\ evaluate_type tenv ty = SOME tv ==>
  toplevel_value_typed (Value (evaluate_literal lit)) tv
Proof
  rw[toplevel_value_typed_def] >> drule_all well_typed_literal_sound >> simp[]
QED

(* ===== Lists ===== *)

Theorem LIST_REL_value_has_type_well_formed:
  LIST_REL value_has_type tvs vs /\ EVERY well_formed_type_value tvs ==>
  LIST_REL value_has_type tvs vs
Proof
  simp[]
QED

Theorem evaluate_type_MAP_well_formed:
  LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) tys tvs ==>
  EVERY well_formed_type_value tvs
Proof
  qid_spec_tac`tvs` >> Induct_on `tys` >> Cases_on `tvs` >> rw[] >>
  drule evaluate_type_well_formed_type_value >> simp[]
QED

(* ===== Top-level values ===== *)

Theorem toplevel_value_typed_Value:
  toplevel_value_typed (Value v) tv <=> value_has_type tv v
Proof
  simp[toplevel_value_typed_def]
QED

Theorem toplevel_value_typed_not_ArrayRef:
  toplevel_value_typed tv tyv /\ tyv <> NoneTV /\ (!t b. tyv <> ArrayTV t b) ==>
  ?v. tv = Value v
Proof
  Cases_on `tv` >> gvs[toplevel_value_typed_def] >>
  first_x_assum irule >> simp[]
QED

Theorem toplevel_value_typed_not_hashmap_material:
  toplevel_value_typed tv tyv /\ is_HashMapRef tv ==> tyv = NoneTV
Proof
  Cases_on `tv` >> simp[toplevel_value_typed_def]
QED
