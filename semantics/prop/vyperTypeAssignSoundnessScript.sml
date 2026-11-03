(*
 * Fresh assignment-target soundness helpers for the executable type system.
 *)

Theory vyperTypeAssignSoundness
Ancestors
  list rich_list finite_map option pair arithmetic
  vyperAST vyperValue vyperValueOperation vyperMisc vyperABI
  vyperInterpreter vyperState vyperContext vyperStorage vyperTyping vyperLookup
  vyperEncodeDecode vyperArith vyperTypeSystem vyperTypeInvariants vyperTypeValues
  vyperTypeEnv vyperTypeExprSoundness vyperTypeStatePreservation
  vyperTypeBuiltins vyperExprNoControl
Libs
  wordsLib markerLib

(* ===== Error-shape lemmas ===== *)

Theorem lift_option_type_error:
  lift_option_type x z y = (INR e, s) ==> e = Error (TypeError z)
Proof
  rw[lift_option_type_def, CaseEq"option", option_CASE_rator, return_def, raise_def]
QED


Theorem get_immutables_error:
  get_immutables x y z = (INR e, s) ==> ?m. e = Error m
Proof
  rw[get_immutables_def, bind_apply, AllCaseEqs(), return_def,
     get_address_immutables_def] >>
  drule lift_option_type_error >> rw[]
QED

Theorem set_storage_backend_no_error[simp]:
  set_storage_backend a b c st <> (INR e, f)
Proof
  Cases_on `b` >> rw[set_storage_backend_def] >>
  gvs[update_transient_def, return_def] >>
  gvs[bind_apply, AllCaseEqs(), get_accounts_def, return_def] >>
  gvs[update_accounts_def, return_def]
QED
