(*
 * Statement exception/result typing infrastructure for Vyper type soundness.
 *)

Theory vyperTypeStmtResult
Ancestors
  list rich_list arithmetic option pair
  vyperAST vyperValue vyperValueOperation vyperMisc vyperTyping
  vyperTypeSystem vyperTypeInvariants vyperTypeExprSoundness vyperExprNoControl
Libs
  wordsLib

Definition return_exception_typed_def:
  return_exception_typed env ret_ty exn <=>
    case exn of
    | ReturnException v => value_runtime_typed env ret_ty v
    | _ => T
End

Definition stmt_error_ok_def:
  stmt_error_ok env ret_ty r <=>
    no_type_error_result r /\
    (case r of INR exn => return_exception_typed env ret_ty exn | _ => T)
End

Theorem return_exception_typed_INR_case:
  return_exception_typed env ret_ty y ==>
  (case INR y of INL v => T | INR exn => return_exception_typed env ret_ty exn)
Proof
  Cases_on `y` >> simp[return_exception_typed_def]
QED

Theorem return_exception_typed_INR_case_eq:
  (case INR y of INL v => T | INR exn => return_exception_typed env ret_ty exn) =
  return_exception_typed env ret_ty y
Proof
  Cases_on `y` >> simp[return_exception_typed_def]
QED

Theorem return_exception_typed_INR_unit_case_elim:
  (case (INR exn : unit + vyperState$exception) of
   | INL _ => T
   | INR exn0 => return_exception_typed env ret_ty exn0) ==>
  return_exception_typed env ret_ty exn
Proof
  Cases_on `exn` >> simp[return_exception_typed_def]
QED

Theorem return_exception_typed_ReturnException_case:
  return_exception_typed env ret_ty (ReturnException rv) ==>
  (case ReturnException rv of
   | ReturnException v => value_runtime_typed env ret_ty v
   | _ => T)
Proof
  simp[return_exception_typed_def]
QED

Theorem return_exception_typed_ReturnException_value:
  return_exception_typed env ret_ty (ReturnException rv) ==>
  value_runtime_typed env ret_ty rv
Proof
  simp[return_exception_typed_def]
QED

Theorem no_type_error_result_INR_not_type_error:
  no_type_error_result (INR y) ==> y <> Error (TypeError msg)
Proof
  simp[no_type_error_result_def]
QED

Theorem no_control_exc_return_exception_typed:
  no_control_exc exn ==> return_exception_typed env ret_ty exn
Proof
  Cases_on `exn` >> rw[no_control_exc_def, return_exception_typed_def]
QED
