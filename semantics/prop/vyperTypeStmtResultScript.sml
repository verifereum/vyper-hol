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

Theorem no_control_exc_return_exception_typed:
  no_control_exc exn ==> return_exception_typed env ret_ty exn
Proof
  Cases_on `exn` >> rw[no_control_exc_def, return_exception_typed_def]
QED
