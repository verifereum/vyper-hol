(* Recover the existing main-module program for the gas exemption gate.
   This does not change the source context or its module lookup. *)
Theory gasContext
Ancestors
  vyperContext vyperState

Definition cx_tops_def:
  cx_tops cx =
    case get_module_code cx NONE of SOME tops => tops | NONE => []
End

Theorem cx_tops_module:
  get_module_code cx NONE = SOME tops ==> cx_tops cx = tops
Proof
  simp[cx_tops_def]
QED

Theorem cx_tops_stk[simp]:
  cx_tops (cx with stk := stk) = cx_tops cx
Proof
  simp[cx_tops_def, get_module_code_def]
QED

(* The entry domain is checked before a producer chooses gas-site marks. *)
Definition gas_admissible_def:
  gas_admissible source admissible es <=>
    !gs res ee.
      source (es with gas_obs := gs) = (res, ee) ==> admissible res
End

Theorem gas_admissible_gas_obs[simp]:
  gas_admissible source admissible (es with gas_obs := gs) <=>
  gas_admissible source admissible es
Proof
  simp[gas_admissible_def]
QED

Theorem gas_admissible_result:
  gas_admissible source admissible es /\
  source (es with gas_obs := gs) = (res, ee) ==> admissible res
Proof
  simp[gas_admissible_def] >> metis_tac[]
QED
