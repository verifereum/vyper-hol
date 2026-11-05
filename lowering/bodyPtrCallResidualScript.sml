(*
 * The raw_log and raw_revert cases of bodyPtrCallCases, held as residuals.
 *
 * compile_call still lowers RawLog and RawRevert to a bare INVALID here, so
 * neither case holds as defined: the source raw_log returns, the source
 * raw_revert raises RuntimeError "raw_revert", and INVALID matches neither.
 * The lowering is being ported on the S1 branch; once it lands, these are
 * proved like the other call cases.
 *
 * TOP-LEVEL:
 *   raw_log_case_ptr_residual
 *   raw_revert_case_ptr_residual
 *)
Theory bodyPtrCallResidual
Ancestors
  bodyPtrPreds vyperAST

val _ = Parse.hide "body";

(* RESIDUAL: false while RawLog lowers to INVALID; waits on the lowering
   port. *)
Theorem raw_log_case_ptr_residual:
  !cx v20 es v21.
    body_exprs_ptr_ok cx es ==> body_expr_ptr_ok cx (Call v20 RawLog es v21)
Proof
  cheat
QED

(* RESIDUAL: false while RawRevert lowers to INVALID; waits on the
   lowering port. *)
Theorem raw_revert_case_ptr_residual:
  !cx v22 es v23.
    body_exprs_ptr_ok cx es ==> body_expr_ptr_ok cx (Call v22 RawRevert es v23)
Proof
  cheat
QED
