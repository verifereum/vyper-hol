(*
 * The raw_log, raw_revert and extcall cases of bodyPtrCallCases, held as
 * residuals.
 *
 * compile_call still lowers RawLog and RawRevert to a bare INVALID here, so
 * neither case holds as defined: the source raw_log returns, the source
 * raw_revert raises RuntimeError "raw_revert", and INVALID matches neither.
 * The lowering is being ported on the S1 branch; once it lands, these are
 * proved like the other call cases.
 *
 * extcall is false here twice over.  The lowering sends the arguments'
 * bound-sized encoding (abi_size_bound) where the source sends the exact
 * one, so the oracle requests differ; the port of the exact-length
 * lowering is on the S1 branch.  And the return decoder forms
 * src + offset from the returndata and compares it with src before its
 * bounds ASSERT, while access_ok's comparison clause wants both compared
 * pointers inside src's site, which a returned offset past the buffer
 * breaks.
 *
 * TOP-LEVEL:
 *   raw_log_case_ptr_residual
 *   raw_revert_case_ptr_residual
 *   extcall_case_ptr_residual
 *)
Theory bodyPtrCallResidual
Ancestors
  bodyPtrPreds vyperAST vyperInterpreter list

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

(* RESIDUAL: false while extcall's calldata is bound-sized and the return
   decoder's offset compare can leave the buffer's site; waits on the S1
   lowering port and a decision on access_ok's comparison clause. *)
Theorem extcall_case_ptr_residual:
  !cx v14 is_static skip_check sig opts es v15.
    (!s'' target t nargs s'3' results t'.
       eval_exprs cx (TAKE 1 es) s'' = (INL target,t) /\
       nargs = LENGTH (FST (SND sig)) /\
       eval_expr_results cx (TAKE nargs (DROP 1 es)) s'3' = (INL results,t') ==>
       body_exprs_ptr_ok cx (DROP (1 + nargs) es)) /\
    (!s'' target t nargs.
       eval_exprs cx (TAKE 1 es) s'' = (INL target,t) /\
       nargs = LENGTH (FST (SND sig)) ==>
       body_results_ptr_ok cx (TAKE nargs (DROP 1 es))) /\
    body_exprs_ptr_ok cx (TAKE 1 es) ==>
    body_expr_ptr_ok cx
      (Call v14 (ExtCall is_static skip_check sig opts) es v15)
Proof
  cheat
QED
