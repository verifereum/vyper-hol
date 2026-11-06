(*
 * The raw_log, raw_revert and extcall cases of bodyPtrCallCases, held as
 * residuals.
 *
 * raw_revert is proved: compile_raw_revert evaluates the bytes operand and
 * REVERTs with its payload, and rawRevertPtr lifts the operand's pointer
 * simulation through that tail.  raw_log still waits on its proof: its
 * lowering (compile_raw_log) and S1 simulation are in, so it is proved like
 * raw_revert, with the topics' words and the data buffer's ranges.
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
  rawRevertPtr exprSimRawRevertCore

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
  rpt gen_tac >> strip_tac >>
  simp[Once body_expr_ptr_ok_def] >> rpt gen_tac >> strip_tac >>
  drule raw_revert_pre_arg >> strip_tac >> gvs[] >>
  qpat_x_assum `body_exprs_ptr_ok _ _`
    (strip_assume_tac o REWRITE_RULE [body_exprs_ptr_ok_def]) >>
  qpat_x_assum `body_expr_ptr_ok _ _`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_expr_ptr_ok_def]) >>
  `expr_sim_ptr d ctx PG func cenv cx (expr_type e) e es'` by metis_tac[] >>
  metis_tac[raw_revert_sim_ptr, raw_revert_vv_sim_ptr]
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
