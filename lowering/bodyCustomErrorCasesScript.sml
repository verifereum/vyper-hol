(*
 * The custom-error rows of the three body inductions: raise E(...) and
 * assert c, E(...), lowered by compile_revert_with_custom_error
 * (stmtLowering) as pinned Python Vyper does.
 *
 * Rows 8 and 12 of body_sim_mutual (bodySimMain), body_mem_mutual
 * (bodyMemory) and body_sim_ptr_mutual (bodySimPtrMain) are vacuous while
 * supported_raise_reason and supported_assert_reason exclude custom errors.
 * Each theorem below is what those rows need once the gate admits them: the
 * premises of body_stmt_ok, body_stmt_mem_ok and body_stmt_ptr_ok, with
 * supported_stmt replaced by the gate the string-reason siblings have
 * (supported_string_reason: a pure reason), here every argument pure, and
 * the error resolved against tops as check_contract has it
 * (custom_errors_stmt_ok): declared, with arguments matching its
 * parameters.  The induction hypotheses are those evaluate_ind gives for
 * the two rows.
 *
 * TOP-LEVEL (all ADMITTED, one per tower):
 *   body_custom_error_cases       S1 (stmt_frag)
 *   body_custom_error_mem_cases   S3 memory (stmt_frag_mem)
 *   body_custom_error_ptr_cases   S3 pointer (stmt_frag_ptr)
 *)
Theory bodyCustomErrorCases
Ancestors
  bodySim bodyMemoryPreds bodyPtrPreds supportedExprs supportedStmtTraverse
  loweringPosts vyperInterpreter vyperAST vyperTypeCallGraph vyperTypeSystem
  vyperTypeContract

val _ = Parse.hide "body";

(* ADMITTED: S1 rows 8 and 12; siblings body_raise_reason_case and
   body_assert_reason_case (bodySimStmtCases). *)
Theorem body_custom_error_cases:
  (!cx err.
     (!id positional kwargs decls params args.
        err = CustomError id positional kwargs /\
        get_module_code cx (FST id) = SOME decls /\
        lookup_custom_error_args_in (SND id) decls = SOME params /\
        order_custom_error_args params err = SOME args ==>
        body_exprs_ok cx args) ==>
     !tops ctx func cenv env env' ret_ty lctx RetQ es.
       body_inv tops ctx cenv cx /\
       EVERY (supported_pure_expr tops) (custom_error_exprs err) /\
       custom_error_resolved [(NONE, tops)] err /\
       (!target. supported_stmt_expr_exists
          (expr_abi_decode_target_root target) (Raise (RaiseCustomError err)) ==>
          occurs_abi_decode_target target tops) /\
       expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
       locals_alloc_ok cenv env /\
       type_stmt env ret_ty (Raise (RaiseCustomError err)) = SOME env' /\
       stmt_exprs_ok cenv (Raise (RaiseCustomError err)) /\
       call_evaluation_safe cx (int_calls_stmt (Raise (RaiseCustomError err))) /\
       frame_ret_ok ctx func cx RetQ cenv ret_ty ==>
       stmt_frag ctx func cx lctx RetQ cenv
         (stmt_env cenv lctx ret_ty (Raise (RaiseCustomError err)))
         (eval_stmt cx (Raise (RaiseCustomError err))) es) /\
  (!cx e err.
     body_expr_ok cx e /\
     (!s0 tv s1 id positional kwargs decls params args.
        eval_expr cx e s0 = (INL tv,s1) /\
        err = CustomError id positional kwargs /\
        get_module_code cx (FST id) = SOME decls /\
        lookup_custom_error_args_in (SND id) decls = SOME params /\
        order_custom_error_args params err = SOME args ==>
        body_exprs_ok cx args) ==>
     !tops ctx func cenv env env' ret_ty lctx RetQ es.
       body_inv tops ctx cenv cx /\ supported_pure_expr tops e /\
       EVERY (supported_pure_expr tops) (custom_error_exprs err) /\
       custom_error_resolved [(NONE, tops)] err /\
       (!target. supported_stmt_expr_exists
          (expr_abi_decode_target_root target) (Assert e (AssertCustomError err)) ==>
          occurs_abi_decode_target target tops) /\
       expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
       locals_alloc_ok cenv env /\
       type_stmt env ret_ty (Assert e (AssertCustomError err)) = SOME env' /\
       stmt_exprs_ok cenv (Assert e (AssertCustomError err)) /\
       call_evaluation_safe cx (int_calls_stmt (Assert e (AssertCustomError err))) /\
       frame_ret_ok ctx func cx RetQ cenv ret_ty ==>
       stmt_frag ctx func cx lctx RetQ cenv
         (stmt_env cenv lctx ret_ty (Assert e (AssertCustomError err)))
         (eval_stmt cx (Assert e (AssertCustomError err))) es)
Proof
  cheat
QED

(* ADMITTED: S3 memory rows 8 and 12; siblings body_raise_reason_mem_case
   (bodyMemRaiseReason) and body_assert_reason_mem_case. *)
Theorem body_custom_error_mem_cases:
  (!cx err.
     (!id positional kwargs decls params args.
        err = CustomError id positional kwargs /\
        get_module_code cx (FST id) = SOME decls /\
        lookup_custom_error_args_in (SND id) decls = SOME params /\
        order_custom_error_args params err = SOME args ==>
        body_exprs_mem_ok cx args) ==>
     !d tops ctx func cenv env env' ret_ty lctx RetQ es.
       body_inv tops ctx cenv cx /\
       EVERY (supported_pure_expr tops) (custom_error_exprs err) /\
       custom_error_resolved [(NONE, tops)] err /\
       (!target. supported_stmt_expr_exists
          (expr_abi_decode_target_root target) (Raise (RaiseCustomError err)) ==>
          occurs_abi_decode_target target tops) /\
       expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
       locals_alloc_ok cenv env /\
       type_stmt env ret_ty (Raise (RaiseCustomError err)) = SOME env' /\
       stmt_exprs_ok cenv (Raise (RaiseCustomError err)) /\
       call_evaluation_safe cx (int_calls_stmt (Raise (RaiseCustomError err))) /\
       frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty ==>
       stmt_frag_mem d ctx func cx lctx RetQ cenv
         (stmt_env cenv lctx ret_ty (Raise (RaiseCustomError err)))
         (eval_stmt cx (Raise (RaiseCustomError err))) es) /\
  (!cx e err.
     body_expr_mem_ok cx e /\
     (!s0 tv s1 id positional kwargs decls params args.
        eval_expr cx e s0 = (INL tv,s1) /\
        err = CustomError id positional kwargs /\
        get_module_code cx (FST id) = SOME decls /\
        lookup_custom_error_args_in (SND id) decls = SOME params /\
        order_custom_error_args params err = SOME args ==>
        body_exprs_mem_ok cx args) ==>
     !d tops ctx func cenv env env' ret_ty lctx RetQ es.
       body_inv tops ctx cenv cx /\ supported_pure_expr tops e /\
       EVERY (supported_pure_expr tops) (custom_error_exprs err) /\
       custom_error_resolved [(NONE, tops)] err /\
       (!target. supported_stmt_expr_exists
          (expr_abi_decode_target_root target) (Assert e (AssertCustomError err)) ==>
          occurs_abi_decode_target target tops) /\
       expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
       locals_alloc_ok cenv env /\
       type_stmt env ret_ty (Assert e (AssertCustomError err)) = SOME env' /\
       stmt_exprs_ok cenv (Assert e (AssertCustomError err)) /\
       call_evaluation_safe cx (int_calls_stmt (Assert e (AssertCustomError err))) /\
       frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty ==>
       stmt_frag_mem d ctx func cx lctx RetQ cenv
         (stmt_env cenv lctx ret_ty (Assert e (AssertCustomError err)))
         (eval_stmt cx (Assert e (AssertCustomError err))) es)
Proof
  cheat
QED

(* ADMITTED: S3 pointer rows 8 and 12; siblings body_raise_reason_case_ptr
   and body_assert_reason_case_ptr (bodyPtrExitCases). *)
Theorem body_custom_error_ptr_cases:
  (!cx err.
     (!id positional kwargs decls params args.
        err = CustomError id positional kwargs /\
        get_module_code cx (FST id) = SOME decls /\
        lookup_custom_error_args_in (SND id) decls = SOME params /\
        order_custom_error_args params err = SOME args ==>
        body_exprs_ptr_ok cx args) ==>
     !d PG tops ctx func cenv env env' ret_ty lctx RetQ es.
       body_inv tops ctx cenv cx /\
       EVERY (supported_pure_expr tops) (custom_error_exprs err) /\
       custom_error_resolved [(NONE, tops)] err /\
       (!target. supported_stmt_expr_exists
          (expr_abi_decode_target_root target) (Raise (RaiseCustomError err)) ==>
          occurs_abi_decode_target target tops) /\
       expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
       locals_alloc_ok cenv env /\
       type_stmt env ret_ty (Raise (RaiseCustomError err)) = SOME env' /\
       stmt_exprs_ok cenv (Raise (RaiseCustomError err)) /\
       call_evaluation_safe cx (int_calls_stmt (Raise (RaiseCustomError err))) /\
       frame_ret_ok_ptr d ctx PG func cx RetQ cenv ret_ty ==>
       stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
         (stmt_env cenv lctx ret_ty (Raise (RaiseCustomError err)))
         (eval_stmt cx (Raise (RaiseCustomError err))) es) /\
  (!cx e err.
     body_expr_ptr_ok cx e /\
     (!s0 tv s1 id positional kwargs decls params args.
        eval_expr cx e s0 = (INL tv,s1) /\
        err = CustomError id positional kwargs /\
        get_module_code cx (FST id) = SOME decls /\
        lookup_custom_error_args_in (SND id) decls = SOME params /\
        order_custom_error_args params err = SOME args ==>
        body_exprs_ptr_ok cx args) ==>
     !d PG tops ctx func cenv env env' ret_ty lctx RetQ es.
       body_inv tops ctx cenv cx /\ supported_pure_expr tops e /\
       EVERY (supported_pure_expr tops) (custom_error_exprs err) /\
       custom_error_resolved [(NONE, tops)] err /\
       (!target. supported_stmt_expr_exists
          (expr_abi_decode_target_root target) (Assert e (AssertCustomError err)) ==>
          occurs_abi_decode_target target tops) /\
       expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
       locals_alloc_ok cenv env /\
       type_stmt env ret_ty (Assert e (AssertCustomError err)) = SOME env' /\
       stmt_exprs_ok cenv (Assert e (AssertCustomError err)) /\
       call_evaluation_safe cx (int_calls_stmt (Assert e (AssertCustomError err))) /\
       frame_ret_ok_ptr d ctx PG func cx RetQ cenv ret_ty ==>
       stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
         (stmt_env cenv lctx ret_ty (Assert e (AssertCustomError err)))
         (eval_stmt cx (Assert e (AssertCustomError err))) es)
Proof
  cheat
QED
