(* Pointer body rows conditional on the shared custom-error raise path. *)
Theory bodyCustomErrorPtrRows
Ancestors
  bodyCustomErrorPtrAssertPrepare stmtSimCustomErrorPtrAssert bodyCustomErrorSource
  bodySim bodyPtrPreds supportedExprs supportedStmtTraverse loweringPosts
  vyperInterpreter vyperAST vyperTypeCallGraph vyperTypeSystem vyperTypeContract

Theorem body_raise_custom_error_using_path_ptr:
  (!cx err d PG tops ctx func cenv env env' ret_ty lctx RetQ es.
    body_inv tops ctx cenv cx /\
    EVERY (supported_pure_expr tops) (custom_error_exprs err) /\
    custom_error_resolved [(NONE,tops)] err /\
    (!target. supported_stmt_expr_exists
      (expr_abi_decode_target_root target) (Raise (RaiseCustomError err)) ==>
      occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Raise (RaiseCustomError err)) = SOME env' /\
    stmt_exprs_ok cenv (Raise (RaiseCustomError err)) /\
    call_evaluation_safe cx (int_calls_stmt (Raise (RaiseCustomError err))) /\
    frame_ret_ok_ptr d ctx PG func cx RetQ cenv ret_ty /\
    body_exprs_ptr_ok cx (custom_error_exprs err) ==>
    stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Raise (RaiseCustomError err)))
      (eval_stmt cx (Raise (RaiseCustomError err))) es) ==>
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
    custom_error_resolved [(NONE,tops)] err /\
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
      (eval_stmt cx (Raise (RaiseCustomError err))) es)
Proof
  rpt strip_tac >>
  `body_exprs_ptr_ok cx (custom_error_exprs err)` by
    (Cases_on `err` >> drule_all custom_error_body_resolution >>
     strip_tac >> metis_tac[]) >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem body_assert_custom_error_using_path_ptr:
  (!cx err d PG tops ctx func cenv env env' ret_ty lctx RetQ es.
    body_inv tops ctx cenv cx /\
    EVERY (supported_pure_expr tops) (custom_error_exprs err) /\
    custom_error_resolved [(NONE,tops)] err /\
    (!target. supported_stmt_expr_exists
      (expr_abi_decode_target_root target) (Raise (RaiseCustomError err)) ==>
      occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Raise (RaiseCustomError err)) = SOME env' /\
    stmt_exprs_ok cenv (Raise (RaiseCustomError err)) /\
    call_evaluation_safe cx (int_calls_stmt (Raise (RaiseCustomError err))) /\
    frame_ret_ok_ptr d ctx PG func cx RetQ cenv ret_ty /\
    body_exprs_ptr_ok cx (custom_error_exprs err) ==>
    stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Raise (RaiseCustomError err)))
      (eval_stmt cx (Raise (RaiseCustomError err))) es) ==>
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
       custom_error_resolved [(NONE,tops)] err /\
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
  disch_tac >> mp_tac body_assert_custom_error_ptr_prepare >>
  (impl_tac >- (conj_tac >- first_assum ACCEPT_TAC >>
                rpt gen_tac >> strip_tac >>
                irule compile_assert_custom_error_frag_general_ptr >> simp[] >>
                first_assum ACCEPT_TAC)) >>
  simp[]
QED
