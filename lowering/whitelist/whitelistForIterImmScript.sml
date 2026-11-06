(* Immutable array iteration uses the location-aware element copy.
   Calldata-origin array arguments are decoded to memory before the body;
   they belong to the memory-valued iterable case, not this leaf. *)
Theory whitelistForIterImm
Ancestors
  whitelistForIterImmCopy whitelistForIterImmSource whitelistForIterImmFrame
  bodySimDeclCases whitelistForIterDynFrag whitelistForIterDynLoop
  exprSimSource bodyExprPreFacts stmtSimProps exprSimHypsDefs list finite_map
  bodySim bodySimStmtCases allocLimits exprSimHyps exprLoweringProps
  stmtSimDecl stmtSimFor stmtSimForParts stmtLowering stmtLoweringMono
  stmtSimForArray stmtSimForArrayFrag stmtSimForArrayLoop
  vyperTyping fragExec compileEnv supportedStmts supportedStmtTraverse
  compileVyper vyperTypeCallGraph vyperTypeCallStackSoundness vyperAST
  vyperInterpreter vyperState vyperValue vyperValueOperation vyperTypeSystem
  vyperTypeInvariants vyperTypeValues vyperTypeEnv valueEncoding
  valueEncodingProps valueEncodingTyping exprSimAggregateEncoding
  exprSimTopLevelImmutable exprSimCopy loweringPosts venomState arithmetic
Libs
  monadsyntax

Theorem body_for_immutable_array:
  !cx id typ bd src name n stmts tops bindings ctx func cenv env env'
   ret_ty lctx RetQ es.
    (!tenv s0 tyv t s1 vs t1 s2 x t2.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s0 =
         (INL tyv,t) /\
       eval_iterator cx (Array (TopLevelName (ArrayT typ bd) (src,name))) s1 =
         (INL vs,t1) /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s2 =
         (INL x,t2) ==>
       body_for_ok cx tyv id stmts vs) /\
    (!tenv s0 tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s0 =
         (INL tyv,t) ==>
       body_iterator_ok cx
         (Array (TopLevelName (ArrayT typ bd) (src,name)))) /\
    body_inv tops ctx cenv cx /\
    supported_type_namespace typ /\ supported_stmts tops bindings stmts /\
    ~supported_stmts_expr_exists expr_internal_call_root stmts /\
    bound_length bd <= n /\
    FLOOKUP env.bare_globals (src,name) = SOME (ArrayT typ bd) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target)
       (For id typ (Array (TopLevelName (ArrayT typ bd) (src,name))) n stmts)
       ==> occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty
      (For id typ (Array (TopLevelName (ArrayT typ bd) (src,name))) n stmts) =
      SOME env' /\
    stmt_exprs_ok cenv
      (For id typ (Array (TopLevelName (ArrayT typ bd) (src,name))) n stmts) /\
    call_evaluation_safe cx
      (int_calls_stmt
        (For id typ (Array (TopLevelName (ArrayT typ bd) (src,name))) n stmts)) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty
        (For id typ (Array (TopLevelName (ArrayT typ bd) (src,name))) n stmts))
      (eval_stmt cx
        (For id typ (Array (TopLevelName (ArrayT typ bd) (src,name))) n stmts)) es
Proof
  cheat
QED
