(*
 * The residual form of the AugAssign body case that S1 still admits: x op= e
 * at a non-local place whose indices are not pure (S1's
 * bodyAugAssignOther$augassign_place_effectful_index_case).  Stated as
 * bodyPtrAssignResidual$body_augassign_other_ptr restricted by that lemma's
 * guards, and admitted until S1 proves its twin.
 *)
Theory bodyPtrAugAssignEffectfulIndex
Ancestors
  bodyPtrPreds bodyPtrDefs bodySim exprSimHyps supportedStmts supportedDecls
  supportedTargets targetPlaceSim stmtLowering exprLowering compileEnv vyperAST
  vyperInterpreter vyperState vyperTypeSystem list finite_map

val _ = Parse.hide "body";

(* RESIDUAL: x op= e at a place with an effectful index, the pointer twin of
   S1's augassign_place_effectful_index_case. *)
Theorem augassign_place_effectful_index_case_ptr:
  !d PG cx ty t bop e tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    (!id. target_root t <> NameTarget id) /\ ~supported_target_pure tops t /\
    ((?b fld. t = AttributeTarget b fld) \/ (?b k. t = SubscriptTarget b k)) /\
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx t s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_ptr_ok cx e) /\ body_base_target_ptr_ok cx t /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (AugAssign ty t bop e) /\
    (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (AugAssign ty t bop e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\
    type_stmt env ret_ty (AugAssign ty t bop e) = SOME env' /\
    stmt_exprs_ok cenv (AugAssign ty t bop e) /\
    call_evaluation_safe cx (int_calls_stmt (AugAssign ty t bop e)) /\
    frame_ret_ok_ptr d ctx PG func cx RetQ cenv ret_ty ==>
    stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign ty t bop e))
      (eval_stmt cx (AugAssign ty t bop e)) es
Proof
  cheat
QED
