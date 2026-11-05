(* Memory case of the body induction, augmented assignment
   (bodyMemAugAssign's dispatch): a local (S1's body_augassign_local). x
   op= e runs as x = x op e: the operator's code, then one MSTORE at the
   local's pointer. *)
Theory bodyMemAugAssignLocal
Ancestors
  bodyMemoryPreds

Theorem body_augassign_local_mem:
  !cx ty id bop e d tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx (NameTarget id) s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_mem_ok cx e) /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings (AugAssign ty (NameTarget id) bop e) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (AugAssign ty (NameTarget id) bop e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (AugAssign ty (NameTarget id) bop e) = SOME env' /\
    stmt_exprs_ok cenv (AugAssign ty (NameTarget id) bop e) /\
    call_evaluation_safe cx (int_calls_stmt (AugAssign ty (NameTarget id) bop e)) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign ty (NameTarget id) bop e))
      (eval_stmt cx (AugAssign ty (NameTarget id) bop e)) es
Proof
  cheat
QED
