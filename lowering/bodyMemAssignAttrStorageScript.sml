(* Memory case of the body induction, assignment to a base target
   (bodyMemAssign's dispatch): a word field of a storage or transient struct (S1's body_assign_attr_storage). *)
Theory bodyMemAssignAttrStorage
Ancestors
  bodyMemoryPreds

Theorem body_assign_attr_storage_mem:
  !cx nsid fld e fty d tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    body_expr_mem_ok cx e /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings
      (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e) = SOME env' /\
    stmt_exprs_ok cenv (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e) /\
    call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e)) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty /\
    supported_storage_field_write tops nsid fld /\
    type_place_target env (AttributeTarget (TopLevelNameTarget nsid) fld) =
      SOME (Type fty) /\
    is_word_type fty ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e))
      (eval_stmt cx (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld)) e)) es
Proof
  cheat
QED
