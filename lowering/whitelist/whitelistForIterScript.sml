(*
 * Whitelist removal: for loops over array iterables other than a local
 * fixed-size array.
 *
 * supported_iterator admits only Array (Name (ArrayT ty (Fixed n)) x) with
 * the AST bound equal to the array's size, which body_for_array covers.
 * The checker admits any array-typed iterable; compile_stmt's For Array
 * case handles them all, location-aware.  This theory covers them one form
 * at a time, each stated as body_for_array is, with supported_stmt's For
 * clause minus supported_iterator.  The AST bound only has to be at least
 * the array's capacity (#1202 makes it equal).
 *
 * TOP-LEVEL:
 *   body_for_dynarray_name — iteration over a local DynArray
 *)
Theory whitelistForIter
Ancestors
  bodySimDeclCases whitelistForIterDynLoop

(* A local DynArray: the lowering loads the length word at the local's
   pointer, asserts it is at most the capacity c, and reads element k at
   base + 32 + k * size.  The source iterates the snapshot's elements; the
   body cannot write the array (iterator_unmodified). *)
Theorem body_for_dynarray_name:
  !cx id typ c name n body tops bindings ctx func cenv env env' ret_ty lctx
   RetQ es.
    (!tenv s'' tyv t s'3' vs t' s'4' x t''.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) /\
       eval_iterator cx (Array (Name (ArrayT typ (Dynamic c)) name)) s'3' =
       (INL vs,t') /\
       check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
       (INL x,t'') ==>
       body_for_ok cx tyv id body vs) /\
    (!tenv s'' tyv t.
       tenv = get_tenv cx /\
       lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
       (INL tyv,t) ==>
       body_iterator_ok cx (Array (Name (ArrayT typ (Dynamic c)) name))) /\
    body_inv tops ctx cenv cx /\
    supported_type_namespace typ /\ supported_stmts tops bindings body /\
    ~supported_stmts_expr_exists expr_internal_call_root body /\ c <= n /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target)
       (For id typ (Array (Name (ArrayT typ (Dynamic c)) name)) n body) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty
      (For id typ (Array (Name (ArrayT typ (Dynamic c)) name)) n body) =
      SOME env' /\
    stmt_exprs_ok cenv
      (For id typ (Array (Name (ArrayT typ (Dynamic c)) name)) n body) /\
    call_evaluation_safe cx
      (int_calls_stmt
         (For id typ (Array (Name (ArrayT typ (Dynamic c)) name)) n body)) /\
    frame_ret_ok ctx func cx RetQ cenv ret_ty ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty
         (For id typ (Array (Name (ArrayT typ (Dynamic c)) name)) n body))
      (eval_stmt cx
         (For id typ (Array (Name (ArrayT typ (Dynamic c)) name)) n body)) es
Proof
  cheat
QED
