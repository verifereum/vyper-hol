(* Residual leaf for Len over an internal call whose lowered return type
   differs from the call site's annotation. *)
Theory bodyPtrEnvBuiltinsLenCallResidual
Ancestors
  bodyPtrDefs exprSimDefs exprSimHyps exprSimHypsDefs loweringPosts
  compileEnv context vyperAST

(* Len of an internal-call source whose lowered return type differs from
   its annotation (Decision 18). Intuition: post_value_type cenv e widens to
   expr_type e (exprSimHyps.post_value_type_widens), and post_type_evaluates
   gives it an evaluated type. Len loads only the 32-byte header word
   [w, w+32); its pointer coverage follows from ptr_val_ok at the post type
   (sized_ptr_val_header_covers, since 32 <= val_footprint), and its
   cleanliness from ptr_mem_ok_header_clean via val_in_memory under
   type_widens_to + value_has_type, as exprSimLen's *_widens lemmas do for
   the non-pointer simulation. The eq-typed sibling
   compile_len_singleton_eq_sim_ptr (bodyPtrEnvBuiltinsLenCase) is the
   template. *)
Theorem compile_len_singleton_call_sim_ptr:
  !d ctx PG func cenv cx env ty e es.
    post_value_type cenv e <> expr_type e /\
    expr_body_pre cenv cx env (Builtin (BaseT (UintT 256)) Len [e]) es /\
    expr_vv_sim_ptr d ctx PG func cenv cx ty e es ==>
    expr_vv_sim_ptr d ctx PG func cenv cx ty
      (Builtin (BaseT (UintT 256)) Len [e]) es
Proof
  cheat
QED
