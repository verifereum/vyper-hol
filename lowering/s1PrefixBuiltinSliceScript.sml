(* Request-prefix companion to bodyFullBuiltinSlice. *)
Theory s1PrefixBuiltinSlice
Ancestors
  s1PrefixPreds bodyFullBuiltinSlice s1PrefixDefs
  s1PrefixBuiltinSliceOrdinary s1PrefixBuiltinSliceCode s1PrefixOfVV

Theorem slice_builtin_sim_prefix:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a n args es.
  (builtin_args_length_ok (Slice n) (LENGTH args) ==>
       case code_slice_source (Slice n) args of
         NONE => body_exprs_full_ok cx args
       | SOME (code_ty,addr) =>
           body_exprs_full_ok cx (TL args) /\
           (!s tail_vs t.
              eval_exprs cx (TL args) s = (INL tail_vs,t) ==>
              body_exprs_full_ok cx [addr])) /\
  (builtin_args_length_ok (Slice n) (LENGTH args) ==>
       case code_slice_source (Slice n) args of
         NONE => body_exprs_prefix_ok cx args
       | SOME (code_ty,addr) =>
           body_exprs_prefix_ok cx (TL args) /\
           (!s tail_vs t.
              eval_exprs cx (TL args) s = (INL tail_vs,t) ==>
              body_exprs_prefix_ok cx [addr])) /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Builtin a (Slice n) args) es ==>
  expr_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a (Slice n) args) es /\
    expr_vv_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a (Slice n) args) es
Proof
  rpt gen_tac >> strip_tac >>
  reverse conj_asm2_tac
  >- (Cases_on `code_slice_source (Slice n) args`
      >- metis_tac[slice_builtin_none_vv_prefix] >>
      Cases_on `x` >> metis_tac[slice_builtin_some_vv_prefix]) >>
  irule expr_sim_prefix_of_vv >> simp[]
QED
