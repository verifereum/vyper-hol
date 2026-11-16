(* Discharge the integrated code Slice runtime interfaces. *)
Theory bodyFullBuiltinSliceCode
Ancestors
  bodyFullBuiltinSliceCodeCompose bodyFullBuiltinSliceCodeTail
  bodyFullBuiltinSliceOperands

Theorem slice_builtin_some_vv_full:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a n args es code_ty addr.
    (builtin_args_length_ok (Slice n) (LENGTH args) ==>
       case code_slice_source (Slice n) args of
         NONE => body_exprs_full_ok cx args
       | SOME (code_ty,addr) =>
           body_exprs_full_ok cx (TL args) /\
           (!s tail_vs t. eval_exprs cx (TL args) s = (INL tail_vs,t) ==>
              body_exprs_full_ok cx [addr])) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin a (Slice n) args) es /\
    code_slice_source (Slice n) args = SOME (code_ty,addr) ==>
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin a (Slice n) args) es
Proof
  mp_tac slice_builtin_some_vv_full_from_tail >>
  (impl_tac >-
    (conj_tac
     >- (rpt gen_tac >> MATCH_ACCEPT_TAC slice_code_tail_full) >>
     rpt gen_tac >> MATCH_ACCEPT_TAC slice_code_child_full)) >>
  disch_then ACCEPT_TAC
QED
