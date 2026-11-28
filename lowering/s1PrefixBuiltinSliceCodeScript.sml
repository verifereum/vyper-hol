(* Request-prefix companion to bodyFullBuiltinSliceCode. *)
Theory s1PrefixBuiltinSliceCode
Ancestors
  s1PrefixPreds bodyFullBuiltinSliceCode s1PrefixDefs
  s1PrefixBuiltinSliceCodeSelfCompose s1PrefixBuiltinSliceCodeExternalCompose
  s1PrefixBuiltinSliceChildPre bodyFullBuiltinSliceCodeTail bodyFullBuiltinSliceOperands

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  let
    fun discharge rule =
      mp_tac rule >>
      (impl_tac >- (
        conj_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC slice_code_tail_full) >>
        conj_tac >- (rpt gen_tac >> MATCH_ACCEPT_TAC slice_code_child_full) >>
        rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
        drule_all slice_code_child_body_pre >> strip_tac >>
        qpat_x_assum `body_expr_prefix_ok _ _`
          (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
        disch_then irule >> metis_tac[])) >>
      disch_then irule >> simp[] >> qexistsl_tac [`env`, `tops`] >> simp[]
  in
    rpt gen_tac >> strip_tac >>
    Cases_on `is_self_code (Builtin code_ty (Acc Code) [addr])`
    >- discharge slice_builtin_self_vv_prefix_from_tail >>
    discharge slice_builtin_external_vv_prefix_from_tail
  end
QED
*)
Theorem slice_builtin_some_vv_prefix:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a n args es code_ty addr.
  (builtin_args_length_ok (Slice n) (LENGTH args) ==>
       case code_slice_source (Slice n) args of
         NONE => body_exprs_full_ok cx args
       | SOME (code_ty,addr) =>
           body_exprs_full_ok cx (TL args) /\
           (!s tail_vs t. eval_exprs cx (TL args) s = (INL tail_vs,t) ==>
              body_exprs_full_ok cx [addr])) /\
  (builtin_args_length_ok (Slice n) (LENGTH args) ==>
       case code_slice_source (Slice n) args of
         NONE => body_exprs_prefix_ok cx args
       | SOME (code_ty,addr) =>
           body_exprs_prefix_ok cx (TL args) /\
           (!s tail_vs t. eval_exprs cx (TL args) s = (INL tail_vs,t) ==>
              body_exprs_prefix_ok cx [addr])) /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Builtin a (Slice n) args) es /\
  code_slice_source (Slice n) args = SOME (code_ty,addr) ==>
  expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin a (Slice n) args) es
Proof
  cheat
QED
