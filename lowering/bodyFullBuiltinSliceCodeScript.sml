(* Discharge the integrated code Slice runtime interfaces. *)
Theory bodyFullBuiltinSliceCode
Ancestors
  bodyFullBuiltinSliceCodeSelfCompose bodyFullBuiltinSliceCodeExternalCompose
  bodyFullBuiltinSliceCodeTail bodyFullBuiltinSliceOperands

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
  rpt gen_tac >> strip_tac >>
  Cases_on `is_self_code (Builtin code_ty (Acc Code) [addr])`
  >- (mp_tac slice_builtin_self_vv_full_from_tail >>
      (impl_tac >- (conj_tac >> rpt gen_tac >>
         FIRST [MATCH_ACCEPT_TAC slice_code_tail_full,
                MATCH_ACCEPT_TAC slice_code_child_full])) >>
      disch_then irule >> simp[] >> conj_tac >- (qexists_tac `tops` >> simp[]) >>
      qexists_tac `env` >> simp[]) >>
  mp_tac slice_builtin_external_vv_full_from_tail >>
  (impl_tac >- (conj_tac >> rpt gen_tac >>
     FIRST [MATCH_ACCEPT_TAC slice_code_tail_full,
            MATCH_ACCEPT_TAC slice_code_child_full])) >>
  disch_then irule >> simp[] >> conj_tac >- (qexists_tac `tops` >> simp[]) >>
  qexists_tac `env` >> simp[]
QED
