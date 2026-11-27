(* Discharge the integrated code Slice runtime interfaces. *)
Theory bodyFullBuiltinSliceCode
Ancestors
  bodyFullShadowBodyInv
  bodyFullBuiltinSliceCodeSelfCompose bodyFullBuiltinSliceCodeExternalCompose
  bodyFullBuiltinSliceCodeTail bodyFullBuiltinSliceOperands
  bodyFullPredsMods[qualified] bodyInvSplit[qualified] exprSimHypsDefs[qualified]

Theorem slice_builtin_some_vv_full:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a n args es code_ty addr.
    (builtin_args_length_ok (Slice n) (LENGTH args) ==>
       case code_slice_source (Slice n) args of
         NONE => body_exprs_full_ok_mods mods exps cx args
       | SOME (code_ty,addr) =>
           body_exprs_full_ok_mods mods exps cx (TL args) /\
           (!s tail_vs t. eval_exprs cx (TL args) s = (INL tail_vs,t) ==>
              body_exprs_full_ok_mods mods exps cx [addr])) /\
    (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    body_const_cells_agree mods cx env es /\
    expr_body_pre_mods mods cenv cx env (Builtin a (Slice n) args) es /\
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
      disch_then irule >> simp[] >> qexistsl_tac [`env`, `tops`] >> simp[]) >>
  mp_tac slice_builtin_external_vv_full_from_tail >>
  (impl_tac >- (conj_tac >> rpt gen_tac >>
     FIRST [MATCH_ACCEPT_TAC slice_code_tail_full,
            MATCH_ACCEPT_TAC slice_code_child_full])) >>
  disch_then irule >> simp[] >> qexistsl_tac [`env`, `tops`] >> simp[]
QED
