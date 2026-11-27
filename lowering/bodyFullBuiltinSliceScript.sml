(* Ordinary, self-code and external-code Slice share one full execution. *)
Theory bodyFullBuiltinSlice
Ancestors
  bodyFullShadowBodyInv
  bodyFullPreds bodySimFull bodyFullOfVV gasOutcomeFullCompose
  bodyFullBuiltinSliceCode bodyFullBuiltinSliceOrdinary
  exprSimHyps exprSimSource exprSimSliceExtcodeTyped
  exprLowering vyperInterpreter vyperAST list
  bodyFullPredsMods[qualified] bodyInvSplit[qualified] exprSimHypsDefs[qualified]

Theorem slice_builtin_sim_full:
  !mods exps DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a n args es.
    (builtin_args_length_ok (Slice n) (LENGTH args) ==>
       case code_slice_source (Slice n) args of
         NONE => body_exprs_full_ok_mods mods exps cx args
       | SOME (code_ty,addr) =>
           body_exprs_full_ok_mods mods exps cx (TL args) /\
           (!s tail_vs t.
              eval_exprs cx (TL args) s = (INL tail_vs,t) ==>
              body_exprs_full_ok_mods mods exps cx [addr])) /\
    (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    body_const_cells_agree mods cx env es /\
    expr_body_pre_mods mods cenv cx env (Builtin a (Slice n) args) es ==>
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a (Slice n) args) es /\
    expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a (Slice n) args) es
Proof
  rpt gen_tac >> strip_tac >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty (Builtin a (Slice n) args) es` by
    (Cases_on `code_slice_source (Slice n) args`
     >- metis_tac[slice_builtin_none_vv_full] >>
     Cases_on `x` >> metis_tac[slice_builtin_some_vv_full]) >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  irule expr_sim_full_of_vv >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> drule_all expr_body_pre_copy_ok >> simp[]) >>
  qpat_assum `expr_body_pre _ _ _ (Builtin _ _ _) _`
    (mp_tac o MATCH_MP expr_body_pre_type_evaluates) >>
  simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  qexists_tac `x` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env (Builtin a (Slice n) args)
     (es with gas_obs := gs)` by simp[] >>
  drule_all expr_body_pre_runtime_typed >>
  strip_tac >> gvs[] >> metis_tac[]
QED
