(* Dispatch the linked array subscript to its copied or located route. *)
Theory bodySubscriptArrayRoutesMods
Ancestors
  bodyFullPredsMods bodySubscriptArrayRouteDefsMods bodySimModsProps
  bodySubscriptArrayCopiedMods bodySubscriptArrayUnframedMods
  bodySubscriptArrayFramedCodeMods bodySubscriptArrayFramedMemoryMods

Theorem subscript_array_full_mods:
  !mods exps cx ann obj idx DF lo d PG src tops ctx shadow_ctx
     func shadow_func cenv env ty es et bd.
    (!s'' res t s3 res' t'.
       eval_expr cx obj s'' = (INL res,t) /\
       (if subscript_reads_base cx obj idx then
          bind (read_result cx res) (\v. return (Value v))
        else return res) s3 = (INL res',t') ==>
       body_expr_full_ok_mods mods exps cx idx) /\
    body_expr_full_ok_mods mods exps cx obj /\
    contract_inv mods exps ctx cenv cx /\
    module_body_inv mods src tops cenv cx /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    body_const_cells_agree_mods mods cx env es /\
    expr_body_pre_mods mods cenv cx env (Subscript ann obj idx) es /\
    expr_type obj = ArrayT et bd /\
    place_type cenv obj = ValPT (ArrayT et bd) /\
    post_value_type cenv obj = expr_type obj ==>
    expr_sim_full_mods
      (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Subscript ann obj idx) es /\
    expr_vv_sim_full_mods
      (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Subscript ann obj idx) es
Proof
  rpt gen_tac >> strip_tac >>
  `linked_subscript_array_context_mods mods exps cx ann obj idx
     DF lo d PG src tops ctx shadow_ctx func shadow_func cenv env ty es et bd`
    by (pure_rewrite_tac[linked_subscript_array_context_mods_def] >>
        rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `subscript_reads_base cx obj idx = copies_subscript_base cenv obj idx`
    by (sym_tac >> drule_all body_inv_copies_subscript_base_mods >> simp[]) >>
  Cases_on `copies_subscript_base cenv obj idx`
  >- (drule subscript_array_copied_full_mods >> simp[]) >>
  Cases_on `subscript_array_framed_code_case_mods cenv cx obj idx bd`
  >- (drule subscript_array_framed_code_full_mods >> simp[]) >>
  Cases_on `subscript_array_framed_memory_case_mods cenv cx obj idx et bd`
  >- (drule subscript_array_framed_memory_full_mods >> simp[]) >>
  drule subscript_array_unframed_full_mods >>
  simp[subscript_array_unframed_case_mods_def]
QED
