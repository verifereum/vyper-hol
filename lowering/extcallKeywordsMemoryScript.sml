(* Source-ordered keyword list composition with its concrete returned options. *)
Theory extcallKeywordsMemory
Ancestors
  stmtReasonVvMemory exprSimWordArgs exprLoweringProps exprLowering stmtLoweringMono
  compileEnv fragExec gasOutcome vyperState list externalEntryShape vyperInterpreter
  exprSimDefs rich_list

Theorem extcall_keywords_mem_cps:
  !es keys sa opts sb ars avs ee s.
    compile_ext_call_kwargs compile_expr ce rt keys es sa = (opts,sb) /\
    LENGTH keys = LENGTH es /\ fn_has_code sa sb func /\ P ars avs ee s sa es /\
    (!key e tail rs vs st t sc sn op ty.
       MEM (key,e) (ZIP (keys,es)) /\ P rs vs st t sc (e::tail) /\
       compile_ext_call_kwarg compile_expr ce rt key e sc = ((op,ty),sn) /\
       fn_has_code sc sn func ==>
       gas_outcome T (cx_tops cx) (ctx,func)
         (bind (eval_expr cx e) (read_result cx)) (st,t)
         (\res fin u. ?v. res = INL v /\
           P (rs ++ [v]) (vs ++ [(key,op,ty)]) fin u sn tail)
         (\res fin r. expr_exit res r)) /\
    (!rs vs st t. P rs vs st t sb [] ==>
       gas_outcome T (cx_tops cx) (ctx,func)
         (next rs (FOLDR (\(key,op,ty) (vo,go,dopt).
             if key = EKValue then (SOME op,go,dopt)
             else if key = EKGas then (vo,SOME op,dopt)
             else (vo,go,SOME (op,ty))) (NONE,NONE,NONE) vs)) (st,t) Q
         (\res fin r. expr_exit res r)) ==>
    gas_outcome T (cx_tops cx) (ctx,func)
      (bind (eval_exprs cx es)
        (\rs. next (ars ++ rs) (FOLDR (\(key,op,ty) (vo,go,dopt).
             if key = EKValue then (SOME op,go,dopt)
             else if key = EKGas then (vo,SOME op,dopt)
             else (vo,go,SOME (op,ty))) opts avs)))
      (ee,s) Q (\res fin r. expr_exit res r)
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >>
      gvs[compile_ext_call_kwargs_def, comp_return_def, Once evaluate_def,
          bind_return] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> Cases_on `keys` >> gvs[] >>
  rename1 `LENGTH ks = LENGTH es` >>
  qpat_x_assum `compile_ext_call_kwargs _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_ext_call_kwargs_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[comp_bind_def,comp_return_def]) >>
  strip_tac >> gvs[] >>
  rename1 `compile_ext_call_kwarg compile_expr ce rt h' h sa = ((op,ty),sm)` >>
  rename1 `compile_ext_call_kwargs compile_expr ce rt ks es sm =
    ((value_op,gas_op,default_opt),sf)` >>
  suspend "head"
QED
Resume extcall_keywords_mem_cps[head]:
  `ci_mono sa sm` by
    (`ci_mono sa (SND (compile_ext_call_kwarg compile_expr ce rt h' h sa))` by
       (irule ci_mono_compile_ext_call_kwarg >>
        simp[cj 1 ci_mono_compile_expr_sa]) >> metis_tac[pairTheory.SND]) >>
  `cs_extends sm sf` by
    (qspecl_then [`ks`,`es`,`compile_expr`,`ce`,`rt`,`sm`]
       mp_tac compile_ext_call_kwargs_labels >>
     simp[cj 1 compile_expr_labels] >> metis_tac[pairTheory.SND]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sf func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_mid,cs_extends_refl]) >>
  `gas_outcome T (cx_tops cx) (ctx,func)
     (bind (eval_expr cx h) (read_result cx)) (ee,s)
     (\res fin u. ?v. res = INL v /\
       P (ars ++ [v]) (avs ++ [(h',op,ty)]) fin u sm es)
     (\res fin r. expr_exit res r)` by
    (qpat_x_assum `!key e tail rs vs st t sc sn op ty. _`
       (qspecl_then [`h'`,`h`,`es`,`ars`,`avs`,`ee`,`s`,`sa`,`sm`,`op`,`ty`]
          mp_tac) >> simp[]) >>
  simp[eval_exprs_cons_action,bind_assoc,bind_return] >>
  once_rewrite_tac[GSYM bind_assoc] >>
  irule gas_outcome_bind_value >>
  goal_assum (drule_at Any) >> conj_tac
  >- suspend "tail" >>
  rpt strip_tac >> Cases_on `res` >> gvs[expr_exit_def] >>
  metis_tac[stmtSimPropsTheory.expr_exit_INR_type]
QED
Resume extcall_keywords_mem_cps[tail]:
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `!keys sa opts sb ars avs ee s. _`
    (qspecl_then [`ks`, `sm`, `(value_op,gas_op,default_opt)`, `sf`,
                 `ars ++ [v]`, `avs ++ [(h',op,ty)]`,
                 `mid with gas_obs := []`, `t`] mp_tac) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC,APPEND,FOLDR_APPEND,FOLDR] >>
  simp[] >> disch_then irule >>
  rpt conj_tac >> metis_tac[]
QED
Finalise extcall_keywords_mem_cps
