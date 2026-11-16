(* MakeArray joint full-family root.  The value bridge is currently a
   LOCAL STUB foreign dependency: this build is conditional development. *)
Theory bodyFullMakeArray
Ancestors
  bodyFullMakeArrayResult bodyFullMakeTuple bodyFullMakeArrayArray
  bodyFullOfVV bodyFullPreds bodySimFull exprSimHyps exprSimSource
  exprSimHypsDefs vyperAST

Theorem make_array_builtin_sim_full:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty ann t n args es.
    (builtin_args_length_ok (MakeArray t n) (LENGTH args) ==>
      body_exprs_full_ok cx args) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin ann (MakeArray t n) args) es ==>
    expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin ann (MakeArray t n) args) es /\
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin ann (MakeArray t n) args) es
Proof
  rpt gen_tac >> strip_tac >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty (Builtin ann (MakeArray t n) args) es` by
    (Cases_on `t`
     >- (irule make_tuple_vv_sim_full_conditional >>
         simp[make_array_completed_full] >> metis_tac[]) >>
     irule make_array_vv_sim_full_conditional >>
     simp[make_array_completed_full] >> metis_tac[]) >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  irule bodyFullOfVVTheory.expr_sim_full_of_vv >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> drule_all exprSimHypsTheory.expr_body_pre_copy_ok >> simp[]) >>
  qpat_assum `expr_body_pre _ _ _ (Builtin ann (MakeArray t n) args) _`
    (mp_tac o MATCH_MP exprSimHypsTheory.expr_body_pre_type_evaluates) >>
  simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  qexists `x` >> simp[] >> rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env (Builtin ann (MakeArray t n) args)
     (es with gas_obs := gs)` by simp[] >>
  drule_all exprSimSourceTheory.expr_body_pre_runtime_typed >>
  strip_tac >> gvs[] >> metis_tac[]
QED
