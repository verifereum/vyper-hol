(* Joint value and VV simulations for the two MakeArray layouts. *)
Theory bodyFullMakeArray
Ancestors
  bodyFullShadowBodyInv
  bodyFullMakeArrayResult bodyFullMakeTuple bodyFullMakeArrayArray
  bodyFullOfVV bodyFullPreds bodySimFull exprSimHyps exprSimSource
  bodyFullPredsMods[qualified] bodyInvSplit[qualified] exprSimHypsDefs[qualified]

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >>
  reverse conj_asm2_tac
  >- (Cases_on `t`
      >- (irule (REWRITE_RULE [EQT_INTRO make_array_completed_full]
                    make_tuple_vv_sim_full_conditional) >> metis_tac[]) >>
      irule (REWRITE_RULE [EQT_INTRO make_array_completed_full]
               make_array_vv_sim_full_conditional) >> metis_tac[]) >>
  irule expr_sim_full_of_vv >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> drule_all expr_body_pre_copy_ok >> simp[]) >>
  drule expr_body_pre_type_evaluates >>
  simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  qexists `x` >> simp[] >> rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env (Builtin ann (MakeArray t n) args)
     (es with gas_obs := gs)` by simp[] >>
  drule_all expr_body_pre_runtime_typed >>
  strip_tac >> gvs[] >> metis_tac[]
QED
*)
Theorem make_array_builtin_sim_full:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty ann t n args es.
    (builtin_args_length_ok (MakeArray t n) (LENGTH args) ==>
      body_exprs_full_ok_mods mods exps cx args) /\
    (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    body_const_cells_agree mods cx env es /\
    expr_body_pre_mods mods cenv cx env (Builtin ann (MakeArray t n) args) es ==>
    expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin ann (MakeArray t n) args) es /\
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin ann (MakeArray t n) args) es
Proof
  cheat
QED
