(* Request-prefix companion to bodyFullMakeArray. *)
Theory s1PrefixMakeArray
Ancestors
  s1PrefixPreds bodyFullMakeArray bodyFullMakeArrayResult s1PrefixDefs
  s1PrefixMakeArrayArray s1PrefixMakeTuple s1PrefixOfVV

Theorem make_array_builtin_sim_prefix:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty ann t n args es.
  (builtin_args_length_ok (MakeArray t n) (LENGTH args) ==>
      body_exprs_full_ok cx args) /\
  (builtin_args_length_ok (MakeArray t n) (LENGTH args) ==>
      body_exprs_prefix_ok cx args) /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Builtin ann (MakeArray t n) args) es ==>
  expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin ann (MakeArray t n) args) es /\
    expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin ann (MakeArray t n) args) es
Proof
  rpt gen_tac >> strip_tac >>
  `make_array_packaging_ok` by
    (pure_rewrite_tac[bodyFullMakeArrayResultDefsTheory.make_array_packaging_ok_def,
                      bodyFullMakeArrayResultDefsTheory.make_array_completed_def] >>
     ACCEPT_TAC make_array_completed_full) >>
  reverse conj_asm2_tac
  >- (Cases_on `t`
      >- (irule make_tuple_vv_sim_prefix_conditional >> metis_tac[]) >>
      irule make_array_vv_sim_prefix_conditional >> metis_tac[]) >>
  irule expr_sim_prefix_of_vv >> first_assum ACCEPT_TAC
QED
