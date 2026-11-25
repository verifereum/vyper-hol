(* Package the three uniform entry observations for a source expression. *)
Theory s1PrefixBoolChainUniformEntries
Ancestors
  s1PrefixPreds s1PrefixDefs

Theorem bool_chain_prefix_ok_of_uniform_entries:
  !cx e.
    (!DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es
       st0 sa sb shadow_sa shadow_sb op s0 G0 tn0.
      body_inv tops ctx cenv cx /\
      shadow_body_inv tops ctx shadow_ctx /\
      body_const_cells_agree [(NONE,tops)] cx env es /\
      expr_body_pre cenv cx env e es /\
      expr_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
        cenv cx ty e es (st0,sa,sb,shadow_sa,shadow_sb,op,s0,G0,tn0) ==>
      gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s0,G0,tn0)) /\
    (!DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es
       st0 sa sb shadow_sa shadow_sb vv s0 G0 tn0.
      body_inv tops ctx cenv cx /\
      shadow_body_inv tops ctx shadow_ctx /\
      body_const_cells_agree [(NONE,tops)] cx env es /\
      expr_body_pre cenv cx env e es /\
      expr_vv_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
        cenv cx ty e es (st0,sa,sb,shadow_sa,shadow_sb,vv,s0,G0,tn0) ==>
      gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        cx st0 (eval_expr cx e) (es,s0,G0,tn0)) /\
    (!a t n elems.
      e = Builtin a (MakeArray t n) elems /\
      builtin_args_length_ok (MakeArray t n) (LENGTH elems) ==>
      body_exprs_prefix_ok cx elems) /\
    (!ann e1 e2 DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es
       st0 sa sb shadow_sa shadow_sb vv s0 G0 tn0.
      e = Subscript ann e1 e2 /\
      body_inv tops ctx cenv cx /\
      shadow_body_inv tops ctx shadow_ctx /\
      body_const_cells_agree [(NONE,tops)] cx env es /\
      expr_map_pre cenv cx env e es /\
      expr_map_sim_full_pre (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
        cenv cx ty e es (st0,sa,sb,shadow_sa,shadow_sb,vv,s0,G0,tn0) ==>
      gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        cx st0 (eval_expr cx e) (es,s0,G0,tn0)) ==>
    body_expr_prefix_ok cx e
Proof
  rpt gen_tac >> strip_tac >>
  once_rewrite_tac[body_expr_prefix_ok_def] >>
  fs[expr_sim_prefix_def, expr_vv_sim_prefix_def, expr_map_sim_prefix_def,
     IMP_CONJ_THM, FORALL_AND_THM, GSYM RIGHT_FORALL_IMP_THM,
     AND_IMP_INTRO, GSYM CONJ_ASSOC] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >> gvs[] >> metis_tac[]
QED
