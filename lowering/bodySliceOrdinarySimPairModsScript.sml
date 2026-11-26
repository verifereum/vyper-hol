(* Close the ordinary Slice route with the checked window run. *)
Theory bodySliceOrdinarySimPairMods
Ancestors
  bodySliceOrdinaryRouteMods bodySliceWindowMods bodyFullPredsMods
  exprLoweringProps vyperAST vyperInterpreter

Theorem slice_ordinary_sim_pair_mods:
  !mods exps DF lo d ctx shadow_ctx PG func shadow_func cenv cx env msrc tops ty ann n args es.
    code_slice_source (Slice n) args = NONE /\
    (builtin_args_length_ok (Slice n) (LENGTH args) ==>
       body_exprs_full_ok_mods mods exps cx args) /\
    contract_inv mods exps ctx cenv cx /\ module_body_inv mods msrc tops cenv cx /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    body_const_cells_agree_mods mods cx env es /\
    expr_body_pre_mods mods cenv cx env (Builtin ann (Slice n) args) es ==>
    expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty
      (Builtin ann (Slice n) args) es /\
    expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty
      (Builtin ann (Slice n) args) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  irule slice_ordinary_from_cuts_mods >> conj_tac
  >- (rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
      irule slice_window_suffix_mods >>
      rpt (conj_tac ORELSE first_assum ACCEPT_TAC) >>
      qexistsl_tac [`N`,`args'`,`bs`,`cnt`,`i`,`k`,`limit`,`n'`,`p`,`root`,`start`] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  asm_rewrite_tac[] >>
  qexistsl_tac [`env`,`exps`,`mods`,`msrc`,`tops`] >> simp[]
QED
