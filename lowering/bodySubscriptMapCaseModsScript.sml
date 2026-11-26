(* For a mapping base the interpreter's preparation step is an identity run. *)
Theory bodySubscriptMapCaseMods
Ancestors
  bodyMapSubscriptExtensionMods bodyMapSubscriptStaticMods bodyFullPredsMods
  bodyFullPostsMods vyperInterpreter vyperState

Theorem subscript_map_leaf_from_reached_mods:
  (!s'' res t s'3' res' t'.
    eval_expr cx obj s'' = (INL res,t) /\
    (if subscript_reads_base cx obj idx then
       bind (read_result cx res) (\v. return (Value v))
     else return res) s'3' = (INL res',t') ==>
    body_expr_full_ok_mods mods exps cx idx) /\
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env (Subscript ann obj idx) es /\
  place_type cenv obj = MapPT kt vt /\
  (expr_map_pre_mods mods cenv cx env obj es ==>
   expr_map_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty obj es) ==>
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Subscript ann obj idx) es
Proof
  strip_tac >>
  drule_all_then strip_assume_tac (cj 2 map_subscript_static_mods) >>
  qpat_assum `!s r t s0 r0 t0. _` mp_tac >>
  simp[return_def] >> strip_tac >>
  qpat_assum `expr_map_pre_mods _ _ _ _ _ _ ==> _` (drule_then assume_tac) >>
  irule subscript_map_full_mods >> simp[] >>
  qexistsl_tac [`env`,`exps`,`mods`,`src`,`tops`] >> simp[] >>
  first_assum ACCEPT_TAC
QED

Theorem subscript_map_result_from_reached_mods:
  (!s'' res t s'3' res' t'.
    eval_expr cx obj s'' = (INL res,t) /\
    (if subscript_reads_base cx obj idx then
       bind (read_result cx res) (\v. return (Value v))
     else return res) s'3' = (INL res',t') ==>
    body_expr_full_ok_mods mods exps cx idx) /\
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\
  expr_map_pre_mods mods cenv cx env (Subscript ann obj idx) es /\
  (expr_map_pre_mods mods cenv cx env obj es ==>
   expr_map_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty obj es) ==>
  expr_map_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Subscript ann obj idx) es
Proof
  strip_tac >>
  drule_then strip_assume_tac (cj 1 map_subscript_static_mods) >>
  qpat_assum `!s r t s0 r0 t0. _` mp_tac >>
  simp[return_def] >> strip_tac >>
  qpat_assum `expr_map_pre_mods _ _ _ _ _ _ ==> _` (drule_then assume_tac) >>
  irule subscript_map_map_full_mods >> simp[] >>
  qexistsl_tac [`env`,`exps`,`mods`,`src`,`tops`] >> simp[] >>
  first_assum ACCEPT_TAC
QED
