(* Request-prefix companion to bodyFullSubscriptMapBase. *)
Theory s1PrefixSubscriptMapBase
Ancestors
  s1PrefixPreds s1PrefixNames s1PrefixFrame s1PrefixDefs bodySim bodyFullSubscriptMapBase
  vyperStorageTrace vyperInterpreter vyperAST

Theorem body_expr_prefix_ok_map:
  body_expr_full_ok cx e /\
  body_expr_prefix_ok cx e /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_map_pre cenv cx env e es ==>
  expr_map_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e es
Proof
  strip_tac >> drule expr_map_pre_shape >> strip_tac >> gvs[]
  >- (namedCases_on `id` ["src nm"] >>
      rw[expr_map_sim_prefix_def, expr_map_sim_full_pre_def] >>
      irule gas_prefix_full_no_outcome >>
      simp[evaluate_storage_trace_frame] >>
      rpt gen_tac >> simp[Once evaluate_def] >>
      strip_tac >> drule lookup_global_no_outcome >> simp[]) >>
  qpat_x_assum `body_expr_prefix_ok _ _`
    (mp_tac o CONJUNCT2 o CONJUNCT2 o ONCE_REWRITE_RULE [body_expr_prefix_ok_def]) >>
  metis_tac[]
QED
