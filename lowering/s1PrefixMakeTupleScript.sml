(* Request-prefix companion to bodyFullMakeTuple. *)
Theory s1PrefixMakeTuple
Ancestors
  s1PrefixPreds bodyFullMakeTuple s1PrefixDefs bodyMakeTupleLoopEntry
  s1PrefixMakeTupleLoop s1PrefixInvalidTraceDomain s1PrefixCompose s1PrefixOfVV
  exprSimAggregateSource vyperStorageTrace exprSimHypsDefs exprSimSource

Theorem make_tuple_vv_sim_prefix_conditional:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty ann n args es.
  make_array_packaging_ok /\
  (builtin_args_length_ok (MakeArray NONE n) (LENGTH args) ==>
      body_exprs_full_ok cx args) /\
  (builtin_args_length_ok (MakeArray NONE n) (LENGTH args) ==>
      body_exprs_prefix_ok cx args) /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Builtin ann (MakeArray NONE n) args) es ==>
  expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin ann (MakeArray NONE n) args) es
Proof
  rpt gen_tac >> strip_tac >>
  `compatible_bound n (LENGTH args)` by
    gvs[expr_body_pre_def,cj 9 vyperTypeSystemTheory.well_typed_expr_def,
        vyperTypeSystemTheory.well_typed_builtin_app_def,
        vyperValueTheory.compatible_bound_def] >>
  `builtin_args_length_ok (MakeArray NONE n) (LENGTH args)` by
    simp[vyperContextTheory.builtin_args_length_ok_def] >>
  `body_exprs_full_ok cx args /\ body_exprs_prefix_ok cx args` by metis_tac[] >>
  `!e ee. MEM e args /\ expr_sim_inv cenv cx env ee ==>
      expr_body_pre cenv cx env e ee` by
    (rpt strip_tac >> irule expr_body_pre_builtin_arg >>
     qpat_assum `expr_body_pre _ _ _ (Builtin _ _ _) _` (irule_at Any) >> simp[]) >>
  pure_rewrite_tac[expr_vv_sim_prefix_def,expr_vv_sim_full_pre_def] >>
  rpt gen_tac >> strip_tac >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (irule gas_prefix_full_invalid_trace_domain >> simp[evaluate_storage_trace_frame]) >>
  drule_all make_tuple_allocation_loop_entry >>
  disch_then (qspecl_then [`shadow_ctx`,`PG`]
    (qx_choosel_then [`tys`,`tvs`,`sm`,`ssm`,`q`,`w`,`si`,`Gi`,`tni`] strip_assume_tac)) >> gvs[] >>
  irule gas_prefix_full_zero_prefix_guarded >> simp[evaluate_storage_trace_frame] >>
  qexistsl_tac [`Gi`,`si`,`tni`] >> conj_tac >- metis_tac[] >>
  `!ee. SND (eval_expr cx (Builtin (TupleT tys) (MakeArray NONE n) args) ee) =
        SND (eval_exprs cx args ee)` by
    (gen_tac >> Cases_on `eval_exprs cx args ee` >>
     drule_all aggregate_eval_make_tuple >> simp[]) >>
  drule_then (fn th => once_rewrite_tac[th]) gas_prefix_full_state_cong >>
  `make_tuple_buffer (DF,lo,d,ctx,func,cenv,cx,st0)
    (es,sa,s0,G0,tn0) (q,sa.cs_next_id,w2n w,type_memory_size_list tvs)
    sm es si Gi tni` by
    (simp[s1PrefixMakeTupleSlotTheory.make_tuple_buffer_def,arithmeticTheory.ADD_COMM] >>
     rpt strip_tac >> res_tac) >>
  irule (Q.SPECL [`args`,`tys`,`tvs`,`0`,`[]`] make_tuple_loop_prefix) >>
  qpat_assum `make_tuple_buffer _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `compile_make_tuple _ _ (MAP _ _) _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `body_const_cells_agree _ _ _ _` (irule_at Any) >>
  simp[s1PrefixMakeTupleSlotTheory.make_tuple_saved_slots_def] >>
  qexists `shadow_func` >> conj_tac >- first_assum ACCEPT_TAC >> simp[]
QED
