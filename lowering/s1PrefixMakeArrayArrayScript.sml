(* Request-prefix companion to bodyFullMakeArrayArray. *)
Theory s1PrefixMakeArrayArray
Ancestors
  s1PrefixPreds bodyFullMakeArrayArray s1PrefixDefs
  bodyMakeArrayHeaderEntry s1PrefixMakeTupleLoop s1PrefixMakeTupleSlot
  s1PrefixInvalidTraceDomain s1PrefixCompose s1PrefixOfVV
  exprSimAggregateSource exprSimHypsDefs exprSimSource vyperTypeSystem vyperStorageTrace

val _ = Parse.hide "base";

Theorem make_array_vv_sim_prefix_conditional:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty ann et n args es.
  make_array_packaging_ok /\
  (builtin_args_length_ok (MakeArray (SOME et) n) (LENGTH args) ==>
       body_exprs_full_ok cx args) /\
  (builtin_args_length_ok (MakeArray (SOME et) n) (LENGTH args) ==>
       body_exprs_prefix_ok cx args) /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Builtin ann (MakeArray (SOME et) n) args) es ==>
  expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin ann (MakeArray (SOME et) n) args) es
Proof
  rpt gen_tac >> strip_tac >>
  `expr_sim_inv cenv cx env es /\ compatible_bound n (LENGTH args)` by
    gvs[expr_body_pre_def,cj 9 well_typed_expr_def,well_typed_builtin_app_def] >>
  `builtin_args_length_ok (MakeArray (SOME et) n) (LENGTH args)` by
    simp[vyperContextTheory.builtin_args_length_ok_def] >>
  `body_exprs_full_ok cx args /\ body_exprs_prefix_ok cx args` by simp[] >>
  `!e ee. MEM e args /\ expr_sim_inv cenv cx env ee ==>
     expr_body_pre cenv cx env e ee` by
    (rpt strip_tac >> irule expr_body_pre_builtin_arg >>
     qpat_assum `expr_body_pre _ _ _ (Builtin _ _ _) _` (irule_at Any) >> simp[]) >>
  rewrite_tac[expr_vv_sim_prefix_def,expr_vv_sim_full_pre_def] >>
  rpt gen_tac >> strip_tac >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (irule gas_prefix_full_invalid_trace_domain >> simp[evaluate_storage_trace_frame]) >>
  drule_all make_array_header_loop_entry >>
  disch_then (qspecl_then [`shadow_ctx`,`PG`]
    (qx_choosel_then [`q`,`tv`,`header`,`off`,`base`,`cap`,`ps`,`sh`,`ssh`,`sj`,`Gj`,`tnj`]
      strip_assume_tac)) >>
  `make_tuple_buffer (DF,lo,d,ctx,func,cenv,cx,st0)
     (es,sa,s0,G0,tn0) (q,sa.cs_next_id,base,cap) sh es sj Gj tnj` by
    (pure_rewrite_tac[make_tuple_buffer_def] >> rpt conj_tac >>
     TRY (first_assum ACCEPT_TAC) >> simp[] >> rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ sj /\ _`
       drule >> simp[]) >>
  `make_tuple_saved_slots base ps off sj tnj` by simp[make_tuple_saved_slots_def] >>
  `!qe. SND (eval_expr cx (Builtin ann (MakeArray (SOME et) n) args) qe) =
        SND (eval_exprs cx args qe)` by
    (gen_tac >> Cases_on `eval_exprs cx args qe` >>
     drule_all aggregate_eval_make_array >> simp[]) >>
  drule_then (fn th => once_rewrite_tac[th]) gas_prefix_full_state_cong >>
  irule gas_prefix_full_zero_prefix_guarded >> simp[evaluate_storage_trace_frame] >>
  qexistsl_tac [`Gj`,`sj`,`tnj`] >> simp[] >>
  drule_at (Pat `make_tuple_buffer _ _ _ _ _ _ _ _`) make_tuple_loop_prefix >>
  disch_then (drule_at (Pat `compile_make_tuple _ (gas_shadow_env _ _) _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_make_tuple _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `OPT_MMAP _ _ = _`)) >>
  disch_then (drule_at (Pat `make_tuple_saved_slots _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `body_const_cells_agree _ _ _ _`)) >>
  disch_then (drule_at (Pat `gas_shadow_function _ _`)) >>
  disch_then irule >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  simp[] >> rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ s0 /\ _`
    drule >> simp[]
QED
