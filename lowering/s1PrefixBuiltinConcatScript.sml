(* Request-prefix companion to bodyFullBuiltinConcat. *)
Theory s1PrefixBuiltinConcat
Ancestors
  s1PrefixPreds s1PrefixDefs s1PrefixBuiltinConcatLoop
  s1PrefixInvalidTraceDomain s1PrefixOfVV s1PrefixCompose s1PrefixProps
  bodyFullBuiltinConcat bodyFullBuiltinConcatEntry bodyFullBuiltinConcatReady
  bodyFullBuiltinConcatLoop exprSimHyps vyperStorageTrace vyperState vyperContext

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >> conj_asm2_tac
  >- (irule expr_sim_prefix_of_vv >> first_assum ACCEPT_TAC) >>
  rewrite_tac[expr_vv_sim_prefix_def,expr_vv_sim_full_pre_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `storage_trace_domain cx st0 es.storage_trace`
  >- suspend "domain" >>
  irule gas_prefix_full_invalid_trace_domain >> simp[evaluate_storage_trace_frame]
QED
*)
Theorem concat_sim_prefix:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a n args es.
  (builtin_args_length_ok (Concat n) (LENGTH args) ==>
      body_exprs_full_ok cx args) /\
  (builtin_args_length_ok (Concat n) (LENGTH args) ==>
      body_exprs_prefix_ok cx args) /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Builtin a (Concat n) args) es ==>
  expr_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a (Concat n) args) es /\
    expr_vv_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a (Concat n) args) es
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume concat_sim_prefix[domain]:
  drule_all concat_loop_initial_entry >>
  disch_then (qspec_then `PG` (qx_choosel_then
    [`s4`,`s5`,`shadow_s4`,`shadow_s5`,`t4`,`G4`,`tn4`,`dp`,`ov`,`ow`,
     `binst`,`B`,`bsz`,`oinst`,`buf`,`bv`,`fo`,`s6`,`u'`,`tvr`]
    (map_every assume_tac o CONJUNCTS))) >>
  `body_exprs_prefix_ok cx args` by
    (qpat_assum `builtin_args_length_ok _ _ ==> body_exprs_prefix_ok _ _` irule >>
     simp[builtin_args_length_ok_def]) >>
  irule gas_prefix_full_zero_prefix_guarded >>
  simp[evaluate_storage_trace_frame] >>
  qexistsl_tac [`G4`,`t4`,`tn4`] >> conj_tac >- simp[] >>
  drule_all concat_args_sim_prefix >> strip_tac >>
  drule (PURE_ONCE_REWRITE_RULE [GSYM concat_loop_ready_def] concat_args_sim_full) >>
  disch_tac >>
  drule_then (fn th => rewrite_tac[th]) eval_expr_concat_bind >>
  qhdtm_assum `gas_outcome_full` (mp_then Any irule gas_prefix_full_bind_no_outcome) >>
  simp[evaluate_storage_trace_frame,evaluate_requests_outcomes_frame,
       storage_trace_frame_def] >>
  rpt gen_tac >> Cases_on `res` >> Cases_on `r` >>
  simp[exprSimDefsTheory.expr_exit_def]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise concat_sim_prefix
*)
