(* Enter a local Assign target at the machine state reached by the RHS. *)
Theory bodyAssignLocalReachedTargetEntryMods
Ancestors
  bodyQualifiedPlaceTargetEntryMods bodyQualifiedPlaceRhsPostMods
  bodyAssignQualifiedStageJoinMods bodyWritePlaceRunMods bodyWriteTargetStageMods
  bodyPlaceWriteSourceMods bodyExprPreFacts targetPlaceSim allocLimits
Libs monadsyntax

Theorem assign_local_reached_target_entry_mods:
  target_root bt = NameTarget id /\
  contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  supported_stmt tops bindings (Assign (BaseTarget bt) e) /\
  type_place_target env bt = SOME (Type dty) /\
  stmt_exprs_ok cenv (Assign (BaseTarget bt) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget bt) e)) /\
  EVERY (source_body_call_supported cx) (int_calls_stmt (Assign (BaseTarget bt) e)) /\
  ~supported_stmt_expr_exists (unallocated_bare_global_root cenv env)
    (Assign (BaseTarget bt) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
       (Assign (BaseTarget bt) e) ==> EXISTS (occurs_abi_decode_target target o SND) mods) /\
  body_base_target_full_ok_mods mods exps cx bt /\
  qualified_assign_code_mods cenv bt e sa sb shadow_sa shadow_sb saved sr st
    shadow_sr shadow_st dst /\
  qualified_assign_rhs_reached_mods cx st0 e es s0
    (qualified_place_rhs_post_mods (DF,lo,d,ctx,func) mods cenv cx env bt e dty
       es sa shadow_sa sr shadow_sr saved s0 G0 tn0) ms v mid Gu tu u /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_inst_ids_distinct func /\ (!H. dead_lo_ok_mods H (DF H) lo cenv cx) ==>
  write_place_sim_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx env bt mid /\
  write_target_entry_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx bt mid st0 sr st shadow_sr shadow_st dst u Gu tu
Proof
  strip_tac >> drule_then strip_assume_tac qualified_place_rhs_entry_view_mods >>
  drule_all_then strip_assume_tac qualified_place_code_intervals_mods >>
  reverse conj_tac
  >- (qpat_assum `qualified_assign_code_mods _ _ _ _ _ _ _ _ _ _ _ _ _`
        (strip_assume_tac o REWRITE_RULE [qualified_assign_code_mods_def]) >>
      simp[write_target_entry_mods_def] >> conj_tac
      >- (rpt strip_tac >> qpat_assum `!fn inst t. frag_reachable _ _ _ _ _ _ ==> _`
            (drule_then ACCEPT_TAC)) >>
      rpt gen_tac >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
        (drule_then (strip_assume_tac o BETA_RULE)) >> simp[]) >>
  `alloc_limits_target cenv bt` by
    (qpat_x_assum `stmt_exprs_ok _ _` mp_tac >>
     simp[stmt_exprs_ok_flat,alloc_limits_stmt_def,alloc_limits_assignment_def] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `!i se. MEM i (target_indices bt) /\ expr_sim_inv_mods mods cenv cx env se ==>
     expr_body_pre_mods mods cenv cx env i se` by
    (mp_tac (Q.INST [`s` |-> `Assign (BaseTarget bt) e`] (SPEC_ALL place_write_index_pre_mods)) >>
     simp[]) >>
  `~immutable_root cx bt` by simp[immutable_root_def] >>
  irule write_target_place_run_mods >> rpt (first_assum (irule_at Any)) >> simp[]
QED
