(* The word store executes after the actual saved operand has been unwrapped. *)
Theory bodyQualifiedAssignImmWordLandingMods
Ancestors
  bodyQualifiedAssignOperandCutMods bodyQualifiedPlaceImmScalarMods
  bodyAssignQualifiedStageJoinMods
  bodyPlaceWriteTailAdmissibleMods bodyImmutableAugAssignStore
  bodyAugGuardedPrefixMods bodyInvCodeProps vyperStorageTrace compileEnv
  gasOutcomeFullPostMods loweringPosts gasContext stmtSimDefs

(* The normal post of stmt_frag_full_mods at an unchanged compiler environment. *)
val normal_post =
  ``\(H : (bool # 256 word # type_value) list # num list) res ef Gf tf q. ?ce.
      stmt_lands lctx sb res q /\ ~q.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ ce = cenv) /\
      cenv_top_ext cenv ce ef.scopes /\
      stmt_state_rel H ctx func ce cx ef q /\ immutable_frame_mods func ce cx ef q /\
      storage_well_formed_on cx ef (FST H) /\
      return_buf_frame d ce sb q /\ alloca_history func q /\ return_buf_sep d ce ef q /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp q) /\ s0.vs_alloca_next <= q.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d ce cx ef Gf tf q /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==> lookup_var x q = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP q.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==>
         FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tf (Var x) = op_taint tn0 (Var x)) /\
      alloca_frame cenv es sa s0 ce ef q /\
      (!aid a n i. FLOOKUP s0.vs_allocas aid = SOME (a,n) /\ aid < sa.cs_next_id /\
         (!name b cap. local_region cenv es.scopes s0 name b cap ==> a+n <= b \/ b+cap <= a) /\
         a <= i /\ i < a+n /\ i IN tf.t_mem ==> i IN tn0.t_mem)``;

Theorem qualified_assign_imm_word_landing_mods:
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env ee /\
  type_widens_to env.type_defs (expr_type e) dty /\
  gas_admissible (eval_stmt cx (Assign (BaseTarget bt) e)) (stmt_res_ok lctx) es /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  qualified_assign_rhs_reached_mods cx st0 e es s0 RhsQ ms v mid Gu tu u /\
  qualified_assign_target_reached_mods (DF,lo,d,ctx,func) cenv cx st0 bt dty
    mid sr st dst u Gu tu marks p ee Gz tz z /\
  qualified_assign_route_mods AssignImmWord (owner,id) p (SOME vv) dty dst /\
  qualified_assign_code_mods cenv bt e sa sb shadow_sa shadow_sb (SOME vv)
    sr st shadow_sr shadow_st dst /\
  qualified_assign_operand_cut_mods
    (DF,lo,d,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) cenv cx st0
    (bt,e,dty) (vv,op,p,dst,v) (sa,st,su,sb) (es,s0,G0,tn0) (ee,z,Gz,tz) (s,G,tn) ==>
  gas_outcome_full_mods (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cenv.ce_modules cx st0 (write_place cx p v) (ee,z,Gz,tz) ^normal_post
    (assign_qualified_exit_mods ctx cx RetQ)
Proof
  simp[qualified_assign_route_mods_def] >> strip_tac >> gvs[] >>
  drule_all_then assume_tac compileEnvTheory.type_widens_to_word >>
  `is_word_type (expr_type e)` by simp[] >>
  qpat_x_assum `qualified_assign_operand_cut_mods _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_operand_cut_mods_def]) >>
  qpat_x_assum `qualified_assign_code_mods _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_code_mods_def]) >>
  qpat_x_assum `if is_word_type (expr_type e) then _ else _` mp_tac >> simp[] >> strip_tac >>
  qpat_x_assum `write_target_location_mods _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[bodyWriteTargetStageModsTheory.write_target_location_mods_def] >> strip_tac >>
  `compile_assign_value cenv (FST dst) LocCode op T (vv_location vv) dty
     (lowered_value_type cenv e) (type_memory_bytes cenv dty) su = ((),sb)` by
    (qpat_x_assum `assign_place_store_code_mods cenv e (SOME vv) dst st = _` mp_tac >>
     qpat_assum `dst = (FST dst,_,_)` (fn th => ONCE_REWRITE_TAC [th]) >>
     simp[qualified_assign_store_code_mods, comp_bind_def]) >>
  `?tops. ALOOKUP cenv.ce_modules owner = SOME tops` by
    (drule_then assume_tac contract_inv_cenv_modules >>
     drule_then (strip_assume_tac o REWRITE_RULE [bodyInvSplitTheory.immutable_section_layout_mods_def])
       bodyInvSplitTheory.contract_inv_immutable_section_layout >>
     `?size. immutable_region_mods mods owner id off size` by metis_tac[] >>
     pop_assum (strip_assume_tac o REWRITE_RULE [bodyInvSplitTheory.immutable_region_mods_def]) >> simp[]) >>
  qpat_x_assum `qualified_assign_rhs_reached_mods _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_rhs_reached_mods_def]) >>
  qpat_x_assum `qualified_assign_target_reached_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [qualified_assign_target_reached_mods_def]) >>
  drule_all_then assume_tac assign_reached_write_admissible_mods >>
  `?ef. write_place cx (ImmutablePlace owner id path) v ee = (INL (),ef)` by
    (Cases_on `write_place cx (ImmutablePlace owner id path) v ee` >>
     rename1 `write_place _ _ _ _ = (wr,ef)` >>
     `stmt_res_ok lctx wr` by
       (qpat_assum `gas_admissible (write_place _ _ _) _ _` (mp_then Any mp_tac gas_admissible_result) >>
        disch_then irule >> qexistsl [`ef`,`ee.gas_obs`] >> simp[]) >>
     drule_all_then strip_assume_tac immutable_augassign_path_write_source >> simp[]) >>
  fs[wb_frame_def, bodyFullTargetDefsTheory.target_ptr_ok_def] >>
  irule augassign_zero_prefix_guarded_mods >>
  simp[storage_trace_frame_write_place] >>
  qexistsl [`G`,`s`,`tn`] >> simp[] >>
  irule gas_outcome_full_mods_post_source >>
  irule_at Any (Q.INST [`lctx` |-> `lctx`, `R` |-> `assign_qualified_exit_mods ctx cx RetQ`]
    qualified_place_imm_word_mods) >>
  qpat_assum `contract_inv _ _ _ _ _` (irule_at Any) >>
  qpat_assum `expr_sim_inv_mods _ _ _ _ _` (irule_at Any) >>
  qpat_assum `write_place _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `return_buf_frame d cenv su s` (irule_at Any) >>
  qpat_assum `alloca_frame _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `ghost_kept_at _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `ALOOKUP cenv.ce_modules owner = SOME _` (irule_at Any) >>
  qpat_assum `ALOOKUP ee.immutables _ = SOME _` (irule_at Any) >>
  qpat_assum `FLOOKUP (get_source_immutables _ _) _ = SOME _` (irule_at Any) >>
  qpat_assum `FLOOKUP cenv.ce_module_vars _ = SOME _` (irule_at Any) >>
  qpat_assum `mem_path_offset _ _ = SOME _` (irule_at Any) >>
  qexistsl [`lctx`,`RetQ`] >>
  `sa.cs_next_var <= su.cs_next_var` by decide_tac >>
  simp[AC arithmeticTheory.ADD_COMM arithmeticTheory.ADD_ASSOC] >>
  conj_tac
  >- (rpt strip_tac >> qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> stmt_state_rel _ _ _ _ _ ee s /\ _`
        (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >> qexists `cenv` >> simp[]
QED
