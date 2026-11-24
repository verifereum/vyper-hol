(* Empty local assignments skip RHS code and clear the destination length word. *)
Theory bodyAssignNameEmptyRouteMods
Ancestors
  bodyAssignNameLinkedSetup bodyAssignLocalInstallMods bodyLocalCopyWritesMods
  bodyFullAssignLocalEmpty bodyFullMemoryFrames gasOutcomeFullPostMods
  stmtSimAssignMem stmtSimDeclMem memoryLocalRhsProps tupleTargetStoreProps
  nameLoweringProps exprSimWordArgs vyperTypeEnv
  exprBodyPreProps exprBodyPreTypingProps vyperTypeEvalCaseProofs bodyFullPostsMods
  bodyInvSplit exprLoweringProps valueEncodingProps bodyFullShadowBodyInv
  vyperStorageFootprint vyperState exprSimHypsDefs vyperTypeInvariants vyperLookup
  stateRelProj allocaFootprint loweringStateRelDefs ptrDiscipline venomState
  typedMemoryCopy loweringPosts loweringShapeRules stmtLowering words
  vyperTyping pred_set stmtSimDefs bodyFullShared bodyPtrDefs reasonCopySourcePtr
  bodyPtrPrecompileBuiltinsArithmeticValue wordArgsPtr
Libs
  monadsyntax

Theorem empty_name_read_mods[local]:
  expr_body_pre_mods mods cenv cx env e es /\
  type_widens_to (get_tenv cx) (expr_type e) ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  has_length_word (expr_type e) /\ is_empty_value_expr e ==>
  !tail. vyperState$bind (eval_expr cx e) (read_result cx) (es with gas_obs := tail) =
    (INL (default_value tv),es with gas_obs := tail)
Proof
  strip_tac >> gen_tac >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then (mp_tac o MATCH_MP expr_sim_inv_mods_env) expr_body_pre_mods_inv >>
  strip_tac >> drule_then assume_tac env_consistent_type_defs_get_tenv >>
  irule (CONV_RULE (DEPTH_CONV ETA_CONV) memory_rhs_empty_read_destination) >>
  simp[] >> qexistsl_tac [`env`,`ty`] >> simp[]
QED

Theorem empty_name_local_bound_mods[local]:
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env es /\
  immutable_frame_mods func cenv cx es s /\ local_region cenv es.scopes s id b n /\
  0 < n /\ dead_lo_ok_mods (H : (bool # 256 word # type_value) list # num list)
    (DF H) lo cenv cx ==> lo <= b
Proof
  strip_tac >> irule (INST_TYPE [alpha |-> ``:256``] body_full_local_region_lower_bound_mods) >>
  goal_assum (drule_at (Pat `contract_inv _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `expr_sim_inv_mods _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `dead_lo_ok_mods _ _ _ _ _`)) >> simp[] >>
  fs[immutable_frame_mods_def, immutable_decl_sep_mods_def,
     immutable_alloca_sep_mods_def, immutable_alloca_sep_def] >> metis_tac[]
QED

Theorem empty_name_robust_memory[local]:
  has_length_word ty /\ evaluate_type tenv ty = SOME tv /\
  t = (mstore a 0w s with vs_inst_idx := pc) /\
  (!i. a <= i /\ i < a + 32 ==> i NOTIN tf.t_mem) ==>
  32 <= type_memory_size tv /\
  !mem. mem_agree_outside tf.t_mem t.vs_memory mem ==>
    val_in_memory tv (default_value tv) a mem
Proof
  strip_tac >>
  `mem_word_at a t.vs_memory = 0w` by simp[mstore_mem_word_at_same] >>
  drule_all_then strip_assume_tac memory_length_word_layout >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >>
  drule_all clean_word_mem_agree >> disch_then (assume_tac o SYM) >>
  `mem_word_at a mem = 0w` by metis_tac[] >>
  drule_all_then strip_assume_tac memory_length_word_layout
QED

Theorem empty_name_gas_obs_frames[local]:
  (immutable_frame_mods func cenv cx (es with gas_obs := gs) s <=>
   immutable_frame_mods func cenv cx es s) /\
  (ghost_inv_at_mods D lo d cenv cx (es with gas_obs := gs) G tn s <=>
   ghost_inv_at_mods D lo d cenv cx es G tn s) /\
  (storage_well_formed_on cx (es with gas_obs := gs) A <=>
   storage_well_formed_on cx es A)
Proof
  rpt conj_tac
  >- (simp[immutable_frame_mods_def, immutables_rel_mods_def,
       immutable_alloca_sep_mods_def, immutable_alloca_sep_def,
       loweringStateRelDefsTheory.immutables_rel_def] >> metis_tac[])
  >- simp[ghost_inv_at_mods_def]
  >> irule storage_well_formed_on_backends >> simp[]
QED

Theorem assign_name_empty_route_mods:
  linked_assign_name_context_mods mods exps cx id e
    (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    src tops bindings cenv env env' ret_ty RetQ es /\
  body_expr_full_ok_mods mods exps cx e /\
  FLOOKUP env.var_types id = SOME ty /\ ~is_word_type ty /\
  0 < type_memory_bytes cenv ty /\
  has_length_word (expr_type e) /\ is_empty_value_expr e ==>
  stmt_frag_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (Assign (BaseTarget (NameTarget id)) e))
    (stmt_env (gas_shadow_env T cenv) lctx ret_ty
      (gas_shadow_stmt (Assign (BaseTarget (NameTarget id)) e)))
    (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
Proof
  strip_tac >> drule_all_then strip_assume_tac linked_assign_name_setup_mods >> gvs[] >>
  qhdtm_x_assum `linked_assign_name_context_mods`
    (strip_assume_tac o REWRITE_RULE [linked_assign_name_context_mods_def]) >>
  `has_length_word ty` by metis_tac[type_widens_to_has_length_word] >>
  drule_all_then assume_tac empty_name_read_mods >>
  rewrite_tac[stmt_frag_full_mods_def] >> rpt gen_tac >> strip_tac >>
  drule_all_then strip_assume_tac assign_local_empty_code_parts >>
  qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC >>
  drule_all_then strip_assume_tac assign_local_identity_rhs_all_tails >>
  reverse (Cases_on `storage_trace_domain cx st0 es.storage_trace`)
  >- (irule gas_outcome_full_mods_bad_nil >> simp[]) >>
  suspend "run"
QED

Resume assign_name_empty_route_mods[run]:
  qabbrev_tac `H0 = storage_trace_horizon es.storage_trace` >>
  `valid_horizon cx st0 H0 es.storage_trace` by
    fs[Abbr `H0`, storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  drule_then assume_tac find_containing_scope_lookup >>
  `state_well_typed es` by fs[expr_sim_inv_mods_def] >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  `entry.type = tv /\ value_has_type tv entry.value` by
    (drule_all env_consistent_lookup_var_type >> simp[]) >>
  `well_formed_type_value tv` by
    (fs[state_well_typed_def] >>
     drule_all_then strip_assume_tac scope_well_typed_lookup_scopes >> gvs[]) >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  drule_all_then strip_assume_tac local_ptrs_rel_value >>
  `lookup_var p s0 = SOME w` by fs[eval_operand_def] >>
  `local_region cenv es.scopes s0 id (w2n w) cap` by simp[local_region_def] >>
  `type_memory_size tv <= cap` by
    (qpat_assum `entry.type = tv` (once_rewrite_tac o single o SYM) >>
     first_assum ACCEPT_TAC) >>
  `0 < cap` by decide_tac >>
  `lo <= w2n w` by
    (irule empty_name_local_bound_mods >>
     goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `immutable_frame_mods _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `contract_inv _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `expr_sim_inv_mods _ _ _ _ _`)) >>
     simp[] >> qexistsl_tac [`DF`,`H0`] >> simp[]) >>
  `ptr_covers G0 tn0 p s0 cap /\ allocas_from lo s0 /\ lo <= s0.vs_alloca_next` by
    (qpat_assum `ghost_inv_at_mods (DF H0) _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [ghost_inv_at_mods_def]) >>
     simp[] >> first_assum (drule_all_then strip_assume_tac) >> simp[]) >>
  `32 <= type_memory_size tv` by
    (irule (cj 3 memory_length_word_layout) >>
     conj_tac >- (qexistsl_tac [`(mstore (w2n w) 0w s0).vs_memory`,`w2n w`] >>
                  simp[mstore_mem_word_at_same]) >>
     qexistsl_tac [`get_tenv cx`,`ty`] >> simp[]) >>
  `32 <= cap` by decide_tac >>
  `ptr_covers G0 tn0 p s0 32` by metis_tac[ptr_covers_mono] >>
  `op_taint tn0 (Var p) = {}` by fs[ptr_covers_def] >>
  `w2n w + 32 <= s0.vs_alloca_next` by decide_tac >>
  `compile_store_at_loc cenv.ce_imm_alloca (Var p) (Lit 0w) (SOME LocMemory)
      sa = ((),sb)` by simp[compile_store_at_loc_def] >>
  drule_at (Pat `compile_store_at_loc _ _ _ _ _ = _`) body_assign_empty_scalar_suffix >>
  disch_then (qspecl_then [`w`,`tn0`,`s0`,`lo`,`func`,
    `gas_explicit_sites ctx shadow_ctx`,`ctx`,`PG`,`G0`] mp_tac) >>
  (impl_tac >- simp[]) >> disch_then (strip_assume_tac o SRULE []) >>
  suspend "post"
QED

Resume assign_name_empty_route_mods[post]:
  qabbrev_tac `ee = es with scopes := pre ++
    (env'' |+ (id,entry with <|value := default_value tv; popped := []|>)) :: rest` >>
  `ee.storage_trace = es.storage_trace` by simp[Abbr `ee`] >>
  irule gas_outcome_full_mods_pure >> simp[] >>
  qabbrev_tac `u = mstore (w2n w) 0w s0 with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  qexistsl_tac [`G0`,`ee`,`INL ()`,`u`,`tf`] >>
  conj_tac >- (gen_tac >> simp[Abbr `ee`]) >>
  simp[] >> gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  suspend "install"
QED

Resume assign_name_empty_route_mods[install]:
  `write_place cx (MemoryPlace id []) (default_value tv) es = (INL (),ee)` by
    (simp[Abbr `ee`] >> irule tuple_target_local_write_safe >> simp[]) >>
  `mem_path_offset entry.type [] = SOME (0,tv)` by simp[mem_path_offset_def] >>
  `value_has_type tv (default_value tv)` by simp[default_value_well_typed] >>
  `u = mstore (w2n w) 0w s0 with vs_inst_idx := LENGTH sb.cs_current_insts` by
    simp[Abbr `u`] >>
  `!mem. mem_agree_outside tf.t_mem u.vs_memory mem ==>
         val_in_memory tv (default_value tv) (w2n w) mem` by
    drule_all_then (ACCEPT_TAC o CONJUNCT2) empty_name_robust_memory >>
  `typed_copy_state_frame sa (w2n w) 32 s0 u` by simp[Abbr `u`, typed_copy_mstore_state_frame] >>
  `sa.cs_next_var <= sb.cs_next_var /\ sb.cs_current_bb = sa.cs_current_bb` by
    (qpat_assum `emit_void _ _ _ = _`
       (mp_tac o REWRITE_RULE [emit_void_eq, pairTheory.PAIR_EQ]) >>
     disch_then (SUBST1_TAC o SYM) >> simp[]) >>
  `~block_is_terminated sb` by
    (irule emit_void_nonterminator_open >> goal_assum (drule_at (Pat `emit_void _ _ _ = _`)) >>
     simp[venomInstTheory.is_terminator_def]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x` by
    (qhdtm_assum `ret_pc_ok` (mp_tac o REWRITE_RULE [ret_pc_ok_def]) >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G0 tn0` by simp[ghost_kept_at_refl] >>
  `alloca_frame cenv es sa s0 cenv es s0` by simp[alloca_frame_same] >>
  suspend "installation_rule"
QED

Resume assign_name_empty_route_mods[installation_rule]:
  qpat_assum `write_place _ _ _ _ = _`
    (mp_then (Pat `write_place _ _ _ _ = _`) mp_tac
      (SRULE [] (Q.INST [`sm` |-> `sa`, `k` |-> `0`, `bytes` |-> `32`]
         (SPEC_ALL (INST_TYPE [alpha |-> ``:256``] assign_local_install_post_mods))))) >>
  disch_then (drule_at (Pat `typed_copy_state_frame _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME (PtrVar _ _)`)) >>
  disch_then (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `mem_path_offset _ _ = _`)) >>
  disch_then (fn th => qpat_assum `stmt_state_rel H ctx func cenv cx es s0`
    (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) mp_tac th)) >>
  disch_then (fn th => qpat_assum `ghost_inv_at_mods (DF H) _ _ _ _ _ _ _ _`
    (mp_then (Pat `ghost_inv_at_mods _ _ _ _ _ _ _ _ _`) mp_tac th)) >>
  disch_then (mp_tac o Q.INST [`tf` |-> `tf`, `sb` |-> `sb`,
                             `lctx` |-> `lctx`, `Gf` |-> `G0`] o SPEC_ALL) >>
  impl_tac >- suspend "install_premises" >>
  suspend "install_result"
QED

Resume assign_name_empty_route_mods[install_premises]:
  conj_tac >-
    (strip_tac >> irule local_copy_immutable_frame_mods >>
     goal_assum (drule_at (Pat `local_region _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `typed_copy_state_frame _ _ _ _ _`)) >> simp[]) >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    (SIMP_TAC (srw_ss()) [] >> NO_TAC),
    (qpat_assum `u = _` (once_rewrite_tac o single) >> simp[mstore_def] >> NO_TAC),
    (rpt strip_tac >> qpat_assum `!x. not_fresh_at sa x ==> lookup_var x u = _ /\ _`
      drule >> simp[] >> NO_TAC),
    (qpat_assum `entry.type = tv` (once_rewrite_tac o single) >> first_assum ACCEPT_TAC)]
QED

Resume assign_name_empty_route_mods[install_result]:
  strip_tac >>
  pure_rewrite_tac[empty_name_gas_obs_frames, return_buf_sep_gas_obs] >>
  rpt conj_tac >> FIRST [first_assum ACCEPT_TAC,
    (qpat_assum `u = _` (once_rewrite_tac o single) >>
     simp[mstore_def, allocas_below_fmp_def]) ]
QED

Finalise assign_name_empty_route_mods
