(* Complete memory endpoints and composite augmented-place consumers. *)
Theory augAssignPlaceCompositeMemory
Ancestors
  augAssignPlaceCompileMemory augAssignPlaceLoadContinuation
  augAssignPlaceSourceMemory augAssignPlaceRhsContinuation
  augAssignPlaceMemoryContinuation bodyMemoryDefs exprSimMemDefs
  bodyAugAssignOther targetPlaceSimMem stmtSimDefs stmtSimAugAssignPlace
  augAssignPlaceMemoryTarget augAssignPlaceTargetReadiness
  augAssignPlaceEndpointMemory augAssignPlaceStorageContinuation
  augAssignPlaceLoadedStorage augAssignPlaceEndpointStorage
  vyperInterpreter exprSimDefs bodySim exprSimHyps

Theorem aug_place_memory_post[local]:
  res = INL () /\
  stmt_post ctx func cx lctx cenv cenv sa sb s0 res ee t /\
  return_buf_frame d cenv sa s0 /\
  sa.cs_next_var <= sb.cs_next_var /\ alloca_history func t /\
  s0.vs_alloca_next <= t.vs_alloca_next ==>
  ?cenv'. stmt_lands lctx sb res t /\ ~t.vs_halted /\
    (res = INL () ==> ~block_is_terminated sb /\ cenv' = cenv) /\
    cenv_top_ext cenv cenv' ee.scopes /\
    stmt_state_rel ctx func cenv' cx ee t /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
      lookup_var x t = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
      FLOOKUP t.vs_allocas aid = SOME b) /\
    return_buf_frame d cenv' sb t /\ alloca_history func t /\
    s0.vs_alloca_next <= t.vs_alloca_next
Proof
  strip_tac >> qexists_tac `cenv` >>
  gvs[stmtSimDefsTheory.stmt_post_def] >>
  irule return_buf_frame_frame >>
  qexistsl_tac [`cenv`, `s0`, `sa`] >> simp[]
QED

Theorem compile_augassign_place_memory_mem_case:
  target_root bt = NameTarget id /\
  ((?b fld. bt = AttributeTarget b fld) \/ (?b k. bt = SubscriptTarget b k)) /\
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (AugAssign ty bt bop e) /\
  type_stmt env ret_ty (AugAssign ty bt bop e) = SOME env' /\
  target_sim_mem ctx func cenv cx env bt es /\
  target_indices_pre cenv cx env bt /\
  (!s p s1 s2 cur s3 s4 ptv s5.
    eval_target_place cx bt s = (INL p,s1) /\
    read_place cx p s2 = (INL cur,s3) /\
    place_type_value cx p s4 = (INL ptv,s5) ==> body_expr_mem_ok cx e) /\
  expr_body_pre cenv cx env e es ==>
  stmt_frag_mem d ctx func cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (AugAssign ty bt bop e))
    (eval_stmt cx (AugAssign ty bt bop e)) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  drule_all aug_place_compilation_mem >> strip_tac >> gnvs[] >>
  drule aug_place_typing >> strip_tac >>
  `gas_admissible (eval_target_place cx bt) target_place_res_ok es` by
    (irule aug_place_target_admissible_mem >> goal_assum (drule_at Any)) >>
  simp[Once evaluate_def] >>
  irule aug_place_target_mem_continuation >>
  simp[] >> (conj_tac
  >- (rpt gen_tac >> strip_tac >> Cases_on `res`
      >- fs[expr_exit_def] >>
      rename1 `expr_exit (INR ex) rr` >> qexists_tac `ex` >>
      simp[stmt_exit_def] >>
      metis_tac[stmtSimPropsTheory.expr_exit_INR_type])) >>
  qexistsl_tac [`cenv`, `env`, `r`, `sa`, `s0'`, `ty`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!tail. eval_target_place _ _ _ = _`
    (qspec_then `mid.gas_obs` assume_tac) >> gnvs[] >>
  `?path. p = MemoryPlace id path` by
    (irule stmtSimAugAssignPlaceTheory.aug_place_name_root_memory >> metis_tac[]) >>
  gnvs[] >>
  `~t.vs_halted` by
    metis_tac[stmtSimAugAssignPlaceMemoryTheory.aug_place_marked_path_not_halted] >>
  `FST (SND r) = SOME LocMemory` by
    fs[loweringPostsTheory.target_post_def, loweringPostsTheory.place_ptr_rel_def] >>
  gnvs[] >>
  simp[SF ETA_ss] >>
  irule (SRULE [vyperStateTheory.bind_assoc, SF ETA_ss] aug_place_memory_endpoint) >>
  simp[] >> goal_assum (drule_at (Pat `target_post`)) >>
  goal_assum (drule_at (Pat `supported_stmt`)) >>
  goal_assum (drule_at (Pat `type_stmt`)) >>
  goal_assum (drule_at (Pat `compile_binop`)) >>
  goal_assum (drule_at (Pat `lower_value`)) >> simp[] >>
  qexistsl_tac [`lctx`, `marks`] >> simp[] >>
  (conj_tac >- metis_tac[]) >>
  rpt strip_tac >> rule_assum_tac BETA_RULE >> RULE_L_ASSUM_TAC CONJUNCTS >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (fs[exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
  drule_all (SRULE [] (Q.INST [`res` |-> `INL ()`] aug_place_memory_post)) >>
  simp[]
QED

Theorem compile_augassign_place_storage_mem_case:
  (!id. target_root bt <> NameTarget id) /\ supported_target_pure tops bt /\
  ((?b fld. bt = AttributeTarget b fld) \/ (?b k. bt = SubscriptTarget b k)) /\
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (AugAssign ty bt bop e) /\
  type_stmt env ret_ty (AugAssign ty bt bop e) = SOME env' /\
  target_sim_mem ctx func cenv cx env bt es /\
  target_indices_pre cenv cx env bt /\
  (!s p s1 s2 cur s3 s4 ptv s5.
    eval_target_place cx bt s = (INL p,s1) /\
    read_place cx p s2 = (INL cur,s3) /\
    place_type_value cx p s4 = (INL ptv,s5) ==> body_expr_mem_ok cx e) /\
  expr_body_pre cenv cx env e es ==>
  stmt_frag_mem d ctx func cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (AugAssign ty bt bop e))
    (eval_stmt cx (AugAssign ty bt bop e)) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `EVERY (supported_pure_expr tops) (target_indices bt)` by
    (qpat_x_assum `supported_target_pure tops bt` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt` >>
     fs[supportedTargetsTheory.supported_target_pure_def, targetPlaceLiveTheory.target_indices_def] >>
     first_x_assum irule >> simp[]) >>
  `?pt. supported_target_info tops bindings bt = SOME pt` by
    metis_tac[bodyAugPlaceTargetTheory.aug_place_supported_stmt_target_info] >>
  simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  drule_all aug_place_compilation_mem >> strip_tac >> gnvs[] >>
  drule aug_place_typing >> strip_tac >>
  `gas_admissible (eval_target_place cx bt) target_place_res_ok es` by
    (irule aug_place_target_admissible_mem >> goal_assum (drule_at Any)) >>
  simp[Once evaluate_def] >>
  irule aug_place_target_mem_continuation >>
  simp[] >> (conj_tac
  >- (rpt gen_tac >> strip_tac >> Cases_on `res`
      >- fs[expr_exit_def] >>
      rename1 `expr_exit (INR ex) rr` >> qexists_tac `ex` >>
      simp[stmt_exit_def] >>
      metis_tac[stmtSimPropsTheory.expr_exit_INR_type])) >>
  qexistsl_tac [`cenv`, `env`, `r`, `sa`, `s0'`, `ty`] >> simp[] >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!tail. eval_target_place _ _ _ = _`
    (qspec_then `mid.gas_obs` assume_tac) >> gnvs[] >>
  `?tr slot tv. p = StoragePlace tr slot tv` by
    metis_tac[stmtSimAugAssignPlaceStorageTheory.aug_place_supported_storage_kind] >>
  gnvs[] >>
  `~t.vs_halted` by
    metis_tac[stmtSimAugAssignPlaceMemoryTheory.aug_place_marked_path_not_halted] >>
  `FST (SND r) = SOME (slot_loc tr)` by
    fs[loweringPostsTheory.target_post_def, loweringPostsTheory.place_ptr_rel_def] >>
  gnvs[] >> simp[SF ETA_ss] >>
  irule (SRULE [vyperStateTheory.bind_assoc, SF ETA_ss] aug_place_storage_endpoint) >>
  simp[] >> goal_assum (drule_at (Pat `target_post`)) >>
  goal_assum (drule_at (Pat `type_stmt`)) >>
  goal_assum (drule_at (Pat `compile_binop`)) >>
  goal_assum (drule_at (Pat `lower_value`)) >> simp[] >>
  qexistsl_tac [`lctx`, `marks`, `sb`, `tops`] >>
  Cases_on `tr` >> gvs[loweringPostsTheory.slot_loc_def] >>
  (conj_tac >- metis_tac[]) >>
  rpt strip_tac >> rule_assum_tac BETA_RULE >> RULE_L_ASSUM_TAC CONJUNCTS >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (fs[exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
  drule_all (SRULE [] (Q.INST [`res` |-> `INL ()`] aug_place_memory_post)) >> simp[]
QED
