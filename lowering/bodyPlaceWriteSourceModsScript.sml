(* Source resources for the indices and the reached cut of a linked place write. *)
Theory bodyPlaceWriteSourceMods
Ancestors
  bodyFullPredsMods bodyWriteSubscriptSourceMods tuplePlaceSourceHead
  bodyExprPreFacts bodyInvCodeProps bodyInvMetadataProps
  entryStatementTargetSupport targetPlaceSimCasesBase supportedStmtTraverse
  supportedExprTraverse
  vyperAST vyperTypeEnv vyperTypeCallGraph vyperTypeCallStackSoundness
  allocLimits allocLimitsProps supportedExprs supportedStmts bodySim option list

Theorem place_write_index_source_facts[local]:
  !bt i. MEM i (target_indices bt) /\
    IS_SOME (type_place_target env bt) /\ alloc_limits_target cenv bt /\
    call_evaluation_safe cx (int_calls_target bt) /\
    EVERY (source_body_call_supported cx) (int_calls_target bt) ==>
    well_typed_expr env i /\ alloc_limits_expr cenv i /\
    call_evaluation_safe cx (int_calls_expr i) /\
    EVERY (source_body_call_supported cx) (int_calls_expr i)
Proof
  recInduct base_assignment_target_induct >>
  simp[target_indices_def, type_place_target_AttributeTarget,
       type_place_target_SubscriptTarget, IS_SOME_EXISTS,
       alloc_limits_expr_def, int_calls_expr_def, EVERY_APPEND, PULL_EXISTS] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[call_evaluation_safe_append_left, call_evaluation_safe_append_right]
QED

Theorem place_write_append_index_support[local]:
  supported_append_target tops bt /\ MEM i (target_indices bt) ==>
  supported_expr tops i
Proof
  `supported_append_target tops bt ==>
   EVERY (supported_pure_expr tops) (target_indices bt)` by
    (Cases_on `bt` >> simp[supported_append_target_def,target_indices_def]) >>
  strip_tac >> first_x_assum drule >>
  simp[EVERY_MEM, supported_expr_def]
QED

Theorem place_write_stmt_index_support[local]:
  ((?e. s = Assign (BaseTarget bt) e) \/ (?e. s = Append bt e) \/
   (?ty op e. s = AugAssign ty bt op e)) /\
  supported_stmt tops bindings s /\ MEM i (target_indices bt) ==>
  supported_expr tops i
Proof
  strip_tac >> gvs[supported_stmt_def] >>
  metis_tac[supported_assignment_base_index, place_write_append_index_support,
            supported_target_index, supported_aug_target_index]
QED

Theorem place_write_stmt_index_guards[local]:
  ((?e. s = Assign (BaseTarget bt) e) \/ (?e. s = Append bt e) \/
   (?ty op e. s = AugAssign ty bt op e)) /\
  stmt_exprs_ok cenv s /\ call_evaluation_safe cx (int_calls_stmt s) /\
  EVERY (source_body_call_supported cx) (int_calls_stmt s) ==>
  alloc_limits_target cenv bt /\ call_evaluation_safe cx (int_calls_target bt) /\
  EVERY (source_body_call_supported cx) (int_calls_target bt) /\
  ~supported_target_exists
    (\e. ~is_extcode e /\ ~(byte_widths_expr e /\
        (array_slot_base cenv e \/ alloc_limits_expr cenv e))) bt /\
  ~supported_target_exists (const_name_root_mods cenv.ce_modules) bt /\
  (!p. supported_target_exists p bt ==> supported_stmt_expr_exists p s)
Proof
  strip_tac >>
  gvs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
      supported_assignment_exists_def, alloc_limits_stmt_def, alloc_limits_assignment_def,
      int_calls_stmt_def, int_calls_atarget_def, EVERY_APPEND] >>
  drule_then assume_tac call_evaluation_safe_append_left >> simp[]
QED

Theorem place_write_index_pre_mods:
  contract_inv mods exps ctx cenv cx /\
  ((?e. s = Assign (BaseTarget bt) e) \/ (?e. s = Append bt e) \/
   (?ty op e. s = AugAssign ty bt op e)) /\
  supported_stmt tops bindings s /\ IS_SOME (type_place_target env bt) /\
  stmt_exprs_ok cenv s /\ call_evaluation_safe cx (int_calls_stmt s) /\
  EVERY (source_body_call_supported cx) (int_calls_stmt s) /\
  ~supported_stmt_expr_exists (unallocated_bare_global_root cenv env) s /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target) s ==>
            EXISTS (occurs_abi_decode_target target o SND) mods) ==>
  !i st. MEM i (target_indices bt) /\ expr_sim_inv_mods mods cenv cx env st ==>
         expr_body_pre_mods mods cenv cx env i st
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> rpt gen_tac >> strip_tac >>
  drule_all_then assume_tac place_write_stmt_index_support >>
  drule_then assume_tac contract_inv_cenv_modules >>
  drule_then assume_tac contract_inv_type_env >>
  drule_all_then strip_assume_tac place_write_stmt_index_guards >>
  drule_all_then strip_assume_tac place_write_index_source_facts >>
  drule_then assume_tac supported_expr_no_evm_run >>
  drule_then assume_tac alloc_limits_expr_not_extcode >>
  `!p. supported_expr_exists p i ==> supported_stmt_expr_exists p s` by
    (rpt strip_tac >> first_x_assum irule >>
     simp[supported_target_exists_indices, EXISTS_MEM] >> metis_tac[]) >>
  irule (Q.INST [`calls` |-> `[]`] (SPEC_ALL stmt_expr_body_pre_mods)) >>
  simp[] >>
  fs[supported_target_exists_indices, EXISTS_MEM] >> metis_tac[]
QED

Theorem place_write_reached_source_mods:
  expr_sim_inv_mods mods cenv cx env es /\
  body_const_cells_agree_mods mods cx env es /\
  IS_SOME (type_place_target env bt) /\
  (!i st. MEM i (target_indices bt) /\ expr_sim_inv_mods mods cenv cx env st ==>
          expr_body_pre_mods mods cenv cx env i st) /\
  eval_target_place cx bt es = (INL p,mid) ==>
  expr_sim_inv_mods mods cenv cx env mid /\
  body_const_cells_agree_mods mods cx env mid
Proof
  strip_tac >> drule_then assume_tac tuple_place_target_base_inversion >>
  drule_all_then ACCEPT_TAC write_base_reached_source_mods
QED
