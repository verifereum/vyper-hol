(* Widening a local assignment preserves the physical return layout until the copy. *)
Theory bodyAssignNameWidenedRouteMods
Ancestors
  bodyAssignNameLinkedSetup exprSimIfExpCompat exprSimSource exprSimHypsDefs
  exprBodyPreProps compileEnv exprLowering exprLoweringProps loweringPosts typedMemoryCopy
  assignRelayoutCaller annassignRelayoutSource exprSimAggregateChildren
  exprOpenTerminals exprOpenPrimitives vyperTypeSystem vyperTypeInvariants
  vyperTypeEvalCaseProofs vyperAST words annassignRelayoutCode stmtLowering
  bodyCopyAtomicRhsTypeMods valueTypingMemoryProps vyperTypeArgFits
  exprSimProps vyperState vyperTypeExprSoundness
Libs monadsyntax

Theorem widened_rhs_is_call[local]:
  expr_body_pre_mods mods ce cx env e es /\
  ~(lowered_value_type ce e = expr_type e \/
    is_bytestring_type (expr_type e) /\ is_bytestring_type (lowered_value_type ce e) /\
    arg_type_fits (lowered_value_type ce e) (expr_type e)) ==>
  ?ty fid args drv. e = Call ty (IntCall fid) args drv
Proof
  strip_tac >> drule expr_body_pre_mods_well_typed >> strip_tac >>
  drule expr_body_pre_mods_inv >> strip_tac >>
  drule expr_sim_inv_mods_env >> strip_tac >>
  drule env_consistent_type_defs_get_tenv >> strip_tac >>
  `!id ty. FLOOKUP env.var_types id = SOME ty ==> well_formed_type env.type_defs ty` by
    (rpt strip_tac >> drule_all env_consistent_var_type_evaluates >>
     simp[well_formed_type_def]) >>
  `sfields_tenv_consistent ce.ce_struct_fields env.type_defs` by fs[expr_sim_inv_mods_def] >>
  `!fid sg. FLOOKUP env.fn_sigs fid = SOME sg ==>
      ce.ce_func_return_type (nsid_to_string fid) = sg.ret_ty` by
    (rpt strip_tac >> drule_all_then ACCEPT_TAC expr_sim_inv_mods_return_type) >>
  drule_all_then strip_assume_tac ifexp_lowered_type_classify >> fs[]
QED

Theorem widened_rhs_layout[local]:
  expr_body_pre_mods mods ce cx env e es /\
  type_widens_to (get_tenv cx) (expr_type e) ty /\ ~is_word_type ty /\
  ~(lowered_value_type ce e = expr_type e \/
    is_bytestring_type (expr_type e) /\ is_bytestring_type (lowered_value_type ce e) /\
    arg_type_fits (lowered_value_type ce e) (expr_type e)) ==>
  ~is_bytestring_type ty /\ ~is_word_type (lowered_value_type ce e) /\
  ~is_bytestring_type (lowered_value_type ce e) /\
  post_value_type ce e = lowered_value_type ce e /\
  type_widens_to (get_tenv cx) (lowered_value_type ce e) ty
Proof
  strip_tac >>
  drule_all widened_rhs_is_call >> strip_tac >> gvs[] >>
  drule expr_body_pre_mods_well_typed >> strip_tac >>
  drule expr_body_pre_mods_inv >> strip_tac >>
  drule expr_sim_inv_mods_env >> strip_tac >>
  drule env_consistent_type_defs_get_tenv >> strip_tac >>
  PairCases_on `fid` >>
  qpat_x_assum `well_typed_expr env _` mp_tac >>
  simp[Once well_typed_expr_def] >> strip_tac >>
  rename1 `FLOOKUP env.fn_sigs _ = SOME sg` >>
  drule_all expr_sim_inv_mods_return_type >> strip_tac >>
  fs[lowered_value_type_def, expr_type_def] >>
  `~is_word_type ty'` by metis_tac[return_source_word_widens_eq] >>
  `arg_type_fits sg.ret_ty ty'` by metis_tac[type_widens_to_def, cj 1 arg_type_fits_refl] >>
  `~is_bytestring_type ty'` by metis_tac[compileEnvTheory.arg_type_fits_bytestring_source] >>
  `~is_bytestring_type ty` by
    metis_tac[type_widens_to_def, compileEnvTheory.arg_type_fits_bytestring_source] >>
  simp[] >> metis_tac[return_source_word_widens_eq, type_widens_from_bytestring,
                     type_widens_to_trans]
QED

Theorem widened_rhs_code[local]:
  expr_body_pre_mods mods ce cx env e es /\
  ~(lowered_value_type ce e = expr_type e \/
    is_bytestring_type (expr_type e) /\ is_bytestring_type (lowered_value_type ce e) /\
    arg_type_fits (lowered_value_type ce e) (expr_type e)) ==>
  ~is_empty_value_expr e /\ ~is_empty_value_expr (gas_shadow_expr e) /\
  (!ty sa vv sb. compile_expr ce ty e sa = (vv,sb) ==>
    (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) /\
    ~block_is_terminated sb)
Proof
  strip_tac >> drule_all widened_rhs_is_call >> strip_tac >> gvs[] >>
  simp[is_empty_value_expr_def, gasShadowTheory.gas_shadow_expr_def] >>
  rpt gen_tac >> simp[Once compile_expr_def] >> strip_tac >>
  metis_tac[internal_call_location_cases, compile_intcall_open]
QED

Theorem widened_rhs_read_layout[local]:
  expr_body_pre_mods mods ce cx env e es /\
  ~(lowered_value_type ce e = expr_type e \/
    is_bytestring_type (expr_type e) /\ is_bytestring_type (lowered_value_type ce e) /\
    arg_type_fits (lowered_value_type ce e) (expr_type e)) /\
  type_widens_to (get_tenv cx) (lowered_value_type ce e) ty /\
  evaluate_type (get_tenv cx) ty = SOME dtv /\
  0 < type_memory_size dtv /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := prefix) = (INL v,mid) ==>
  ?stv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
        type_memory_bytes ce (lowered_value_type ce e) = type_memory_size stv /\
        0 < type_memory_size stv /\ type_memory_size stv <= type_memory_size dtv /\
        value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v
Proof
  strip_tac >> drule_all widened_rhs_is_call >> strip_tac >> gvs[] >>
  drule expr_body_pre_mods_well_typed >> strip_tac >>
  drule expr_body_pre_mods_inv >> strip_tac >>
  `expr_sim_inv_mods mods ce cx env (es with gas_obs := prefix)` by
    (qpat_x_assum `expr_sim_inv_mods mods ce cx env es` mp_tac >>
     pure_rewrite_tac[expr_sim_inv_mods_def, env_consistent_def, state_well_typed_def,
                      env_scopes_consistent_def, env_immutables_consistent_def,
                      evaluation_state_accfupds] >> simp[]) >>
  drule_all (REWRITE_RULE [ETA_THM] copy_intcall_read_lowered_mods) >> strip_tac >>
  drule expr_sim_inv_mods_env >> strip_tac >>
  drule env_consistent_type_defs_get_tenv >> strip_tac >>
  gvs[value_runtime_typed_def] >>
  drule_all assign_name_memory_bytes_mods >> strip_tac >>
  drule_all type_widens_to_value_has_type >> strip_tac >> gvs[] >>
  drule_all widening_zero_memory_size >> strip_tac >>
  `type_memory_bytes ce ty = type_memory_size dtv` by
    (irule assign_name_memory_bytes_mods >>
     goal_assum (drule_at (Pat `evaluate_type _ _ = SOME _`)) >>
     qexistsl_tac [`env`,`es`,`mods`] >> simp[]) >>
  `type_memory_bytes ce (lowered_value_type ce (Call ty' (IntCall fid) args drv)) <=
     type_memory_bytes ce ty` by
    (qpat_x_assum `type_widens_to _ _ _` mp_tac >>
     pure_rewrite_tac[type_widens_to_def] >> strip_tac
     >- gvs[] >>
     drule (cj 1 arg_type_fits_memory_bytes_mono) >>
     disch_then (qspec_then `ce` mp_tac) >> simp[]) >>
  fs[value_has_type_memory_wf] >> decide_tac
QED
