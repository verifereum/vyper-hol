(* Static and successful-read typing for a fresh nonword declaration. *)
Theory bodyAnnNonwordReadTypesMods
Ancestors
  bodyCopyReadPhysicalTypeMods bodyAssignNameLinkedSetup
  exprSimIfExpCompat exprSimAggregateChildren annassignRelayoutSource
  exprBodyPreProps exprBodyPreTypingProps vyperTypeEvalCaseProofs
  vyperTypeArgFits valueTypingMemoryProps typedMemoryCopy typedCopyCompatibility
  exprSimSource exprSimHypsDefs loweringPosts logArgumentTypeEval
  vyperTypeSystem valueCopyBytes exprLowering vyperAST

Theorem ann_copy_nonword_layout_mods:
  expr_body_pre_mods mods ce cx env e es /\
  type_widens_to (get_tenv cx) (expr_type e) typ /\ ~is_word_type typ ==>
  ~is_word_type (expr_type e) /\ ~is_word_type (lowered_value_type ce e) /\
  ~is_word_type (post_value_type ce e) /\
  type_widens_to (get_tenv cx) (lowered_value_type ce e) typ /\
  (post_value_type ce e = lowered_value_type ce e \/
   is_bytestring_type (post_value_type ce e) /\
   is_bytestring_type (lowered_value_type ce e))
Proof
  strip_tac >> drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  `~is_word_type (expr_type e)` by metis_tac[return_source_word_widens_eq] >>
  `!id ty. FLOOKUP env.var_types id = SOME ty ==> well_formed_type env.type_defs ty` by
    (rpt strip_tac >> drule_all env_consistent_var_type_evaluates >>
     simp[well_formed_type_def]) >>
  `sfields_tenv_consistent ce.ce_struct_fields env.type_defs` by
    (qpat_assum `expr_sim_inv_mods _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_sim_inv_mods_def]) >> simp[]) >>
  `!fid sg. FLOOKUP env.fn_sigs fid = SOME sg ==>
      ce.ce_func_return_type (nsid_to_string fid) = sg.ret_ty` by
    (rpt strip_tac >> drule_all_then ACCEPT_TAC expr_sim_inv_mods_return_type) >>
  drule_all ifexp_lowered_type_classify >>
  disch_then (DISJ_CASES_THEN2 assume_tac (DISJ_CASES_THEN2 strip_assume_tac strip_assume_tac))
  >- fs[post_value_type_lowered]
  >- (`well_formed_type (get_tenv cx) (expr_type e)` by
        metis_tac[checked_expr_type_well_formed] >>
      `type_widens_to (get_tenv cx) (lowered_value_type ce e) (expr_type e)` by
        simp[type_widens_to_def] >>
      simp[is_bytestring_word_type] >> metis_tac[type_widens_to_trans]) >>
  qpat_x_assum `e = Call _ (IntCall _) _ _` SUBST_ALL_TAC >>
  PairCases_on `fid` >>
  qpat_x_assum `well_typed_expr env _` mp_tac >>
  simp[Once well_typed_expr_def] >> strip_tac >>
  rename1 `FLOOKUP env.fn_sigs _ = SOME sg` >>
  drule_all expr_sim_inv_mods_return_type >> strip_tac >>
  fs[lowered_value_type_def,expr_type_def] >>
  `~is_word_type sg.ret_ty` by metis_tac[return_source_word_widens_eq] >>
  Cases_on `is_bytestring_type ty` >> simp[] >>
  metis_tac[type_widens_to_trans,typed_copy_bytestring_source]
QED

Theorem ann_copy_nonword_read_types_mods:
  expr_body_pre_mods mods ce cx env e es /\
  type_widens_to (get_tenv cx) (expr_type e) typ /\ ~is_word_type typ /\
  evaluate_type (get_tenv cx) typ = SOME dtv /\ 0 < type_memory_size dtv /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := prefix) = (INL v,mid) ==>
  ?pt rt. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME pt /\
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
    value_has_type pt v /\ value_has_type rt v /\ value_has_type dtv v /\
    val_wf rt v /\ val_wf dtv v /\
    type_memory_bytes ce (lowered_value_type ce e) = type_memory_size rt /\
    type_memory_bytes ce typ = type_memory_size dtv /\
    0 < type_memory_size rt /\ type_memory_size rt <= type_memory_size dtv
Proof
  strip_tac >> drule_all_then strip_assume_tac ann_copy_nonword_layout_mods >>
  drule_all_then strip_assume_tac copy_read_physical_type_gas_obs_mods >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  `type_memory_bytes ce typ = type_memory_size dtv` by
    (irule assign_name_memory_bytes_mods >>
     goal_assum (drule_at (Pat `evaluate_type _ _ = SOME _`)) >>
     qexistsl_tac [`env`,`es`,`mods`] >> simp[]) >>
  `value_has_type dtv v` by
    (qpat_assum `type_widens_to _ (lowered_value_type _ _) _`
       (mp_then Any mp_tac type_widens_to_value_has_type) >>
     disch_then (drule_at (Pat `evaluate_type _ _ = SOME _`)) >>
     disch_then (drule_at (Pat `value_has_type _ _`)) >> simp[]) >>
  `0 < type_memory_size rt` by
    (qpat_assum `type_widens_to _ (lowered_value_type _ _) _`
       (mp_then Any mp_tac widening_zero_memory_size) >>
     disch_then drule_all >> simp[]) >>
  `type_memory_bytes ce (lowered_value_type ce e) <= type_memory_bytes ce typ` by
    (qpat_assum `type_widens_to _ (lowered_value_type _ _) _` mp_tac >>
     pure_rewrite_tac[type_widens_to_def] >> strip_tac
     >- (qpat_assum `lowered_value_type ce e = typ` (fn th => simp[NoAsms,th])) >>
     irule (cj 1 arg_type_fits_memory_bytes_mono) >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`pt`,`rt`] >> simp[value_has_type_memory_wf]
QED
