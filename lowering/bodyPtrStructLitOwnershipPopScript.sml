Theory bodyPtrStructLitOwnershipPop
Ancestors bodyPtrStructLitOwnershipSubscriptTails bodyPtrStructLitOwnershipInterfaces
  bodyPtrStructLitOwnershipMemory bodyPtrStructLitOwnershipFreshness
  bodyPtrStructLitOwnershipSteps loweringShapeProps loweringShapeDefs
  exprLowering compileEnv context supportedExprTraverse
  bodyPtrStructLitTargetScalar bodyPtrStructLitTargetArray
  bodyPtrStructLitOwnershipFrame bodyPtrStructLitOwnershipShape
  loweringShapeRules stackPlanTypes gasShadowCompileBase

Theorem alloc_run_compile_dynarray_pop:
  alloc_run fresh_outputs (compile_dynarray_pop base_op ws sz ctor imm loc)
    (\v s. fresh_outputs s)
Proof
  simp[compile_dynarray_pop_def, comp_ignore_bind_def] >>
  rpt (irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
    reverse conj_tac >- simp[SF ETA_ss,
      SRULE [SF ETA_ss] alloc_run_compile_ptr_load,
      SRULE [SF ETA_ss] alloc_run_compile_ptr_store,
      SRULE [SF ETA_ss] alloc_run_emit_op_fresh,
      SRULE [SF ETA_ss] alloc_run_emit_void_fresh] >> rpt gen_tac >> simp[]) >>
  simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh]
QED

Theorem ownership_target_induct[local]:
  !P. (!id. P (NameTarget id)) /\ (!nsid. P (TopLevelNameTarget nsid)) /\
    (!bt e. P bt ==> P (SubscriptTarget bt e)) /\
    (!bt s. P bt ==> P (AttributeTarget bt s)) ==> !bt. P bt
Proof
  rpt strip_tac >>
  `(!e:expr. T) /\ !bt. P bt` suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >> simp[]
QED

Theorem target_lower_shape[local]:
  shape_step internal compiler_label (\s. cenv_shape_ok s ce)
    (cfn ce ty e) (\v s. value_shape_ok s v) /\ shape_stable R ==>
  shape_step internal compiler_label (\s. R s /\ cenv_shape_ok s ce)
    (lower_value cfn ce ty e) (\v s. R s /\ cenv_shape_ok s ce /\ plain_operand s v)
Proof
  strip_tac >> simp[lower_value_def] >> irule shape_step_bind >>
  qexists `\v s. (R s /\ cenv_shape_ok s ce) /\ value_shape_ok s v` >>
  reverse conj_tac
  >- (irule shape_step_conseq >> irule_at Any shape_step_frame >>
      qpat_assum `shape_step _ _ _ _ _` (irule_at Any) >>
      qexists `\s. R s /\ cenv_shape_ok s ce` >>
      simp[shape_stable_conj, cenv_shape_ok_stable]) >>
  gen_tac >> simp[] >> irule shape_step_conseq >> irule_at Any shape_step_frame >>
  irule_at Any unwrap_value_shape >> qexists `\s. R s /\ cenv_shape_ok s ce` >>
  simp[shape_stable_conj, cenv_shape_ok_stable]
QED

Theorem target_array_cont_shape[local]:
  shape_step internal compiler_label (\s. cenv_shape_ok s ce)
    (cfn ce ty e) (\v s. value_shape_ok s v) ==>
  shape_step internal compiler_label (\s. plain_operand s base_op /\ cenv_shape_ok s ce)
    (comp_bind (lower_value cfn ce ty e) (\idx.
       comp_bind (compile_array_subscript base_op idx dyn count_n scale_n bytes_n signed_idx
         (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca loc))
         (\p. comp_return (p, lo, pt)))) (\r s. plain_operand s (FST r))
Proof
  strip_tac >> irule shape_step_bind >>
  qexists `\v s. plain_operand s base_op /\ cenv_shape_ok s ce /\ plain_operand s v` >>
  reverse conj_tac
  >- (ho_match_mp_tac target_lower_shape >>
      simp[SRULE [] (Q.SPEC `[op]` shape_stable_plain_operands)]) >>
  qx_gen_tac `idx` >> simp[] >> irule shape_step_bind >>
  qexists `\v s. cenv_shape_ok s ce /\ plain_operand s v` >>
  reverse conj_tac
  >- (irule shape_step_conseq >> irule_at Any (cj 1 target_array_certificate) >>
      qexists `\s. cenv_shape_ok s ce` >>
      simp[cenv_shape_ok_stable, compile_ptr_load_cenv_shape,
        alloc_run_compile_ptr_load]) >>
  gen_tac >> simp[] >> irule shape_step_return >> simp[]
QED

Theorem target_lower_fresh[local]:
  shape_step internal compiler_label (\s. cenv_shape_ok s ce)
    (cfn ce ty e) (\v s. value_shape_ok s v) /\
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce) (cfn ce ty e) (\v s. T) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (lower_value cfn ce ty e) (\v s. fresh_outputs s)
Proof
  strip_tac >> irule alloc_run_conseq >> irule_at Any alloc_run_lower_value_frame >>
  qpat_assum `shape_step _ _ _ _ _` (irule_at Any) >>
  qpat_assum `alloc_run _ _ _` (irule_at Any) >> qexists `\s. T` >>
  simp[shape_stable_def, shape_state_def, shape_base_fresh_outputs]
QED

Theorem target_array_cont_owned[local]:
  shape_step internal compiler_label (\s. cenv_shape_ok s ce)
    (cfn ce ty e) (\v s. value_shape_ok s v) /\
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce) (cfn ce ty e) (\v s. T) ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (comp_bind (lower_value cfn ce ty e) (\idx.
       comp_bind (compile_array_subscript base_op idx dyn count_n scale_n bytes_n signed_idx
         (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca loc))
         (\p. comp_return (p, lo, pt)))) (\r s. T)
Proof
  strip_tac >> irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
  reverse conj_tac >- (irule target_lower_fresh >> metis_tac[]) >>
  gen_tac >> simp[] >> irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
  reverse conj_tac
  >- (simp[SF ETA_ss] >> irule (SRULE [SF ETA_ss] alloc_run_compile_array_subscript) >>
      simp[SRULE [SF ETA_ss] alloc_run_compile_ptr_load]) >>
  gen_tac >> simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED

Theorem target_prefix_certificate:
  !bt ce.
    (!env ty child. supported_target_exists (\e. e = child) bt /\
       ~supported_expr_exists expr_shape_root child ==>
       shape_step internal compiler_label (\s. cenv_shape_ok s env)
         (cfn env ty child) (\v s. value_shape_ok s v) /\
       alloc_run (\s. shape_state s /\ cenv_shape_ok s env)
         (cfn env ty child) (\v s. T)) /\
    ~supported_target_exists expr_shape_root bt ==>
    shape_step internal compiler_label (\s. cenv_shape_ok s ce)
      (compile_get_target_ptr cfn ce bt) (\r s. plain_operand s (FST r)) /\
    alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
      (compile_get_target_ptr cfn ce bt) (\r s. T)
Proof
  recInduct ownership_target_induct >> rpt conj_tac >> BETA_TAC >>
  rpt gen_tac >> simp[supported_expr_exists_def]
  >- suspend "name"
  >- suspend "toplevel"
  >- suspend "subscript"
  >> suspend "attribute"
QED

Resume target_prefix_certificate[name]:
  simp[Once compile_get_target_ptr_def] >> conj_tac
  >- (BasicProvers.TOP_CASE_TAC
      >- (irule shape_step_return >> simp[plain_operand_def, is_label_operand_def]) >>
      rename1 `FLOOKUP _ _ = SOME vl` >> Cases_on `vl` >> simp[] >>
      irule shape_step_return >> BETA_TAC >> rpt strip_tac >>
      gvs[cenv_shape_ok_def] >>
      first_x_assum drule >>
      simp[loc_shape_ok_def, plain_operand_def, is_label_operand_def]) >>
  simp[compile_get_target_ptr_def] >>
  BasicProvers.TOP_CASE_TAC >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl] >>
  rename1 `FLOOKUP _ _ = SOME vl` >> Cases_on `vl` >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED
Resume target_prefix_certificate[toplevel]:
  simp[Once compile_get_target_ptr_def] >> conj_tac
  >- (BasicProvers.TOP_CASE_TAC
      >- (irule shape_step_return >> simp[plain_operand_def, is_label_operand_def]) >>
      rename1 `FLOOKUP _ _ = SOME vl` >> Cases_on `vl` >> simp[] >>
      irule shape_step_return >> simp[plain_operand_def, is_label_operand_def]) >>
  simp[compile_get_target_ptr_def] >>
  BasicProvers.TOP_CASE_TAC >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl] >>
  rename1 `FLOOKUP _ _ = SOME vl` >> Cases_on `vl` >>
  simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED
Resume target_prefix_certificate[subscript]:
  disch_tac >> gen_tac >> strip_tac >>
  `shape_step internal compiler_label (\s. cenv_shape_ok s ce)
     (compile_get_target_ptr cfn ce bt) (\r s. plain_operand s (FST r)) /\
   alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
     (compile_get_target_ptr cfn ce bt) (\r s. T)` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  `shape_step internal compiler_label (\s. cenv_shape_ok s ce)
     (cfn ce (expr_type e) e) (\v s. value_shape_ok s v) /\
   alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
     (cfn ce (expr_type e) e) (\v s. T)` by
    (first_x_assum irule >> simp[] >>
     disj2_tac >> irule supported_expr_exists_root >> simp[]) >>
  conj_tac >- suspend "subscript_shape" >> suspend "subscript_owned"
QED
Resume target_prefix_certificate[attribute]:
  disch_tac >> gen_tac >> strip_tac >>
  `shape_step internal compiler_label (\s. cenv_shape_ok s ce)
     (compile_get_target_ptr cfn ce bt) (\r s. plain_operand s (FST r)) /\
   alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
     (compile_get_target_ptr cfn ce bt) (\r s. T)` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  conj_tac >- suspend "attribute_shape" >> suspend "attribute_owned"
QED
Resume target_prefix_certificate[attribute_shape]:
  simp[Once compile_get_target_ptr_def] >>
  irule shape_step_bind >> qexists `\r s. plain_operand s (FST r)` >>
  reverse conj_tac >- simp[] >>
  gen_tac >> simp[] >> irule target_scalar_op_bind >>
  simp[SRULE [] (Q.SPEC `[op]` shape_stable_plain_operands),
    plain_operand_def, is_label_operand_def] >>
  gen_tac >> irule shape_step_return >> simp[plain_operand_def, is_label_operand_def]
QED
Resume target_prefix_certificate[attribute_owned]:
  simp[Once compile_get_target_ptr_def] >>
  irule alloc_run_bind >> qexists `\r s. fresh_outputs s` >>
  reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_shape_join >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
      simp[shape_state_def] >> metis_tac[shape_base_fresh_outputs]) >>
  gen_tac >> simp[] >> irule alloc_run_bind >>
  qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_emit_op_fresh] >>
  gen_tac >> simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED
Resume target_prefix_certificate[subscript_shape]:
  simp[Once compile_get_target_ptr_def] >> irule shape_step_bind >>
  qexists `\r s. plain_operand s (FST r) /\ cenv_shape_ok s ce` >>
  reverse conj_tac
  >- (irule shape_step_conseq >> irule_at Any shape_step_frame >>
      qpat_assum `shape_step _ _ _ (compile_get_target_ptr _ _ _) _` (irule_at Any) >>
      qexists `\s. cenv_shape_ok s ce` >> simp[cenv_shape_ok_stable]) >>
  qx_gen_tac `r` >> simp[] >> Cases_on `SND (SND r)` >> simp[]
  >- (irule target_array_cont_shape >> simp[]) >>
  rename1 `SND (SND r) = SOME pt` >> Cases_on `pt` >> simp[]
  >- suspend "mapping_shape" >>
  rename1 `ValPT ty` >> Cases_on `ty` >> simp[] >>
  (irule target_array_cont_shape >> simp[])
QED
Resume target_prefix_certificate[subscript_owned]:
  simp[Once compile_get_target_ptr_def] >> irule alloc_run_bind >>
  qexists `\r s. shape_state s /\ cenv_shape_ok s ce` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_shape_frame >>
      qpat_assum `shape_step _ _ _ (compile_get_target_ptr _ _ _) _` (irule_at Any) >>
      simp[] >>
      qpat_assum `alloc_run _ (compile_get_target_ptr _ _ _) _` (irule_at Any) >>
      qexists `\s. cenv_shape_ok s ce` >> simp[cenv_shape_ok_stable]) >>
  qx_gen_tac `r` >> simp[] >> Cases_on `SND (SND r)` >> simp[]
  >- (irule target_array_cont_owned >> metis_tac[]) >>
  rename1 `SND (SND r) = SOME pt` >> Cases_on `pt` >> simp[]
  >- suspend "mapping_owned" >>
  rename1 `ValPT ty` >> Cases_on `ty` >> simp[] >>
  (irule target_array_cont_owned >> metis_tac[])
QED
Resume target_prefix_certificate[mapping_shape]:
  irule shape_step_bind >>
  qexists `\v s. plain_operand s (FST r) /\ cenv_shape_ok s ce /\ plain_operand s v` >>
  reverse conj_tac
  >- (ho_match_mp_tac target_lower_shape >>
      simp[SRULE [] (Q.SPEC `[op]` shape_stable_plain_operands)]) >>
  qx_gen_tac `key` >> simp[] >> irule shape_step_bind >>
  qexists `\v s. (plain_operand s (FST r) /\ cenv_shape_ok s ce) /\ plain_operand s v` >>
  reverse conj_tac
  >- (IF_CASES_TAC >> simp[]
      >- (irule shape_step_conseq >> irule_at Any (cj 1 target_key_hash_certificate) >>
          qexists `\s. plain_operand s (FST r) /\ cenv_shape_ok s ce` >>
          simp[shape_stable_conj, cenv_shape_ok_stable,
            SRULE [] (Q.SPEC `[op]` shape_stable_plain_operands)]) >>
      irule shape_step_return >> simp[]) >>
  qx_gen_tac `hashed` >> simp[] >> irule shape_step_bind >>
  qexists `\v s. (\s. T) s /\ plain_operand s v` >> reverse conj_tac
  >- (irule shape_step_conseq >> irule_at Any (cj 1 target_mapping_certificate) >>
      qexists `\s. T` >> simp[shape_stable_def]) >>
  gen_tac >> simp[] >> irule shape_step_return >> simp[]
QED
Resume target_prefix_certificate[mapping_owned]:
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >> reverse conj_tac
  >- (irule target_lower_fresh >> metis_tac[]) >>
  gen_tac >> simp[] >> irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
  reverse conj_tac
  >- (IF_CASES_TAC
      >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_keccak256_key] >>
      simp[comp_return_def, alloc_run_def, alloc_frame_refl]) >>
  gen_tac >> simp[] >> irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
  reverse conj_tac >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_mapping_subscript] >>
  gen_tac >> simp[comp_return_def, alloc_run_def, alloc_frame_refl]
QED
Finalise target_prefix_certificate

Theorem alloc_run_target_prefix_frame:
  (!env ty child. supported_target_exists (\e. e = child) bt /\
     ~supported_expr_exists expr_shape_root child ==>
     shape_step internal compiler_label (\s. cenv_shape_ok s env)
       (cfn env ty child) (\v s. value_shape_ok s v) /\
     alloc_run (\s. shape_state s /\ cenv_shape_ok s env)
       (cfn env ty child) (\v s. T)) /\
  ~supported_target_exists expr_shape_root bt /\ shape_stable R ==>
  alloc_run (\s. shape_state s /\ R s /\ cenv_shape_ok s ce)
    (compile_get_target_ptr cfn ce bt)
    (\r s. shape_state s /\ R s /\ cenv_shape_ok s ce /\ plain_operand s (FST r))
Proof
  strip_tac >>
  `shape_step internal compiler_label (\s. cenv_shape_ok s ce)
     (compile_get_target_ptr cfn ce bt) (\r s. plain_operand s (FST r)) /\
   alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
     (compile_get_target_ptr cfn ce bt) (\r s. T)` by
    (irule target_prefix_certificate >> simp[]) >>
  irule alloc_run_conseq >> irule_at Any alloc_run_shape_frame >>
  qpat_assum `shape_step _ _ _ _ _` (irule_at Any) >> simp[] >>
  qpat_assum `alloc_run _ _ _` (irule_at Any) >>
  qexists `\s. R s /\ cenv_shape_ok s ce` >>
  simp[shape_stable_conj, cenv_shape_ok_stable]
QED

Theorem alloc_run_compile_expr_body_pop:
  (!env ty child. supported_target_exists (\e. e = child) bt /\
     ~supported_expr_exists expr_shape_root child ==>
     shape_step internal compiler_label (\s. cenv_shape_ok s env)
       (cfn env ty child) (\v s. value_shape_ok s v) /\
     alloc_run (\s. shape_state s /\ cenv_shape_ok s env)
       (cfn env ty child) (\v s. T)) /\
  ~supported_target_exists expr_shape_root bt ==>
  alloc_run (\s. shape_state s /\ cenv_shape_ok s ce)
    (compile_expr_body cfn bfn tfn ce ty (Pop ann bt)) (\v s. T)
Proof
  strip_tac >>
  GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) empty_rewrites [GSYM ETA_AX] >>
  simp[compile_expr_body_def, comp_bind_uncurry] >>
  simp[SF ETA_ss] >> irule alloc_run_bind >>
  qexists `\r s. fresh_outputs s` >> reverse conj_tac
  >- (irule alloc_run_conseq >> irule_at Any alloc_run_target_prefix_frame >>
      qexistsl [`internal`, `\s. T`] >>
      simp[shape_stable_def, shape_state_def, shape_base_fresh_outputs]) >>
  gen_tac >> PairCases_on `v` >> simp[] >>
  irule alloc_run_bind >> qexists `\v s. fresh_outputs s` >>
  reverse conj_tac >- simp[SF ETA_ss, SRULE [SF ETA_ss] alloc_run_compile_dynarray_pop] >>
  gen_tac >> simp[alloc_run_def, alloc_frame_refl]
QED
