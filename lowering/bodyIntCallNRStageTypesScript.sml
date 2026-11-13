(* Declared parameter types and the producer's post-value representation. *)
Theory bodyIntCallNRStageTypes
Ancestors
  bodyIntCallJointForce bodyIntCallFamStmtReturnEndpointTypes
  bodyIntCallFamStmtReturnTypes bodyPtrStructLitLayoutTransfer
  assignTuplePtrLocalCompat valueEncodingTyping vyperTypeArgFits
  exprSimHyps exprSimHypsDefs exprSimDefs compileEnv vyperTypeInvariants
  bodyIntCallJointInputs compileVyper bodySim
Libs monadsyntax

Theorem intcall_stage_declared_word:
  expr_body_pre ce cx env e es /\
  type_widens_to env.type_defs (expr_type e) dty /\ is_word_type dty /\
  bind (eval_expr cx e) (read_result cx) es = (INL v,ee) ==>
  post_value_type ce e = dty /\
  ?tv. evaluate_type (get_tenv cx) dty = SOME tv /\
       value_has_type tv v /\ val_wf tv v /\
       type_memory_bytes ce dty = type_memory_size tv
Proof
  strip_tac >>
  `expr_sim_inv ce cx env es /\ well_typed_expr env e` by
    fs[expr_body_pre_def] >>
  drule_all return_post_type_widens >> strip_tac >>
  `post_value_type ce e = dty` by metis_tac[type_widens_to_word] >>
  simp[] >>
  drule_all (REWRITE_RULE [ETA_THM] memory_rhs_read_post_typed) >>
  simp[vyperTypeExprSoundnessTheory.value_runtime_typed_def] >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  qexists `tv` >> gvs[] >> conj_tac
  >- metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
  metis_tac[expr_sim_inv_memory_size]
QED

(* No equality of source and destination layouts is assumed. *)
Theorem intcall_stage_declared_layout:
  expr_body_pre ce cx env e es /\
  type_widens_to env.type_defs (expr_type e) dty /\
  bind (eval_expr cx e) (read_result cx) es = (INL v,ee) ==>
  ?stv dtv.
    evaluate_type (get_tenv cx) (post_value_type ce e) = SOME stv /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    val_wf stv v /\ val_wf dtv v /\
    type_widens_to (get_tenv cx) (post_value_type ce e) dty /\
    type_memory_bytes ce (post_value_type ce e) = type_memory_size stv /\
    type_memory_bytes ce dty = type_memory_size dtv /\
    type_memory_size stv <= type_memory_size dtv
Proof
  strip_tac >>
  `expr_sim_inv ce cx env es /\ well_typed_expr env e` by
    fs[expr_body_pre_def] >>
  drule_all return_post_type_widens >> strip_tac >>
  drule_all (REWRITE_RULE [ETA_THM] memory_rhs_read_post_typed) >>
  simp[vyperTypeExprSoundnessTheory.value_runtime_typed_def] >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  gvs[] >> drule_all type_widens_to_value_has_type >> strip_tac >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  simp[] >> rpt conj_tac
  >- metis_tac[valueEncodingTypingTheory.value_has_type_val_wf]
  >- metis_tac[valueEncodingTypingTheory.value_has_type_val_wf]
  >- metis_tac[expr_sim_inv_memory_size]
  >- metis_tac[expr_sim_inv_memory_size] >>
  metis_tac[type_widens_to_memory_size]
QED

Theorem intcall_stage_declared_bytes:
  expr_body_pre ce cx env e es /\
  type_widens_to env.type_defs (expr_type e) dty /\
  is_bytestring_type dty /\
  bind (eval_expr cx e) (read_result cx) es = (INL v,ee) ==>
  ?stv dtv.
    evaluate_type (get_tenv cx) (post_value_type ce e) = SOME stv /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\
    value_has_type dtv v /\ val_wf dtv v /\
    type_memory_bytes ce dty = type_memory_size dtv /\
    type_memory_size stv <= type_memory_size dtv /\
    (!a mem. val_in_memory stv v a mem <=>
             val_in_memory dtv v a mem) /\
    val_store_size stv v = val_store_size dtv v
Proof
  strip_tac >> drule_all intcall_stage_declared_layout >> strip_tac >>
  `is_bytestring_type (post_value_type ce e)` by
    metis_tac[typedMemoryCopyTheory.typed_copy_bytestring_source] >>
  qexistsl [`stv`, `dtv`] >> simp[] >>
  metis_tac[bytestring_representation_compat_ptr]
QED

Theorem intcall_stage_declared_capacity:
  body_inv tops ctx ce cx /\
  MEM (FunctionDecl Internal mut nr rr fname args dflts ret ss) tops /\
  MEM (name,ty) args ==>
  type_memory_bytes ce ty < 2 ** 64
Proof
  strip_tac >> drule_all body_inv_internal_allocs_ok >>
  simp[fn_allocs_ok_def, listTheory.EVERY_MEM] >> strip_tac >>
  first_x_assum drule >> simp[] >>
  `ce.ce_struct_fields =
   (build_compile_env tops Internal mut fname args ret ss F).ce_struct_fields`
    by fs[body_inv_def, build_compile_env_ce_struct_fields] >>
  metis_tac[type_memory_bytes_struct_fields]
QED
