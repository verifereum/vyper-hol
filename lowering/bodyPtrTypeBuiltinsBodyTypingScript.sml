Theory bodyPtrTypeBuiltinsBodyTyping
Ancestors bodySim exprSimHypsDefs memoryLocalRhsProps vyperTypeEvalSoundness
  vyperTypeExprSoundness vyperTypeInvariants vyperTypeSystem vyperInterpreter
  vyperState vyperAST exprLowering compileEnv valueTypingMemoryProps
  abiTypeBoundProps
Libs monadsyntax

Theorem body_frame_signature_well_formed:
  expr_sim_inv cenv cx env es /\ FLOOKUP env.fn_sigs id = SOME sig ==>
  well_formed_type env.type_defs sig.ret_ty
Proof
  strip_tac >>
  `env_consistent env cx es /\ functions_well_typed cx` by
    gvs[expr_sim_inv_def] >>
  `env.type_defs = get_tenv cx /\ fn_sigs_consistent env.fn_sigs cx` by
    (qpat_x_assum `env_consistent _ _ _` mp_tac >>
     simp[env_consistent_def, env_context_consistent_def]) >>
  Cases_on `id` >>
  qpat_assum `fn_sigs_consistent _ _` mp_tac >>
  pure_rewrite_tac[fn_sigs_consistent_def] >>
  disch_then drule >> strip_tac >>
  `IS_SOME (FLOOKUP env.fn_sigs (q,r))` by simp[] >>
  drule_all callable_body_typing_from_env_consistent >>
  simp[] >> strip_tac >> simp[well_formed_type_def]
QED

Theorem body_internal_annotation_eval:
  !cx a b id args drv.
  eval_expr cx (Call a (IntCall id) args drv) =
  eval_expr cx (Call b (IntCall id) args drv)
Proof
  rpt gen_tac >> Cases_on `id` >> once_rewrite_tac[evaluate_def] >> REFL_TAC
QED

Theorem body_internal_read_signature_typed:
  expr_body_pre cenv cx env (Call ann (IntCall id) args drv) es /\
  FLOOKUP env.fn_sigs id = SOME sig /\
  (do r <- eval_expr cx (Call ann (IntCall id) args drv);
      read_result cx r od) es = (INL v,ee) ==>
  value_runtime_typed env sig.ret_ty v
Proof
  strip_tac >>
  `expr_sim_inv cenv cx env es` by gvs[expr_body_pre_def] >>
  `well_formed_type env.type_defs sig.ret_ty` by
    (drule_all body_frame_signature_well_formed >> simp[]) >>
  `well_typed_expr env (Call sig.ret_ty (IntCall id) args drv)` by
    (Cases_on `id` >>
     gvs[expr_body_pre_def, well_typed_expr_def, type_widens_to_def] >>
     metis_tac[]) >>
  `(do r <- eval_expr cx (Call sig.ret_ty (IntCall id) args drv);
      read_result cx r od) es = (INL v,ee)` by
    metis_tac[body_internal_annotation_eval] >>
  drule_at (Pat `bind _ _ _ = _`) eval_expr_read_type_sound >>
  disch_then (qspec_then `env` mp_tac) >>
  gvs[expr_body_pre_def, expr_sim_inv_def, vyperTypeCallGraphTheory.int_calls_expr_def, expr_type_def]
QED
