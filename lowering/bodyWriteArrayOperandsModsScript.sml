(* Scalar index and saved base operand at the same post-index cut. *)
Theory bodyWriteArrayOperandsMods
Ancestors
  bodyWriteArrayPacketMods bodyWriteTargetStageMods bodyFullPostsMods
  bodyFullTargetDefs bodyPtrDefs loweringPosts exprBodyPreProps exprOperandVar
  exprWordOperand exprSimArith exprSimSource exprSimHypsDefs exprLowering
  exprLoweringProps stmtSimAugAssignPlace vyperTypeEvalCaseProofs freshWrites
  compileEnv vyperTypeEnv vyperTypeSystem vyperTypeExprSoundness vyperValue
  vyperTyping valueEncoding venomState ptrDiscipline

Theorem linked_array_int_word[local]:
  is_int_type ty ==> is_word_type ty
Proof
  Cases_on `ty` >> simp[] >> rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[is_word_type_def]
QED

Theorem linked_array_index_word[local]:
  is_int_type ty /\ value_runtime_typed env ty v /\
  env.type_defs = get_tenv cx /\ expr_val_rel cx ty v op t ==>
  ?i iw. v = IntV i /\ eval_operand op t = SOME iw /\
    i = (if is_signed_type ty then w2i iw else &(w2n iw))
Proof
  simp[value_runtime_typed_def] >> strip_tac >>
  Cases_on `ty` >> gvs[] >> rename1 `BaseT bt` >> Cases_on `bt` >>
  gvs[is_int_type_def, evaluate_type_def, value_has_type_def,
      expr_val_rel_def, is_word_type_def] >>
  Cases_on `v` >> gvs[value_has_type_def, typed_val_to_w256_def, val_to_w256_def] >>
  once_rewrite_tac[GSYM arithmeticPropsTheory.math_val_def] >>
  sym_tac >> irule math_val_i2w >>
  gvs[is_signed_type_def, type_bits_def, within_int_bound_def]
QED

Theorem linked_array_base_not_label[local]:
  expr_sim_inv_mods mods cenv cx env es /\
  type_place_target env bt = SOME vt /\
  compile_get_target_ptr compile_expr cenv bt sa = (rb,sm) ==>
  !l. FST rb <> Label l
Proof
  Cases_on `bt`
  >~ [`NameTarget id`]
  >- (simp[type_place_target_NameTarget] >> strip_tac >>
      `?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
        fs[expr_sim_inv_mods_def] >>
      gvs[compile_get_target_ptr_def, comp_return_def])
  >~ [`TopLevelNameTarget nsid`]
  >- (simp[compile_get_target_ptr_def] >> rpt strip_tac >>
      Cases_on `FLOOKUP cenv.ce_module_vars nsid` >>
      gvs[comp_return_def] >> rename1 `SOME entry` >> Cases_on `entry` >>
      gvs[comp_return_def]) >>
  strip_tac >> drule aug_place_target_ptr_not_label >> simp[]
QED

Theorem linked_array_base_operand_frame[local]:
  (!x. arg = Var x ==> not_fresh_at sm x) /\
  (!l. arg <> Label l) /\ eval_operand arg t1 = SOME b /\
  ghost_kept_at lo cenv mid1 sm G1 tn1 t1 G2 tn2 /\
  expr_post H ctx func cenv cx e mid1 sm sn t1 mid2 v iop t2 ==>
  eval_operand arg t2 = SOME b /\
  op_taint tn2 arg = op_taint tn1 arg /\ op_prov G2 arg = op_prov G1 arg
Proof
  Cases_on `arg` >>
  simp[expr_post_def, ghost_kept_at_def, op_taint_def, op_prov_def,
       eval_operand_def] >>
  metis_tac[]
QED

Theorem linked_array_base_has_word[local]:
  write_target_location_mods cenv cx bt mid1 pv vt rb G1 t1 ==>
  ?b. eval_operand (FST rb) t1 = SOME b
Proof
  Cases_on `pv`
  >~ [`PlaceR p`]
  >- (Cases_on `p` >> simp[write_target_location_mods_def] >> metis_tac[]) >>
  simp[write_target_location_mods_def] >> metis_tac[]
QED

Theorem write_array_reached_operands_mods:
  write_array_reached_mods
    ((DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func),
     (mods,exps,cenv,cx,env,bt,e,et,bd,vt),
     (st0,es,sa,s0,G0,tn0),
     (sm,sn,sb,shadow_sa,shadow_sb,rb,iop,r),
     (base_gas,mid1,pv,t1,G1,tn1),
     (index_gas,mid2,v,t2,G2,tn2)) /\
  valid_horizon cx st0 H mid2.storage_trace ==>
  is_int_type (expr_type e) /\
  (!x. FST rb = Var x ==> not_fresh_at sn x) /\
  (!x. iop = Var x ==> not_fresh_at sn x) /\
  (!l. FST rb <> Label l) /\ (!l. iop <> Label l) /\
  op_taint tn2 (FST rb) = {} /\ op_prov G2 (FST rb) = op_prov G1 (FST rb) /\
  op_taint tn2 iop = {} /\ op_prov G2 iop = NONE /\
  ?b i iw. eval_operand (FST rb) t1 = SOME b /\
    eval_operand (FST rb) t2 = SOME b /\
    v = IntV i /\ eval_operand iop t2 = SOME iw /\
    i = (if is_signed_type (expr_type e) then w2i iw else &(w2n iw))
Proof
  strip_tac >> drule_all write_array_reached_posts_mods >> strip_tac >>
  drule write_target_post_view_mods >> strip_tac >>
  qpat_x_assum `write_array_reached_mods _` mp_tac >>
  simp[write_array_reached_mods_def] >> strip_tac >>
  qpat_x_assum `!h. valid_horizon _ _ h _ ==> _`
    (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
  `is_int_type (expr_type e)` by
    gvs[type_place_target_SubscriptTarget, subscript_vtype_def, AllCaseEqs()] >>
  `is_word_type (expr_type e)` by simp[linked_array_int_word] >>
  `post_value_type cenv e = expr_type e` by simp[] >>
  `!l. FST rb <> Label l` by (drule_all linked_array_base_not_label >> simp[]) >>
  qpat_assum `expr_sim_inv_mods _ _ _ _ mid2`
    (assume_tac o MATCH_MP expr_sim_inv_mods_env) >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  `(!x. iop = Var x ==> not_fresh_at sn x) /\ (!l. iop <> Label l)` by
    (drule_then assume_tac expr_body_pre_mods_well_typed >>
     `!id ty. FLOOKUP env.var_types id = SOME ty ==>
                 well_formed_type env.type_defs ty` by
       (simp[well_formed_type_def] >> rpt strip_tac >>
        drule_all env_consistent_var_type_evaluates >> simp[]) >>
     drule_all lower_value_word_shape >> simp[]) >>
  `!x. FST rb = Var x ==> not_fresh_at sn x` by
    (rpt strip_tac >>
     qpat_assum `!x. FST rb = Var x ==> not_fresh_at sm x`
       (drule_then assume_tac) >>
     qpat_assum `ci_mono sm sn` (strip_assume_tac o REWRITE_RULE[ci_mono_def]) >>
     drule_all not_fresh_at_mono >> simp[]) >>
  `expr_post H ctx func cenv cx e mid1 sm sn t1 mid2 v iop t2` by
    fs[expr_post_mods_def] >>
  `?b. eval_operand (FST rb) t1 = SOME b` by
    (drule linked_array_base_has_word >> simp[]) >>
  drule_all linked_array_base_operand_frame >> strip_tac >>
  `expr_val_rel cx (expr_type e) v iop t2` by
    (qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[expr_post_def]) >>
  simp[] >>
  fs[target_ptr_ok_def, ptr_val_ok_def] >>
  drule_all linked_array_index_word >> simp[]
QED
