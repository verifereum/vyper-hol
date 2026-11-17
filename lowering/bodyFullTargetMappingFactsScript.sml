(* Source typing and compiler boundaries for the joint mapping suffix. *)
Theory bodyFullTargetMappingFacts
Ancestors
  bodyFullTargetSubscript exprSimIfExp exprSimSource
  vyperTypeEnv vyperTypeSystem vyperInterpreter vyperState loweringPosts
  exprLowering compileEnv targetPlaceSim targetSubscriptSplit venomState

Theorem target_mapping_source_cut:
  target_pre cenv cx env (SubscriptTarget bt e) es /\
  type_place_target env bt = SOME (HashMapT kt vt) /\
  type_place_target env (SubscriptTarget bt e) = SOME et /\
  expr_sim_inv cenv cx env mid1 /\
  compile_get_target_ptr compile_expr cenv bt sa = (rb,sm) /\
  bind (eval_expr cx e) (read_result cx)
    (mid1 with gas_obs := gs) = (INL v, mid2) /\
  target_post H ctx func cenv cx es sa sm s0 mid1 pv
    (HashMapT kt vt) rb t1 /\
  expr_post H ctx func cenv cx e mid1 sm sn t1 mid2 v iop t2 ==>
  et = vt /\ expr_type e = kt /\ hashmap_key_type kt /\
  (?tv. evaluate_type (get_tenv cx) kt = SOME tv /\ value_has_type tv v) /\
  ?tr base_slot bop loc.
    pv = HashMapRef tr base_slot kt vt /\
    rb = (bop,loc,SOME (MapPT kt vt)) /\
    loc = SOME (slot_loc tr) /\
    eval_operand bop t2 = SOME base_slot
Proof
  strip_tac >>
  `et = vt /\ expr_type e = kt /\ hashmap_key_type kt` by
    gvs[type_place_target_SubscriptTarget, subscript_vtype_def, AllCaseEqs()] >>
  simp[] >>
  `expr_body_pre cenv cx env e (mid1 with gas_obs := gs)` by
    gvs[target_pre_def, target_indices_pre_def] >>
  `?tv. evaluate_type (get_tenv cx) kt = SOME tv /\ value_has_type tv v` by
    metis_tac[ifexp_body_pre_read_typed] >>
  simp[] >>
  `!l. FST rb <> Label l` by
    metis_tac[target_subscript_typed_base_not_label] >>
  PairCases_on `rb` >> Cases_on `pv` >>
  gvs[target_post_def, place_ptr_rel_def, value_type_place_def] >>
  TRY (rename1 `PlaceR p` >> Cases_on `p` >>
       gvs[place_ptr_rel_def] >> NO_TAC) >>
  gvs[expr_post_def] >>
  Cases_on `rb0` >> gvs[eval_operand_def]
QED

Theorem target_mapping_compile_cut:
  compile_get_target_ptr cfn ce bt sa = ((bop,loc,SOME (MapPT kt vt)),sm) /\
  lower_value cfn ce (expr_type e) e sm = (iop,sn) /\
  compile_get_target_ptr cfn ce (SubscriptTarget bt e) sa = (r,sb) ==>
  ?hashed sp slot.
    (if is_bytestring_type kt then compile_keccak256_key iop F sn
     else (iop,sn)) = (hashed,sp) /\
    compile_mapping_subscript bop hashed sp = (slot,sb) /\
    r = (slot,loc,SOME (value_type_place vt))
Proof
  strip_tac >>
  qpat_x_assum `compile_get_target_ptr _ _ (SubscriptTarget _ _) _ = _`
    (mp_tac o PURE_ONCE_REWRITE_RULE [compile_get_target_ptr_def]) >>
  simp[comp_bind_def, comp_return_def, LET_THM] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  Cases_on `is_bytestring_type kt` >> gvs[comp_return_def] >> metis_tac[]
QED
