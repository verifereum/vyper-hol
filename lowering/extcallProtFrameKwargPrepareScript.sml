Theory extcallProtFrameKwargPrepare
Ancestors
  exprExtRequestDefaultProbe exprExtRequestTyping exprExtRequestRetained
  memoryLocalRhsProps exprSimHypsDefs exprSimHyps loweringPosts
  exprLoweringProps exprLowering compileEnv valueEncodingTyping exprSimProps
  vyperInterpreter vyperTypeSystem loweringStateRelDefs valueEncodingDefs

Theorem extcall_default_read_conversion:
  expr_body_pre cenv cx env e es /\ ~expr_has_effect e /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) /\
  ~is_word_type (expr_type e) /\
  ~is_word_type (lowered_value_type cenv e) /\
  evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME dtv /\
  value_has_type dtv v /\ val_wf dtv v /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME rtv ==>
  !src z. expr_val_rel cx (expr_type e) v src z ==>
    expr_val_rel cx (lowered_value_type cenv e) v src z
Proof
  strip_tac >> rpt gen_tac >>
  simp[NoAsms, expr_val_rel_def] >> strip_tac >>
  `val_in_memory rtv v (w2n w) z.vs_memory` by metis_tac[] >>
  drule_all extrequest_default_lowered_memory >> strip_tac >>
  simp[] >> metis_tac[optionTheory.SOME_11]
QED

Theorem extcall_default_read_prepare:
  expr_body_pre cenv cx env e es /\ ~expr_has_effect e /\
  expr_type e = ret /\ ~is_word_type ret /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) ==>
  ?dtv rtv.
    ~is_word_type (lowered_value_type cenv e) /\
    (lowered_value_type cenv e = ret \/
      is_bytestring_type (lowered_value_type cenv e) /\ is_bytestring_type ret) /\
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME dtv /\
    value_has_type dtv v /\ val_wf dtv v /\
    type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size dtv /\
    evaluate_type (get_tenv cx) ret = SOME rtv /\
    value_has_type rtv v /\ val_wf rtv v /\
    type_memory_size dtv < 2 ** 64 /\
    type_memory_size dtv + 64 < dimword (:256) /\
    (!src z. expr_val_rel cx (expr_type e) v src z ==>
      expr_val_rel cx (lowered_value_type cenv e) v src z)
Proof
  strip_tac >>
  `type_widens_to env.type_defs (expr_type e) ret` by
    simp[type_widens_to_def] >>
  drule_all extrequest_default_runtime_types >> strip_tac >>
  `well_typed_expr env e` by fs[expr_body_pre_def] >>
  `lowered_value_type cenv e = ret \/
    is_bytestring_type (lowered_value_type cenv e) /\ is_bytestring_type ret` by
    (drule_all extrequest_lowered_type_compatible >> metis_tac[]) >>
  `~is_word_type (lowered_value_type cenv e)` by
    (Cases_on `lowered_value_type cenv e = ret` >- metis_tac[] >>
     `is_bytestring_type (lowered_value_type cenv e)` by metis_tac[] >>
     Cases_on `lowered_value_type cenv e` >>
     gvs[is_bytestring_type_def, is_word_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[is_bytestring_type_def, is_word_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     gvs[is_bytestring_type_def, is_word_type_def]) >>
  drule_all extrequest_default_copy_capacity >> strip_tac >>
  qexistsl_tac [`dtv`, `rtv`] >> simp[] >>
  metis_tac[extcall_default_read_conversion]
QED

Theorem extcall_read_runtime_prepare:
  expr_body_pre cenv cx env e es /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee) ==>
  value_runtime_typed env (expr_type e) v /\
  ?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
    value_has_type tv v /\ val_wf tv v /\
    type_memory_bytes cenv (expr_type e) = type_memory_size tv
Proof
  strip_tac >>
  `value_runtime_typed env (expr_type e) v` by
    (drule_all memory_rhs_read_annotation_typed >> simp[]) >>
  simp[] >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  drule_all memory_rhs_runtime_layout >> strip_tac >>
  qexists_tac `tv` >> simp[] >> metis_tac[value_has_type_val_wf]
QED

Theorem extcall_materialized_retained:
  safe_operand sb op /\ expr_val_rel cx ty v op z /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes cenv ty = type_memory_size tv /\
  eval_operand op z = SOME w /\ aid < sb.cs_next_id /\
  FLOOKUP z.vs_allocas aid = SOME (w2n w,type_memory_bytes cenv ty) /\
  w2n w + val_footprint tv v <= z.vs_alloca_next /\
  (!name b len. local_region cenv ee.scopes z name b len ==>
    loweringStateRelDefs$regions_disjoint (w2n w) (type_memory_bytes cenv ty) b len) ==>
  extrequest_retained_value cenv cx ty v op ee sb z
Proof
  strip_tac >> simp[extrequest_retained_value_def] >>
  strip_tac >>
  qexistsl_tac [`aid`, `type_memory_size tv`] >> simp[] >>
  metis_tac[val_footprint_le]
QED
