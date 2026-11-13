Theory exprSimIfExpWidenedArm
Ancestors
  exprSimIfExpWidenedNormalize exprSimIfExpWidenedNoCopy
  exprSimIfExpWidenedAggregate exprSimIfExpCompat exprSimUnwrapProps
  exprSimHyps exprSimHypsDefs exprSimProps exprLowering compileEnv
  loweringPosts vyperAST vyperState context fragExec exprSimUnwrap

Theorem punnable_reflexive:
  (!t. punnable ce t t) /\ (!ts. punnable_list ce ts ts)
Proof
  ho_match_mp_tac (legacyInduction.mutual_ind_from_ops type_induction) >>
  simp[punnable_def]
QED

Theorem aggregate_widen_source:
  type_widens_to tenv st dt /\ ~is_word_type dt /\ ~is_bytestring_type dt ==>
  ~is_word_type st /\ ~is_bytestring_type st
Proof
  Cases_on `st` >> Cases_on `dt` >>
  simp[vyperTypeSystemTheory.type_widens_to_def,
    vyperTypeSystemTheory.arg_type_fits_def, is_word_type_def,
    is_bytestring_type_def] >>
  rename1 `arg_type_fits (BaseT x) (BaseT y)` >>
  Cases_on `x` >> Cases_on `y` >>
  gvs[vyperTypeSystemTheory.arg_type_fits_def, is_word_type_def,
    is_bytestring_type_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  gvs[vyperTypeSystemTheory.arg_type_fits_def, is_word_type_def,
    is_bytestring_type_def] >>
  Cases_on `b'` >>
  gvs[vyperTypeSystemTheory.arg_type_fits_def, is_word_type_def,
    is_bytestring_type_def, vyperValueTheory.compatible_bound_def] >> metis_tac[]
QED

Theorem compile_selected_ifexp_post_frag:
  (~expr_has_effect (IfExp (expr_type e) c a b) ==> ~expr_has_effect e) /\
  expr_body_pre ce cx env e es /\
  eval_expr cx e es = (INL tvv,ee) /\
  read_result cx tvv ee = (INL v,ee) /\
  compile_expr ce ty e sc = (vv,sa) /\
  compile_ifexp_arm ce (expr_type e) (lowered_value_type ce e) vv sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sc /\ local_ptrs_reserved ce origin /\
  local_ptrs_reserved ce sa /\ local_ptrs_rel func ce es.scopes s0 /\
  origin.cs_next_var <= sa.cs_next_var /\ origin.cs_next_id <= sa.cs_next_id /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  acyclic_struct_metadata ce.ce_struct_fields ==>
  frag_exec ctx sa sb
    (\s. vv_post ctx func ce cx e es origin sa s0 ee tvv vv s)
    (\q. expr_post ctx func ce cx (IfExp (expr_type e) c a b)
      es origin sb s0 ee v op q) R
Proof
  strip_tac >>
  Cases_on `is_word_type (expr_type e) \/
    same_memory_layout ce (lowered_value_type ce e) (expr_type e)`
  >- (irule compile_nocopy_ifexp_post_frag >> metis_tac[]) >>
  fs[] >> Cases_on `is_bytestring_type (expr_type e)`
  >- (irule compile_bytes_ifexp_post_frag >> simp[] >> metis_tac[]) >>
  `lowered_value_type ce e <> expr_type e` by
    (strip_tac >> fs[same_memory_layout_def, punnable_reflexive]) >>
  `?ann fid args drv. e = Call ann (IntCall fid) args drv` by
    (drule exprSimSourceTheory.expr_body_pre_var_types_well_formed >> disch_then assume_tac >>
     qspecl_then [`ce`, `e`, `env`] mp_tac ifexp_lowered_type_classify >>
     (impl_tac >- (gvs[expr_body_pre_def, expr_sim_inv_def,
       vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def] >> metis_tac[])) >> metis_tac[]) >>
  suspend "aggregate"
QED

Resume compile_selected_ifexp_post_frag[aggregate]:
  markerLib.RESUME_TAC >>
  `post_value_type ce e = lowered_value_type ce e /\
   type_widens_to (get_tenv cx) (lowered_value_type ce e) (expr_type e)` by
    (gvs[vyperASTTheory.expr_type_def] >>
     drule_all ifexp_intcall_copy_source >> simp[]) >>
  `~is_word_type (post_value_type ce e) /\
   ~is_bytestring_type (post_value_type ce e)` by
    (irule aggregate_widen_source >> metis_tac[]) >>
  `(do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee)` by
    simp[ignore_bind_def, bind_def] >>
  `post_value_type ce e <> expr_type e` by metis_tac[] >>
  drule_all (SIMP_RULE (srw_ss()) [] compile_changed_aggregate_post_frag) >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  qpat_x_assum `frag_exec _ _ _ _ _ _`
    (mp_then Any mp_tac frag_exec_conseq) >>
  disch_then irule >> simp[] >>
  qx_gen_tac `s` >> strip_tac >>
  `?t op'. vv = StackValue t op' \/
     ?p. vv = LocatedValue t p /\ p.ptr_location = LocMemory` by
    (qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
     gvs[] >>
     simp[Once compile_expr_raw_def, compile_expr_body_def, expr_type_def,
       compile_call_def] >>
     rpt (pairarg_tac >> gvs[]) >> rpt IF_CASES_TAC >>
     rpt (pairarg_tac >> gvs[]) >>
     Cases_on `return_buf` >> gvs[] >>
     rpt (pairarg_tac >> gvs[]) >> strip_tac >>
     gvs[base_ptr_def] >> metis_tac[])
  >- (gvs[unwrap_value_def, comp_return_def] >>
      drule_all vv_post_read_result >> strip_tac >>
      irule expr_post_of_vv_post_stack >> goal_assum drule) >>
  `t = post_value_type ce e` by
    (gvs[] >> fs[vv_post_def, vv_holds_def] >> gvs[]) >>
  gvs[unwrap_value_def, comp_return_def] >>
  drule_all vv_post_read_result >> strip_tac >>
  irule expr_post_of_vv_post_memory >> metis_tac[]
QED

Finalise compile_selected_ifexp_post_frag
