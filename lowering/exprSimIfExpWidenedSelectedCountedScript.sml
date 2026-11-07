Theory exprSimIfExpWidenedSelectedCounted
Ancestors
  exprSimIfExpWidenedArmCounted exprSimIfExpWidenedSource
  exprSimIfExpWidenedCounted exprSimUnwrap exprOperandVar
  exprSimIfExpWidenedArm exprSimIfExpCompat exprSimUnwrapProps
  exprSimSource exprSimProps exprSimHyps exprSimHypsDefs exprLoweringProps
  exprLowering compileEnv loweringPosts vyperAST vyperState context fragGasMode

Theorem compile_selected_ifexp_post_path:
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
  acyclic_struct_metadata ce.ce_struct_fields /\
  vv_post ctx func ce cx e es origin sa s0 ee tvv vv s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  (!tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
    type_memory_bytes ce (expr_type e) = type_memory_size tv /\
    type_memory_size tv < dimword (:256)) ==>
  ?q. gas_marked_path F ctx func s 0 (OK q) /\
    expr_post ctx func ce cx (IfExp (expr_type e) c a b)
      es origin sb s0 ee v op q /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  Cases_on `is_word_type (expr_type e) \/
    same_memory_layout ce (lowered_value_type ce e) (expr_type e)`
  >- (irule compile_nocopy_ifexp_post_path >> metis_tac[]) >>
  fs[] >> Cases_on `is_bytestring_type (expr_type e)`
  >- (irule compile_bytes_ifexp_post_path >> metis_tac[]) >>
  `lowered_value_type ce e <> expr_type e` by
    (strip_tac >> fs[same_memory_layout_def, punnable_reflexive]) >>
  `?ann fid args drv. e = Call ann (IntCall fid) args drv` by
    (drule expr_body_pre_var_types_well_formed >> disch_then assume_tac >>
     qspecl_then [`ce`, `e`, `env`] mp_tac ifexp_lowered_type_classify >>
     (impl_tac >- (gvs[expr_body_pre_def, expr_sim_inv_def,
       vyperTypeInvariantsTheory.env_consistent_def,
       vyperTypeInvariantsTheory.env_context_consistent_def] >> metis_tac[])) >> metis_tac[]) >>
  `post_value_type ce e = lowered_value_type ce e /\
   type_widens_to (get_tenv cx) (lowered_value_type ce e) (expr_type e)` by
    (gvs[vyperASTTheory.expr_type_def] >>
     drule_all ifexp_intcall_copy_source >> simp[]) >>
  `~is_word_type (post_value_type ce e) /\
   ~is_bytestring_type (post_value_type ce e)` by
    (irule aggregate_widen_source >> metis_tac[]) >>
  `post_value_type ce e <> expr_type e` by metis_tac[] >>
  `(do r <- eval_expr cx e; read_result cx r od) es = (INL v,ee)` by
    simp[ignore_bind_def, bind_def] >>
  `?src. expr_post ctx func ce cx e es origin sa s0 ee v src s /\
    (!st. unwrap_value ce vv st = (src,st)) /\
    (!x. src = Var x ==> not_fresh_at sa x)` by
    (drule_all compile_changed_physical_unwrap_shape >> strip_tac >>
     drule_all vv_post_read_result >> disch_then (fs o single) >>
     gvs[]
     >- (qexists_tac `op'` >>
         simp[unwrap_value_def, comp_return_def] >> conj_tac
         >- (irule expr_post_of_vv_post_stack >> goal_assum drule) >>
         metis_tac[cj 1 compiler_compile_var, vv_operand_def]) >>
     qexists_tac `p.ptr_operand` >>
     simp[unwrap_value_def, comp_return_def] >> conj_tac
     >- (irule expr_post_of_vv_post_memory >> metis_tac[]) >>
     metis_tac[cj 1 compiler_compile_var, vv_operand_def]) >>
  qpat_x_assum `e = Call _ _ _ _` kall_tac >>
  qpat_x_assum `compile_ifexp_arm _ _ _ _ _ = _` mp_tac >>
  simp[compile_ifexp_arm_def, comp_bind_def] >>
  pairarg_tac >> simp[comp_bind_def] >>
  simp[compile_store_memory_def, comp_ignore_bind_def, comp_bind_def] >>
  pairarg_tac >> simp[comp_return_def] >> strip_tac >>
  gvs[] >> irule changed_aggregate_post_path >> metis_tac[]
QED
