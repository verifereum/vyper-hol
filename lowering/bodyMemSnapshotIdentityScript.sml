(* Identity unwrapping retains both actual-value and lowered-type room. *)
Theory bodyMemSnapshotIdentity
Ancestors
  exprSimMemDefs exprSimUnwrap exprSimUnwrapProps loweringPosts
  exprLowering context compileEnv fragGasPathMem valueCopyBytes
  vyperInterpreter vyperState

Theorem snapshot_identity_unwrap_mem:
  !ctx func cenv cx e es sa sm sb s0 ee tv v vv op s.
    post_value_type cenv e = expr_type e /\
    ~is_word_type (expr_type e) /\
    ~is_word_type (lowered_value_type cenv e) /\
    (!t p. vv = LocatedValue t p ==> p.ptr_location = LocMemory) /\
    unwrap_value cenv (vv_with_type (lowered_value_type cenv e) vv) sm =
      (op,sb) /\
    read_result cx tv ee = (INL v,ee) /\
    vv_post ctx func cenv cx e es sa sm s0 ee tv vv s /\
    vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv s /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    sb = sm /\ op = vv_operand vv /\
    gas_path_mem ctx func s 0 (OK s) /\
    expr_post ctx func cenv cx e es sa sb s0 ee v op s /\
    expr_store_bound cx (expr_type e) v op s /\
    (!sw tvt. eval_operand op s = SOME sw /\
       evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tvt ==>
       type_memory_size tvt = 0 \/
       w2n sw + type_memory_size tvt <= s.vs_alloca_next) /\
    pure_frame cenv func ee sm s s /\
    s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >>
  drule_all vv_post_read_result >> strip_tac >>
  Cases_on `vv`
  >- (gvs[vv_with_type_def, unwrap_value_def, comp_return_def,
          vv_operand_def, vv_location_def] >>
      simp[cj 1 gas_path_mem_rules] >>
      conj_tac >- metis_tac[expr_post_of_vv_post_stack] >>
      qpat_x_assum `vv_store_bound _ _ _ _ _ _ _` mp_tac >>
      simp[vv_store_bound_def, expr_store_bound_def] >> metis_tac[]) >>
  rename1 `LocatedValue t p` >>
  gvs[vv_location_def] >>
  `~is_word_type t` by
    (gvs[vv_post_def, vv_holds_def] >> metis_tac[is_bytestring_word_type]) >>
  gvs[vv_with_type_def, unwrap_value_def, comp_return_def, vv_operand_def] >>
  simp[cj 1 gas_path_mem_rules] >>
  conj_tac >- metis_tac[expr_post_of_vv_post_memory] >>
  qpat_x_assum `vv_store_bound _ _ _ _ _ _ _` mp_tac >>
  simp[vv_store_bound_def, expr_store_bound_def] >> metis_tac[]
QED
