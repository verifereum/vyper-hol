(* Word forcing is independent of the compiler that produced its input. *)
Theory assignBasePtrFieldForce
Ancestors exprPtrUnwrapMarked exprPtrUnwrapIdentity exprPtrUnwrapLoad
  exprPtrUnwrapStorage exprPtrUnwrapCode bodyPtrDefs loweringPosts
  compileEnv context

Theorem assign_base_word_unwrap_marked_read_ptr:
  unwrap_value cenv vv sm = (op,sb) /\ is_word_type (expr_type e) /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sm.cs_next_var /\
  fn_has_code sm sb func /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME rty /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
  vv_post ctx func cenv cx e es sa sm s0 ee tv vv s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ghost_inv d cenv cx ee G tn s /\
  ptr_vv_ok cx (expr_type e) tv vv ee G tn s /\
  ghost_kept cenv es sa Gi ti s0 G tn /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ?v H tf z.
    gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG (read_result cx tv)
      (ee,s,G,tn) [] (INL v) ee H tf (OK z) /\
    expr_post ctx func cenv cx e es sa sb s0 ee v op z /\
    z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ghost_inv d cenv cx ee H tf z /\
    ptr_val_ok cx (expr_type e) v op H tf z /\
    (~is_word_type (expr_type e) ==> ptr_buf_ok cenv e op H z) /\
    ghost_kept cenv es sa Gi ti s0 H tf
Proof
  strip_tac >> Cases_on `vv`
  >- (irule unwrap_stack_marked_read_ptr >> simp[] >>
      goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[]) >>
  rename1 `LocatedValue t p` >>
  `t = expr_type e` by metis_tac[vv_post_located_type] >>
  `p.ptr_location <> LocCalldata` by metis_tac[vv_post_not_calldata] >>
  Cases_on `p.ptr_location = LocStorage \/ p.ptr_location = LocTransient`
  >- (`?tr. p.ptr_location = slot_loc tr` by
        (simp[slot_loc_def] >> metis_tac[]) >> pop_assum strip_assume_tac >>
      irule unwrap_storage_word_marked_read_ptr >> simp[] >>
      goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      qexists_tac `tr` >> simp[]) >>
  Cases_on `p.ptr_location`
  >- (irule unwrap_memory_word_marked_read_ptr >> simp[] >>
      goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[])
  >- gvs[]
  >- gvs[]
  >- (irule unwrap_code_word_marked_read_ptr >> simp[] >>
      goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[])
  >> gvs[]
QED
