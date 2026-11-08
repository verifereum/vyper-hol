(* Compiler-indexed dispatch for pointer-safe forcing; location inversion stays here. *)
Theory exprPtrUnwrapMarked
Ancestors
  exprPtrUnwrapIdentity exprPtrUnwrapLoad exprPtrUnwrapStorage
  exprPtrUnwrapStorageMarked exprPtrUnwrapCode exprPtrUnwrapCodeCopyMarked
  exprPtrUnwrapStorageShape exprPtrUnwrapStorageSource
  bodyPtrDefs loweringPosts compileEnv context

Theorem vv_post_located_type:
  vv_post ctx func cenv cx e es sa sm s0 ee tv (LocatedValue t p) s ==>
  t = expr_type e
Proof
  simp[vv_post_def, vv_holds_def]
QED

Theorem vv_post_not_calldata:
  vv_post ctx func cenv cx e es sa sm s0 ee tv (LocatedValue t p) s ==>
  p.ptr_location <> LocCalldata
Proof
  simp[vv_post_def, vv_holds_def] >> rpt strip_tac >> gvs[]
QED

Theorem vv_post_slot_input[local]:
  vv_post ctx func cenv cx e es sa sm s0 ee tv (LocatedValue t p) s /\
  p.ptr_location = slot_loc tr /\
  ptr_vv_ok cx (expr_type e) tv (LocatedValue t p) ee G tn s ==>
  ?w. eval_operand p.ptr_operand s = SOME w /\
    storage_holds cx tr (expr_type e) tv w ee s /\
    op_taint tn p.ptr_operand = {}
Proof
  Cases_on `tr` >> strip_tac >>
  fs[slot_loc_def, vv_post_def, vv_holds_def, ptr_vv_ok_def] >>
  metis_tac[]
QED

Theorem unwrap_value_marked_read_ptr:
  compile_expr cenv ty e sa = (vv,sm) /\
  unwrap_value cenv vv sm = (op,sb) /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!rt. evaluate_type (get_tenv cx) (expr_type e) = SOME rt /\
    ~is_word_type (expr_type e) ==>
    type_memory_bytes cenv (expr_type e) = type_memory_size rt /\
    type_memory_size rt < 2**64) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME rty /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type rty v) /\
  vv_post ctx func cenv cx e es sa sm s0 ee tv vv s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  ghost_inv d cenv cx ee G tn s /\
  ptr_vv_ok cx (expr_type e) tv vv ee G tn s /\
  (!t op0. vv = StackValue t op0 /\ ~is_word_type (expr_type e) ==>
    ptr_buf_ok cenv e op0 G s) /\
  (!t p. vv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok cenv e p.ptr_operand G s) /\
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
  >- suspend "slot" >>
  Cases_on `p.ptr_location`
  >- (Cases_on `is_word_type t`
      >- suspend "memory_word"
      >> suspend "memory_aggregate")
  >- gvs[]
  >- gvs[]
  >- suspend "code"
  >> gvs[]
QED

Resume unwrap_value_marked_read_ptr[memory_word]:
  irule unwrap_memory_word_marked_read_ptr >> simp[] >>
  goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[]
QED

Resume unwrap_value_marked_read_ptr[memory_aggregate]:
  irule unwrap_memory_marked_read_ptr >> simp[] >>
  goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[]
QED

Resume unwrap_value_marked_read_ptr[slot]:
  `?tr. p.ptr_location = slot_loc tr` by
    (simp[slot_loc_def] >> metis_tac[]) >>
  pop_assum strip_assume_tac >>
  Cases_on `is_word_type t`
  >- (irule unwrap_storage_word_marked_read_ptr >> simp[] >>
      goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      qexists `tr` >> simp[]) >>
  `lowered_value_type cenv e = expr_type e` by
    (drule compile_nonmemory_lowered_value_type >> simp[slot_loc_def] >>
     disch_then irule >> Cases_on `tr` >> gvs[slot_loc_def]) >>
  drule_all vv_post_slot_input >> strip_tac >>
  gvs[vv_operand_def] >>
  irule unwrap_storage_marked_read_ptr >> simp[] >>
  goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `storage_holds _ _ _ _ _ _ _`)) >> simp[]
QED
Resume unwrap_value_marked_read_ptr[code]:
  Cases_on `is_word_type t`
  >- (irule unwrap_code_word_marked_read_ptr >> simp[] >>
      goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[]) >>
  `lowered_value_type cenv e = expr_type e` by
    (drule compile_nonmemory_lowered_value_type >> simp[] >> disch_then irule >> simp[]) >>
  gvs[vv_operand_def] >>
  irule unwrap_code_marked_read_ptr >> simp[] >>
  goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[]
QED
Finalise unwrap_value_marked_read_ptr
