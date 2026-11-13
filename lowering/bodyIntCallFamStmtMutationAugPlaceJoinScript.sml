(* Backend-independent counted continuation from a loaded mutable place. *)
Theory bodyIntCallFamStmtMutationAugPlaceJoin
Ancestors
  bodyIntCallFamStmtMutationAugPlaceMemoryJoin
  bodyIntCallFamStmtMutationAugPlaceStorageJoin
  bodyIntCallJointContract

Theorem intcall_aug_place_suffix_outcome:
  intcall_forced_producer fp e /\ intcall_frame_ok fp /\
  body_inv fp.jc_tops fp.jc_ctx ce fp.jc_cx /\
  supported_program fp.jc_tops /\
  get_module_code fp.jc_cx NONE = SOME fp.jc_tops /\
  supported_stmt fp.jc_tops bindings (AugAssign ty bt bop e) /\
  supported_target_info fp.jc_tops bindings bt = SOME info /\
  supportedExprs$supported_expr fp.jc_tops e /\
  calls_follow_call_graph fp.jc_edges fp.jc_owner (int_calls_expr e) /\
  call_evaluation_safe fp.jc_cx (int_calls_stmt (AugAssign ty bt bop e)) /\
  type_stmt env ret_ty (AugAssign ty bt bop e) = SOME env /\
  expr_sim_inv ce fp.jc_cx env es /\ ce.ce_alloca_locals /\
  ce_locals_declared ce env /\ expr_body_pre ce fp.jc_cx env e mid /\
  (!tail. eval_target_place fp.jc_cx bt (es with gas_obs := prefix ++ tail) =
    (INL p,mid with gas_obs := tail)) /\
  gas_admissible (eval_stmt fp.jc_cx (AugAssign ty bt bop e)) (stmt_res_ok lctx) es /\
  read_place fp.jc_cx p mid = (INL old,mid) /\
  place_type_value fp.jc_cx p mid = (INL tv,mid) /\
  evaluate_type (get_tenv fp.jc_cx) ty = SOME tv /\ value_has_type tv old /\
  type_bits ty MOD 8 = 0 /\ word_value_type ty /\ word_value_type (expr_type e) /\
  IS_SOME (evaluate_type (get_tenv fp.jc_cx) (expr_type e)) /\
  lower_value compile_expr ce ty e sl = (rhsop,s2) /\
  compile_binop bop cur rhsop ty NONE
    (if bop = Exp then expr_int_literal e else NONE) s2 = (result,s3) /\
  fn_has_code sl s2 fp.jc_func /\ fn_has_code s2 s3 fp.jc_func /\
  fn_has_code s3 sf fp.jc_func /\ fn_inst_ids_distinct fp.jc_func /\
  (!z. cur = Var z ==> not_fresh_at sl z) /\
  (!z. dst = Var z ==> not_fresh_at sl z) /\
  (!z. not_fresh_at sl z ==> not_fresh_at s2 z) /\
  eval_operand cur u = SOME (typed_val_to_w256 tv old) /\
  eval_operand dst u = SOME w /\
  place_ptr_rel ce fp.jc_cx u (PlaceR p) w (SOME loc) (Type ty) /\
  intcall_expr_res fp ce env mid sl u /\
  ~u.vs_halted /\ u.vs_current_bb = sl.cs_current_bb /\
  u.vs_inst_idx = LENGTH sl.cs_current_insts /\
  (case p of
     MemoryPlace id path => loc = LocMemory /\ emit_void MSTORE [dst;result] s3 = ((),sf)
   | StoragePlace tr slot ptv => loc = slot_loc tr /\ w = slot /\ tv = ptv /\
       storage_place_region fp.jc_cx p /\ ~fp.jc_cx.txn.is_static /\
       emit_void (if tr then TSTORE else SSTORE) [dst;result] s3 = ((),sf)
   | ImmutablePlace src id path => F) ==>
  gas_outcome F (cx_tops fp.jc_cx) (fp.jc_ctx,fp.jc_func)
    (bind (bind (eval_expr fp.jc_cx e) (read_result fp.jc_cx))
      (\rhs. bind (lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        tv bop old rhs)) (write_place fp.jc_cx p))) (mid,u)
    (\res ff t. res = INL () /\ intcall_joint_res fp ce env ff sf t /\
      ~t.vs_halted /\ t.vs_current_bb = sf.cs_current_bb /\
      t.vs_inst_idx = LENGTH sf.cs_current_insts /\
      (!z v. not_fresh_at sl z /\ lookup_var z u = SOME v ==> lookup_var z t = SOME v) /\
      (!aid b. FLOOKUP u.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
      u.vs_alloca_next <= t.vs_alloca_next)
    (\res ff r. intcall_stmt_exit fp res ff r)
Proof
  Cases_on `p` >> simp[] >> strip_tac >> gvs[]
  >- (drule_all intcall_aug_place_storage_outcome >> simp[])
  >> drule_all intcall_aug_place_memory_outcome >> simp[]
QED
