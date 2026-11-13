(* Resource-preserving backend endings for the loaded AugAssign suffix. *)
Theory bodyIntCallFamStmtMutationAugPlaceSuffix
Ancestors
  bodyIntCallFamStmtMutationAugMemoryStore
  bodyIntCallFamStmtMutationAugStorageStore
  bodyIntCallFamStmtMutationBinopCont stmtSimAugAssignPlaceMemory
  bodyIntCallJointContract compileEnv exprLoweringProps emitHelperProps
  loweringShapeDefs venomState
  bodyIntCallFamStmtMutationAugPlaceMemorySuffix
  bodyIntCallFamStmtMutationAugPlaceStorageSuffix
  bodyIntCallFamStmtMutationAugPlaceSourceLanding
  exprSimHypsDefs vyperInterpreter vyperState

Theorem intcall_aug_memory_store_cont:
  intcall_frame_ok fp /\
  intcall_expr_cont fp ce env es sa s es sb u /\
  gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
  ce_locals_declared ce env /\ local_ptrs_reserved ce sa /\
  emit_void MSTORE [dst;op] sb = ((),sc) /\
  fn_has_code sb sc fp.jc_func /\
  eval_operand dst s = SOME w /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand op u = SOME (typed_val_to_w256 tv v) /\
  place_ptr_rel ce fp.jc_cx s (PlaceR (MemoryPlace id path)) w
    (SOME LocMemory) (Type ty) /\
  is_word_type ty /\ evaluate_type (get_tenv fp.jc_cx) ty = SOME tv /\
  value_has_type tv v /\
  write_place fp.jc_cx (MemoryPlace id path) v es = (INL (),ee) /\
  expr_sim_inv ce fp.jc_cx env ee ==>
  ?t. gas_marked_path F fp.jc_ctx fp.jc_func u 0 (OK t) /\
      intcall_joint_res fp ce env ee sc t /\
      ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
      t.vs_inst_idx = LENGTH sc.cs_current_insts /\
      (!x. lookup_var x t = lookup_var x u) /\
      t.vs_allocas = u.vs_allocas /\ t.vs_alloca_next = u.vs_alloca_next
Proof
  strip_tac >>
  `intcall_joint_res fp ce env es sb u` by
    fs[intcall_expr_cont_def,intcall_joint_res_def] >>
  `local_ptrs_reserved ce sb` by
    fs[intcall_expr_cont_def,intcall_expr_res_def] >>
  `place_ptr_rel ce fp.jc_cx u (PlaceR (MemoryPlace id path)) w
     (SOME LocMemory) (Type ty)` by
    (irule aug_place_memory_ptr_frame >>
     fs[intcall_expr_cont_def] >> metis_tac[]) >>
  `eval_operand dst u = SOME w` by
    (irule aug_place_saved_operand >>
     fs[intcall_expr_cont_def] >> metis_tac[]) >>
  `(!entry t0. lookup_scopes id es.scopes = SOME entry /\
      ce.ce_var_type id = SOME t0 ==>
      evaluate_type (get_tenv fp.jc_cx) t0 = SOME entry.type)` by
    (fs[intcall_expr_cont_def,intcall_expr_res_def] >>
     metis_tac[aug_place_store_entry_types]) >>
  `sb.cs_next_var = sc.cs_next_var` by metis_tac[emitted_insts_emit_void] >>
  `local_ptrs_reserved ce sc` by
    (irule local_ptrs_reserved_next_var >> qexists `sb` >> simp[]) >>
  `!x. not_fresh_at sb x ==> not_fresh_at sc x` by
    simp[loweringStateRelDefsTheory.not_fresh_at_def] >>
  drule intcall_memory_place_word_store_path >>
  fs[intcall_expr_cont_def] >> disch_then drule_all >> simp[]
QED

Theorem intcall_aug_storage_store_cont:
  intcall_frame_ok fp /\
  intcall_expr_cont fp ce env es sa s es sb u /\
  gas_marked_path F fp.jc_ctx fp.jc_func s 0 (OK u) /\
  ce_locals_declared ce env /\
  emit_void (if tr then TSTORE else SSTORE) [dst;op] sb = ((),sc) /\
  fn_has_code sb sc fp.jc_func /\
  eval_operand dst s = SOME slot /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand op u = SOME (typed_val_to_w256 tv v) /\
  storage_place_region fp.jc_cx (StoragePlace tr slot tv) /\
  is_word_type ty /\ evaluate_type (get_tenv fp.jc_cx) ty = SOME tv /\
  value_has_type tv v /\ ~u.vs_call_ctx.cc_static /\
  write_place fp.jc_cx (StoragePlace tr slot tv) v es = (INL (),ee) /\
  expr_sim_inv ce fp.jc_cx env ee ==>
  ?t. gas_marked_path F fp.jc_ctx fp.jc_func u 0 (OK t) /\
      intcall_joint_res fp ce env ee sc t /\
      ~t.vs_halted /\ t.vs_current_bb = sc.cs_current_bb /\
      t.vs_inst_idx = LENGTH sc.cs_current_insts /\
      (!x. lookup_var x t = lookup_var x u) /\
      t.vs_memory = u.vs_memory /\ t.vs_allocas = u.vs_allocas /\
      t.vs_alloca_next = u.vs_alloca_next
Proof
  strip_tac >>
  `intcall_joint_res fp ce env es sb u` by
    fs[intcall_expr_cont_def,intcall_joint_res_def] >>
  `locals_alloc_ok ce env` by
    fs[intcall_expr_cont_def,intcall_expr_res_def] >>
  `eval_operand dst u = SOME slot` by
    (irule aug_place_saved_operand >>
     fs[intcall_expr_cont_def] >> metis_tac[]) >>
  drule intcall_storage_place_word_store_path >>
  fs[intcall_expr_cont_def] >> disch_then drule_all >> simp[]
QED

(* Replay only the successful source prefix; this is backend-independent. *)
Theorem intcall_aug_place_source_replay_landing:
  supported_program tops /\ get_module_code cx NONE = SOME tops /\
  supported_stmt tops bindings (AugAssign ty bt bop e) /\
  expr_sim_inv ce cx env es /\ ce.ce_alloca_locals /\
  type_stmt env ret_ty (AugAssign ty bt bop e) = SOME env /\
  call_evaluation_safe cx (int_calls_stmt (AugAssign ty bt bop e)) /\
  eval_target_place cx bt (es with gas_obs := gs) = (INL p,mid) /\
  read_place cx p mid = (INL cur,mid) /\
  place_type_value cx p mid = (INL ptv,mid) /\
  bind (eval_expr cx e) (read_result cx) mid = (INL rhs,ee) /\
  evaluate_binop
    (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
    ptv bop cur rhs = INL v /\
  write_place cx p v ee = (INL (),ff) ==>
  expr_sim_inv ce cx env ff
Proof
  strip_tac >>
  `eval_stmt cx (AugAssign ty bt bop e) (es with gas_obs := gs) = (INL (),ff)` by
    (simp[Once evaluate_def,bind_def,lift_sum_def,return_def] >>
     qpat_x_assum `bind _ _ mid = _` mp_tac >>
     simp[bind_def] >> strip_tac >>
     gvs[AllCaseEqs(),lift_sum_def,return_def]) >>
  `expr_sim_inv ce cx env (es with gas_obs := gs)` by simp[] >>
  drule_all intcall_aug_place_source_landing >> simp[]
QED
