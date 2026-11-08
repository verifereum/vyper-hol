Theory bodyPtrIfExpOldUnwrapPath
Ancestors bodyPtrIfExpUnwrapContract bodyPtrIfExpNoopPost
  bodyPtrIfExpOldRuntimeMaterialize bodyPtrIfExpOldStorageMaterialize
  bodyPtrIfExpMaterializedPost bodyPtrIfExpBytesEndpoint
  bodyPtrDefs exprSimProps context compileEnv loweringPosts fragGasPathPtr
  exprLowering exprSimUnwrap valueEncodingTyping vyperState venomState finite_map words arithmetic
  copyExecution exprSimCopy

Theorem ifexp_old_unwrap_nonword_path_capacity:
  post_value_type ce e = expr_type e /\
  ~is_word_type (expr_type e) /\ ~ce.ce_is_ctor /\
  expr_body_pre ce cx env e es /\ eval_expr cx e es = (INL raw,ee) /\
  read_result cx raw ee = (INL v,ee) /\ unwrap_value ce vv sm = (op,sb) /\
  stmt_state_rel ctx fn ce cx es s0 /\
  vv_post ctx fn ce cx e es sa sm s0 ee raw vv s /\
  ptr_vv_ok cx (expr_type e) raw vv ee G tn s /\
  (!ty src. vv = StackValue ty src ==> ptr_buf_ok ce e src G s) /\
  (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand G s) /\
  ghost_inv rty ce cx ee G tn s /\ ghost_kept ce es sa G0 tn0 s0 G tn /\
  local_ptrs_reserved ce sa /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  fn_has_code sm sb fn /\ fn_inst_ids_distinct fn /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!ty. evaluate_type (get_tenv cx) (expr_type e) = SOME ty ==>
    type_memory_bytes ce (expr_type e) = type_memory_size ty /\
    type_memory_size ty < 2**64) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t H tt. gas_path_ptr D 0 ctx fn PG G tn s 0 H tt (OK t) /\
    expr_post ctx fn ce cx e es sa sb s0 ee v op t /\
    ptr_val_ok cx (expr_type e) v op H tt t /\
    ghost_inv rty ce cx ee H tt t /\ ghost_kept ce es sa G0 tn0 s0 H tt /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (same_memory_layout ce (lowered_value_type ce e) (expr_type e) ==>
      !w. eval_operand op t = SOME w /\ type_memory_bytes ce (expr_type e) <> 0 ==>
      ?x b sz. op = Var x /\ FLOOKUP H x = SOME (b,sz) /\ b <= w2n w /\
        w2n w + type_memory_bytes ce (expr_type e) <= b+sz)
Proof
  strip_tac >> Cases_on `vv`
  >- suspend "stack" >>
  rename1 `LocatedValue tag pp` >>
  `~is_word_type tag` by
    metis_tac[exprPtrUnwrapMarkedTheory.vv_post_located_type,
              valueCopyBytesTheory.is_bytestring_word_type] >>
  `pp.ptr_location <> LocCalldata` by metis_tac[vv_post_calldata] >>
  `copy_old_operand sm pp.ptr_operand` by
    fs[copy_old_operand_def, vv_operand_def] >>
  Cases_on `pp.ptr_location = LocMemory`
  >- suspend "memory" >>
  `tag = expr_type e` by
    metis_tac[exprPtrUnwrapMarkedTheory.vv_post_located_type] >>
  Cases_on `pp.ptr_location = LocCode`
  >- suspend "runtime" >>
  suspend "storage"
QED

Resume ifexp_old_unwrap_nonword_path_capacity[stack]:
  drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`) unwrap_value_noop_post >>
  disch_then (qspecl_then [`v`, `tn`, `sb`, `op`, `G`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  qexistsl_tac [`s`, `G`, `tn`] >> simp[] >>
  conj_tac >- (irule (cj 1 gas_path_ptr_rules) >> simp[]) >>
  metis_tac[ifexp_noop_annotation_capacity]
QED

Resume ifexp_old_unwrap_nonword_path_capacity[memory]:
  drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`) unwrap_value_noop_post >>
  disch_then (qspecl_then [`v`, `tn`, `sb`, `op`, `G`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  qexistsl_tac [`s`, `G`, `tn`] >> simp[] >>
  conj_tac >- (irule (cj 1 gas_path_ptr_rules) >> simp[]) >>
  metis_tac[ifexp_noop_annotation_capacity]
QED

Resume ifexp_old_unwrap_nonword_path_capacity[runtime]:
  `compile_ensure_in_memory pp.ptr_operand pp.ptr_location
    (type_memory_bytes ce (expr_type e))
    ((type_memory_bytes ce (expr_type e)+31) DIV 32) F ce.ce_imm_alloca sm = (op,sb)` by
    (qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >> simp[unwrap_value_def]) >>
  `?ty. evaluate_type (get_tenv cx) (expr_type e) = SOME ty` by
    metis_tac[bodyPtrIfExpBytesInputsTheory.ifexp_arm_annotation_typed] >>
  `type_memory_bytes ce (expr_type e) < dimword (:256)` by
    (fs[dimword_def] >> decide_tac) >>
  drule_all (SRULE [] (Q.INST
    [`n` |-> `(type_memory_bytes ce (expr_type e)+31) DIV 32`]
    ifexp_old_ensure_memory_runtime)) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  suspend "runtime_post"
QED

Resume ifexp_old_unwrap_nonword_path_capacity[runtime_post]:
  qpat_x_assum `op = Var out` SUBST_ALL_TAC >>
  drule_all bodyPtrIfExpBytesInputsTheory.ifexp_arm_annotation_typed >> strip_tac >>
  `val_store_size ty' v <= type_memory_bytes ce (expr_type e)` by
    metis_tac[val_store_size_le, value_has_type_val_wf, optionTheory.SOME_11] >>
  `ptr_val_ok cx (expr_type e) v (Var out) H tt t` by
    (irule ifexp_materialized_ptr_post >> simp[] >>
     qexists_tac `type_memory_bytes ce (expr_type e)` >> metis_tac[optionTheory.SOME_11]) >>
  qexistsl_tac [`t`, `H`, `tt`] >> simp[] >> rpt strip_tac >>
  drule_all ifexp_materialized_capacity >> strip_tac >> metis_tac[ADD_COMM]
QED

Resume ifexp_old_unwrap_nonword_path_capacity[storage]:
  `pp.ptr_location = LocStorage \/ pp.ptr_location = LocTransient` by
    (Cases_on `pp.ptr_location` >> gvs[]) >>
  `compile_ensure_in_memory pp.ptr_operand pp.ptr_location
    (type_memory_bytes ce (expr_type e))
    ((type_memory_bytes ce (expr_type e)+31) DIV 32) ce.ce_is_ctor ce.ce_imm_alloca sm = (op,sb)` by
    (qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >> simp[unwrap_value_def]) >>
  `?ty. evaluate_type (get_tenv cx) (expr_type e) = SOME ty` by
    metis_tac[bodyPtrIfExpBytesInputsTheory.ifexp_arm_annotation_typed] >>
  `type_memory_bytes ce (expr_type e) < dimword (:256)` by
    (fs[dimword_def] >> decide_tac) >>
  FIRST [
    drule_all (cj 1 (SRULE [LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, DISJ_IMP_THM]
      (Q.INST [`n` |-> `(type_memory_bytes ce (expr_type e)+31) DIV 32`]
        ifexp_old_ensure_memory_storage))),
    drule_all (cj 2 (SRULE [LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, DISJ_IMP_THM]
      (Q.INST [`n` |-> `(type_memory_bytes ce (expr_type e)+31) DIV 32`]
        ifexp_old_ensure_memory_storage)))] >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  suspend "storage_post"
QED

Resume ifexp_old_unwrap_nonword_path_capacity[storage_post]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `op = Var out` SUBST_ALL_TAC >>
  drule_all bodyPtrIfExpBytesInputsTheory.ifexp_arm_annotation_typed >> strip_tac >>
  `val_store_size ty' v <= type_memory_bytes ce (expr_type e)` by
    metis_tac[val_store_size_le, value_has_type_val_wf, optionTheory.SOME_11] >>
  `ptr_val_ok cx (expr_type e) v (Var out) G' tn' t` by
    (irule ifexp_materialized_ptr_post >> simp[] >>
     qexists_tac `type_memory_bytes ce (expr_type e)` >> metis_tac[optionTheory.SOME_11]) >>
  qexistsl_tac [`t`, `G'`, `tn'`] >> simp[] >> rpt strip_tac >>
  drule_all ifexp_materialized_capacity >> strip_tac >> metis_tac[ADD_COMM]
QED

Finalise ifexp_old_unwrap_nonword_path_capacity
