(* Memory-place continuation after a counted target traversal. *)
Theory augAssignPlaceEndpointMemory
Ancestors
  augAssignPlaceLoadedMemory augAssignPlaceLoadedContinuation
  augAssignPlaceLoadContinuation augAssignPlaceSourceMemory
  bodyAugAssignOther bodyMemoryDefs exprSimHyps vyperInterpreter exprSimMemDefs
  stmtSimAugAssignPlace bodySim

Theorem aug_place_memory_reads_suffix[local]:
  read_place cx (MemoryPlace id path) mid = (INL old,mid) /\
  place_type_value cx (MemoryPlace id path) mid = (INL tv,mid) /\
  ~t.vs_halted /\ gas_marked_path T ctx func t 0 (OK u) /\
  gas_outcome T (cx_tops cx) (ctx,func)
    (bind (bind (eval_expr cx e) (read_result cx))
      (\rhs. bind (lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        tv bop old rhs)) (write_place cx (MemoryPlace id path)))) (mid,u) P R /\
  (!res ee v. P res ee v ==> Q res ee v) ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (bind (read_place cx (MemoryPlace id path)) (\old.
      bind (place_type_value cx (MemoryPlace id path)) (\tv.
      bind (bind (eval_expr cx e) (read_result cx)) (\rhs.
      bind (lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        tv bop old rhs)) (write_place cx (MemoryPlace id path)))))) (mid,t) Q R
Proof
  strip_tac >>
  drule_all augAssignPlaceSourcePrefixTheory.aug_place_memory_reads_replay >> strip_tac >>
  ho_match_mp_tac (Q.INST [`cur` |-> `old`, `ptv` |-> `tv`]
    aug_place_read_type_load_mem) >>
  goal_assum (drule_at (Pat `gas_marked_path`)) >> simp[] >>
  drule stmtForArrayMemorySupportTheory.gas_outcome_start_gas_obs >>
  disch_then (qspec_then `[]` (assume_tac o SRULE [vyperStateTheory.bind_assoc])) >>
  simp[SF ETA_ss, vyperStateTheory.bind_assoc] >> irule gas_outcome_post_mono >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem aug_place_memory_endpoint:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (AugAssign ty bt bop e) /\
  ((?b fld. bt = AttributeTarget b fld) \/ (?b k. bt = SubscriptTarget b k)) /\
  type_stmt env ret_ty (AugAssign ty bt bop e) = SOME env' /\
  expr_body_pre cenv cx env e es /\ target_indices_pre cenv cx env bt /\
  (!s p s1 s2 cur s3 s4 ptv s5.
    eval_target_place cx bt s = (INL p,s1) /\ read_place cx p s2 = (INL cur,s3) /\
    place_type_value cx p s4 = (INL ptv,s5) ==> body_expr_mem_ok cx e) /\
  target_post ctx func cenv cx es sa sp s0 mid
    (PlaceR (MemoryPlace id path)) (Type ty) r t /\
  (!tail. eval_target_place cx bt
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (INL (MemoryPlace id path),mid with gas_obs := tail)) /\
  gas_admissible (eval_stmt cx (AugAssign ty bt bop e)) (stmt_res_ok lctx) es /\
  compile_get_target_ptr compile_expr cenv bt sa = (r,sp) /\
  emit_op MLOAD [FST r] sp = (cur,sl) /\
  lower_value compile_expr cenv ty e sl = (rhs,s2) /\
  compile_binop bop cur rhs ty NONE
    (if bop = Exp then expr_int_literal e else NONE) s2 = (result,s3) /\
  emit_void MSTORE [FST r;result] s3 = ((),sf) /\
  fn_has_code sp sl func /\ fn_has_code sl s2 func /\
  fn_has_code s2 s3 func /\ fn_has_code s3 sf func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sp /\ local_ptrs_reserved cenv s2 /\
  local_ptrs_reserved cenv s3 /\
  (!z. not_fresh_at sa z ==> not_fresh_at sp z) /\
  (!z. not_fresh_at sp z ==> not_fresh_at sl z) /\
  (!z. not_fresh_at sl z ==> not_fresh_at s2 z) /\
  (!z. not_fresh_at s2 z ==> not_fresh_at s3 z) /\
  alloca_history func t /\ ~t.vs_halted /\
  t.vs_current_bb = sp.cs_current_bb /\ t.vs_inst_idx = LENGTH sp.cs_current_insts /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  (!res ee v. res = INL () /\
    stmt_post ctx func cx lctx cenv cenv sa sf s0 res ee v /\
    alloca_history func v /\ s0.vs_alloca_next <= v.vs_alloca_next ==> Q res ee v) ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (bind (read_place cx (MemoryPlace id path)) (\old.
      bind (place_type_value cx (MemoryPlace id path)) (\tv.
      bind (bind (eval_expr cx e) (read_result cx)) (\rhs.
      bind (lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        tv bop old rhs)) (write_place cx (MemoryPlace id path)))))) (mid,t) Q
    (\res ff rr. !tail. stmt_exit RetQ (ff with gas_obs := tail) res rr)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule aug_place_typing >> strip_tac >>
  qpat_assum `!tail. eval_target_place _ _ _ = _`
    (assume_tac o SRULE [] o Q.SPEC `mid.gas_obs`) >>
  drule_at (Pat `target_post`) aug_place_memory_loaded >>
  disch_then (drule_at (Pat `eval_target_place`)) >>
  disch_then (drule_at (Pat `supported_stmt`)) >>
  disch_then (drule_at (Pat `type_stmt`)) >>
  disch_then (drule_at (Pat `emit_op`)) >> simp[] >> strip_tac >>
  `expr_sim_mem ctx func cenv cx ty e mid` by
    (`body_expr_mem_ok cx e` by metis_tac[] >>
     fs[bodyMemoryPredsTheory.body_expr_mem_ok_def] >> metis_tac[]) >>
  `?info. supported_target_info tops bindings bt = SOME info` by
    metis_tac[bodyAugPlaceTargetTheory.aug_place_supported_stmt_target_info] >>
  `acyclic_struct_metadata cenv.ce_struct_fields` by fs[body_inv_def] >>
  `IS_SOME (evaluate_type (get_tenv cx) (expr_type e))` by
    metis_tac[exprSimHypsTheory.expr_body_pre_type_evaluates] >>
  `~block_is_terminated sf` by
    (irule stmtSimDeclMemTheory.emit_void_nonterminator_open >>
     goal_assum (drule_at Any) >> simp[venomInstTheory.is_terminator_def]) >>
  `!l. cur <> Label l /\ FST r <> Label l` by
    (drule_all stmtSimAugAssignPlaceTheory.aug_place_target_ptr_not_label >>
     strip_tac >> gvs[]) >>
  `!z. not_fresh_at sa z ==> not_fresh_at sl z` by metis_tac[] >>
  `s0.vs_alloca_next <= u.vs_alloca_next` by simp[] >>
  irule aug_place_memory_reads_suffix >> simp[] >>
  qexists_tac `\res ee v. res = INL () /\
    stmt_post ctx func cx lctx cenv cenv sa sf s0 res ee v /\
    alloca_history func v /\ s0.vs_alloca_next <= v.vs_alloca_next` >> simp[] >>
  goal_assum (drule_at (Pat `gas_marked_path`)) >> simp[] >>
  irule aug_place_loaded_memory_suffix >> simp[] >> conj_tac
  >- (goal_assum (drule_at (Pat `supported_stmt`)) >>
      goal_assum (drule_at (Pat `supported_target_info`)) >>
      goal_assum (drule_at (Pat `type_stmt`)) >>
      goal_assum (drule_at (Pat `eval_target_place`)) >> simp[]) >>
  goal_assum (drule_at (Pat `lower_value`)) >>
  goal_assum (drule_at (Pat `compile_binop`)) >>
  goal_assum (drule_at (Pat `place_ptr_rel`)) >> simp[] >> metis_tac[]
QED
