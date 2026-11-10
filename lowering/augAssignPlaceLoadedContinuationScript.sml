(* Source-aware RHS/operator/write continuation at a loaded memory place. *)
Theory augAssignPlaceLoadedContinuation
Ancestors
  augAssignPlaceSourceMemory augAssignPlaceRhsContinuation
  exprSimProps exprSimSource exprSimHypsDefs bodyMemoryPreds
  stmtSimAugAssignPlaceMemory stmtSimAugAssignPlace
  augAssignPlaceSourcePrefix vyperStoragePlaceProvenance

Theorem aug_place_loaded_memory_suffix:
  supported_stmt tops bindings (AugAssign ty bt bop e) /\
  supported_target_info tops bindings bt = SOME info /\
  type_stmt env ret_ty (AugAssign ty bt bop e) = SOME env' /\
  expr_body_pre cenv cx env e mid /\ expr_sim_mem ctx func cenv cx ty e mid /\
  (!tail. eval_target_place cx bt (es with gas_obs := prefix ++ tail) =
    (INL (MemoryPlace id path),mid with gas_obs := tail)) /\
  gas_admissible (eval_stmt cx (AugAssign ty bt bop e)) (stmt_res_ok lctx) es /\
  read_place cx (MemoryPlace id path) mid = (INL old,mid) /\
  place_type_value cx (MemoryPlace id path) mid = (INL tv,mid) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv old /\
  type_bits ty MOD 8 = 0 /\ word_value_type ty /\
  word_value_type (expr_type e) /\
  IS_SOME (evaluate_type (get_tenv cx) (expr_type e)) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  lower_value compile_expr cenv ty e sl = (rhs,s2) /\
  compile_binop bop cur rhs ty NONE
    (if bop = Exp then expr_int_literal e else NONE) s2 = (result,s3) /\
  emit_void MSTORE [dst;result] s3 = ((),sf) /\
  fn_has_code sl s2 func /\ fn_has_code s2 s3 func /\ fn_has_code s3 sf func /\
  fn_inst_ids_distinct func /\ bop <> In /\ bop <> NotIn /\
  local_ptrs_reserved cenv sl /\ local_ptrs_reserved cenv s2 /\
  local_ptrs_reserved cenv s3 /\
  (!z. cur = Var z ==> not_fresh_at sl z) /\
  (!z. dst = Var z ==> not_fresh_at sl z) /\
  (!z. not_fresh_at sa z ==> not_fresh_at sl z) /\
  (!z. not_fresh_at sl z ==> not_fresh_at s2 z) /\
  (!z. not_fresh_at s2 z ==> not_fresh_at s3 z) /\
  (!l. cur <> Label l /\ dst <> Label l) /\
  eval_operand cur u = SOME (typed_val_to_w256 tv old) /\
  eval_operand dst u = SOME w /\
  place_ptr_rel cenv cx u (PlaceR (MemoryPlace id path)) w (SOME LocMemory) (Type ty) /\
  w2n w + 32 <= u.vs_alloca_next /\
  stmt_state_rel ctx func cenv cx mid u /\ alloca_history func u /\
  s0.vs_alloca_next <= u.vs_alloca_next /\
  ~u.vs_halted /\ u.vs_current_bb = sl.cs_current_bb /\
  u.vs_inst_idx = LENGTH sl.cs_current_insts /\ ~block_is_terminated sf /\
  (!z v. not_fresh_at sa z /\ lookup_var z s0 = SOME v ==> lookup_var z u = SOME v) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) ==>
  gas_outcome T (cx_tops cx) (ctx,func)
    (bind (bind (eval_expr cx e) (read_result cx))
      (\rhs. bind (lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        tv bop old rhs)) (write_place cx (MemoryPlace id path)))) (mid,u)
    (\res ff v. res = INL () /\
      stmt_post ctx func cx lctx cenv cenv sa sf s0 res ff v /\
      alloca_history func v /\ s0.vs_alloca_next <= v.vs_alloca_next)
    (\res ff r. !tail. stmt_exit RetQ (ff with gas_obs := tail) res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all aug_place_memory_reads_replay >> strip_tac >>
  drule_all aug_place_rhs_suffix_admissible >> strip_tac >>
  `word_value old` by metis_tac[word_value_type_typed] >>
  `is_word_type ty /\ is_word_type (expr_type e)` by
    metis_tac[word_value_type_word] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok mid` by
    metis_tac[expr_body_pre_gas_admissible] >>
  irule aug_place_rhs_operator_write_mem >>
  simp[typed_val_to_w256_word_value, storage_place_region_def] >>
  goal_assum (drule_at (Pat `lower_value`)) >>
  goal_assum (drule_at (Pat `compile_binop`)) >>
  goal_assum (drule_at (Pat `place_ptr_rel`)) >>
  qexistsl_tac [`dst`, `env`] >>
  simp[typed_val_to_w256_word_value] >> rpt strip_tac >>
  `?entry old'. lookup_scopes id ee.scopes = SOME entry /\
    evaluate_subscripts entry.type entry.value path = INL old'` by
    (irule aug_place_rhs_memory_live >> goal_assum (drule_at (Pat `supported_stmt`)) >>
     goal_assum (drule_at (Pat `supported_target_info`)) >>
     goal_assum (drule_at (Pat `bind _ _ _ = _`)) >>
     qexists_tac `es with gas_obs := prefix ++ gs` >> simp[]) >>
  drule_all aug_place_memory_rhs_callback >> simp[]
QED
