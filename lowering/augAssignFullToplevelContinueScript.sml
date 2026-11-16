(* Scalar top-level AugAssign: the observed root protects the final word store. *)
Theory augAssignFullToplevelContinue
Ancestors
  augAssignFullStore augAssignFullStoreGhost stmtSimAssignStorage
  bodySimFull accountsRelProps exprLoweringProps
  vyperStorageFootprint vyperStorageBackend vyperState vyperValue
  venomState bodyPtrDefs ptrDiscipline list
  stmtSimAugAssignStorage exprSimHypsDefs exprSimUnwrap
  vyperTypeStatePreservation vyperTyping vyperInterpreter vyperTypeSystem
  exprSimSource exprSimHyps exprBopSimProps stmtSimAugAssign
  augAssignFullToplevelOperator augAssignFullToplevelLanding
  augAssignFullStateFrame augAssignFullHistory stmtSimDefs freshWrites
  loweringPosts emitHelperProps loweringShapeRules bodyMemoryDefs loweringStateRelDefs
  stmtSimProps gasOutcomeFullCompose fragGasOriginPtr exprSimProps fragExec

Theorem augassign_toplevel_store_relations_full[local]:
  root_es.storage_trace = es.storage_trace ++ [StorageRoot tr slot tvt] /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    valid_horizon cx st0 H root_es.storage_trace) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid operated /\
    storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx mid G tn operated) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  type_slot_size tvt = 1 /\ well_formed_type_value tvt /\
  value_has_type tvt result /\ encode_value tvt result = SOME [(0,w)] /\
  write_storage_slot cx tr (n2w slot) tvt result (mid with gas_obs := []) =
    (INL (),fin) /\
  fin.storage_trace = mid.storage_trace /\ fin.scopes = mid.scopes /\
  operated.vs_call_ctx.cc_address = cx.txn.target ==>
  !H. valid_horizon cx st0 H fin.storage_trace ==>
    stmt_state_rel H ctx func cenv cx fin
      ((if tr then tstore (n2w slot) w operated else sstore (n2w slot) w operated)
        with vs_inst_idx := pc) /\
    storage_well_formed_on cx fin (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx fin G
      (if tr then tn with t_trans := key_update tn.t_trans (n2w slot) {}
       else tn with t_stor := key_update tn.t_stor (n2w slot) {})
      ((if tr then tstore (n2w slot) w operated else sstore (n2w slot) w operated)
        with vs_inst_idx := pc)
Proof
  strip_tac >> qx_gen_tac `H` >> strip_tac >>
  `valid_horizon cx st0 H mid.storage_trace` by metis_tac[] >>
  `valid_horizon cx st0 H root_es.storage_trace` by metis_tac[] >>
  `MEM (tr,n2w slot,tvt) (FST H) /\ regions_consistent (FST H)` by
    gvs[valid_horizon_def, storage_observations_ok_def, storage_trace_regions_def] >>
  `stmt_state_rel H ctx func cenv cx mid operated /\
   storage_well_formed_on cx mid (FST H) /\
   ghost_inv_at (DF H) lo d cenv cx mid G tn operated` by metis_tac[] >>
  `!u st. storage_dead H tr (update_storage (n2w slot) u st) = storage_dead H tr st`
    by metis_tac[storage_dead_update_word_region] >>
  `stmt_state_rel H ctx func cenv cx (mid with gas_obs := []) operated` by
    simp[stmt_state_rel_start_gas_obs] >>
  `storage_well_formed_on cx (mid with gas_obs := []) (FST H)` by
    (irule (iffRL storage_well_formed_on_backends) >> qexists_tac `mid` >> simp[]) >>
  `~cx.txn.is_static` by
    (Cases_on `cx.txn.is_static` >> gvs[write_storage_slot_eq]) >>
  drule_all stmt_state_rel_write_storage_word >> strip_tac >>
  `storage_well_formed_on cx fin (FST H)` by
    metis_tac[typed_write_preserves_storage_well_formed_on] >>
  simp[stmt_state_rel_inst_idx] >>
  irule (INST_TYPE [alpha |-> ``:256``] ghost_inv_at_storage_word_store) >>
  simp[] >> conj_tac
  >- (qexists_tac `H` >> simp[]) >>
  qexists_tac `mid` >> simp[]
QED

Theorem augassign_toplevel_rhs_numeric_facts_full[local]:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr ty,id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) ty = SOME tvt /\
  read_storage_slot cx tr (n2w slot) tvt es = (INL cur,es) /\
  root_es = es with storage_trace := es.storage_trace ++ [StorageRoot tr slot tvt] /\
  expr_body_pre cenv cx env e root_es /\
  bind (eval_expr cx e) (read_result cx) (root_es with gas_obs := gs) =
    (INL rhs,mid with gas_obs := []) /\
  gas_admissible (eval_stmt cx (AugAssign ty (TopLevelNameTarget (src,id)) bop e))
    (stmt_res_ok lctx) es /\
  well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn /\
  (bop = Exp ==> nonneg_int_literal e) /\
  (bop = ShL \/ bop = ShR ==> shift_amount_ok e) ==>
  word_value rhs /\
  (?etv. evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
    value_has_type etv rhs) /\
  (!n. expr_int_literal e = SOME n ==> rhs = IntV n) /\
  (bop = Exp ==> ?n. expr_int_literal e = SOME n /\ 0 <= n) /\
  (bop = ShL \/ bop = ShR ==> ?i. rhs = IntV i /\ 0 <= i) /\
  expr_res_ok (bop_result cx ty bop [ty;expr_type e] cur rhs (mid with gas_obs := []))
Proof
  strip_tac >>
  `expr_body_pre cenv cx env e (root_es with gas_obs := gs)` by simp[] >>
  `word_value_type ty /\ word_value_type (expr_type e)` by
    metis_tac[well_typed_binop_augassign_word] >>
  drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_word_result) >> strip_tac >>
  `word_value rhs /\ ?etv. evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
    value_has_type etv rhs` by metis_tac[] >>
  qpat_assum `bind (eval_expr cx e) _ _ = _`
    (strip_assume_tac o MATCH_MP (REWRITE_RULE [ETA_AX] eval_expr_read_INL)) >>
  `!n. expr_int_literal e = SOME n ==> rhs = IntV n` by
    metis_tac[eval_expr_int_literal_agrees] >>
  `(bop = Exp ==> ?n. expr_int_literal e = SOME n /\ 0 <= n)` by
    (strip_tac >> qpat_x_assum `bop = Exp ==> nonneg_int_literal e` mp_tac >>
     simp[nonneg_int_literal_def, GSYM expr_int_literal_value] >>
     Cases_on `expr_int_literal e` >> simp[]) >>
  `(bop = ShL \/ bop = ShR ==> ?i. rhs = IntV i /\ 0 <= i)` by
    (strip_tac >> `shift_amount_ok e` by metis_tac[] >>
     drule_all eval_expr_shift_amount >> simp[]) >>
  simp[] >> reverse conj_tac
  >- (gvs[] >> drule_all augassign_toplevel_binop_admissible >> simp[]) >>
  metis_tac[]
QED

(* The loaded scalar remains clean across the RHS, and the RHS word is clean. *)
Theorem augassign_toplevel_rhs_operands_full[local]:
  emit_op (if tr then TLOAD else SLOAD) [Lit (n2w slot)] sa = (Var out,s1) /\
  lower_value compile_expr cenv ty e s1 = (op,s2) /\
  expr_body_pre cenv cx env e root_es /\ is_word_type (expr_type e) /\
  word_value rhs /\ evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
  expr_post H ctx func cenv cx e root_es s1 s2 t mid rhs op u /\
  ghost_kept_at lo cenv root_es s1 Gload tnload t Gr tnr /\
  ptr_val_ok cx (post_value_type cenv e) rhs op Gr tnr u /\
  eval_operand (Var out) t = SOME (val_to_w256 cur) /\
  op_prov Gload (Var out) = NONE /\ op_taint tnload (Var out) = {} ==>
  eval_operand (Var out) u = SOME (val_to_w256 cur) /\
  eval_operand op u = SOME (val_to_w256 rhs) /\
  op_prov Gr (Var out) = NONE /\ op_taint tnr (Var out) = {} /\
  op_prov Gr op = NONE /\ op_taint tnr op = {} /\
  not_fresh_at s2 out /\ (!z. op = Var z ==> not_fresh_at s2 z) /\
  (!l. op <> Label l)
Proof
  strip_tac >>
  drule_all expr_body_pre_lower_value_word_shape >> strip_tac >>
  `not_fresh_at s1 out` by
    (drule emit_op_facts >> simp[]) >>
  `not_fresh_at s2 out` by metis_tac[not_fresh_at_mono] >>
  `eval_operand (Var out) u = SOME (val_to_w256 cur)` by
    (irule eval_operand_frame >> conj_tac >- simp[] >>
     qexistsl_tac [`s1`, `t`] >> gvs[expr_post_def]) >>
  `expr_val_rel cx (expr_type e) rhs op u` by gvs[expr_post_def] >>
  `eval_operand op u = SOME (val_to_w256 rhs)` by
    (irule expr_val_rel_word >> simp[] >>
     qexistsl_tac [`cx`, `expr_type e`] >> simp[]) >>
  gvs[ghost_kept_at_def, ptr_val_ok_def, op_prov_def, op_taint_def]
QED

Theorem augassign_toplevel_rhs_alloca_frame_full[local]:
  emit_op (if tr then TLOAD else SLOAD) [Lit (n2w slot)] sa = (Var out,s1) /\
  root_es = es with storage_trace := es.storage_trace ++ [StorageRoot tr slot tvt] /\
  t = update_var out (if tr then tload (n2w slot) s0 else sload (n2w slot) s0)
    (s0 with vs_inst_idx := LENGTH s1.cs_current_insts) /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s0) /\
  stmt_state_rel H ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel H ctx func cenv cx root_es t /\
  expr_post H ctx func cenv cx e root_es s1 s2 t mid rhs op u /\
  MAP FDOM mid.scopes = MAP FDOM root_es.scopes /\
  operated = (u with vs_inst_idx := pc) with vs_vars := operated.vs_vars /\
  sa.cs_next_var <= s2.cs_next_var /\
  (!z. not_fresh_at s2 z ==> lookup_var z operated = lookup_var z u) ==>
  alloca_frame cenv es sa s0 cenv mid operated /\
  (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
    lookup_var x operated = SOME v) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
    FLOOKUP operated.vs_allocas aid = SOME b) /\
  operated.vs_alloca_next = u.vs_alloca_next /\
  t.vs_alloca_next = s0.vs_alloca_next
Proof
  strip_tac >>
  `sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id` by
    (drule emitted_insts_emit_op >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at s1 x /\ not_fresh_at s2 x` by
    metis_tac[not_fresh_at_mono] >>
  `local_ptrs_reserved cenv s1` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  `alloca_frame cenv root_es s1 t cenv mid u` by
    (drule_all expr_post_alloca_frame >> simp[]) >>
  `alloca_frame cenv es sa s0 cenv mid u` by
    (irule alloca_frame_expr_prefix >> simp[] >>
     reverse conj_tac >- metis_tac[] >>
     qexistsl_tac [`root_es`, `s1`, `t`] >> simp[] >>
     qpat_x_assum `t = _` SUBST1_TAC >> simp[update_var_def]) >>
  `!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
     lookup_var x operated = SOME v` by
    (rpt strip_tac >> gvs[expr_post_def] >> metis_tac[]) >>
  conj_tac
  >- (irule alloca_frame_of_mem_frame >> simp[] >>
      reverse conj_tac >- metis_tac[] >>
      qpat_x_assum `alloca_frame cenv es sa s0 cenv mid u` mp_tac >>
      simp[alloca_frame_def] >>
      qpat_x_assum `operated = _` (fn th => ONCE_REWRITE_TAC [th]) >>
      simp[] >> metis_tac[]) >>
  simp[] >>
  qpat_assum `operated = _` (fn th => ONCE_REWRITE_TAC [th]) >>
  gvs[expr_post_def, update_var_def]
QED

(* Transport the loaded reserved frame through the RHS and numeric endpoint. *)
Theorem augassign_toplevel_rhs_operator_frame_full[local]:
  emit_op (if tr then TLOAD else SLOAD) [Lit (n2w slot)] sa = (Var out,s1) /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var /\
  s2.cs_next_var <= s3.cs_next_var /\ t.vs_alloca_next <= u.vs_alloca_next /\
  return_buf_frame d cenv s1 t /\ ret_pc_ok cenv s1 t /\
  local_ptrs_reserved cenv s1 /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s1 x) /\
  (!x. not_fresh_at sa x ==> FLOOKUP Gload x = FLOOKUP G0 x /\
    op_taint tnload (Var x) = op_taint tn0 (Var x)) /\
  expr_post H ctx func cenv cx e root_es s1 s2 t mid rhs op u /\
  ghost_inv_at (DF H) lo d cenv cx mid Gr tnr u /\
  ghost_kept_at lo cenv root_es s1 Gload tnload t Gr tnr /\
  operated = (u with vs_inst_idx := LENGTH s3.cs_current_insts)
    with vs_vars := operated.vs_vars /\
  (!x. not_fresh_at s2 x ==> lookup_var x operated = lookup_var x u /\
    FLOOKUP Gop x = FLOOKUP Gr x /\
    op_taint tnop (Var x) = op_taint tnr (Var x)) /\
  tnop.t_mem = tnr.t_mem /\ tnop.t_stor = tnr.t_stor /\
  tnop.t_trans = tnr.t_trans /\ tnop.t_imm = tnr.t_imm ==>
  stmt_state_rel H ctx func cenv cx mid operated /\
  storage_well_formed_on cx mid (FST H) /\
  ghost_inv_at (DF H) lo d cenv cx mid Gop tnop operated /\
  return_buf_frame d cenv s3 operated /\ ret_pc_ok cenv s3 operated /\
  local_ptrs_reserved cenv s3 /\
  (!x. not_fresh_at sa x ==> FLOOKUP Gop x = FLOOKUP G0 x /\
    op_taint tnop (Var x) = op_taint tn0 (Var x))
Proof
  strip_tac >>
  `return_buf_frame d cenv s2 u` by
    (irule return_buf_frame_frame >> qexistsl_tac [`cenv`, `t`, `s1`] >>
     gvs[expr_post_def]) >>
  `ret_pc_ok cenv s2 u` by
    (irule ret_pc_ok_frame >> qexistsl_tac [`cenv`, `t`, `s1`] >>
     gvs[expr_post_def]) >>
  `local_ptrs_reserved cenv s2` by
    (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s2 x` by
    metis_tac[not_fresh_at_mono] >>
  `stmt_state_rel H ctx func cenv cx mid u /\
   storage_well_formed_on cx mid (FST H)` by fs[expr_post_def] >>
  drule_all augassign_exterior_state_frame >> strip_tac >> simp[] >>
  gvs[ghost_kept_at_def] >> metis_tac[not_fresh_at_mono]
QED

(* Close the successful numeric/store continuation at the original statement frame. *)
Theorem augassign_toplevel_store_outcome_full[local]:
  evaluate_binop bound tvt bop cur rhs = INL result /\
  write_storage_slot cx tr (n2w slot) tvt result (mid with gas_obs := []) =
    (INL (),fin) /\ fin.gas_obs = [] /\
  ~u.vs_halted /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (u,Gr,tnr) []
      (OK operated,Gop,tnop) /\
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (operated,Gop,tnop) []
      (OK last,Gop,tnlast) /\
    stmt_post H ctx func cx lctx cenv cenv sa sb es s0 (INL ()) fin last /\
    return_buf_frame d cenv sb last /\ alloca_history func last /\
    s0.vs_alloca_next <= last.vs_alloca_next /\
    ghost_inv_at (DF H) lo d cenv cx fin Gop tnlast last /\
    (!x. not_fresh_at sa x ==> FLOOKUP Gop x = FLOOKUP G0 x /\
      op_taint tnlast (Var x) = op_taint tn0 (Var x))) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (bind (lift_sum (evaluate_binop bound tvt bop cur rhs))
      (write_place cx (StoragePlace tr (n2w slot) tvt)))
    (mid,u,Gr,tnr)
    (\H res ee G tn t. ?cenv''.
      stmt_lands lctx sb res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv) /\
      cenv_top_ext cenv cenv'' ee.scopes /\
      stmt_state_rel H ctx func cenv'' cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv'' sb t /\ alloca_history func t /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv'' cx ee G tn t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
        lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
        FLOOKUP t.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
        op_taint tn (Var x) = op_taint tn0 (Var x)))
    (\H res ee gt r. !tail.
      stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r)
Proof
  strip_tac >> irule gas_outcome_full_pure >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`Gop`, `fin`, `INL ()`, `last`, `tnlast`] >> conj_tac
  >- (gen_tac >>
      qspecl_then [`cx`, `tr`, `n2w slot`, `tvt`, `result`,
        `mid with gas_obs := []`, `tail`] mp_tac write_storage_slot_gas_obs >>
      simp[lift_sum_def, bind_def, return_def, write_place_def]) >>
  qx_gen_tac `H` >> strip_tac >>
  `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (u,Gr,tnr) []
     (OK operated,Gop,tnop) /\
   gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (operated,Gop,tnop) []
     (OK last,Gop,tnlast)` by metis_tac[] >>
  conj_tac
  >- (qpat_assum `gas_origin_ptr_path _ (u,Gr,tnr) [] (OK operated,Gop,tnop)`
        (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
      disch_then (qspecl_then [`operated`, `Gop`, `tnop`, `[]`, `OK last`,
        `Gop`, `tnlast`] mp_tac) >> simp[]) >>
  `fin with gas_obs := [] = fin` by simp[evaluation_state_component_equality] >>
  simp[] >> fs[stmt_post_def] >> metis_tac[]
QED


Theorem augassign_toplevel_success_frames_full[local]:
  emit_op (if tr then TLOAD else SLOAD) [Lit (n2w slot)] sa = (Var out,s1) /\
  sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var /\
  s2.cs_next_var <= s3.cs_next_var /\
  return_buf_frame d cenv s1 t /\ ret_pc_ok cenv s1 t /\
  local_ptrs_reserved cenv s1 /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s1 x) /\
  (!x. not_fresh_at sa x ==> FLOOKUP Gload x = FLOOKUP G0 x /\
    op_taint tnload (Var x) = op_taint tn0 (Var x)) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post H ctx func cenv cx e root_es s1 s2 t mid rhs op u /\
    t.vs_alloca_next <= u.vs_alloca_next /\
    ghost_inv_at (DF H) lo d cenv cx mid Gr tnr u /\
    ghost_kept_at lo cenv root_es s1 Gload tnload t Gr tnr) /\
  operated = (u with vs_inst_idx := LENGTH s3.cs_current_insts)
    with vs_vars := operated.vs_vars /\
  (!x. not_fresh_at s2 x ==> lookup_var x operated = lookup_var x u /\
    FLOOKUP Gop x = FLOOKUP Gr x /\ op_taint tnop (Var x) = op_taint tnr (Var x)) /\
  tnop.t_mem = tnr.t_mem /\ tnop.t_stor = tnr.t_stor /\
  tnop.t_trans = tnr.t_trans /\ tnop.t_imm = tnr.t_imm ==>
  !H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid operated /\
    storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx mid Gop tnop operated /\
    return_buf_frame d cenv s3 operated /\ ret_pc_ok cenv s3 operated /\
    local_ptrs_reserved cenv s3 /\
    (!x. not_fresh_at sa x ==> FLOOKUP Gop x = FLOOKUP G0 x /\
      op_taint tnop (Var x) = op_taint tn0 (Var x))
Proof
  strip_tac >> gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then strip_assume_tac) >>
  drule_all augassign_toplevel_rhs_operator_frame_full >> simp[]
QED

Theorem augassign_toplevel_success_alloca_full[local]:
  emit_op (if tr then TLOAD else SLOAD) [Lit (n2w slot)] sa = (Var out,s1) /\
  root_es = es with storage_trace := es.storage_trace ++ [StorageRoot tr slot tvt] /\
  bind (eval_expr cx e) (read_result cx) (root_es with gas_obs := gs) =
    (INL rhs,mid with gas_obs := []) /\
  valid_horizon cx st0 H0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0) /\
  (!H. valid_horizon cx st0 H root_es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx root_es t) /\
  t = update_var out (if tr then tload (n2w slot) s0 else sload (n2w slot) s0)
    (s0 with vs_inst_idx := LENGTH s1.cs_current_insts) /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s0) /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= s2.cs_next_var /\
  expr_post H0 ctx func cenv cx e root_es s1 s2 t mid rhs op u /\
  t.vs_alloca_next <= u.vs_alloca_next /\
  operated = (u with vs_inst_idx := LENGTH s3.cs_current_insts)
    with vs_vars := operated.vs_vars /\
  (!z. not_fresh_at s2 z ==> lookup_var z operated = lookup_var z u) /\
  alloca_history func u /\ u.vs_current_bb = s2.cs_current_bb /\
  u.vs_inst_idx = LENGTH s2.cs_current_insts /\
  fn_has_code s2 s3 func /\ fn_inst_ids_distinct func /\
  s3.cs_current_bb = s2.cs_current_bb /\
  s3.cs_current_insts = s2.cs_current_insts ++ emitted_insts s2 s3 /\
  EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts s2 s3) /\
  run_inst_seq (emitted_insts s2 s3) u = OK oprun /\
  operated = oprun with vs_inst_idx := LENGTH s3.cs_current_insts ==>
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    valid_horizon cx st0 H root_es.storage_trace /\
    valid_horizon cx st0 H es.storage_trace) /\
  alloca_frame cenv es sa s0 cenv mid operated /\
  (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
    lookup_var x operated = SOME v) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
    FLOOKUP operated.vs_allocas aid = SOME b) /\
  s0.vs_alloca_next <= operated.vs_alloca_next /\
  alloca_inv operated /\ alloca_history func operated
Proof
  strip_tac >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    valid_horizon cx st0 H root_es.storage_trace` by
    (gen_tac >> strip_tac >>
     drule_at (Pos (el 2)) valid_horizon_frame >>
     simp[augassign_rhs_trace_frame]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    valid_horizon cx st0 H es.storage_trace` by
    (gen_tac >> strip_tac >>
     `valid_horizon cx st0 H root_es.storage_trace` by metis_tac[] >>
     qpat_assum `valid_horizon cx st0 H root_es.storage_trace` mp_tac >>
     qpat_assum `root_es = _` (fn th => ONCE_REWRITE_TAC [th]) >>
     simp[] >> metis_tac[gasOutcomeFullTheory.valid_horizon_append]) >>
  `stmt_state_rel H0 ctx func cenv cx es s0 /\
   stmt_state_rel H0 ctx func cenv cx root_es t` by metis_tac[] >>
  `MAP FDOM mid.scopes = MAP FDOM root_es.scopes` by
    (drule eval_read_preserves_scopes_dom >> simp[]) >>
  drule_all augassign_toplevel_rhs_alloca_frame_full >> strip_tac >>
  `alloca_inv u` by fs[expr_post_def, stmt_state_rel_def, state_rel_def] >>
  `alloca_inv operated` by
    (qpat_assum `operated = (u with vs_inst_idx := _) with vs_vars := _`
       SUBST1_TAC >> fs[venomMemDefsTheory.alloca_inv_def,
         venomMemDefsTheory.allocas_non_overlapping_def,
         venomMemDefsTheory.alloca_next_valid_def] >> metis_tac[]) >>
  `alloca_history func operated` by
    (qpat_assum `operated = oprun with vs_inst_idx := _` SUBST1_TAC >>
     irule bodyFullUnwrapRunTheory.emitted_alloca_history >>
     conj_tac >- simp[] >>
     qexistsl_tac [`emitted_insts s2 s3`, `u`, `s2`] >> simp[]) >>
  simp[]
QED

Theorem augassign_toplevel_success_continue_full[local]:
  evaluate_binop bound tvt bop cur rhs = INL result /\
  value_has_type tvt result /\ encode_value tvt result = SOME [(0,w)] /\
  type_slot_size tvt = 1 /\ well_formed_type_value tvt /\
  ~u.vs_halted /\ ~cx.txn.is_static /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (u,Gr,tnr) []
      (OK operated,Gop,tnop)) /\
  emit_void (if tr then TSTORE else SSTORE) [Lit (n2w slot);res_op] s3 = ((),sb) /\
  fn_has_code s3 sb func /\ fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\
  ~operated.vs_halted /\ operated.vs_current_bb = s3.cs_current_bb /\
  operated.vs_inst_idx = LENGTH s3.cs_current_insts /\
  ~operated.vs_call_ctx.cc_static /\ operated.vs_call_ctx.cc_address = cx.txn.target /\
  eval_operand res_op operated = SOME w /\ op_taint tnop res_op = {} /\
  alloca_frame cenv es sa s0 cenv mid operated /\
  (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
    lookup_var x operated = SOME v) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
    FLOOKUP operated.vs_allocas aid = SOME b) /\
  (!x. not_fresh_at sa x ==> FLOOKUP Gop x = FLOOKUP G0 x /\
    op_taint tnop (Var x) = op_taint tn0 (Var x)) /\
  return_buf_frame d cenv s3 operated /\ alloca_history func operated /\
  alloca_inv operated /\ s0.vs_alloca_next <= operated.vs_alloca_next /\
  root_es.storage_trace = es.storage_trace ++ [StorageRoot tr slot tvt] /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    valid_horizon cx st0 H root_es.storage_trace) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid operated /\
    storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx mid Gop tnop operated) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (bind (lift_sum (evaluate_binop bound tvt bop cur rhs))
      (write_place cx (StoragePlace tr (n2w slot) tvt)))
    (mid,u,Gr,tnr)
    (\H res ee G tn t. ?cenv''.
      stmt_lands lctx sb res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv) /\
      cenv_top_ext cenv cenv'' ee.scopes /\
      stmt_state_rel H ctx func cenv'' cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv'' sb t /\ alloca_history func t /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv'' cx ee G tn t /\
      (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
        lookup_var x t = SOME v) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
        FLOOKUP t.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
        op_taint tn (Var x) = op_taint tn0 (Var x)))
    (\H res ee gt r. !tail.
      stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r)
Proof
  strip_tac >>
  Cases_on `write_storage_slot cx tr (n2w slot) tvt result (mid with gas_obs := [])` >>
  rename1 `write_storage_slot _ _ _ _ _ _ = (store_res,fin)` >>
  `store_res = INL ()` by
    (qpat_x_assum `write_storage_slot _ _ _ _ _ _ = _` mp_tac >>
     simp[write_storage_slot_eq]) >> pop_assum SUBST_ALL_TAC >>
  `fin.gas_obs = [] /\ fin.scopes = mid.scopes /\
   fin.storage_trace = mid.storage_trace` by
    (map_every (fn pat => qpat_assum pat mp_tac)
       [`write_storage_slot _ _ _ _ _ _ = (INL (),fin)`,
        `encode_value tvt result = SOME _`, `~cx.txn.is_static`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     fs[write_storage_slot_eq] >> Cases_on `tr` >> gvs[set_storage_def]) >>
  qabbrev_tac `last = (if tr then tstore (n2w slot) w operated
    else sstore (n2w slot) w operated) with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  qabbrev_tac `tnlast = if tr then tnop with t_trans := key_update tnop.t_trans (n2w slot) {}
    else tnop with t_stor := key_update tnop.t_stor (n2w slot) {}` >>
  `!H. valid_horizon cx st0 H fin.storage_trace ==>
    stmt_state_rel H ctx func cenv cx fin last /\
    storage_well_formed_on cx fin (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx fin Gop tnlast last` by
    (qunabbrev_tac `last` >> qunabbrev_tac `tnlast` >>
     gen_tac >> strip_tac >>
     irule augassign_toplevel_store_relations_full >>
     conj_tac >- simp[] >> conj_tac >- simp[] >>
     qexistsl_tac [`es`, `mid`, `result`, `root_es`, `st0`, `tvt`] >> simp[]) >>
  `(!D lo. allocas_from lo operated /\ lo <= operated.vs_alloca_next ==>
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (operated,Gop,tnop) []
        (OK last,Gop,tnlast)) /\
   (!H. valid_horizon cx st0 H fin.storage_trace ==>
      stmt_post H ctx func cx lctx cenv cenv sa sb es s0 (INL ()) fin last /\
      return_buf_frame d cenv sb last /\ alloca_history func last /\
      s0.vs_alloca_next <= last.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx fin Gop tnlast last /\
      (!x. not_fresh_at sa x ==> FLOOKUP Gop x = FLOOKUP G0 x /\
        op_taint tnlast (Var x) = op_taint tn0 (Var x)))` by
    (irule augassign_toplevel_store_landing_full >>
     simp[] >> conj_tac
     >- (qexistsl_tac [`res_op`, `s3`, `slot`, `tr`, `w`] >>
         simp[Abbr `last`, Abbr `tnlast`]) >>
     qexists_tac `mid` >> simp[]) >>
  irule augassign_toplevel_store_outcome_full >> simp[] >>
  qexistsl_tac [`Gop`, `es`, `last`, `operated`, `tnlast`, `tnop`] >>
  simp[] >> qx_gen_tac `H` >> strip_tac >>
  `allocas_from lo operated /\ lo <= operated.vs_alloca_next` by
    (qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ _ /\ _`
       (qspec_then `H` mp_tac) >> simp[ghost_inv_at_def]) >>
  qpat_x_assum `!H. valid_horizon _ _ H fin.storage_trace ==> stmt_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >> simp[]
QED

(* Prepare the concrete and all-horizon frames of a successful scalar update. *)
Theorem augassign_toplevel_success_prepare_full[local]:
  emit_op (if tr then TLOAD else SLOAD) [Lit (n2w slot)] sa = (Var out,s1) /\
  lower_value compile_expr cenv ty e s1 = (op,s2) /\
  compile_binop bop (Var out) op ty NONE
    (if bop = Exp then expr_int_literal e else NONE) s2 = (res_op,s3) /\
  well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn /\
  return_buf_frame d cenv s1 t /\ ret_pc_ok cenv s1 t /\
  local_ptrs_reserved cenv s1 /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s0 /\
    FLOOKUP Gload x = FLOOKUP G0 x /\ op_taint tnload (Var x) = op_taint tn0 (Var x)) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post H ctx func cenv cx e root_es s1 s2 t mid rhs op u /\
    t.vs_alloca_next <= u.vs_alloca_next /\ ghost_inv_at (DF H) lo d cenv cx mid Gr tnr u /\
    ghost_kept_at lo cenv root_es s1 Gload tnload t Gr tnr) /\
  operated = (u with vs_inst_idx := LENGTH s3.cs_current_insts)
    with vs_vars := operated.vs_vars /\
  (!x. not_fresh_at s2 x ==> lookup_var x operated = lookup_var x u /\
    FLOOKUP Gop x = FLOOKUP Gr x /\ op_taint tnop (Var x) = op_taint tnr (Var x)) /\
  tnop.t_mem = tnr.t_mem /\ tnop.t_stor = tnr.t_stor /\
  tnop.t_trans = tnr.t_trans /\ tnop.t_imm = tnr.t_imm /\
  root_es = es with storage_trace := es.storage_trace ++ [StorageRoot tr slot tvt] /\
  bind (eval_expr cx e) (read_result cx) (root_es with gas_obs := gs) =
    (INL rhs,mid with gas_obs := []) /\ valid_horizon cx st0 H0 mid.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func cenv cx es s0) /\
  (!H. valid_horizon cx st0 H root_es.storage_trace ==> stmt_state_rel H ctx func cenv cx root_es t) /\
  t = update_var out (if tr then tload (n2w slot) s0 else sload (n2w slot) s0)
    (s0 with vs_inst_idx := LENGTH s1.cs_current_insts) /\
  alloca_history func u /\ u.vs_current_bb = s2.cs_current_bb /\
  u.vs_inst_idx = LENGTH s2.cs_current_insts /\ fn_has_code s2 s3 func /\
  fn_inst_ids_distinct func /\ run_inst_seq (emitted_insts s2 s3) u = OK oprun /\
  operated = oprun with vs_inst_idx := LENGTH s3.cs_current_insts ==>
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid operated /\
    storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx mid Gop tnop operated /\
    return_buf_frame d cenv s3 operated /\ ret_pc_ok cenv s3 operated /\
    local_ptrs_reserved cenv s3 /\
    (!x. not_fresh_at sa x ==> FLOOKUP Gop x = FLOOKUP G0 x /\
      op_taint tnop (Var x) = op_taint tn0 (Var x))) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    valid_horizon cx st0 H root_es.storage_trace /\ valid_horizon cx st0 H es.storage_trace) /\
  alloca_frame cenv es sa s0 cenv mid operated /\
  (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==> lookup_var x operated = SOME v) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==> FLOOKUP operated.vs_allocas aid = SOME b) /\
  s0.vs_alloca_next <= operated.vs_alloca_next /\ alloca_inv operated /\ alloca_history func operated /\
  s3.cs_current_bb = s2.cs_current_bb /\
  s3.cs_current_insts = s2.cs_current_insts ++ emitted_insts s2 s3
Proof
  strip_tac >>
  `sa.cs_next_var <= s1.cs_next_var /\ s1.cs_next_var <= s2.cs_next_var /\
   s2.cs_next_var <= s3.cs_next_var` by
    (drule emitted_insts_emit_op >>
     `ci_mono s1 s2` by metis_tac[ci_mono_lower_value_compile_expr, pairTheory.SND] >>
     `ci_mono s2 s3` by metis_tac[cj 3 stmtLoweringMonoTheory.ci_mono_compile_expr_sa, pairTheory.SND] >>
     fs[ci_mono_def]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s1 x` by
    metis_tac[not_fresh_at_mono] >>
  `(!x. not_fresh_at sa x ==> FLOOKUP Gload x = FLOOKUP G0 x /\
      op_taint tnload (Var x) = op_taint tn0 (Var x))` by metis_tac[] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    stmt_state_rel H ctx func cenv cx mid operated /\
    storage_well_formed_on cx mid (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx mid Gop tnop operated /\
    return_buf_frame d cenv s3 operated /\ ret_pc_ok cenv s3 operated /\
    local_ptrs_reserved cenv s3 /\
    (!x. not_fresh_at sa x ==> FLOOKUP Gop x = FLOOKUP G0 x /\
      op_taint tnop (Var x) = op_taint tn0 (Var x))` by
    (gen_tac >> strip_tac >> drule_all augassign_toplevel_success_frames_full >> simp[]) >>
  `straight_fresh (compile_binop bop (Var out) op ty NONE
    (if bop = Exp then expr_int_literal e else NONE))` by
    (irule augAssignPtrCompilerTheory.compile_binop_straight_fresh_ptr >>
     qpat_assum `well_typed_binop _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> Cases_on `bop` >> simp[well_typed_binop_def]) >>
  drule (iffLR straight_fresh_def) >> disch_then (drule_then strip_assume_tac) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) (emitted_insts s2 s3)` by
    (drule fragGasFreshTheory.writes_fresh_path_opcodes >> simp[EVERY_MEM] >> metis_tac[]) >>
  `(!z. not_fresh_at s2 z ==> lookup_var z operated = lookup_var z u) /\
   (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s0)` by metis_tac[] >>
  `sa.cs_next_var <= s2.cs_next_var` by decide_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  drule_all augassign_toplevel_success_alloca_full >> strip_tac >> metis_tac[]
QED

Theorem augassign_toplevel_continue_full:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr ty,id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) ty = SOME tvt /\
  read_storage_slot cx tr (n2w slot) tvt es = (INL cur,es) /\
  root_es = es with storage_trace := es.storage_trace ++ [StorageRoot tr slot tvt] /\
  expr_body_pre cenv cx env e root_es /\
  (!tail. bind (eval_expr cx e) (read_result cx)
    (root_es with gas_obs := gs ++ tail) = (INL rhs,mid with gas_obs := tail)) /\
  storage_trace_domain cx st0 mid.storage_trace /\
  gas_admissible (eval_stmt cx (AugAssign ty (TopLevelNameTarget (src,id)) bop e))
    (stmt_res_ok lctx) es /\
  well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn /\
  (bop = Exp ==> nonneg_int_literal e) /\
  (bop = ShL \/ bop = ShR ==> shift_amount_ok e) /\
  is_word_type ty /\ type_bits ty MOD 8 = 0 /\ value_has_type tvt cur /\
  word_value cur /\ type_slot_size tvt = 1 /\ well_formed_type_value tvt /\
  emit_op (if tr then TLOAD else SLOAD) [Lit (n2w slot)] sa = (Var out,s1) /\
  lower_value compile_expr cenv ty e s1 = (op,s2) /\
  compile_binop bop (Var out) op ty NONE
    (if bop = Exp then expr_int_literal e else NONE) s2 = (res_op,s3) /\
  emit_void (if tr then TSTORE else SSTORE) [Lit (n2w slot);res_op] s3 = ((),sb) /\
  fn_has_code s2 s3 func /\ fn_has_code s3 sb func /\
  fn_inst_ids_distinct func /\ ~ctx_has_dalloca ctx /\
  t = update_var out (if tr then tload (n2w slot) s0 else sload (n2w slot) s0)
    (s0 with vs_inst_idx := LENGTH s1.cs_current_insts) /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s0 /\
    FLOOKUP Gload x = FLOOKUP G0 x /\
    op_taint tnload (Var x) = op_taint tn0 (Var x)) /\
  tnload.t_mem = tn0.t_mem /\ tnload.t_stor = tn0.t_stor /\
  tnload.t_trans = tn0.t_trans /\ tnload.t_imm = tn0.t_imm /\
  return_buf_frame d cenv s1 t /\ ret_pc_ok cenv s1 t /\
  local_ptrs_reserved cenv s1 /\
  (!H. valid_horizon cx st0 H root_es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx root_es t /\
    storage_well_formed_on cx root_es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx root_es Gload tnload t) /\
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s0,G0,tn0) [] (OK t,Gload,tnload)) /\
  eval_operand (Var out) t = SOME (typed_val_to_w256 tvt cur) /\
  op_prov Gload (Var out) = NONE /\ op_taint tnload (Var out) = {} /\
  ~t.vs_halted /\ t.vs_current_bb = s1.cs_current_bb /\
  t.vs_inst_idx = LENGTH s1.cs_current_insts /\ alloca_history func t /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0) /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!H. valid_horizon cx st0 H mid.storage_trace ==>
    ~u.vs_halted /\
    expr_post H ctx func cenv cx e root_es s1 s2 t mid rhs op u /\
    expr_store_bound cx (post_value_type cenv e) rhs op u /\
    u.vs_current_bb = s2.cs_current_bb /\
    u.vs_inst_idx = LENGTH s2.cs_current_insts /\
    alloca_history func u /\ t.vs_alloca_next <= u.vs_alloca_next /\
    ghost_inv_at (DF H) lo d cenv cx mid Gr tnr u /\
    ptr_val_ok cx (post_value_type cenv e) rhs op Gr tnr u /\
    (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op Gr u) /\
    ghost_kept_at lo cenv root_es s1 Gload tnload t Gr tnr) ==>
  gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
    (bind (lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0) tvt bop cur rhs))
      (write_place cx (StoragePlace tr (n2w slot) tvt)))
    (mid,u,Gr,tnr)
    (\H res ee G tn t. ?cenv''.
      stmt_lands lctx sb res t /\ ~t.vs_halted /\
      (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv) /\
      cenv_top_ext cenv cenv'' ee.scopes /\
      stmt_state_rel H ctx func cenv'' cx ee t /\
      storage_well_formed_on cx ee (FST H) /\
      return_buf_frame d cenv'' sb t /\ alloca_history func t /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv'' cx ee G tn t /\
      (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
        lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
        FLOOKUP t.vs_allocas aid = SOME b) /\
      (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
        op_taint tn (Var x) = op_taint tn0 (Var x)))
    (\H res ee gt r. !tail.
      stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r)
Proof
  strip_tac >> qabbrev_tac `H0 = storage_trace_horizon mid.storage_trace` >>
  `valid_horizon cx st0 H0 mid.storage_trace` by fs[storage_trace_domain_def, Abbr `H0`] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> ~u.vs_halted /\ _`
    (drule_then strip_assume_tac) >>
  `bind (eval_expr cx e) (read_result cx) (root_es with gas_obs := gs) =
    (INL rhs,mid with gas_obs := [])` by
    (qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >> simp[NoAsms]) >>
  drule_all augassign_toplevel_rhs_numeric_facts_full >> strip_tac >>
  `is_word_type (expr_type e)` by
    metis_tac[well_typed_binop_augassign_word, word_value_type_word] >>
  `eval_operand (Var out) t = SOME (val_to_w256 cur)` by
    metis_tac[typed_val_to_w256_word_value] >>
  drule_all augassign_toplevel_rhs_operands_full >> strip_tac >>
  drule_all augassign_toplevel_operator_endpoint_full >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac)
  >- suspend "success" >>
  irule gas_outcome_full_exit >> reverse conj_tac >- simp[] >>
  qexistsl_tac [`Gabort`, `mid`,
    `Abort Revert_abort (abort_state with vs_inst_idx := abort_idx)`,
    `INR (Error (RuntimeError msg))`, `tnabort`] >>
  simp[lift_sum_def, bind_def, raise_def, exit_result_def, stmt_exit_ptr_def,
    exprSimDefsTheory.expr_exit_def] >> fs[ghost_inv_at_def]
QED

Resume augassign_toplevel_continue_full[success]:
  `(!H. valid_horizon cx st0 H root_es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx root_es t) /\
   (!H. valid_horizon cx st0 H mid.storage_trace ==>
      expr_post H ctx func cenv cx e root_es s1 s2 t mid rhs op u /\
      t.vs_alloca_next <= u.vs_alloca_next /\ ghost_inv_at (DF H) lo d cenv cx mid Gr tnr u /\
      ghost_kept_at lo cenv root_es s1 Gload tnload t Gr tnr)` by metis_tac[] >>
  drule_all augassign_toplevel_success_prepare_full >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> stmt_state_rel _ _ _ _ _ _ operated /\ _`
    (drule_then strip_assume_tac) >>
  `~operated.vs_halted /\ operated.vs_current_bb = s3.cs_current_bb /\
   operated.vs_inst_idx = LENGTH s3.cs_current_insts` by
    (qpat_assum `operated = (u with vs_inst_idx := _) with vs_vars := _` SUBST1_TAC >> simp[]) >>
  Cases_on `cx.txn.is_static`
  >- (irule gas_outcome_full_exit >> reverse conj_tac >- simp[] >>
      qexistsl_tac [`Gop`, `mid`,
        `Abort ExHalt_abort (halt_state (set_returndata [] operated))`,
        `INR (Error (RuntimeError "write in static context"))`, `tnop`] >>
      simp[lift_sum_def, bind_def, return_def, write_place_def,
        write_storage_slot_eq, exit_result_def] >>
      qx_gen_tac `H` >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> stmt_state_rel _ _ _ _ _ _ operated /\ _`
        (drule_then strip_assume_tac) >>
      qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> ~u.vs_halted /\ _`
        (drule_then strip_assume_tac) >>
      `allocas_from lo u /\ lo <= u.vs_alloca_next /\ allocas_from lo operated` by
        fs[ghost_inv_at_def] >>
      `operated.vs_call_ctx.cc_static` by
        (qpat_assum `stmt_state_rel H ctx func cenv cx mid operated` mp_tac >>
         simp[NoAsms, stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
         rpt strip_tac >> gvs[]) >>
      `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (u,Gr,tnr) []
        (OK operated,Gop,tnop)` by
        (qpat_assum `!D lo. _ ==> gas_origin_ptr_path _ (u,Gr,tnr) _ _`
          (qspecl_then [`DF H`, `lo`] mp_tac) >> simp[]) >>
      `gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (operated,Gop,tnop) []
        (Abort ExHalt_abort (halt_state (set_returndata [] operated)),Gop,tnop)` by
        (irule storage_emit_static_origin_ptr >> simp[] >>
         qexistsl_tac [`n2w slot`, `Lit (n2w slot)`, `s3`, `sb`, `tr`,
           `res_op`, `val_to_w256 result`] >> gvs[eval_operand_def, op_taint_def]) >>
      conj_tac
      >- (`oprun with vs_inst_idx := LENGTH s2.cs_current_insts +
              LENGTH (emitted_insts s2 s3) = operated` by simp[LENGTH_APPEND] >>
          qpat_assum `oprun with vs_inst_idx := _ = operated`
            (fn th => pure_rewrite_tac[th]) >>
          qpat_assum `gas_origin_ptr_path _ (u,Gr,tnr) [] (OK operated,Gop,tnop)`
            (mp_then Any mp_tac gas_origin_ptr_path_append) >>
          disch_then (qspecl_then [`operated`, `Gop`, `tnop`, `[]`,
            `Abort ExHalt_abort (halt_state (set_returndata [] operated))`,
            `Gop`, `tnop`] mp_tac) >>
          pure_rewrite_tac[APPEND] >> disch_then irule >>
          conj_tac >- REFL_TAC >> first_assum ACCEPT_TAC) >>
      simp[stmt_exit_ptr_def, exprSimDefsTheory.expr_exit_def,
        halt_state_def, set_returndata_def]) >>
  `~operated.vs_call_ctx.cc_static /\
   operated.vs_call_ctx.cc_address = cx.txn.target` by
    (qpat_assum `stmt_state_rel H0 ctx func cenv cx mid operated` mp_tac >>
     simp[NoAsms, stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
         rpt strip_tac >> gvs[]) >>
  irule augassign_toplevel_success_continue_full >> simp[] >>
  qexistsl_tac [`Gop`, `es`, `operated`, `res_op`, `root_es`, `s3`, `tnop`] >> simp[] >>
  gen_tac >> strip_tac >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by fs[ghost_inv_at_def] >>
  qpat_assum `!D lo. _ ==> gas_origin_ptr_path _ (u,Gr,tnr) _ _`
    (qspecl_then [`DF H`, `lo`] mp_tac) >>
  impl_tac >- simp[] >>
  `oprun with vs_inst_idx := LENGTH s2.cs_current_insts + LENGTH (emitted_insts s2 s3) = operated` by
    simp[LENGTH_APPEND] >>
  metis_tac[]
QED

Finalise augassign_toplevel_continue_full
