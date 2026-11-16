(* Source readiness and a common loaded endpoint for scalar AugAssign. *)
Theory augAssignFullToplevelPrefix
Ancestors
  augAssignFullLoad augAssignFullStateFrame augAssignFullHistory augAssignFullRhs
  stmtSimAugAssignStorage bodyFullPreds bodySimFull bodyPtrDefs
  exprSimHypsDefs exprSimProps loweringPosts exprLoweringProps emitHelperProps
  freshWrites gasShadow gasOutcomeFull vyperStorageFootprint loweringSlice
  ptrDiscipline exprSimUnwrap augAssignStorageFieldSource
  vyperInterpreter vyperState venomState venomInst venomExecSemantics finite_map list

Theorem augassign_toplevel_rhs_ready_full[local]:
  (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
     eval_target_place cx (TopLevelNameTarget (src,id)) s'' = (INL p,t') /\
     read_place cx p s'3' = (INL cur,t'') /\
     place_type_value cx p s'4' = (INL ptv,t'3') ==>
     body_expr_full_ok cx e) /\
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr ty,id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) ty = SOME tvt /\
  read_storage_slot cx tr (n2w slot) tvt es = (INL cur,es) ==>
  body_expr_full_ok cx e
Proof
  strip_tac >>
  drule_all eval_target_place_toplevel >>
  disch_then (qspec_then `es` strip_assume_tac) >>
  first_x_assum irule >>
  goal_assum (drule_at Any) >>
  simp[read_place_def, place_type_value_def, return_def] >> metis_tac[]
QED

Theorem augassign_toplevel_loaded_frame_full[local]:
  emit_op (if tr then TLOAD else SLOAD) [Lit (n2w slot)] sa = (Var out,sb) /\
  cs_extends sa sb /\ fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
     not_fresh_at sa x) /\
  storage_trace_domain cx st0 (es.storage_trace ++ [StorageRoot tr slot tvt]) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
     stmt_state_rel H ctx func cenv cx es s /\
     storage_well_formed_on cx es (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  t = update_var out (if tr then tload (n2w slot) s else sload (n2w slot) s)
        (s with vs_inst_idx := LENGTH sb.cs_current_insts) /\
  (!x. not_fresh_at sa x ==>
     lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
     op_taint tn' (Var x) = op_taint tn (Var x)) /\
  tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
  tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm ==>
  ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func t /\
  return_buf_frame d cenv sb t /\ ret_pc_ok cenv sb t /\
  local_ptrs_reserved cenv sb /\
  (!H. valid_horizon cx st0 H (es.storage_trace ++ [StorageRoot tr slot tvt]) ==>
     stmt_state_rel H ctx func cenv cx es t /\
     storage_well_formed_on cx es (FST H) /\
     ghost_inv_at (DF H) lo d cenv cx es G' tn' t)
Proof
  strip_tac >>
  qabbrev_tac `H0 = storage_trace_horizon
    (es.storage_trace ++ [StorageRoot tr slot tvt])` >>
  `valid_horizon cx st0 H0 (es.storage_trace ++ [StorageRoot tr slot tvt])` by
    fs[storage_trace_domain_def, Abbr `H0`] >>
  `valid_horizon cx st0 H0 es.storage_trace` by
    metis_tac[valid_horizon_append] >>
  `alloca_inv s` by metis_tac[stmt_state_rel_def] >>
  `alloca_history func t` by
    (qpat_assum `t = _` SUBST1_TAC >>
     irule augassign_emit_word_history >>
     simp[] >> qexistsl_tac [`[Lit (n2w slot)]`, `if tr then TLOAD else SLOAD`, `sa`] >>
     Cases_on `tr` >>
     simp[step_inst_base_opcode_eqs, mk_inst_def, exec_read1_def,
          eval_operand_def, is_terminator_def]) >>
  `same_blocks sa sb` by metis_tac[emit_op_same_blocks] >>
  simp[same_blocks_def, update_var_def] >>
  `!H. valid_horizon cx st0 H (es.storage_trace ++ [StorageRoot tr slot tvt]) ==>
     stmt_state_rel H ctx func cenv cx es t /\
     ghost_inv_at (DF H) lo d cenv cx es G' tn' t /\
     return_buf_frame d cenv sb t /\ ret_pc_ok cenv sb t /\
     local_ptrs_reserved cenv sb /\ storage_well_formed_on cx es (FST H)` by
    (qx_gen_tac `H` >> strip_tac >>
     `valid_horizon cx st0 H es.storage_trace` by
       metis_tac[valid_horizon_append] >>
     `stmt_state_rel H ctx func cenv cx es s /\
      ghost_inv_at (DF H) lo d cenv cx es G tn s /\
      storage_well_formed_on cx es (FST H)` by metis_tac[] >>
     qsuff_tac `stmt_state_rel H ctx func cenv cx es t /\
       ghost_inv_at (DF H) lo d cenv cx es G' tn' t /\
       return_buf_frame d cenv sb t /\ ret_pc_ok cenv sb t /\
       local_ptrs_reserved cenv sb` >- metis_tac[] >>
     irule augassign_exterior_state_frame >>
     qexistsl_tac [`G`, `LENGTH sb.cs_current_insts`, `s`, `sa`, `tn`] >>
     drule emitted_insts_emit_op >> strip_tac >>
     fs[update_var_def]) >>
  gvs[same_blocks_def, update_var_def] >> metis_tac[]
QED

Theorem augassign_toplevel_load_full[local]:
  emit_op (if tr then TLOAD else SLOAD) [Lit (n2w slot)] sa = (Var out,sb) /\
  cs_extends sa sb /\ fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  storage_trace_domain cx st0 (es.storage_trace ++ [StorageRoot tr slot tvt]) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  (!H. valid_horizon cx st0 H (es.storage_trace ++ [StorageRoot tr slot tvt]) ==>
    storage_holds cx tr ty (Value cur) (n2w slot) es s /\
    key_taint (if tr then tn.t_trans else tn.t_stor) (n2w slot) = {}) /\
  evaluate_type (get_tenv cx) ty = SOME tvt /\ is_word_type ty ==>
  ?t G' tn'.
    t = update_var out (if tr then tload (n2w slot) s else sload (n2w slot) s)
      (s with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
       (s,G,tn) [] (OK t,G',tn')) /\
    eval_operand (Var out) t = SOME (typed_val_to_w256 tvt cur) /\
    op_prov G' (Var out) = NONE /\ op_taint tn' (Var out) = {} /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func t /\
    return_buf_frame d cenv sb t /\ ret_pc_ok cenv sb t /\
    local_ptrs_reserved cenv sb /\
    (!H. valid_horizon cx st0 H (es.storage_trace ++ [StorageRoot tr slot tvt]) ==>
      stmt_state_rel H ctx func cenv cx es t /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx es G' tn' t)
Proof
  strip_tac >>
  qabbrev_tac `H0 = storage_trace_horizon
    (es.storage_trace ++ [StorageRoot tr slot tvt])` >>
  `valid_horizon cx st0 H0 (es.storage_trace ++ [StorageRoot tr slot tvt])` by
    fs[storage_trace_domain_def, Abbr `H0`] >>
  `valid_horizon cx st0 H0 es.storage_trace` by
    metis_tac[valid_horizon_append] >>
  `allocas_from lo s` by metis_tac[ghost_inv_at_def] >>
  `key_taint (if tr then tn.t_trans else tn.t_stor) (n2w slot) = {} /\
   storage_holds cx tr ty (Value cur) (n2w slot) es s` by metis_tac[] >>
  `eval_operand (Lit (n2w slot)) s = SOME (n2w slot) /\
   op_prov G (Lit (n2w slot)) = NONE /\ op_taint tn (Lit (n2w slot)) = {}` by
    simp[eval_operand_def, op_prov_def, op_taint_def] >>
  drule_all storage_address_load_origin_ptr >>
  disch_then (qspecl_then [`explicit`, `PG`]
    (qx_choosel_then [`t`, `G'`, `tn'`] strip_assume_tac)) >>
  drule_all augassign_toplevel_loaded_frame_full >> strip_tac >>
  qexistsl_tac [`t`, `G'`, `tn'`] >> simp[] >>
  `(if tr then tload (n2w slot) s else sload (n2w slot) s) =
     typed_val_to_w256 tvt cur` by (irule storage_holds_load >> metis_tac[]) >>
  simp[update_var_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem augassign_toplevel_rhs_entry_full:
  (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
     eval_target_place cx (TopLevelNameTarget (src,id)) s'' = (INL p,t') /\
     read_place cx p s'3' = (INL cur,t'') /\
     place_type_value cx p s'4' = (INL ptv,t'3') ==> body_expr_full_ok cx e) /\
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr ty,id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) ty = SOME tvt /\ is_word_type ty /\
  read_storage_slot cx tr (n2w slot) tvt es = (INL cur,es) /\
  root_es = es with storage_trace := es.storage_trace ++ [StorageRoot tr slot tvt] /\
  body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env e root_es /\
  gas_admissible (eval_stmt cx (AugAssign ty (TopLevelNameTarget (src,id)) bop e))
    (stmt_res_ok lctx) es /\
  emit_op (if tr then TLOAD else SLOAD) [Lit (n2w slot)] sa = (Var out,s1) /\
  lower_value compile_expr cenv ty e s1 = (op,s2) /\
  lower_value compile_expr cenv ty (gas_shadow_expr e) ss1 = (op,ss2) /\
  gas_shadow_state s1 ss1 /\ gas_shadow_state s2 ss2 /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  cs_extends sa s1 /\ fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
  fn_has_code ss1 ss2 shadow_func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s /\
  return_buf_frame d cenv sa s /\ alloca_history func s /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  storage_trace_domain cx st0 root_es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  (!H. valid_horizon cx st0 H root_es.storage_trace ==>
    storage_holds cx tr ty (Value cur) (n2w slot) es s /\
    key_taint (if tr then tn.t_trans else tn.t_stor) (n2w slot) = {}) ==>
  ?t G' tn'.
    t = update_var out (if tr then tload (n2w slot) s else sload (n2w slot) s)
      (s with vs_inst_idx := LENGTH s1.cs_current_insts) /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    return_buf_frame d cenv s1 t /\ ret_pc_ok cenv s1 t /\
    local_ptrs_reserved cenv s1 /\
    (!H. valid_horizon cx st0 H root_es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx root_es t /\
      storage_well_formed_on cx root_es (FST H) /\
      ghost_inv_at (DF H) lo d cenv cx root_es G' tn' t) /\
    (!D. gas_origin_ptr_path (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       (s,G,tn) [] (OK t,G',tn')) /\
    eval_operand (Var out) t = SOME (typed_val_to_w256 tvt cur) /\
    op_prov G' (Var out) = NONE /\ op_taint tn' (Var out) = {} /\
    ~t.vs_halted /\ t.vs_current_bb = s1.cs_current_bb /\
    t.vs_inst_idx = LENGTH s1.cs_current_insts /\ alloca_history func t /\
    gas_outcome_full
      (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx))
      (root_es,t,G',tn')
      (\H res ee G2 tn2 u. ?v. res = INL v /\
        expr_post H ctx func cenv cx e root_es s1 s2 t ee v op u /\
        expr_store_bound cx (post_value_type cenv e) v op u /\
        u.vs_current_bb = s2.cs_current_bb /\
        u.vs_inst_idx = LENGTH s2.cs_current_insts /\
        alloca_history func u /\ t.vs_alloca_next <= u.vs_alloca_next /\
        ghost_inv_at (DF H) lo d cenv cx ee G2 tn2 u /\
        ptr_val_ok cx (post_value_type cenv e) v op G2 tn2 u /\
        (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G2 u) /\
        ghost_kept_at lo cenv root_es s1 G' tn' t G2 tn2)
      (\H res ee gt r. ?ex. res = INR ex /\
        !tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) (INR ex) gt r)
Proof
  strip_tac >>
  `body_expr_full_ok cx e` by (irule augassign_toplevel_rhs_ready_full >> metis_tac[]) >>
  `!es'. eval_target_place cx (TopLevelNameTarget (src,id)) es' =
    (INL (StoragePlace tr (n2w slot) tvt),
     es' with storage_trace := es'.storage_trace ++ [StorageRoot tr slot tvt])` by
    metis_tac[eval_target_place_toplevel] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok root_es` by
    (qpat_assum `root_es = _` SUBST1_TAC >>
     irule augassign_storage_place_rhs_admissible >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
  `storage_trace_domain cx st0 (es.storage_trace ++ [StorageRoot tr slot tvt]) /\
   (!H. valid_horizon cx st0 H (es.storage_trace ++ [StorageRoot tr slot tvt]) ==>
    storage_holds cx tr ty (Value cur) (n2w slot) es s /\
    key_taint (if tr then tn.t_trans else tn.t_stor) (n2w slot) = {})` by (gvs[] >> metis_tac[]) >>
  drule_all augassign_toplevel_load_full >>
  disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`, `PG`]
    (qx_choosel_then [`t`, `G'`, `tn'`] strip_assume_tac)) >>
  `!H. valid_horizon cx st0 H root_es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx root_es t /\
    storage_well_formed_on cx root_es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx root_es G' tn' t` by
    (gvs[storage_well_formed_on_def] >> metis_tac[]) >>
  `sa.cs_next_var <= s1.cs_next_var` by
    (drule emitted_insts_emit_op >> simp[]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s1 x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s1 x)` by
    (conj_tac >- metis_tac[not_fresh_at_mono] >> fs[ret_pc_ok_def]) >>
  qexistsl_tac [`t`, `G'`, `tn'`] >> simp[IgnAsm `root_es = _`, IgnAsm `t = _`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  irule augassign_rhs_invoke_full >>
  simp[IgnAsm `root_es = _`, IgnAsm `t = _`] >>
  reverse conj_tac >- metis_tac[] >>
  qexistsl_tac [`shadow_func`, `ss1`, `ss2`, `ty`] >> simp[]
QED
