(* Memory case of the body induction, augmented assignment
   (bodyMemAugAssign's dispatch): a word storage or transient variable
   (S1's body_augassign_toplevel_word).  The lowering loads x with an
   SLOAD or TLOAD, lowers e at x's type, runs the operator and stores the
   result with an SSTORE or TSTORE; neither touches memory, so the pieces
   compose as in bodyMemAugAssignLocal.

   The *_mem_src helpers are copies of S1 source-side lemmas that live only
   on the S1 branch (stmtSimAugAssignStorage there), generalised over the
   memory flag where S1's fix it to F. *)
Theory bodyMemAugAssignTopWord
Ancestors
  bodySim vyperTypeCallGraph
  bodyMemoryPreds bodyMemoryDefs bodyMemAssignTopWord bodyDeclMemoryCounted
  bodyDeclMemoryCore allocaFootprint instMemFrontier memSafeRun
  bodyBinopFamiliesMemory bodyBinopFragMemory
  exprSimMemDefs exprSimSource exprSimHyps bodyExprPreFacts
  stmtSimAugAssign stmtSimAssignStorage exprSimTopLevelProps
  accountsRelProps exprSimUnwrap exprSimProps bodyStorageMetadata
  vyperTypeEnv vyperStorageLayoutSafety vyperStorageBackend
  exprBopSimDefs exprBopSimProps
  gasOutcome gasContext gasExemptCert gasSummary gasSummaryCompose
  fragGasMode fragGasPath fragGasPathMem fragGasSeq
  stmtSimProps exprSimHypsDefs stmtSimDefs exprSimDefs loweringPosts
  allocLimits fragExec fragExecMem localPtrsProps freshWrites
  exprOpenPrimitives exprOperandVar
  exprLowering exprBopLowering stmtLowering emitHelper emitHelperProps
  exprLoweringProps compileEnv loweringStateRelDefs valueEncoding
  supportedStmtTraverse supportedStmts supportedExprs supportedTypes
  vyperInterpreter vyperState vyperValue vyperValueOperation vyperContext
  vyperExprNoControl vyperTypeSystem vyperTyping
  vyperTypeExprResult vyperTypeExprSoundness
  vyperTypeInvariants vyperTypeBuiltins vyperTypeStatePreservation
  vyperLookup vyperAST
  venomExecSemantics venomExecProofs venomInst venomState
  list rich_list finite_map pred_set
Libs
  monadsyntax

(* ===== The source side (S1 copies) ===== *)

(* S1 stmtSimAugAssignStorage's eval_target_place_toplevel. *)
Theorem eval_target_place_toplevel_mem_src[local]:
  !cx src id es ts tr typ id_str slot tvt.
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    evaluate_type (get_tenv cx) typ = SOME tvt ==>
    eval_target_place cx (TopLevelNameTarget (src, id)) es =
      (INL (StoragePlace tr (n2w slot) tvt), es) /\
    place_type_value cx (StoragePlace tr (n2w slot) tvt) es = (INL tvt, es)
Proof
  rpt strip_tac >>
  simp[Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
       return_def, LET_THM, get_place_def, place_type_value_def]
QED

(* S1 stmtSimAugAssignStorage's read_storage_slot_gas_obs. *)
Theorem read_storage_slot_gas_obs_mem_src[local]:
  read_storage_slot cx tr slot tv es = (res, ee) ==>
  read_storage_slot cx tr slot tv (es with gas_obs := gs) =
    (res, ee with gas_obs := gs)
Proof
  Cases_on `tr` >>
  simp[read_storage_slot_def, get_storage_backend_def, bind_def,
       get_accounts_def, get_transient_storage_def]
  >- (Cases_on `decode_value (lookup_transient_storage cx.txn.target es.tStorage)
        (w2n slot) tv` >>
      simp[lift_option_def, return_def, raise_def] >> strip_tac >>
      gvs[return_def, raise_def]) >>
  Cases_on `decode_value (lookup_account cx.txn.target es.accounts).storage
    (w2n slot) tv` >>
  simp[lift_option_def, return_def, raise_def] >> strip_tac >>
  gvs[return_def, raise_def]
QED

(* S1 stmtSimAugAssignStorage's eval_augassign_toplevel_forced. *)
Theorem eval_augassign_toplevel_forced_mem_src[local]:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME tvt /\
  read_storage_slot cx tr (n2w slot) tvt es = (INL v0, es) ==>
  eval_stmt cx (AugAssign ty (TopLevelNameTarget (src,id)) bop e) es =
  (do v <- bind (eval_expr cx e) (read_result cx);
      r <- lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        tvt bop v0 v);
      write_storage_slot cx tr (n2w slot) tvt r od) es
Proof
  strip_tac >> drule_all eval_target_place_toplevel_mem_src >>
  disch_then (qspec_then `es` strip_assume_tac) >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, read_place_def,
       write_place_def] >>
  Cases_on `eval_expr cx e es` >> rename1 `_ = (raw, st)` >>
  Cases_on `raw` >> simp[bind_def]
QED

(* S1 stmtSimAugAssignStorage's augassign_toplevel_rhs_exception. *)
Theorem augassign_toplevel_rhs_exception_mem_src[local]:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME tvt /\
  read_storage_slot cx tr (n2w slot) tvt es = (INL v0, es) /\
  bind (eval_expr cx e) (read_result cx) es = (INR ex, ee) ==>
  eval_stmt cx (AugAssign ty (TopLevelNameTarget (src,id)) bop e) es =
    (INR ex, ee)
Proof
  strip_tac >> drule_all eval_augassign_toplevel_forced_mem_src >>
  disch_then (qspecl_then [`ty`, `e`, `bop`] mp_tac) >>
  simp[Once bind_def]
QED

(* S1 stmtSimAugAssignStorage's augassign_toplevel_rhs_normal. *)
Theorem augassign_toplevel_rhs_normal_mem_src[local]:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME tvt /\
  read_storage_slot cx tr (n2w slot) tvt es = (INL v0, es) /\
  bind (eval_expr cx e) (read_result cx) es = (INL v, ee) ==>
  eval_stmt cx (AugAssign ty (TopLevelNameTarget (src,id)) bop e) es =
  bind (lift_sum (evaluate_binop
    (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
    tvt bop v0 v)) (write_storage_slot cx tr (n2w slot) tvt) ee
Proof
  strip_tac >> drule_all eval_augassign_toplevel_forced_mem_src >>
  disch_then (qspecl_then [`ty`, `e`, `bop`] mp_tac) >>
  simp[Once bind_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

(* S1 stmtSimAugAssignStorage's augassign_toplevel_rhs_admissible. *)
Theorem augassign_toplevel_rhs_admissible_mem_src[local]:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME tvt /\
  read_storage_slot cx tr (n2w slot) tvt es = (INL v0, es) /\
  gas_admissible (eval_stmt cx
    (AugAssign ty (TopLevelNameTarget (src,id)) bop e)) (stmt_res_ok lctx) es ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es
Proof
  strip_tac >> rw[gas_admissible_def] >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  rename1 `INR ex` >>
  `read_storage_slot cx tr (n2w slot) tvt (es with gas_obs := gs) =
     (INL v0, es with gas_obs := gs)` by
    metis_tac[read_storage_slot_gas_obs_mem_src] >>
  `eval_stmt cx (AugAssign ty (TopLevelNameTarget (src,id)) bop e)
     (es with gas_obs := gs) = (INR ex, ee)` by
    (irule augassign_toplevel_rhs_exception_mem_src >> metis_tac[]) >>
  `stmt_res_ok lctx (INR ex)` by metis_tac[gas_admissible_result] >>
  qpat_x_assum `bind _ _ _ = _` mp_tac >> simp[bind_def] >>
  Cases_on `eval_expr cx e (es with gas_obs := gs)` >>
  rename1 `_ = (raw, est)` >> Cases_on `raw` >> simp[] >> strip_tac >>
  imp_res_tac read_result_no_control >>
  imp_res_tac (cj 1 eval_expr_no_control) >>
  gvs[no_control_exc_def, expr_res_ok_def, stmt_res_ok_def]
QED

(* S1 stmtSimAugAssignStorage's augassign_toplevel_binop_admissible. *)
Theorem augassign_toplevel_binop_admissible_mem_src[local]:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME tvt /\
  read_storage_slot cx tr (n2w slot) tvt es = (INL v0, es) /\
  bop <> In /\ bop <> NotIn /\
  gas_admissible (eval_stmt cx
    (AugAssign ty (TopLevelNameTarget (src,id)) bop e)) (stmt_res_ok lctx) es /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v, ee) ==>
  expr_res_ok (bop_result cx ty bop [ty; expr_type e] v0 v ee)
Proof
  strip_tac >>
  `bop_result cx ty bop [ty; expr_type e] v0 v ee =
   case evaluate_binop
     (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
     tvt bop v0 v of INL w => INL w | INR err => INR (Error err)` by
    (irule bop_result_augassign >> simp[]) >>
  pop_assum SUBST1_TAC >>
  Cases_on `evaluate_binop
    (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
    tvt bop v0 v` >- simp[expr_res_ok_def] >>
  rename1 `_ = INR err` >>
  `read_storage_slot cx tr (n2w slot) tvt (es with gas_obs := gs) =
     (INL v0, es with gas_obs := gs)` by
    metis_tac[read_storage_slot_gas_obs_mem_src] >>
  `eval_stmt cx (AugAssign ty (TopLevelNameTarget (src,id)) bop e)
     (es with gas_obs := gs) = (INR (Error err), ee)` by
    (drule_all augassign_toplevel_rhs_normal_mem_src >>
     disch_then (qspecl_then [`ty`, `bop`] mp_tac) >>
     simp[lift_sum_def, bind_def, raise_def]) >>
  `stmt_res_ok lctx (INR (Error err))` by metis_tac[gas_admissible_result] >>
  gvs[stmt_res_ok_def, expr_res_ok_def]
QED

(* S1 stmtSimAugAssignStorage's declared_storage_holds_value. *)
Theorem declared_storage_holds_value_mem_src[local]:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr ty, id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) ty = SOME tvt /\
  read_storage_slot cx tr (n2w slot) tvt es = (INL v, es) /\
  contract_storage_well_formed cx es /\ storage_layout_safe cx /\
  stmt_state_rel ctx func cenv cx es s ==>
  storage_holds cx tr ty (Value v) (n2w slot) es s
Proof
  strip_tac >>
  `slots_in_range (get_storage cx es tr) (w2n ((n2w slot):bytes32)) tvt` by
    (irule toplevel_storage_slots_in_range >> metis_tac[]) >>
  `declared_storage_region cx src id [] = SOME (tr,n2w slot,tvt)` by
    simp[declared_storage_region_def] >>
  `!st. storage_read_live cx tr st (n2w slot) tvt` by
    (gen_tac >> irule declared_storage_region_read_live >> metis_tac[]) >>
  `w2n ((n2w slot):bytes32) + type_slot_size tvt <= dimword (:256)` by
    (drule_all storage_layout_safe_region_nonoverflow >> simp[]) >>
  `storage_range_agree (get_storage cx es tr)
    (if tr then contract_transient s else contract_storage s) (n2w slot) tvt` by
    (irule storage_range_agree_of_live >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`cx`, `tr`] >> simp[] >> Cases_on `tr` >>
     gvs[stmt_state_rel_def, state_rel_def, storage_rel_def,
         transient_rel_def, get_storage_def, vfmStateTheory.lookup_account_def]) >>
  gvs[storage_holds_def, read_result_def, return_def]
QED

(* S1 stmtSimAugAssignStorage's augassign_toplevel_place_exec. *)
Theorem augassign_toplevel_place_exec_mem_src[local]:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME tvt /\
  gas_marked_path memory ctx func s0 0 (OK t) ==>
  gas_marked_exec memory (ctx,func)
    (eval_target_place cx (TopLevelNameTarget (src,id)))
    (es,s0) [] (INL (StoragePlace tr (n2w slot) tvt)) es (OK t)
Proof
  strip_tac >> simp[gas_marked_exec_def, gas_explicit_def] >>
  gen_tac >> irule (cj 1 eval_target_place_toplevel_mem_src) >> metis_tac[]
QED

(* S1 stmtSimAugAssignStorage's augassign_toplevel_rhs_exempt. *)
Theorem augassign_toplevel_rhs_exempt_mem_src[local]:
  read_storage_slot cx tr slot tvt es = (INL v0, es) /\
  gas_marked_exec memory (ctx,func)
    (eval_target_place cx (TopLevelNameTarget (src,id)))
    (es,s0) [] (INL (StoragePlace tr slot tvt)) es (OK t) /\
  ~t.vs_halted /\
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()))
    (es with gas_obs := [],t) marks (err,ee) (leaf,fin) ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (eval_stmt cx
      (AugAssign ty (TopLevelNameTarget (src,id)) bop e)) (return ()))
    (es,s0) marks (err,ee) (leaf,fin)
Proof
  strip_tac >>
  `ignore_bind (eval_stmt cx
     (AugAssign ty (TopLevelNameTarget (src,id)) bop e)) (return ()) =
   do p <- eval_target_place cx (TopLevelNameTarget (src,id));
      cur <- read_place cx p;
      ptv <- place_type_value cx p;
      v <- bind (eval_expr cx e) (read_result cx);
      r <- lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        ptv bop cur v);
      ignore_bind (write_place cx p r) (return ()) od` by
    simp[Once evaluate_def, ignore_bind_def, bind_assoc] >>
  pop_assum SUBST1_TAC >>
  drule gas_exempt_cert_bind_place >> simp[] >> disch_then irule >>
  `gas_marked_exec memory (ctx,func) (read_place cx (StoragePlace tr slot tvt))
     (es with gas_obs := [],t) [] (INL v0)
     (es with gas_obs := []) (OK t)` by
    (simp[gas_marked_exec_def, gas_explicit_def] >> conj_tac
     >- (gen_tac >> simp[read_place_def] >>
         metis_tac[read_storage_slot_gas_obs_mem_src]) >>
     irule gas_marked_path_from_mem >> simp[gas_path_mem_rules]) >>
  drule gas_exempt_cert_bind_value >> simp[] >> disch_then irule >>
  simp[place_type_value_def, bind_return] >>
  irule gas_exempt_cert_error_value >> simp[]
QED

(* S1 stmtSimAugAssign's gas_marked_exec_zero_prefix, at either memory
   flag. *)
Theorem gas_marked_exec_zero_prefix_mem_src[local]:
  gas_marked_path memory ctx func s0 0 (OK t) /\
  gas_marked_exec memory (ctx,func) source (es with gas_obs := [],t)
    marks res ee r ==>
  gas_marked_exec memory (ctx,func) source (es,s0) marks res ee r
Proof
  strip_tac >>
  `gas_explicit marks s0.vs_gas_readings =
   gas_explicit marks t.vs_gas_readings` by
    (drule gas_marked_path_ok_suffix >> simp[]) >>
  gvs[gas_marked_exec_def] >>
  drule_all gas_marked_path_then >> simp[]
QED

(* S1 stmtSimAugAssignStorage's augassign_toplevel_rhs_exception_exec, at
   either memory flag. *)
Theorem augassign_toplevel_rhs_exception_exec_mem_src[local]:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME tvt /\
  read_storage_slot cx tr (n2w slot) tvt es = (INL v0, es) /\
  gas_marked_path memory ctx func s0 0 (OK t) /\
  gas_marked_exec memory (ctx,func) (bind (eval_expr cx e) (read_result cx))
    (es with gas_obs := [],t) marks (INR ex) ee r ==>
  gas_marked_exec memory (ctx,func)
    (eval_stmt cx (AugAssign ty (TopLevelNameTarget (src,id)) bop e))
    (es,s0) marks (INR ex) ee r
Proof
  strip_tac >> drule_all gas_marked_exec_zero_prefix_mem_src >>
  simp[gas_marked_exec_def] >> strip_tac >> simp[] >>
  gen_tac >> irule augassign_toplevel_rhs_exception_mem_src >> simp[] >>
  qexists_tac `v0` >> metis_tac[read_storage_slot_gas_obs_mem_src]
QED

(* S1 stmtSimAugAssignStorage's augassign_toplevel_rhs_normal_exec, at
   either memory flag. *)
Theorem augassign_toplevel_rhs_normal_exec_mem_src[local]:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME tvt /\
  read_storage_slot cx tr (n2w slot) tvt es = (INL v0, es) /\
  gas_marked_path memory ctx func s0 0 (OK t) /\
  gas_marked_exec memory (ctx,func) (bind (eval_expr cx e) (read_result cx))
    (es with gas_obs := [],t) marks (INL v) ee (OK u) /\
  gas_marked_exec memory (ctx,func)
    (bind (lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      tvt bop v0 v)) (write_storage_slot cx tr (n2w slot) tvt))
    (ee with gas_obs := [],u) [] res fin r ==>
  gas_marked_exec memory (ctx,func)
    (eval_stmt cx (AugAssign ty (TopLevelNameTarget (src,id)) bop e))
    (es,s0) marks res fin r
Proof
  strip_tac >> drule_all gas_marked_exec_zero_prefix_mem_src >> strip_tac >>
  gvs[gas_marked_exec_def] >> conj_tac
  >- (gen_tac >>
      qpat_x_assum `!tail. bind (eval_expr cx e) _ _ = _`
        (qspec_then `tail` assume_tac) >>
      `read_storage_slot cx tr (n2w slot) tvt
         (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
         (INL v0, es with gas_obs :=
            gas_explicit marks s0.vs_gas_readings ++ tail)` by
        metis_tac[read_storage_slot_gas_obs_mem_src] >>
      drule_all augassign_toplevel_rhs_normal_mem_src >>
      disch_then (qspecl_then [`ty`, `bop`] mp_tac) >> simp[]) >>
  drule_all gas_marked_path_then >> simp[]
QED

(* S1 stmtSimAugAssignStorage's augassign_storage_continuation_exec, at
   either memory flag. *)
Theorem augassign_storage_continuation_exec_mem_src[local]:
  bind (lift_sum br) (write_storage_slot cx tr slot tvt) ee = (res,fin) /\
  gas_marked_path memory ctx func u 0 r ==>
  gas_marked_exec memory (ctx,func)
    (bind (lift_sum br) (write_storage_slot cx tr slot tvt))
    (ee,u) [] res fin r
Proof
  Cases_on `br` >>
  simp[gas_marked_exec_def, lift_sum_def, bind_def, return_def, raise_def] >>
  strip_tac >> simp[] >> gen_tac >>
  simp[write_storage_slot_gas_obs] >> gvs[]
QED

(* S1 stmtSimAugAssignStorage's augassign_toplevel_code_parts. *)
Theorem augassign_toplevel_code_parts_mem_src[local]:
  !cenv lctx ty0 ty nsid bop e sa c sf tr slot.
    stmt_env cenv lctx ty0 (AugAssign ty (TopLevelNameTarget nsid) bop e) sa =
      (c, sf) /\
    FLOOKUP cenv.ce_module_vars nsid =
      SOME (if tr then TransientLoc slot else StorageLoc slot) /\
    cenv.ce_hashmap_info nsid = NONE ==>
    c = cenv /\
    ?s1 s2 s3 cur_op rhs_op res_op.
      emit_op (if tr then TLOAD else SLOAD) [Lit slot] sa = (cur_op, s1) /\
      lower_value compile_expr cenv ty e s1 = (rhs_op, s2) /\
      compile_binop bop cur_op rhs_op ty NONE
        (if bop = Exp then expr_int_literal e else NONE) s2 = (res_op, s3) /\
      emit_void (if tr then TSTORE else SSTORE) [Lit slot; res_op] s3 =
        ((), sf)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all compile_get_target_ptr_toplevel >>
  disch_then (qspec_then `sa` assume_tac) >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` mp_tac >>
  simp[stmt_env_def, declare_stmt_local_def, compile_stmt_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  Cases_on `tr` >> simp[] >>
  qmatch_goalsub_abbrev_tac `emit_op ld [Lit slot] sa` >>
  Cases_on `emit_op ld [Lit slot] sa` >> rename1 `_ = (cur_op, s1)` >>
  simp[] >>
  Cases_on `lower_value compile_expr cenv ty e s1` >>
  rename1 `_ = (rhs_op, s2)` >> simp[] >>
  qmatch_goalsub_abbrev_tac `compile_binop bop cur_op rhs_op ty NONE lit s2` >>
  Cases_on `compile_binop bop cur_op rhs_op ty NONE lit s2` >>
  rename1 `_ = (res_op, s3)` >> simp[] >>
  qmatch_goalsub_abbrev_tac `emit_void st [Lit slot; res_op] s3` >>
  Cases_on `emit_void st [Lit slot; res_op] s3` >> simp[oneTheory.one]
QED

(* ===== The load of x, on a memory-safe path ===== *)

Theorem augassign_storage_load_frame_mem[local]:
  emit_op (if tr then TLOAD else SLOAD) [Lit slot] sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 /\
  alloca_history func s0 /\
  is_word_type ty /\ storage_holds cx tr ty (Value v) slot es s0 /\
  evaluate_type (get_tenv cx) ty = SOME tvt ==>
  ?t. gas_marked_path T ctx func s0 0 (OK t) /\
    eval_operand op t = SOME (typed_val_to_w256 tvt v) /\
    stmt_state_rel ctx func cenv cx es t /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    local_ptrs_reserved cenv sb /\ alloca_history func t /\
    (!rp. not_fresh_at sa rp ==> lookup_var rp t = lookup_var rp s0) /\
    t.vs_allocas = s0.vs_allocas /\ t.vs_alloca_next = s0.vs_alloca_next /\
    (?out. op = Var out /\ not_fresh_at sb out)
Proof
  strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_same_blocks >> strip_tac >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `w = if tr then tload slot s0 else sload slot s0` >>
  `run_inst_seq (emitted_insts sa sb) s0 = OK (update_var out w s0)` by
    (Cases_on `tr` >>
     FIRST [simp[Abbr `w`, Abbr `out`, run_inst_seq_def,
                 step_inst_base_opcode_eqs,
                 mk_inst_def, exec_read1_def, eval_operand_def]]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s0` by
    (drule emit_op_mem_ok >> disch_then irule >> Cases_on `tr` >>
     simp[below_frontier_no_ranges, mk_inst_def]) >>
  `EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
     ~is_terminator i.inst_opcode) (emitted_insts sa sb)` by
    (Cases_on `tr` >> simp[mk_inst_def, is_terminator_def]) >>
  `gas_path_mem ctx func s0 0
     (OK (update_var out w s0 with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
   ~(update_var out w s0).vs_halted /\
   (update_var out w s0).vs_current_bb = sb.cs_current_bb` by
    (irule body_decl_cursor_path >> simp[] >> qexists_tac `sa` >> simp[]) >>
  `alloca_inv s0` by fs[stmt_state_rel_def] >>
  `alloca_history func
     (update_var out w s0 with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule body_store_memory_history >> simp[] >>
     qexistsl_tac [`s0`, `sa`] >> Cases_on `tr` >>
     simp[mk_inst_def, is_terminator_def]) >>
  `w = typed_val_to_w256 tvt v` by
    (simp[Abbr `w`] >> irule storage_holds_load >> metis_tac[]) >>
  `not_local_ptr cenv es.scopes out` by
    (simp[Abbr `out`] >> irule local_ptrs_reserved_fresh >>
     qexists_tac `sa` >> simp[]) >>
  `local_ptrs_reserved cenv sb` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `stmt_state_rel ctx func cenv cx es (update_var out w s0)` by
    (irule stmt_state_rel_update_var >> simp[]) >>
  qexists_tac `update_var out w s0 with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  simp[gas_marked_path_def, stmt_state_rel_inst_idx, eval_operand_def] >>
  gvs[update_var_def] >>
  simp[Abbr `out`, lookup_var_def, FLOOKUP_UPDATE] >>
  rw[not_fresh_at_def, ASCIInumbersTheory.toString_inj] >>
  gvs[not_fresh_at_def, ASCIInumbersTheory.toString_inj]
QED

(* ===== The statement ===== *)

Theorem compile_augassign_toplevel_mem[local]:
  !d ctx func cx lctx RetQ cenv ty0 env ty src id bop e es
   ts tr id_str slot tvt vtyp.
    (!gs. expr_sim_mem ctx func cenv cx ty e (es with gas_obs := gs)) /\
    expr_body_pre cenv cx env e es /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr ty, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    evaluate_type (get_tenv cx) ty = SOME tvt /\
    well_formed_type env.type_defs ty /\
    cenv.ce_hashmap_info (src, id) = NONE /\
    cenv.ce_module_var_type (src, id) = SOME vtyp /\ is_word_type vtyp /\
    (bop = Exp ==> nonneg_int_literal e) /\
    (bop = ShL \/ bop = ShR ==> shift_amount_ok e) /\
    well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ty0
         (AugAssign ty (TopLevelNameTarget (src, id)) bop e))
      (eval_stmt cx (AugAssign ty (TopLevelNameTarget (src, id)) bop e)) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_mem_def] >> rpt gen_tac >> strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  `word_value_type ty /\ word_value_type (expr_type e)` by
    metis_tac[well_typed_binop_augassign_word] >>
  `is_word_type ty` by metis_tac[word_value_type_word] >>
  `contract_storage_well_formed cx es /\ storage_layout_safe cx /\
   storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
    fs[expr_sim_inv_def, stmt_state_rel_def, state_rel_def] >>
  drule_all toplevel_storage_ce_vars >> strip_tac >>
  drule_all toplevel_storage_read_decodes >> strip_tac >>
  drule_all augassign_toplevel_code_parts_mem_src >> strip_tac >> gvs[] >>
  suspend "load"
QED

Resume compile_augassign_toplevel_mem[load]:
  `cs_extends sa s1` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  drule compile_binop_grows >> strip_tac >>
  `cs_extends s3 sb` by
    metis_tac[cs_appends_emit_helpers, cs_appends_def] >>
  `cs_extends s1 s3 /\ cs_extends s1 sb /\ cs_extends s2 sb /\
   cs_extends sa s2 /\ cs_extends sa s3` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa s1 func /\ fn_has_code s1 s2 func /\
   fn_has_code s2 s3 func /\ fn_has_code s3 sb func` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  rename1 `read_storage_slot cx tr (n2w slot) tvt es = (INL v0,es)` >>
  `storage_holds cx tr ty (Value v0) (n2w slot) es s0` by
    (irule declared_storage_holds_value_mem_src >> metis_tac[]) >>
  drule_all augassign_storage_load_frame_mem >> strip_tac >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok
    (es with gas_obs := [])` by
    (simp[] >> irule augassign_toplevel_rhs_admissible_mem_src >> metis_tac[]) >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) t` by simp[] >>
  qpat_x_assum `!gs. expr_sim_mem _ _ _ _ _ _ _`
    (qspec_then `[]` (mp_tac o REWRITE_RULE [expr_sim_mem_def])) >>
  disch_then (qspecl_then [`s1`, `s2`, `rhs_op`, `t`] mp_tac) >>
  impl_tac >- simp[] >>
  simp[gas_outcome_def] >> strip_tac
  >- suspend "rhs_summary" >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  irule augassign_toplevel_rhs_exempt_mem_src >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  irule augassign_toplevel_place_exec_mem_src >> metis_tac[]
QED

Resume compile_augassign_toplevel_mem[rhs_summary]:
  qexists_tac `marks` >> disj1_tac >>
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
  simp[gas_summary_at_def] >> strip_tac
  >- suspend "rhs_normal" >>
  `?ex. res = INR ex` by (Cases_on `res` >> gvs[]) >> gvs[] >>
  qexistsl_tac [`INR ex`, `es_end`, `r`] >> conj_tac
  >- (irule augassign_toplevel_rhs_exception_exec_mem_src >>
      conj_tac >- metis_tac[] >>
      qexists_tac `t` >> simp[]) >>
  disj2_tac >> simp[] >> gen_tac >> simp[stmt_exit_def] >> disj1_tac >>
  metis_tac[expr_exit_INR_type]
QED

Resume compile_augassign_toplevel_mem[rhs_normal]:
  gvs[] >>
  rename1 `expr_post ctx func cenv cx e _ s1 s2 t (ee with gas_obs := []) v rhs_op u` >>
  `bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks t.vs_gas_readings) =
      (INL v, ee with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ (bind _ _) _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `expr_res_ok (bop_result cx ty bop [ty; expr_type e] v0 v
     (ee with gas_obs := []))` by
    (irule augassign_toplevel_binop_admissible_mem_src >> metis_tac[]) >>
  `well_formed_type_value tvt` by
    metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value] >>
  `value_has_type tvt v0` by
    metis_tac[read_storage_slot_success_type] >>
  `word_value v0` by metis_tac[word_value_type_typed] >>
  `type_bits ty MOD 8 = 0` by metis_tac[well_formed_type_bits] >>
  `expr_body_pre cenv cx env e
     (es with gas_obs := gas_explicit marks t.vs_gas_readings)` by simp[] >>
  drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_word_result) >>
  strip_tac >> gvs[] >>
  rename1 `value_has_type etv v` >>
  drule (REWRITE_RULE [ETA_AX] eval_expr_read_INL) >> strip_tac >>
  `!n. expr_int_literal e = SOME n ==> v = IntV n` by
    metis_tac[eval_expr_int_literal_agrees] >>
  `(bop = ShL \/ bop = ShR ==> ?i. v = IntV i /\ 0 <= i)` by
    (disch_then (fn th =>
       qpat_x_assum `_ ==> shift_amount_ok e` (assume_tac o C MP th)) >>
     drule_all eval_expr_shift_amount >> simp[]) >>
  suspend "binop"
QED

Resume compile_augassign_toplevel_mem[binop]:
  `binop_frag_val_mem ctx func cenv cx bop ty ty NONE
     (if bop = Exp then expr_int_literal e else NONE)
     [ty; expr_type e] v0 v (ee with gas_obs := [])` by
    (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `bop`, `ty`,
       `TopLevelName ty (src, id)`, `e`, `v0`, `v`, `ee with gas_obs := []`,
       `tvt`, `etv`] mp_tac binop_frag_typed_mem >>
     simp[vyperASTTheory.expr_type_def, expr_int_literal_def] >>
     disch_then irule >>
     strip_tac >> gvs[nonneg_int_literal_def, GSYM expr_int_literal_value] >>
     Cases_on `expr_int_literal e` >> gvs[]) >>
  `eval_operand (Var out) t = SOME (val_to_w256 v0)` by
    simp[typed_val_to_w256_word_value] >>
  `eval_operand rhs_op u = SOME (val_to_w256 v)` by
    (irule expr_val_rel_word >>
     fs[expr_post_def] >> goal_assum (drule_at Any) >>
     simp[word_value_type_word]) >>
  `eval_operand (Var out) u = SOME (val_to_w256 v0)` by
    (irule eval_operand_frame >> simp[] >>
     qexistsl_tac [`s1`, `t`] >> gvs[expr_post_def]) >>
  `not_fresh_at s2 out /\ local_ptrs_reserved cenv s2` by
    metis_tac[freshWritesTheory.not_fresh_at_mono, local_ptrs_reserved_next_var] >>
  `stmt_state_rel ctx func cenv cx (ee with gas_obs := []) u` by
    fs[expr_post_def] >>
  `~u.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  qpat_x_assum `binop_frag_val_mem _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [binop_frag_val_mem_def, binop_frag_mem_def]) >>
  disch_then (qspecl_then [`s2`, `s3`, `Var out`, `rhs_op`, `res_op`, `u`] mp_tac) >>
  impl_tac >- (simp[] >> metis_tac[compile_lower_value_var]) >>
  strip_tac >- suspend "operator_normal" >> suspend "operator_exit"
QED

Resume compile_augassign_toplevel_mem[operator_normal]:
  gvs[] >> rename1 `eval_operand res_op s = SOME (val_to_w256 result)` >>
  `bop_result cx ty bop [ty; expr_type e] v0 v ee =
     case evaluate_binop
       (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
       tvt bop v0 v of
       INL x => INL x | INR err => INR (Error err)` by
    (irule bop_result_augassign >> simp[]) >>
  `evaluate_binop
     (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
     tvt bop v0 v = INL result` by gvs[AllCaseEqs()] >>
  `value_has_type tvt result` by
    (mp_tac (Q.INST [`t1` |-> `ty`, `t2` |-> `expr_type e`,
       `tenv` |-> `get_tenv cx`, `result_tv` |-> `tvt`,
       `tv1` |-> `tvt`, `tv2` |-> `etv`, `tv` |-> `tvt`,
       `v1` |-> `v0`, `v2` |-> `v`, `v` |-> `result`,
       `u` |-> `case type_to_int_bound ty of NONE => Unsigned 0 | SOME u => u`]
       well_typed_binop_success_type) >> simp[]) >>
  `type_slot_size tvt = 1` by metis_tac[word_type_slot_size] >>
  `eval_operand res_op s = SOME (typed_val_to_w256 tvt result)` by
    simp[typed_val_to_w256_word_value] >>
  `encode_value tvt result = SOME [(0, typed_val_to_w256 tvt result)]` by
    metis_tac[encode_value_word_typed] >>
  `declared_storage_region cx src id [] = SOME (tr, n2w slot, tvt)` by
    simp[declared_storage_region_def] >>
  `!u' sto. storage_dead cx tr (update_storage (n2w slot) u' sto) =
            storage_dead cx tr sto` by
    metis_tac[storage_dead_update_word_region] >>
  Cases_on `write_storage_slot cx tr (n2w slot) tvt result
    (ee with gas_obs := [])` >>
  rename1 `_ = (wres, fin)` >>
  qspecl_then [`func`, `cenv`, `cx`, `ee with gas_obs := []`, `s`, `tr`,
    `n2w slot`, `tvt`, `result`, `typed_val_to_w256 tvt result`, `wres`,
    `fin`, `ctx`] mp_tac stmt_state_rel_write_storage_word >>
  impl_tac >- simp[] >> strip_tac >> gvs[] >>
  `fin.gas_obs = [] /\ fin.scopes = ee.scopes` by
    (qpat_x_assum `write_storage_slot _ _ _ _ _ _ = _` mp_tac >>
     simp[write_storage_slot_eq] >> Cases_on `tr` >>
     Cases_on `cx.txn.is_static` >>
     simp[set_storage_def] >> strip_tac >> gvs[]) >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  suspend "store"
QED

Resume compile_augassign_toplevel_mem[store]:
  qspecl_then [`ctx`, `func`, `cenv`, `cx`, `fin`, `s`, `tr`, `n2w slot`,
    `res_op`, `typed_val_to_w256 tvt result`, `s3`, `sb`] mp_tac
    assign_storage_store_path_mem >>
  impl_tac >- simp[] >> strip_tac >>
  rename1 `gas_marked_path T ctx func s 0 (OK last)` >>
  `gas_marked_path T ctx func u 0 (OK last)` by
    (drule_all gas_marked_path_then >> simp[]) >>
  qexistsl_tac [`INL ()`, `fin`, `OK last`] >>
  conj_tac
  >- (irule augassign_toplevel_rhs_normal_exec_mem_src >>
      qexistsl_tac [`ee`, `id_str`, `slot`, `t`, `tr`, `ts`, `tvt`, `ty`,
                    `u`, `v`, `v0`] >> simp[] >>
      irule augassign_storage_continuation_exec_mem_src >>
      simp[lift_sum_def, bind_def, return_def]) >>
  disj1_tac >> simp[] >>
  suspend "post"
QED

Resume compile_augassign_toplevel_mem[post]:
  `sa.cs_next_var <= s1.cs_next_var` by
    (qpat_x_assum `emit_op _ _ sa = _` mp_tac >>
     disch_then (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
     simp[]) >>
  `s3.cs_next_var <= sb.cs_next_var` by
    (qpat_x_assum `emit_void _ _ s3 = _` mp_tac >>
     disch_then (strip_assume_tac o MATCH_MP emitted_insts_emit_void) >>
     simp[]) >>
  `~block_is_terminated sb` by
    (qpat_x_assum `emit_void _ _ s3 = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[emit_void_def, comp_bind_def, comp_ignore_bind_def,
          fresh_id_def, emit_def, comp_return_def] >>
     strip_tac >> Cases_on `s3.cs_current_insts` >> Cases_on `tr` >>
     gvs[block_is_terminated_def, LAST_APPEND, LAST_CONS_cond,
         venomInstTheory.mk_inst_def, is_terminator_def]) >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
         lookup_var x s = SOME w` by
    (rpt strip_tac >>
     `lookup_var x t = SOME w` by metis_tac[] >>
     `not_fresh_at s1 x /\ not_fresh_at s2 x` by
       metis_tac[freshWritesTheory.not_fresh_at_mono,
                 arithmeticTheory.LESS_EQ_TRANS] >>
     `lookup_var x u = SOME w` by
       (qpat_x_assum `expr_post _ _ _ _ e _ _ _ _ _ _ _ _` mp_tac >>
        simp[expr_post_def]) >>
     metis_tac[]) >>
  `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
           FLOOKUP s.vs_allocas aid = SOME b` by
    (rpt strip_tac >>
     `FLOOKUP u.vs_allocas aid = SOME b` by
       (qpat_x_assum `expr_post _ _ _ _ e _ _ _ _ _ _ _ _` mp_tac >>
        simp[expr_post_def] >> metis_tac[]) >>
     metis_tac[]) >>
  simp[stmt_lands_def, cenv_top_ext_refl] >>
  irule return_buf_frame_frame >>
  qexistsl_tac [`cenv`, `s0`, `sa`] >> simp[]
QED

Resume compile_augassign_toplevel_mem[operator_exit]:
  `bop_result cx ty bop [ty; expr_type e] v0 v ee =
     case evaluate_binop
       (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
       tvt bop v0 v of
       INL x => INL x | INR err => INR (Error err)` by
    (irule bop_result_augassign >> simp[]) >>
  Cases_on `evaluate_binop
       (case type_to_int_bound ty of SOME bound => bound | NONE => Unsigned 0)
       tvt bop v0 v`
  >- (gvs[] >> fs[expr_exit_def, exit_result_def]) >>
  gvs[] >>
  qexistsl_tac [`INR (Error y)`, `ee with gas_obs := []`, `r`] >>
  conj_tac
  >- (irule augassign_toplevel_rhs_normal_exec_mem_src >>
      qexistsl_tac [`ee`, `id_str`, `slot`, `t`, `tr`, `ts`, `tvt`, `ty`,
                    `u`, `v`, `v0`] >> simp[] >>
      irule augassign_storage_continuation_exec_mem_src >>
      simp[lift_sum_def, bind_def, raise_def]) >>
  disj2_tac >> simp[stmt_exit_def] >>
  metis_tac[expr_exit_INR_type]
QED

Finalise compile_augassign_toplevel_mem

Theorem body_augassign_toplevel_word_mem:
  !cx ty src id bop e d tops bindings ctx func cenv env env' ret_ty lctx RetQ es.
    (!s'' p t' s'3' cur t'' s'4' ptv t'3'.
       eval_target_place cx (TopLevelNameTarget (src, id)) s'' = (INL p,t') /\
       read_place cx p s'3' = (INL cur,t'') /\
       place_type_value cx p s'4' = (INL ptv,t'3') ==>
       body_expr_mem_ok cx e) /\
    body_inv tops ctx cenv cx /\ supported_stmt tops bindings (AugAssign ty (TopLevelNameTarget (src, id)) bop e) /\
    (!target. supported_stmt_expr_exists
       (expr_abi_decode_target_root target) (AugAssign ty (TopLevelNameTarget (src, id)) bop e) ==>
       occurs_abi_decode_target target tops) /\
    expr_sim_inv cenv cx env es /\ ce_locals_declared cenv env /\
    locals_alloc_ok cenv env /\
    type_stmt env ret_ty (AugAssign ty (TopLevelNameTarget (src, id)) bop e) = SOME env' /\
    stmt_exprs_ok cenv (AugAssign ty (TopLevelNameTarget (src, id)) bop e) /\
    call_evaluation_safe cx (int_calls_stmt (AugAssign ty (TopLevelNameTarget (src, id)) bop e)) /\
    frame_ret_ok_mem d ctx func cx RetQ cenv ret_ty /\
    supported_scalar_target tops (src, id) ==>
    stmt_frag_mem d ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign ty (TopLevelNameTarget (src, id)) bop e))
      (eval_stmt cx (AugAssign ty (TopLevelNameTarget (src, id)) bop e)) es
Proof
  rpt strip_tac >>
  `supported_expr tops e` by gvs[supported_stmt_def] >>
  `!ts vis mut id ty init.
     MEM (VariableDecl vis mut id ty init) ts /\
     (mut = Storage \/ mut = Transient) ==>
     find_var_decl_by_name id ts <> NONE` by
    (Induct >> simp[] >> Cases >> rw[find_var_decl_by_name_def] >>
     metis_tac[]) >>
  `src = NONE /\ find_var_decl_by_name id tops <> NONE /\
   ?vis mut dty slot. MEM (VariableDecl vis mut id dty slot) tops /\
     is_word_type dty` by
    (qpat_x_assum `supported_scalar_target _ _` mp_tac >>
     simp[supported_scalar_target_def] >>
     Cases_on `supported_variable_decl tops (src, id)` >> simp[] >>
     rename1 `SOME x` >> PairCases_on `x` >>
     Cases_on `x0` >> Cases_on `x1` >> Cases_on `x3` >> simp[] >>
     strip_tac >> drule supported_variable_decl_mem >> strip_tac >>
     `find_var_decl_by_name id tops <> NONE` by metis_tac[] >>
     gvs[supported_full_word_type_def] >> first_assum (irule_at Any) >>
     simp[is_word_type_def]) >>
  gvs[] >>
  `get_module_code cx NONE = SOME tops /\ supported_program tops /\
   ALL_DISTINCT
     (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) /\
   cenv.ce_hashmap_info = build_hashmap_info tops /\
   cenv.ce_module_var_type (NONE, id) =
     build_var_type_map tops (NONE, id)` by
    fs[body_inv_def] >>
  drule_all build_maps_variable >> strip_tac >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  `type_place_target env (TopLevelNameTarget (NONE, id)) = SOME (Type ty) /\
   well_typed_expr env e /\ assignable_type env.type_defs ty /\
   well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn /\
   (bop = Exp ==> nonneg_int_literal e) /\
   (bop = ShL ==> shift_amount_ok e) /\ (bop = ShR ==> shift_amount_ok e)` by
    gvs[type_stmt_def, well_typed_target_def, DISJ_IMP_THM, AllCaseEqs()] >>
  gvs[vyperTypeEnvTheory.type_place_target_TopLevelNameTarget]
  >- (qpat_x_assum `env_consistent _ _ _`
        (strip_assume_tac o REWRITE_RULE [env_consistent_def,
           env_context_consistent_def]) >>
      first_x_assum drule >> strip_tac >> gvs[]) >>
  drule_all vyperTypeEnvTheory.env_consistent_toplevel_storage_static >>
  strip_tac >> drule find_var_decl_storage_mem >> strip_tac >> gvs[] >>
  rename1 `find_var_decl_by_name id tops = SOME (StorageVarDecl tr _, _)` >>
  `dty = ty` by metis_tac[build_maps_variable, optionTheory.SOME_11] >>
  gvs[optionTheory.IS_SOME_EXISTS] >>
  rename1 `lookup_var_slot_from_layout _ _ _ _ = SOME slot'` >>
  rename1 `evaluate_type _ ty = SOME tvt` >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `cx_tops cx = tops` by (drule cx_tops_module >> simp[]) >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[stmt_exprs_ok_flat, supported_stmt_expr_exists_def,
         supportedExprTraverseTheory.supported_expr_exists_def,
         int_calls_stmt_def, int_calls_expr_def, body_inv_def] >>
     qexists_tac `[]` >> simp[]) >>
  `?v0. read_storage_slot cx tr (n2w slot') tvt es = (INL v0, es)` by
    (irule toplevel_storage_read_decodes >>
     gvs[expr_sim_inv_def] >> metis_tac[]) >>
  drule_all eval_target_place_toplevel_mem_src >> strip_tac >>
  `body_expr_mem_ok cx e` by
    (first_x_assum irule >> simp[read_place_def] >> metis_tac[]) >>
  irule compile_augassign_toplevel_mem >> simp[DISJ_IMP_THM] >>
  conj_tac
  >- (gen_tac >>
      qpat_x_assum `body_expr_mem_ok cx e`
        (mp_tac o REWRITE_RULE [body_expr_mem_ok_def]) >>
      disch_then (qspecl_then [`tops`, `ctx`, `func`, `cenv`, `env`, `ty`,
        `es with gas_obs := gs`] mp_tac) >>
      simp[]) >>
  qexists_tac `env` >> simp[] >>
  metis_tac[assignable_type_well_formed]
QED
