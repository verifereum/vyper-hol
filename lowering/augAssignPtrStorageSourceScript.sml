(* Declared-storage source representation at the initial AugAssign load. *)
Theory augAssignPtrStorageSource
Ancestors
  exprSimTopLevelProps accountsRelProps vyperStorageLayoutSafety
  vyperLookupStorage exprSimDefs stmtSimDefs loweringPosts codegenRel
  vyperState vyperInterpreter vfmState compileEnv exprLoweringProps
  vyperStorageBackend stmtSimAssignStorage stmtSimAugAssignStorage gasSummaryComposePtr gasCount gasSummary
  gasExemptCert fragGasPath fragGasMode fragGasSeqPtr fragGasPathPtr vyperExprNoControl
Libs
  monadsyntax

Theorem declared_storage_holds_value_ptr:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr ty,id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) ty = SOME tvt /\
  read_storage_slot cx tr (n2w slot) tvt es = (INL v,es) /\
  contract_storage_well_formed cx es /\ storage_layout_safe cx /\
  stmt_state_rel ctx func cenv cx es s ==>
  storage_holds cx tr ty (Value v) (n2w slot) es s
Proof
  strip_tac >>
  `slots_in_range (get_storage cx es tr) (w2n ((n2w slot):bytes32)) tvt` by
    (irule toplevel_storage_slots_in_range >> metis_tac[]) >>
  `storage_var_info cx src id = SOME (tr,slot,tvt)` by
    simp[storage_var_info_def] >>
  `declared_storage_region cx src id [] = SOME (tr,n2w slot,tvt)` by
    (irule declared_storage_region_ordinary >> simp[]) >>
  `!st. storage_read_live cx tr st (n2w slot) tvt` by
    (gen_tac >> irule declared_storage_region_read_live >> metis_tac[]) >>
  `w2n ((n2w slot):bytes32) + type_slot_size tvt <= dimword (:256)` by
    (drule_all storage_layout_safe_region_nonoverflow >> simp[]) >>
  `storage_range_agree (get_storage cx es tr)
     (if tr then contract_transient s else contract_storage s) (n2w slot) tvt` by
    (irule storage_range_agree_of_live >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`cx`, `tr`] >> simp[] >> Cases_on `tr` >>
     gvs[stmt_state_rel_def, state_rel_def, storage_rel_def,
         transient_rel_def, get_storage_def, lookup_account_def]) >>
  gvs[storage_holds_def, read_result_def, return_def]
QED

Theorem augassign_toplevel_place_exec_ptr:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ,id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME tvt /\
  gas_path_ptr D 0 ctx func PG G tn s0 0 H tm (OK t) ==>
  gas_marked_exec_ptr D (ctx,func) PG
    (eval_target_place cx (TopLevelNameTarget (src,id)))
    (es,s0,G,tn) [] (INL (StoragePlace tr (n2w slot) tvt)) es H tm (OK t)
Proof
  strip_tac >> simp[gas_marked_exec_ptr_def, gas_explicit_def] >>
  gen_tac >> irule (cj 1 eval_target_place_toplevel) >> metis_tac[]
QED

Theorem read_storage_slot_gas_obs_ptr:
  read_storage_slot cx tr slot tv es = (res,ee) ==>
  read_storage_slot cx tr slot tv (es with gas_obs := gs) =
    (res,ee with gas_obs := gs)
Proof
  Cases_on `tr` >>
  simp[read_storage_slot_def, get_storage_backend_def, get_accounts_def,
       get_transient_storage_def, bind_def, return_def, lift_option_def,
       AllCaseEqs()] >>
  qmatch_goalsub_abbrev_tac `decode_value storage offset tv` >>
  Cases_on `decode_value storage offset tv` >> simp[return_def, raise_def] >> rpt strip_tac >> gvs[]
QED

Theorem augassign_toplevel_rhs_exempt_ptr:
  read_storage_slot cx tr slot tvt es = (INL v0,es) /\
  gas_marked_exec_ptr D (ctx,func) PG
    (eval_target_place cx (TopLevelNameTarget (src,id)))
    (es,s0,G,tn) [] (INL (StoragePlace tr slot tvt)) es H tm (OK t) /\
  ~t.vs_halted /\
  gas_exempt_cert F tops (ctx,func)
    (ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()))
    (es with gas_obs := [],t) marks (err,ee) (leaf,fin) ==>
  gas_exempt_cert F tops (ctx,func)
    (ignore_bind (eval_stmt cx
      (AugAssign ty (TopLevelNameTarget (src,id)) bop e)) (return ()))
    (es,s0) marks (err,ee) (leaf,fin)
Proof
  strip_tac >> drule gas_marked_exec_ptr_exec >> strip_tac >>
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
  `gas_marked_exec F (ctx,func) (read_place cx (StoragePlace tr slot tvt))
     (es with gas_obs := [],t) [] (INL v0)
     (es with gas_obs := []) (OK t)` by
    (simp[gas_marked_exec_def, gas_explicit_def] >> conj_tac
     >- (gen_tac >> simp[read_place_def] >>
         metis_tac[read_storage_slot_gas_obs_ptr]) >>
     simp[gas_marked_path_def, gas_path_rules]) >>
  drule gas_exempt_cert_bind_value >> simp[] >> disch_then irule >>
  simp[place_type_value_def, bind_return] >>
  irule gas_exempt_cert_error_value >> simp[]
QED

Theorem eval_augassign_toplevel_forced_ptr:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ,id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME tvt /\
  read_storage_slot cx tr (n2w slot) tvt es = (INL v0,es) ==>
  eval_stmt cx (AugAssign ty (TopLevelNameTarget (src,id)) bop e) es =
  (do v <- bind (eval_expr cx e) (read_result cx);
      r <- lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        tvt bop v0 v);
      write_storage_slot cx tr (n2w slot) tvt r od) es
Proof
  strip_tac >> drule_all eval_target_place_toplevel >>
  disch_then (qspec_then `es` strip_assume_tac) >>
  simp[Once evaluate_def, bind_def, ignore_bind_def, read_place_def,
       write_place_def] >>
  Cases_on `eval_expr cx e es` >> rename1 `_ = (raw,st)` >>
  Cases_on `raw` >> simp[bind_def]
QED

Theorem augassign_toplevel_rhs_exception_ptr:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ,id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME tvt /\
  read_storage_slot cx tr (n2w slot) tvt es = (INL v0,es) /\
  bind (eval_expr cx e) (read_result cx) es = (INR ex,ee) ==>
  eval_stmt cx (AugAssign ty (TopLevelNameTarget (src,id)) bop e) es = (INR ex,ee)
Proof
  strip_tac >> drule_all eval_augassign_toplevel_forced_ptr >>
  disch_then (qspecl_then [`ty`, `e`, `bop`] mp_tac) >> simp[Once bind_def]
QED

Theorem augassign_toplevel_rhs_normal_ptr:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ,id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME tvt /\
  read_storage_slot cx tr (n2w slot) tvt es = (INL v0,es) /\
  bind (eval_expr cx e) (read_result cx) es = (INL v,ee) ==>
  eval_stmt cx (AugAssign ty (TopLevelNameTarget (src,id)) bop e) es =
  bind (lift_sum (evaluate_binop
    (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
    tvt bop v0 v)) (write_storage_slot cx tr (n2w slot) tvt) ee
Proof
  strip_tac >> drule_all eval_augassign_toplevel_forced_ptr >>
  disch_then (qspecl_then [`ty`, `e`, `bop`] mp_tac) >>
  simp[Once bind_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

Theorem gas_marked_exec_ptr_zero_prefix:
  gas_path_ptr D 0 ctx func PG G tn s0 0 H tm (OK t) /\
  gas_marked_exec_ptr D (ctx,func) PG source
    (es with gas_obs := [],t,H,tm) marks res ee J un r ==>
  gas_marked_exec_ptr D (ctx,func) PG source
    (es,s0,G,tn) marks res ee J un r
Proof
  strip_tac >> drule gas_path_ptr_ok_suffix >> simp[] >> strip_tac >>
  gvs[gas_marked_exec_ptr_def] >>
  metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES]
QED

Theorem augassign_toplevel_rhs_exception_exec_ptr:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ,id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME tvt /\
  read_storage_slot cx tr (n2w slot) tvt es = (INL v0,es) /\
  gas_path_ptr D 0 ctx func PG G tn s0 0 H tm (OK t) /\
  gas_marked_exec_ptr D (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx))
    (es with gas_obs := [],t,H,tm) marks (INR ex) ee J un r ==>
  gas_marked_exec_ptr D (ctx,func) PG
    (eval_stmt cx (AugAssign ty (TopLevelNameTarget (src,id)) bop e))
    (es,s0,G,tn) marks (INR ex) ee J un r
Proof
  strip_tac >> drule_all gas_marked_exec_ptr_zero_prefix >>
  simp[gas_marked_exec_ptr_def] >> strip_tac >> simp[] >>
  gen_tac >> irule augassign_toplevel_rhs_exception_ptr >> simp[] >>
  qexists_tac `v0` >> metis_tac[read_storage_slot_gas_obs_ptr]
QED

Theorem augassign_toplevel_rhs_normal_exec_ptr:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ,id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME tvt /\
  read_storage_slot cx tr (n2w slot) tvt es = (INL v0,es) /\
  gas_path_ptr D 0 ctx func PG G tn s0 0 H tm (OK t) /\
  gas_marked_exec_ptr D (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx))
    (es with gas_obs := [],t,H,tm) marks (INL v) ee J un (OK u) /\
  gas_marked_exec_ptr D (ctx,func) PG
    (bind (lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      tvt bop v0 v)) (write_storage_slot cx tr (n2w slot) tvt))
    (ee with gas_obs := [],u,J,un) [] res fin Hfin uk r ==>
  gas_marked_exec_ptr D (ctx,func) PG
    (eval_stmt cx (AugAssign ty (TopLevelNameTarget (src,id)) bop e))
    (es,s0,G,tn) marks res fin Hfin uk r
Proof
  strip_tac >> drule_all gas_marked_exec_ptr_zero_prefix >> strip_tac >>
  gvs[gas_marked_exec_ptr_def] >> conj_tac
  >- (gen_tac >>
      qpat_x_assum `!tail. bind (eval_expr cx e) _ _ = _`
        (qspec_then `tail` assume_tac) >>
      `read_storage_slot cx tr (n2w slot) tvt
         (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
         (INL v0,es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail)` by
        metis_tac[read_storage_slot_gas_obs_ptr] >>
      drule_all augassign_toplevel_rhs_normal_ptr >>
      disch_then (qspecl_then [`ty`, `bop`] mp_tac) >> simp[]) >>
  metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES]
QED

Theorem augassign_storage_continuation_exec_ptr:
  bind (lift_sum br) (write_storage_slot cx tr slot tvt) ee = (res,fin) /\
  gas_path_ptr D 0 ctx func PG G tn u 0 H tm r ==>
  gas_marked_exec_ptr D (ctx,func) PG
    (bind (lift_sum br) (write_storage_slot cx tr slot tvt))
    (ee,u,G,tn) [] res fin H tm r
Proof
  Cases_on `br` >>
  simp[gas_marked_exec_ptr_def, lift_sum_def, bind_def, return_def, raise_def] >>
  strip_tac >> simp[] >> gen_tac >>
  simp[write_storage_slot_gas_obs] >> gvs[]
QED
