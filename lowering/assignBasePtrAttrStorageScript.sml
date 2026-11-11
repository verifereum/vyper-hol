(* Storage fields: source equations and counted scalar-store continuation. *)
Theory assignBasePtrAttrStorage
Ancestors assignBasePtrAttrLocal assignBasePtrFieldAddress assignTuplePtrStorage
  stmtSimAssignAttrStorage stmtSimAssignStorage stmtSimForced stmtSimProps
  bodyPtrDefs bodyPtrPreds stmtFragPtr gasSummaryComposePtr gasExemptCert
  fragGasPathPtr fragGasPath fragGasMode gasSummary gasSummaryCompose gasContext
  exprLoweringProps emitHelperProps emitHelper exprLowering stmtLowering
  compileEnv loweringStateRelDefs loweringPosts venomState venomInst vyperState vyperStorageBackend
  ptrDiscipline stmtSimDeclMem vyperStorageLayoutSafety accountsRelProps
  exprSimTopLevelProps finite_map list vyperEvalExprPreservesScopesDom
  vyperInterpreter exprSimFieldLayout exprSimHypsDefs exprSimUnwrap
  valueEncoding accountsRelProps exprSimMemorySource stmtSimDefs
  exprSimAttributeFields fragExec exprSimDefs bodySim bodyExprPreFacts
  supportedExprTraverse supportedStmtTraverse supportedExprs supportedStmts
  vyperTypeEnv vyperTyping exprSimHyps vyperTypeCallGraph vyperTypeSystem
  vyperTypeInvariants bodyStorageMetadata compileVyper supportedDecls
  stmtSimAssignAttr supportedExprForms assignBasePtrStorageBody
Libs monadsyntax

Theorem assign_base_attr_storage_target:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ,id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME (StructTV fs) /\
  struct_field_slot fs fld = SOME (off,ftv) ==>
  eval_target_place cx (AttributeTarget (TopLevelNameTarget (src,id)) fld) =
    return (StoragePlace tr (n2w slot + n2w off) ftv)
Proof
  strip_tac >> simp[FUN_EQ_THM, Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, bind_def] >>
  simp[Once evaluate_def, lookup_global_def, lift_option_type_def,
       bind_def, return_def, extend_place_def, extend_storage_place_def,
       get_place_def]
QED

Theorem assign_base_attr_storage_tail:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ,id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME (StructTV fs) /\
  struct_field_slot fs fld = SOME (off,ftv) /\
  read_result cx raw ee = (INL v,ee) /\
  write_storage_slot cx tr (n2w slot + n2w off) ftv v ee = (res,ee') ==>
  !tail. (do
    p <- eval_target_place cx (AttributeTarget (TopLevelNameTarget (src,id)) fld);
    v <- read_result cx raw; write_place cx p v
  od) (ee with gas_obs := tail) = (res,ee' with gas_obs := tail)
Proof
  strip_tac >> drule_all assign_base_attr_storage_target >>
  disch_then SUBST1_TAC >> drule read_result_gas_obs >> strip_tac >>
  simp[bind_def, return_def, write_place_def, write_storage_slot_gas_obs]
QED

Theorem assign_base_struct_field_slot_lookup:
  !fs fld off ftv. struct_field_slot fs fld = SOME (off,ftv) ==>
    ALOOKUP fs fld = SOME ftv
Proof
  Induct >> simp[struct_field_slot_def] >> PairCases >> rpt gen_tac >>
  simp[struct_field_slot_def] >> IF_CASES_TAC >> simp[] >>
  strip_tac >> gvs[] >> rename1 `struct_field_slot fs fld = SOME q` >>
  PairCases_on `q` >> gvs[] >> metis_tac[]
QED

Theorem assign_base_attr_storage_source_counted:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr (StructT sid),id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld =
    SOME (fty,fsz) /\ is_word_type fty /\ expr_type e = fty /\
  expr_body_pre cenv cx env e es /\
  gas_admissible (eval_stmt cx
    (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src,id)) fld)) e))
    (stmt_res_ok lctx) es /\
  eval_expr cx e (es with gas_obs := gs) = (INL raw,ee) /\
  read_result cx raw ee = (INL v,ee) ==>
  ?fs off ftv res ee'.
    evaluate_type (get_tenv cx) (StructT sid) = SOME (StructTV fs) /\
    struct_field_slot fs fld = SOME (off,ftv) /\
    off = struct_field_offset_slots
      (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld /\
    evaluate_type (get_tenv cx) fty = SOME ftv /\
    encode_value ftv v = SOME [(0,typed_val_to_w256 ftv v)] /\
    write_storage_slot cx tr (n2w slot + n2w off) ftv v ee = (res,ee') /\
    (!tail. (do
      p <- eval_target_place cx (AttributeTarget (TopLevelNameTarget (src,id)) fld);
      v <- read_result cx raw; write_place cx p v
    od) (ee with gas_obs := tail) = (res,ee' with gas_obs := tail)) /\
    (!u st. storage_dead cx tr (update_storage (n2w slot + n2w off) u st) =
      storage_dead cx tr st)
Proof
  strip_tac >>
  Cases_on `eval_stmt cx
    (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src,id)) fld)) e)
    (es with gas_obs := gs)` >> rename1 `_ = (res,ee')` >>
  `stmt_res_ok lctx res` by (drule_all gas_admissible_result >> simp[]) >>
  `expr_body_pre cenv cx env e (es with gas_obs := gs)` by simp[] >>
  `!m. res <> INR (Error (TypeError m))` by
    (rpt strip_tac >> gvs[stmt_res_ok_def]) >>
  drule_all eval_assign_attr_toplevel >> simp[bind_def] >> strip_tac >>
  drule_all assign_attr_storage_source >> simp[bind_def] >> strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  drule_all struct_fields_layout >> strip_tac >> gvs[] >>
  drule_all struct_field_offset_slots_eq >> strip_tac >> gvs[] >>
  drule_all struct_field_type >> strip_tac >>
  imp_res_tac assign_base_struct_field_slot_lookup >> gvs[] >>
  drule_all assign_base_attr_storage_tail >> simp[bind_def]
QED

Theorem assign_base_attr_storage_store_post_ptr:
  emit_void (if tr then TSTORE else SSTORE) [dst;op] su = ((),sb) /\
  fn_has_code su sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  ~block_is_terminated sb /\
  s.vs_current_bb = su.cs_current_bb /\ s.vs_inst_idx = LENGTH su.cs_current_insts /\
  expr_post ctx fn cenv cx e es sa su s0 ee v op s /\
  ghost_inv d cenv cx ee G tn s /\ ghost_kept cenv es sa Gi ti s0 G tn /\
  is_word_type (expr_type e) /\ ptr_val_ok cx (expr_type e) v op G tn s /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME ftv /\
  eval_operand dst s = SOME slot /\ op_taint tn dst = {} /\
  encode_value ftv v = SOME [(0,typed_val_to_w256 ftv v)] /\
  write_storage_slot cx tr slot ftv v ee = (res,ff) /\
  (!u st. storage_dead cx tr (update_storage slot u st) = storage_dead cx tr st) /\
  (!tail. k (ee with gas_obs := tail) = (res,ff with gas_obs := tail)) ==>
  ?tf u.
    gas_marked_exec_ptr (cx_dead cx) (ctx,fn) PG k
      (ee,s,G,tn) [] (INL ()) ff G tf (OK u) /\
    stmt_post ctx fn cx lctx cenv cenv sa sb s0 (INL ()) ff u /\
    ghost_inv d cenv cx ff G tf u /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP G x = FLOOKUP Gi x /\ op_taint tf (Var x) = op_taint ti (Var x))
Proof
  strip_tac >>
  `stmt_state_rel ctx fn cenv cx ee s /\
   eval_operand op s = SOME (typed_val_to_w256 ftv v)` by
    (fs[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
  `op_taint tn op = {}` by fs[ptr_val_ok_def] >>
  drule_all stmt_state_rel_write_storage_word >> strip_tac >> gvs[] >>
  `compile_store_at_loc cenv.ce_imm_alloca dst op
    (SOME (if tr then LocTransient else LocStorage)) su = ((),sb)` by
    (Cases_on `tr` >> gvs[compile_store_at_loc_def]) >>
  drule_all tuple_storage_store_head_path_ptr >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  qexistsl_tac [`tn'`, `t`] >> conj_tac
  >- simp[gas_marked_exec_ptr_def] >>
  simp[] >> conj_tac
  >- (simp[stmt_post_def, stmt_lands_def, cenv_top_ext_refl] >>
      fs[expr_post_def] >> metis_tac[]) >>
  fs[ghost_kept_def] >> metis_tac[]
QED

Theorem assign_base_attr_storage_normal_ptr:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr (StructT sid),id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld =
    SOME (fty,fsz) /\ is_word_type fty /\ expr_type e = fty /\
  expr_body_pre cenv cx env e es /\
  gas_admissible (eval_stmt cx
    (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src,id)) fld)) e))
    (stmt_res_ok lctx) es /\
  compile_expr cenv (expr_type e) e sa = (vv,sm) /\
  emit_op ADD [Lit (n2w slot); Lit (n2w (struct_field_offset_slots
    (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld))]
    sm = (dst,sn) /\ unwrap_value cenv vv sn = (op,su) /\
  emit_void (if tr then TSTORE else SSTORE) [dst;op] su = ((),sb) /\
  fn_has_code sm sn fn /\ fn_has_code sn su fn /\ fn_has_code su sb fn /\
  ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\ ~block_is_terminated sb /\
  sa.cs_next_var <= sm.cs_next_var /\ local_ptrs_reserved cenv sa /\
  stmt_state_rel ctx fn cenv cx es s0 /\
  gas_marked_exec_ptr (cx_dead cx) (ctx,fn) PG (eval_expr cx e)
    (es,s0,Gi,ti) marks (INL raw) ee G tn (OK s) /\
  vv_post ctx fn cenv cx e es sa sm s0 (ee with gas_obs := []) raw vv s /\
  ghost_inv d cenv cx (ee with gas_obs := []) G tn s /\
  ghost_kept cenv es sa Gi ti s0 G tn /\
  ptr_vv_ok cx (expr_type e) raw vv (ee with gas_obs := []) G tn s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!x cap. cenv.ce_return_buf = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) /\
  (!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x) ==>
  ?ff H tf u.
    gas_marked_exec_ptr (cx_dead cx) (ctx,fn) PG
      (eval_stmt cx (Assign (BaseTarget
        (AttributeTarget (TopLevelNameTarget (src,id)) fld)) e))
      (es,s0,Gi,ti) marks (INL ()) ff H tf (OK u) /\
    stmt_post ctx fn cx lctx cenv cenv sa sb s0 (INL ()) ff u /\
    ghost_inv d cenv cx ff H tf u /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP H x = FLOOKUP Gi x /\ op_taint tf (Var x) = op_taint ti (Var x))
Proof
  strip_tac >> drule_all assign_base_attr_local_rhs_source >> strip_tac >>
  `MAP FDOM es.scopes = MAP FDOM (ee with gas_obs := []).scopes /\
   is_word_type (expr_type e)` by simp[] >>
  `eval_operand (Lit (n2w slot)) s = SOME (n2w slot) /\
   op_taint tn (Lit (n2w slot)) = {}` by simp[eval_operand_def,op_taint_def] >>
  drule_all assign_base_field_add_word_read_ptr >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
    (INL raw,ee with gas_obs := [])` by
    (fs[gas_marked_exec_ptr_def] >> metis_tac[APPEND_NIL]) >>
  `read_result cx raw (ee with gas_obs := []) = (INL v,ee with gas_obs := [])` by
    (fs[gas_marked_exec_ptr_def] >> metis_tac[gas_explicit_def,APPEND_NIL]) >>
  drule_all assign_base_attr_storage_source_counted >> strip_tac >>
  suspend "store"
QED

Resume assign_base_attr_storage_normal_ptr[store]:
  gvs[] >>
  `~z.vs_halted` by
    (drule_all gas_marked_exec_ptr_exec >> simp[gas_marked_exec_def] >> strip_tac >>
     drule gas_marked_path_exec >> strip_tac >> drule gas_path_normal >> simp[]) >>
  `?tf' u.
    gas_marked_exec_ptr (cx_dead cx) (ctx,fn) PG
      (do p <- eval_target_place cx
        (AttributeTarget (TopLevelNameTarget (src,id)) fld);
        v <- read_result cx raw; write_place cx p v od)
      (ee with gas_obs := [],z,H,tf) [] (INL ()) ee' H tf' (OK u) /\
    stmt_post ctx fn cx lctx cenv cenv sa sb s0 (INL ()) ee' u /\
    ghost_inv d cenv cx ee' H tf' u /\
    (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP Gi x /\
      op_taint tf' (Var x) = op_taint ti (Var x))` by
    (irule assign_base_attr_storage_store_post_ptr >> simp[] >>
     goal_assum (drule_at (Pat `emit_void _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     simp[] >> metis_tac[]) >>
  qexistsl_tac [`ee'`, `H`, `tf'`, `u`] >> simp[] >>
  rewrite_tac[eval_assign_attr_toplevel_action] >>
  irule (SIMP_RULE std_ss [APPEND_NIL]
    (Q.INST [`right` |-> `[]`] gas_marked_exec_ptr_bind_normal)) >>
  qexistsl_tac [`G`, `ee`, `s`, `tn`, `raw`] >> simp[] >>
  fs[gas_marked_exec_ptr_def] >>
  metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES]
QED
Finalise assign_base_attr_storage_normal_ptr

Theorem compile_assign_attr_storage_case_ptr:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr (StructT sid),id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  cenv.ce_hashmap_info (src,id) = NONE /\
  cenv.ce_module_var_type (src,id) = SOME (StructT sid) /\
  ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld =
    SOME (fty,fsz) /\ is_word_type fty /\ expr_type e = fty /\
  expr_vv_sim_ptr d ctx PG fn cenv cx (expr_type e) e es /\
  expr_body_pre cenv cx env e es ==>
  stmt_frag_ptr d ctx PG fn cx lctx RetQ cenv
    (stmt_env cenv lctx ty
      (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src,id)) fld)) e))
    (eval_stmt cx
      (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src,id)) fld)) e)) es
Proof
  strip_tac >> simp[stmt_frag_ptr_def] >> rpt gen_tac >> strip_tac >>
  `FLOOKUP cenv.ce_module_vars (src,id) =
    SOME (if tr then TransientLoc (n2w slot) else StorageLoc (n2w slot))` by
    (irule toplevel_storage_ce_vars >>
     gvs[stmt_state_rel_def,state_rel_def] >> metis_tac[]) >>
  `is_word_type (expr_type e)` by simp[] >>
  drule_all assign_attr_storage_code_parts >> strip_tac >> gvs[] >>
  `cs_extends sa sm /\ cs_extends sm sn /\ cs_extends sn su /\ cs_extends su sb` by
    metis_tac[cj 1 compile_expr_ci_mono,ci_mono_emit_op,
      ci_mono_unwrap_value,ci_mono_emit_void,pairTheory.SND,ci_mono_def] >>
  `fn_has_code sa sm fn /\ fn_has_code sm sn fn /\
   fn_has_code sn su fn /\ fn_has_code su sb fn` by
    metis_tac[fn_has_code_split,cs_extends_trans] >>
  `~block_is_terminated sb` by
    (Cases_on `tr` >> gvs[] >> drule emit_void_nonterminator_open >>
     simp[is_terminator_def]) >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[exprSimHypsTheory.expr_body_pre_vv_gas_admissible] >>
  `!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x`
    by metis_tac[ret_pc_ok_def] >>
  qpat_x_assum `expr_vv_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_ptr_def]) >>
  disch_then drule_all >> simp[gas_outcome_ptr_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ _ _` mp_tac >>
      simp[gas_summary_ptr_at_marked] >> strip_tac
      >- suspend "normal" >>
      `?ex. res = INR ex` by (Cases_on `res` >> gvs[expr_exit_def]) >> gvs[] >>
      qexistsl_tac [`INR ex`,`es_end`,`G`,`tn`,`r`] >> conj_tac
      >- (rewrite_tac[eval_assign_attr_toplevel_action] >>
          irule gas_marked_exec_ptr_bind_exception >> simp[]) >>
      disj2_tac >> simp[stmt_exit_ptr_def] >> metis_tac[expr_exit_INR_type]) >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`finish'`] >>
  rewrite_tac[eval_assign_attr_toplevel_action] >>
  once_rewrite_tac[ignore_bind_def] >> once_rewrite_tac[bind_assoc] >>
  BETA_TAC >> rewrite_tac[GSYM ignore_bind_def] >>
  irule gas_exempt_cert_error_result >> simp[GSYM ignore_bind_def]
QED

Resume compile_assign_attr_storage_case_ptr[normal]:
  gvs[] >>
  `sa.cs_next_var <= sm.cs_next_var` by
    metis_tac[cj 1 compile_expr_ci_mono,ci_mono_def,pairTheory.SND] >>
  `~t.vs_halted` by
    (drule_all gas_marked_exec_ptr_exec >> simp[gas_marked_exec_def] >> strip_tac >>
     drule gas_marked_path_exec >> strip_tac >> drule gas_path_normal >> simp[]) >>
  `?ff H tf u.
    gas_marked_exec_ptr (cx_dead cx) (ctx,fn) PG
      (eval_stmt cx (Assign (BaseTarget
        (AttributeTarget (TopLevelNameTarget (src,id)) fld)) e))
      (es,s0,G0,tn0) marks (INL ()) ff H tf (OK u) /\
    stmt_post ctx fn cx lctx cenv cenv sa sb s0 (INL ()) ff u /\
    ghost_inv d cenv cx ff H tf u /\
    (!x. not_fresh_at sa x ==>
      FLOOKUP H x = FLOOKUP G0 x /\ op_taint tf (Var x) = op_taint tn0 (Var x))` by
    (irule assign_base_attr_storage_normal_ptr >> simp[] >>
     (conj_tac >- metis_tac[]) >>
     goal_assum (drule_at (Pat `gas_marked_exec_ptr _ _ _ _ _ _ _ _ _ _ _`)) >>
     simp[] >> metis_tac[]) >>
  qexistsl_tac [`INL ()`,`ff`,`H`,`tf`,`OK u`] >> simp[] >>
  disj1_tac >> fs[stmt_post_def] >>
  simp[ghost_inv_gas_obs] >> metis_tac[]
QED
Finalise compile_assign_attr_storage_case_ptr

Theorem assign_base_storage_decl_present[local]:
  !ts vis mut id ty init.
    MEM (VariableDecl vis mut id ty init) ts /\
    (mut = Storage \/ mut = Transient) ==>
    find_var_decl_by_name id ts <> NONE
Proof
  Induct >> simp[] >> Cases >> rw[find_var_decl_by_name_def] >> metis_tac[]
QED

Theorem assign_base_storage_field_decl:
  supported_storage_field_write tops (src,id) fld ==>
  src = NONE /\ find_var_decl_by_name id tops <> NONE /\
  ?mut sid slot. MEM (VariableDecl Private mut id (StructT sid) slot) tops
Proof
  simp[supported_storage_field_write_def,supported_storage_fields_def] >>
  Cases_on `supported_variable_decl tops (src,id)` >> simp[] >>
  rename1 `SOME x` >> PairCases_on `x` >>
  drule supported_variable_decl_mem >> strip_tac >> gvs[] >>
  Cases_on `x0` >> Cases_on `x1` >> Cases_on `x2` >> Cases_on `x3` >> simp[] >>
  metis_tac[assign_base_storage_decl_present]
QED

Theorem body_assign_attr_storage_ptr:
  body_expr_ptr_ok cx e /\ body_inv tops ctx cenv cx /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
    (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src,id)) fld)) e) ==>
    occurs_abi_decode_target target tops) /\ supported_expr tops e /\
  expr_sim_inv cenv cx env es /\
  supported_storage_field_write tops (src,id) fld /\
  type_place_target env (AttributeTarget (TopLevelNameTarget (src,id)) fld) =
    SOME (Type fty) /\ is_word_type fty /\
  type_stmt env ret_ty
    (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src,id)) fld)) e) =
    SOME env' /\
  stmt_exprs_ok cenv
    (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src,id)) fld)) e) /\
  call_evaluation_safe cx (int_calls_stmt
    (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src,id)) fld)) e)) ==>
  stmt_frag_ptr d ctx PG fn cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty
      (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src,id)) fld)) e))
    (eval_stmt cx
      (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src,id)) fld)) e)) es
Proof
  strip_tac >>
  `well_typed_expr env e /\ expr_type e = fty` by
    (gvs[type_stmt_def,atarget_accepts_def] >> metis_tac[type_widens_to_word]) >>
  drule assign_base_storage_field_decl >> strip_tac >> gvs[] >>
  `get_module_code cx NONE = SOME tops /\ supported_program tops /\
   ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE:num option)) tops)) /\
   cenv.ce_hashmap_info = build_hashmap_info tops /\
   cenv.ce_module_var_type (NONE,id) = build_var_type_map tops (NONE,id)` by
    fs[body_inv_def] >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  gvs[vyperTypeEnvTheory.type_place_target_AttributeTarget,
      vyperTypeEnvTheory.type_place_target_TopLevelNameTarget]
  >- (drule_all assign_base_bare_assignable_no_decl >> strip_tac >> gvs[]) >>
  drule_all vyperTypeEnvTheory.env_consistent_toplevel_storage_static >> strip_tac >>
  drule find_var_decl_storage_mem >> strip_tac >> gvs[] >>
  rename1 `attribute_type _ tgt_ty fld = SOME _` >>
  `tgt_ty = StructT sid` by metis_tac[build_maps_variable,optionTheory.SOME_11] >>
  gvs[] >> drule_all build_maps_variable >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[env_consistent_def,env_context_consistent_def] >>
  `?fsz. ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
    fld = SOME (expr_type e,fsz)` by metis_tac[attribute_type_struct_field] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `cx_tops cx = tops` by (irule cx_tops_module >> fs[body_inv_def]) >>
  `expr_body_pre cenv cx env e es` by
    (irule stmt_expr_body_pre >>
     gvs[stmt_exprs_ok_def,supported_stmt_expr_exists_def,
       supported_assignment_exists_def,supported_expr_exists_def,
       int_calls_stmt_def,int_calls_atarget_def,int_calls_expr_def] >>
     (conj_tac >- fs[body_inv_def]) >> qexists_tac `[]` >> simp[]) >>
  `expr_vv_sim_ptr d ctx PG fn cenv cx (expr_type e) e es` by
    metis_tac[body_expr_ptr_ok_def] >>
  qpat_x_assum `IS_SOME (lookup_var_slot_from_layout _ _ _ _)`
    (strip_assume_tac o REWRITE_RULE[optionTheory.IS_SOME_EXISTS]) >>
  irule compile_assign_attr_storage_case_ptr >> simp[] >> metis_tac[]
QED
