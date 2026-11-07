(* Source/environment boundaries for the supported storage assignment branch. *)
Theory assignBasePtrStorageBody
Ancestors
  assignBasePtrStorageFragment bodyPtrPreds bodySimStmtCases bodySim
  bodyExprPreFacts exprSimHypsDefs exprSimHyps exprSimSource
  exprSimTopLevelProps stmtSimAssignStorage compileEnv context
  vyperStorageLayoutSafety vyperLookupStorage vyperStorageBackend
  vyperTypeEnv vyperTyping vyperTypeContractStaticMaps
  supportedDecls supportedProgram supportedTypes supportedStmtTraverse
  supportedExprTraverse supportedExprs supportedStmts
  vyperInterpreter vyperState vyperTypeValues valueEncodingProps
  stmtLowering exprLowering finite_map list words
  vyperTypeSystem vyperTypeCallGraph gasContext bodyStorageMetadata vyperTypeContract vyperTypeInvariants
  assignTuplePtrBodyReady vyperTypeExprSoundness
Libs monadsyntax

Theorem assign_base_storage_rhs_pre:
  body_inv tops ctx cenv cx /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
    (Assign (BaseTarget (TopLevelNameTarget nid)) e) ==>
    occurs_abi_decode_target target tops) /\ supported_expr tops e /\
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (Assign (BaseTarget (TopLevelNameTarget nid)) e) = SOME env' /\
  stmt_exprs_ok cenv (Assign (BaseTarget (TopLevelNameTarget nid)) e) /\
  call_evaluation_safe cx
    (int_calls_stmt (Assign (BaseTarget (TopLevelNameTarget nid)) e)) ==>
  expr_body_pre cenv cx env e es
Proof
  rpt strip_tac >>
  `well_typed_expr env e` by
    gvs[type_stmt_def, atarget_accepts_def, AllCaseEqs()] >>
  drule_then strip_assume_tac supported_expr_body_calls >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops` by
    gvs[body_inv_def] >>
  `cx_tops cx = tops` by simp[cx_tops_def] >>
  irule stmt_expr_body_pre >>
  gvs[stmt_exprs_ok_def, supported_stmt_expr_exists_def,
    supported_assignment_exists_def, int_calls_stmt_def,
    int_calls_atarget_def, int_calls_expr_def] >>
  conj_tac >- fs[body_inv_def] >> qexists_tac `[]` >> simp[]
QED

Theorem assign_base_storage_region:
  storage_layout_safe cx /\
  storage_var_info cx mid id = SOME (tr,off,tv) /\
  0 < type_slot_size tv ==>
  off + type_slot_size tv <= dimword (:256) /\
  (!mid' id' subs' k' tv'.
    declared_storage_region cx mid' id' subs' = SOME (tr,k',tv') /\
    (k',tv') <> (n2w off,tv) ==>
    ranges_disjoint off (type_slot_size tv) (w2n k') (type_slot_size tv'))
Proof
  strip_tac >>
  `off + type_slot_size tv <= dimword (:256)` by
    (drule storage_layout_safe_layout >>
     simp[well_formed_layout_def] >> metis_tac[]) >>
  `off < dimword (:256)` by decide_tac >>
  `w2n (n2w off : 256 word) = off` by simp[] >>
  drule declared_storage_region_ordinary >> strip_tac >>
  simp[] >> rpt strip_tac >>
  `(mid,id,[]) <> (mid',id',subs')` by (strip_tac >> gvs[]) >>
  drule_all storage_layout_safe_region_separation >> simp[]
QED

Theorem assign_base_storage_decl_found:
  !ts vis mut id ty init.
    MEM (VariableDecl vis mut id ty init) ts /\
    (mut = Storage \/ mut = Transient) ==>
    find_var_decl_by_name id ts <> NONE
Proof
  Induct >> simp[] >> Cases >> rw[find_var_decl_by_name_def] >> metis_tac[]
QED

Theorem assign_base_bare_assignable_no_decl:
  env_consistent env cx st /\
  FLOOKUP env.bare_global_assignable (src,id) = SOME ty ==>
  ?ts. get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = NONE
Proof
  rw[env_consistent_def, env_context_consistent_def] >>
  first_x_assum drule >> strip_tac >> simp[]
QED

Theorem assign_base_storage_target:
  body_inv tops ctx cenv cx /\
  supported_variable_decl tops (src,id) = SOME (Private,mut,ty,SOME ast_slot) /\
  (mut = Storage \/ mut = Transient) /\ expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (Assign (BaseTarget (TopLevelNameTarget (src,id))) e) =
    SOME env' ==>
  src = NONE /\ get_module_code cx NONE = SOME tops /\
  cenv.ce_hashmap_info (NONE,id) = NONE /\
  cenv.ce_module_var_type (NONE,id) = SOME ty /\
  ?tr id_str off tv.
    find_var_decl_by_name id tops = SOME (StorageVarDecl tr ty,id_str) /\
    lookup_var_slot_from_layout cx tr NONE id_str = SOME off /\
    evaluate_type (get_tenv cx) ty = SOME tv
Proof
  strip_tac >> (
  drule supported_variable_decl_mem >> strip_tac >> gvs[] >>
  `get_module_code cx NONE = SOME tops /\
   ALL_DISTINCT
     (FLAT (MAP (toplevel_vtype_keys_toplevel (NONE : num option)) tops)) /\
   cenv.ce_hashmap_info = build_hashmap_info tops /\
   cenv.ce_module_var_type (NONE,id) = build_var_type_map tops (NONE,id)` by
    fs[body_inv_def] >>
  drule_all build_maps_variable >> strip_tac >>
  `env_consistent env cx es` by fs[expr_sim_inv_def] >>
  `find_var_decl_by_name id tops <> NONE` by
    metis_tac[assign_base_storage_decl_found] >>
  Cases_on `type_place_target env (TopLevelNameTarget (NONE,id))` >>
  gvs[type_stmt_def, atarget_accepts_def] >>
  rename1 `type_place_target _ _ = SOME vt` >> Cases_on `vt` >> gvs[] >>
  gvs[type_place_target_TopLevelNameTarget]
  >- (drule_all assign_base_bare_assignable_no_decl >> strip_tac >> gvs[]) >>
  drule_all env_consistent_toplevel_storage_static >>
  strip_tac >> drule find_var_decl_storage_mem >> strip_tac >> gvs[] >>
  `t = ty` by metis_tac[build_maps_variable, optionTheory.SOME_11] >>
  gvs[] >>
  qpat_x_assum `IS_SOME (lookup_var_slot_from_layout _ _ _ _)`
    (strip_assume_tac o REWRITE_RULE[optionTheory.IS_SOME_EXISTS]) >>
  qpat_x_assum `IS_SOME (evaluate_type _ _)`
    (strip_assume_tac o REWRITE_RULE[optionTheory.IS_SOME_EXISTS]) >>
  metis_tac[])
QED

Theorem body_assign_toplevel_copy_ptr:
  body_expr_ptr_ok cx e /\ body_inv tops ctx cenv cx /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
    (Assign (BaseTarget (TopLevelNameTarget nid)) e) ==>
    occurs_abi_decode_target target tops) /\
  supported_variable_decl tops nid = SOME (Private,mut,ty,SOME slot) /\
  (mut = Storage \/ mut = Transient) /\
  ~is_word_type ty /\ (!elem n. ty <> ArrayT elem (Dynamic n)) /\
  0 < type_memory_bytes cenv ty /\ expr_type e = ty /\
  supported_expr tops e /\ expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (Assign (BaseTarget (TopLevelNameTarget nid)) e) = SOME env' /\
  stmt_exprs_ok cenv (Assign (BaseTarget (TopLevelNameTarget nid)) e) /\
  call_evaluation_safe cx
    (int_calls_stmt (Assign (BaseTarget (TopLevelNameTarget nid)) e)) ==>
  stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
    (stmt_env cenv lctx ret_ty (Assign (BaseTarget (TopLevelNameTarget nid)) e))
    (eval_stmt cx (Assign (BaseTarget (TopLevelNameTarget nid)) e)) es
Proof
  Cases_on `nid` >> rename1 `supported_variable_decl tops (src,id)` >>
  strip_tac >> (
  drule_at (Pos (el 2)) assign_base_storage_target >>
  disch_then drule >> simp[] >> disch_then drule >>
  disch_then drule >> strip_tac >> gvs[] >>
  drule_all assign_base_storage_rhs_pre >> strip_tac >>
  drule_all expr_sim_inv_memory_size >> strip_tac >>
  `0 < type_slot_size tv` by gvs[type_memory_size_slots] >>
  `storage_layout_safe cx /\ env_consistent env cx es` by fs[expr_sim_inv_def] >>
  `storage_var_info cx NONE id = SOME (tr,off,tv)` by simp[storage_var_info_def] >>
  drule_all assign_base_storage_region >> strip_tac >>
  `supported_storage_type tops (expr_type e)` by
    (`supported_program tops` by fs[body_inv_def] >>
     drule supported_variable_decl_mem >> strip_tac >>
     drule_all supported_program_declaration >> simp[supported_declaration_header_def]) >>
  `expr_sim_ptr d ctx PG func cenv cx (expr_type e) e es` by
    metis_tac[body_expr_ptr_ok_def] >>
  irule compile_assign_storage_copy_stmt_frag_ptr >>
  simp[] >> reverse conj_tac >- metis_tac[] >>
  qexistsl_tac [`id`, `n2w off`, `NONE`, `tr`] >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> drule_all expr_body_pre_eval_gas_ptr >> strip_tac >>
      `env.type_defs = get_tenv cx` by
        gvs[env_consistent_def, env_context_consistent_def] >>
      gvs[value_runtime_typed_def]) >>
  conj_tac >- (rpt strip_tac >> first_x_assum irule >> simp[] >> metis_tac[]) >>
  conj_tac >- metis_tac[evaluate_type_well_formed_type_value] >>
  conj_tac >- metis_tac[eval_assign_toplevel_action] >>
  conj_tac >- simp[declared_storage_region_def] >>
  strip_tac >> irule toplevel_storage_ce_vars >> metis_tac[])

QED
