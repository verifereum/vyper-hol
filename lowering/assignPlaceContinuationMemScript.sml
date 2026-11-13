(* Assignment-site producers and unwrap/store composition. *)
Theory assignPlaceContinuationMem
Ancestors
  assignPlaceMemoryContinuationMem assignPlaceBackendContinuationMem
  assignPlaceBytestringContinuationMem assignPlaceBytestringSourceMem
  assignPlaceSourceCapacityMem assignPlaceMaterializedSourceMem
  assignPlaceBytestringBackendTypes assignPlacePointerFrame
  assignPlaceScalarContinuationMem assignPlaceValueFrame bodyAssignPlace
  bodySimAugPlaceLoad memoryLocalRhsProps vyperStoragePlaceProvenance
  exprSimHypsDefs vyperTypeInvariants bodySimStmtCases bodySim supportedStmts
  loweringPosts exprSimUnwrapProps exprSimDefs context stmtLowering assignPlaceStackShape
  vyperAST vyperTypeSystem supportedExprs internalReturnMetadata exprLowering
  exprOpenCases exprSimTopLevelProps compileEnv vyperInterpreter vyperState
  supportedExprForms exprCallBounds

Theorem assign_site_root_layout[local]:
  expr_sim_inv cenv cx env ee /\
  lookup_scopes id ee.scopes = SOME entry /\
  cenv.ce_var_type id = SOME t0 ==>
  evaluate_type (get_tenv cx) t0 = SOME entry.type
Proof
  simp[expr_sim_inv_def, env_consistent_def, env_scopes_consistent_def] >>
  rpt strip_tac >>
  `?ty. FLOOKUP env.var_types id = SOME ty` by metis_tac[optionTheory.IS_SOME_EXISTS] >>
  metis_tac[optionTheory.SOME_11]
QED

Theorem assign_place_empty_continuation_mem_site:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (Assign (BaseTarget bt) e) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
     (Assign (BaseTarget bt) e) ==> occurs_abi_decode_target target tops) /\
  expr_sim_inv cenv cx env es /\
  type_stmt env ret_ty (Assign (BaseTarget bt) e) = SOME env' /\
  stmt_exprs_ok cenv (Assign (BaseTarget bt) e) /\
  call_evaluation_safe cx (int_calls_stmt (Assign (BaseTarget bt) e)) /\
  has_length_word (expr_type e) /\ is_empty_value_expr e /\
  eval_target_place cx bt es = (INL p,ee) /\
  type_place_target env bt = SOME (Type dty) /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  eval_operand dst s = SOME w /\
  place_ptr_rel cenv cx s (PlaceR p) w (SOME loc) (Type dty) /\
  stmt_state_rel ctx func cenv cx ee s /\
  write_place cx p (default_value dtv) ee = (INL (),ff) /\
  compile_store_at_loc cenv.ce_imm_alloca dst (Lit 0w) (SOME loc) sa = ((),sb) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?z. gas_path_mem ctx func s 0 (OK z) /\
      stmt_state_rel ctx func cenv cx ff z /\
      (!x. not_fresh_at sa x ==> lookup_var x z = lookup_var x s) /\
      ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
      z.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `target_indices_pre cenv cx env bt` by
    metis_tac[body_assign_place_indices_pre] >>
  `expr_sim_inv cenv cx env ee` by metis_tac[aug_place_target_inv] >>
  `has_length_word dty` by
    (drule assign_place_typing >> strip_tac >> gvs[] >>
     metis_tac[type_widens_to_has_length_word]) >>
  `!id path entry t0. p = MemoryPlace id path /\
     lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
     evaluate_type (get_tenv cx) t0 = SOME entry.type` by
    metis_tac[assign_site_root_layout] >>
  drule_all assign_place_empty_continuation_mem >> strip_tac >>
  qexists_tac `t` >> simp[]
QED

Theorem assign_site_rhs_read[local]:
  FST (read_result cx raw ee) = FST (read_result cx raw er) /\
  eval_expr cx e es = (INL raw,er) /\
  eval_target_place cx bt er = (INL p,ee) /\
  read_result cx raw ee = (INL v,ee) ==>
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v,er)
Proof
  strip_tac >>
  `FST (read_result cx raw er) = INL v` by
    metis_tac[pairTheory.FST] >>
  Cases_on `read_result cx raw er` >> gvs[] >>
  drule vyperStateTheory.read_result_state >> strip_tac >>
  simp[vyperStateTheory.bind_def]
QED

Theorem assign_site_runtime_types[local]:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (Assign (BaseTarget bt) e) /\
  expr_body_pre cenv cx env e es /\ target_indices_pre cenv cx env bt /\
  type_stmt env ret_ty (Assign (BaseTarget bt) e) = SOME env' /\
  type_place_target env bt = SOME (Type dty) /\
  FST (read_result cx raw ee) = FST (read_result cx raw er) /\
  eval_expr cx e es = (INL raw,er) /\
  eval_target_place cx bt er = (INL p,ee) /\
  read_result cx raw ee = (INL v,ee) ==>
  expr_sim_inv cenv cx env ee /\
  ?stv dtv. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv /\
    evaluate_type (get_tenv cx) dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size stv /\
    type_memory_bytes cenv dty = type_memory_size dtv
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_sim_inv cenv cx env er` by metis_tac[expr_body_pre_eval_result] >>
  `expr_sim_inv cenv cx env ee` by metis_tac[aug_place_target_inv] >>
  `supported_expr tops e` by fs[supported_stmt_def, supported_assignment_def] >>
  `supported_program tops /\ get_module_code cx NONE = SOME tops /\
   cenv.ce_func_return_type = build_func_return_type tops` by fs[body_inv_def] >>
  `well_typed_expr env e /\
   type_widens_to env.type_defs (expr_type e) dty /\
   assignable_type env.type_defs (expr_type e)` by
    (drule assign_place_typing >> strip_tac >> gvs[]) >>
  `(do r <- eval_expr cx e; read_result cx r od) es = (INL v,er)` by
    metis_tac[assign_site_rhs_read] >>
  `value_runtime_typed env (lowered_value_type cenv e) v` by
    metis_tac[memory_rhs_read_lowered_typed] >>
  `value_runtime_typed env dty v` by metis_tac[memory_rhs_read_destination_typed] >>
  metis_tac[memory_rhs_runtime_layout]
QED

Theorem assign_site_internal_stack_impossible[local]:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (Assign (BaseTarget bt) (Call ann (IntCall id) args drv)) /\
  expr_body_pre cenv cx env (Call ann (IntCall id) args drv) es /\
  target_indices_pre cenv cx env bt /\
  type_stmt env ret_ty (Assign (BaseTarget bt) (Call ann (IntCall id) args drv)) = SOME env' /\
  type_place_target env bt = SOME (Type dty) /\
  FST (read_result cx raw ee) = FST (read_result cx raw er) /\
  eval_expr cx (Call ann (IntCall id) args drv) es = (INL raw,er) /\
  eval_target_place cx bt er = (INL p,ee) /\
  read_result cx raw ee = (INL v,ee) /\
  compile_call f cenv ann ty (IntCall id) args drv sa = (StackValue vt op,sb) ==>
  F
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all assign_site_runtime_types >> strip_tac >>
  `well_typed_expr env (Call ann (IntCall id) args drv) /\
   assignable_type env.type_defs ann` by
    (drule assign_place_typing >> simp[expr_type_def] >> metis_tac[]) >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `?sig. FLOOKUP env.fn_sigs id = SOME sig /\
         type_widens_to env.type_defs sig.ret_ty ann` by
    (Cases_on `id` >> gvs[well_typed_expr_def] >> metis_tac[]) >>
  `cenv.ce_func_return_type (nsid_to_string id) = sig.ret_ty` by
    fs[expr_sim_inv_def] >>
  `supported_program tops /\
   cenv.ce_func_info = build_func_info (get_struct_fields (make_struct_fields_map tops)) tops /\
   cenv.ce_struct_fields = make_struct_fields_map tops` by fs[body_inv_def] >>
  `?mut nr rr pars dflts rt body.
     supported_function_decl tops id Internal = SOME (mut,nr,rr,pars,dflts,rt,body)` by
    (Cases_on `drv` >>
     gvs[supported_stmt_def, supported_assignment_def, supported_expr_def,
         supported_pure_expr_def, supported_effect_expr_def,
         optionTheory.IS_SOME_EXISTS] >>
     rename1 `supported_function_decl tops id Internal = SOME info` >>
     PairCases_on `info` >> metis_tac[]) >>
  drule_all supported_internal_call_info >> strip_tac >>
  `rt = sig.ret_ty` by
    (fs[body_inv_def] >> drule_all supported_internal_return_type >> simp[]) >>
  gvs[lowered_value_type_def] >>
  metis_tac[assign_internal_stack_typed_impossible]
QED

Theorem assign_site_name_not_stack[local]:
  expr_body_pre cenv cx env (Name ann id) es /\
  compile_expr cenv ty (Name ann id) sa = (StackValue vt op,sb) ==> F
Proof
  strip_tac >>
  `?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    gvs[expr_body_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
  gvs[compile_expr_def, compile_name_vv_def, compileEnvTheory.comp_return_def]
QED

Theorem assign_site_flag_word[local]:
  well_typed_expr env (FlagMember ann nsid mid) ==> is_word_type ann
Proof
  simp[well_typed_expr_def, compileEnvTheory.is_word_type_def]
QED

Theorem assign_site_toplevel_not_stack[local]:
  expr_body_pre cenv cx env (TopLevelName ann (src,id)) es /\
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
  eval_expr cx (TopLevelName ann (src,id)) es = (INL raw,er) /\
  compile_expr cenv ty (TopLevelName ann (src,id)) sa = (StackValue vt op,sb) ==> F
Proof
  strip_tac >>
  `?ts. get_module_code cx src = SOME ts` by
    (Cases_on `get_module_code cx src` >> simp[] >>
     qpat_x_assum `eval_expr _ _ _ = _` mp_tac >>
     simp[Once evaluate_def, lookup_global_def, vyperStateTheory.bind_def,
          lift_option_type_def, vyperStateTheory.raise_def]) >>
  Cases_on `find_var_decl_by_name id ts`
  >- (`FLOOKUP env.bare_globals (src,id) = SOME ann` by
        (irule toplevel_find_NONE_bare_global >>
         fs[expr_body_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
      `?off. FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off)` by
        (fs[expr_body_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
      gvs[compile_expr_def]) >>
  rename1 `find_var_decl_by_name id ts = SOME decl` >> PairCases_on `decl` >>
  drule_all eval_toplevel_decl_bound >> strip_tac >> gvs[compile_expr_def]
QED

Theorem assign_site_core_stack_word:
  expr_body_pre cenv cx env e es /\
  storage_vars_rel cenv cx /\ transient_vars_rel cenv cx /\
  eval_expr cx e es = (INL raw,er) /\
  compile_expr cenv (expr_type e) e sa = (StackValue vt op,sb) /\
  (!ann bi args. e <> Builtin ann bi args) /\
  (!ann tb dst args. e <> TypeBuiltin ann tb dst args) /\
  (!ann call args drv. e <> Call ann call args drv) ==>
  is_word_type (expr_type e)
Proof
  strip_tac >> Cases_on `e` >> gvs[expr_type_def]
  >~ [`Name ann id`] >- metis_tac[assign_site_name_not_stack]
  >~ [`TopLevelName ann nsid`] >-
    (PairCases_on `nsid` >> metis_tac[assign_site_toplevel_not_stack])
  >~ [`FlagMember ann nsid mid`] >-
    (fs[expr_body_pre_def] >> metis_tac[assign_site_flag_word]) >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[Once compile_expr_raw_def] >> strip_tac
  >~ [`Literal ann lit`] >-
    (fs[compile_expr_body_def, expr_type_def, expr_body_pre_def,
        well_typed_expr_def] >> metis_tac[compile_typed_literal_stack_is_word])
  >~ [`IfExp ann c a b`] >- metis_tac[compile_ifexp_stack_is_word]
  >~ [`StructLit ann name fields`] >- metis_tac[compile_structlit_not_stack]
  >~ [`Pop ann target`] >- metis_tac[compile_pop_not_stack] >>
  fs[compile_expr_body_def, expr_type_def] >>
  metis_tac[compile_attribute_not_stack, compile_subscript_not_stack]
QED

Theorem assign_site_type_builtin_stack_shape[local]:
  supported_expr tops (TypeBuiltin ann tb dst args) /\
  type_stmt env ret (Assign (BaseTarget bt) (TypeBuiltin ann tb dst args)) = SOME env' /\
  type_place_target env bt = SOME (Type dty) /\
  compile_expr cenv ann (TypeBuiltin ann tb dst args) sa = (StackValue vt op,sb) ==>
  is_word_type ann \/
  (is_bytestring_type ann /\
   is_bytestring_type (lowered_value_type cenv (TypeBuiltin ann tb dst args)) /\
   is_bytestring_type dty)
Proof
  strip_tac >> Cases_on `tb = Convert`
  >- (gvs[] >> metis_tac[assign_place_convert_result_shape]) >>
  `supported_type_builtin_form tops ann tb dst args` by
    fs[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def] >>
  disj1_tac >> irule supported_type_builtin_stack_word >>
  goal_assum (drule_at Any) >> simp[] >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[Once compile_expr_raw_def, compile_expr_body_def, expr_type_def] >>
  simp[Once compile_expr_raw_def] >> metis_tac[]
QED

Theorem assign_site_names_builtin_word[local]:
  !bi args. names_builtin bi args ==>
  !env ann. well_typed_expr env (Builtin ann bi args) ==> is_word_type ann
Proof
  ho_match_mp_tac names_builtin_ind >>
  simp[names_builtin_def, well_typed_expr_def, well_typed_builtin_app_def,
       is_word_type_def]
QED

Theorem assign_site_builtin_stack_word[local]:
  supported_expr tops (Builtin ann bi args) /\
  well_typed_expr env (Builtin ann bi args) /\
  compile_expr cenv ann (Builtin ann bi args) sa = (StackValue vt op,sb) ==>
  is_word_type ann
Proof
  strip_tac >> Cases_on `is_word_type ann` >> gvs[] >>
  `~names_builtin bi args` by metis_tac[assign_site_names_builtin_word] >>
  `supported_builtin_form tops ann bi args /\
   well_typed_builtin_app ann bi (MAP expr_type args)` by
    fs[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
       well_typed_expr_def] >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_expr_builtin_dispatch, Once compile_expr_raw_def] >>
  metis_tac[supported_builtin_stack_word]
QED

Theorem assign_site_dispatch_stack_shape[local]:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (Assign (BaseTarget bt) e) /\
  expr_body_pre cenv cx env e es /\ target_indices_pre cenv cx env bt /\
  type_stmt env ret_ty (Assign (BaseTarget bt) e) = SOME env' /\
  type_place_target env bt = SOME (Type dty) /\
  FST (read_result cx raw ee) = FST (read_result cx raw er) /\
  eval_expr cx e es = (INL raw,er) /\
  eval_target_place cx bt er = (INL p,ee) /\
  read_result cx raw ee = (INL v,ee) /\
  compile_expr cenv (expr_type e) e sa = (StackValue vt op,sb) /\
  ((?ann bi args. e = Builtin ann bi args) \/
   (?ann tb dst args. e = TypeBuiltin ann tb dst args) \/
   (?ann ct args drv. e = Call ann ct args drv)) ==>
  is_word_type (expr_type e) \/
  (is_bytestring_type (expr_type e) /\
   is_bytestring_type (lowered_value_type cenv e) /\ is_bytestring_type dty)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `supported_expr tops e` by fs[supported_stmt_def, supported_assignment_def] >>
  `well_typed_expr env e /\ assignable_type env.type_defs (expr_type e)` by
    (drule assign_place_typing >> metis_tac[]) >>
  Cases_on `e` >> gvs[expr_type_def]
  >~ [`Builtin ann bi args`] >-
    metis_tac[assign_site_builtin_stack_word]
  >~ [`TypeBuiltin ann tb dst args`] >-
    metis_tac[assign_site_type_builtin_stack_shape] >>
  rename1 `Call ann ct args drv` >>
  `compile_call compile_expr cenv ann ann ct args drv sa = (StackValue vt op,sb)` by
    fs[exprSimSendTheory.compile_expr_call] >>
  Cases_on `ct`
  >~ [`IntCall id`] >- metis_tac[assign_site_internal_stack_impossible, pairTheory.FST] >>
  Cases_on `drv` >>
  gvs[supported_expr_def, supported_pure_expr_def, supported_effect_expr_def,
      well_typed_expr_def, assignable_type_def] >>
  rename1 `ExtCall static skip signature opts` >> PairCases_on `signature` >>
  gvs[well_typed_expr_def] >>
  `args <> []` by (strip_tac >> gvs[]) >>
  drule_all compile_external_stack_void >>
  strip_tac >> gvs[assignable_type_def]
QED

(* The nonempty site starts after pure target evaluation, before unwrapping. *)
Theorem assign_place_nonempty_continuation_mem_site:
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (Assign (BaseTarget bt) e) /\
  expr_body_pre cenv cx env e es /\ target_indices_pre cenv cx env bt /\
  type_stmt env ret_ty (Assign (BaseTarget bt) e) = SOME env' /\
  type_place_target env bt = SOME (Type dty) /\
  target_store_place cenv bt = SOME (SOME (ValPT dty)) /\
  stmt_exprs_ok cenv (Assign (BaseTarget bt) e) /\
  FST (read_result cx raw ee) = FST (read_result cx raw er) /\
  ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
  (lowered_value_type cenv e = expr_type e \/
   is_bytestring_type (expr_type e) /\
   is_bytestring_type (lowered_value_type cenv e) /\
   arg_type_fits (lowered_value_type cenv e) (expr_type e)) /\
  eval_expr cx e es = (INL raw,er) /\
  eval_target_place cx bt er = (INL p,ee) /\
  read_result cx raw ee = (INL v,ee) /\
  write_place cx p v ee = (INL (),ff) /\
  compile_expr cenv (expr_type e) e sa = (vv,sr) /\
  unwrap_value cenv vv sm = (op,sn) /\
  compile_assign_value cenv dst loc op (is_word_type dty) (vv_location vv)
    dty (lowered_value_type cenv e)
    (case dty of ArrayT et (Dynamic _) =>
      SOME ((type_memory_bytes cenv et+31) DIV 32,type_memory_bytes cenv et)
     | _ => NONE) (type_memory_bytes cenv dty) sn = ((),sb) /\
  vv_post ctx func cenv cx e es sa sm s0 ee raw vv s /\
  vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee raw vv s /\
  eval_operand dst s = SOME w /\
  place_ptr_rel cenv cx s (PlaceR p) w (SOME loc) (Type dty) /\
  storage_place_region cx p /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!x. vv_operand vv = Var x \/ dst = Var x ==> not_fresh_at sm x) /\
  alloca_history func s /\ fn_inst_ids_distinct func /\
  fn_has_code sm sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?z. gas_path_mem ctx func s 0 (OK z) /\
    stmt_state_rel ctx func cenv cx ff z /\
    (!x v0. not_fresh_at sm x /\ lookup_var x s = SOME v0 ==>
             lookup_var x z = SOME v0) /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all assign_site_runtime_types >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `type_widens_to (get_tenv cx) (expr_type e) dty /\
   assignable_type (get_tenv cx) (expr_type e)` by
    (drule assign_place_typing >> strip_tac >> gvs[]) >>
  `(do r <- eval_expr cx e; read_result cx r od) es = (INL v,er)` by
    metis_tac[assign_site_rhs_read] >>
  `value_runtime_typed env (expr_type e) v` by
    metis_tac[exprSimHypsTheory.memory_rhs_read_annotation_typed] >>
  `?etv. evaluate_type (get_tenv cx) (expr_type e) = SOME etv /\
     value_has_type etv v /\
     type_memory_bytes cenv (expr_type e) = type_memory_size etv` by
    metis_tac[memory_rhs_runtime_layout] >>
  `post_value_type cenv e = expr_type e` by
    metis_tac[post_value_type_lowered, post_value_type_bytestring] >>
  `stmt_state_rel ctx func cenv cx ee s /\
   vv_holds cenv cx (expr_type e) raw vv ee s /\
   vv_at cenv cx (expr_type e) sa sm ee raw vv s` by fs[vv_post_def] >>
  `!id path entry t0. p = MemoryPlace id path /\
     lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
     evaluate_type (get_tenv cx) t0 = SOME entry.type` by
    metis_tac[assign_site_root_layout] >>
  Cases_on `is_word_type dty`
  >- suspend "word" >>
  `~is_word_type (expr_type e)` by
    metis_tac[typedMemoryCopyTheory.return_source_word_widens_eq] >>
  `~is_word_type (lowered_value_type cenv e) /\
   type_widens_to (get_tenv cx) (lowered_value_type cenv e) dty /\
   assignable_type (get_tenv cx) (lowered_value_type cenv e)` by
    (Cases_on `lowered_value_type cenv e = expr_type e` >- gvs[] >>
     `is_bytestring_type (expr_type e) /\
      is_bytestring_type (lowered_value_type cenv e) /\
      arg_type_fits (lowered_value_type cenv e) (expr_type e)` by metis_tac[] >>
     `is_bytestring_type dty` by
       metis_tac[typedMemoryCopyTheory.type_widens_from_bytestring] >>
     metis_tac[assign_bytestring_backend_types, valueCopyBytesTheory.is_bytestring_word_type]) >>
  Cases_on `vv`
  >- suspend "stack" >>
  rename1 `LocatedValue vt srcp` >>
  Cases_on `srcp.ptr_location = LocMemory`
  >- suspend "memory" >>
  suspend "materialized"
QED

Resume assign_place_nonempty_continuation_mem_site[word]:
  `expr_type e = dty` by
    (drule_all compileEnvTheory.type_widens_to_word >> simp[]) >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  drule bodyMemAssignAttrStorageTheory.vv_post_rebase_mem_src >> strip_tac >>
  `local_ptrs_reserved cenv (sa with cs_next_var := sm.cs_next_var)` by
    (qpat_x_assum `local_ptrs_reserved cenv sm` mp_tac >>
     simp_tac (srw_ss()) [local_ptrs_reserved_def, not_fresh_at_def] >> metis_tac[]) >>
  `emit_void (case loc of LocStorage => SSTORE | LocTransient => TSTORE
               | _ => MSTORE) [dst; op] sn = ((),sb)` by
    (`loc = LocMemory \/ loc = LocStorage \/ loc = LocTransient` by
       (qpat_x_assum `place_ptr_rel _ _ _ _ _ _ _` mp_tac >>
        Cases_on `p` >> simp[place_ptr_rel_def, slot_loc_def] >> metis_tac[]) >>
     qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     Cases_on `loc` >> fs[] >> simp[compile_assign_value_def,
         compile_store_at_loc_def, comp_bind_def, comp_return_def]) >>
  `cs_extends sm sn /\ cs_extends sn sb` by
    metis_tac[exprSimUnwrapTheory.unwrap_value_extends, stmtSimAugAssignPlaceTheory.aug_place_emit_void_grows] >>
  drule_all fragExecTheory.fn_has_code_split >> strip_tac >>
  drule_at (Pat `unwrap_value _ _ _ = _`) exprSimMemUnwrapTheory.unwrap_value_marked_read_mem >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ ee _ _ _ _ _ _ _`)) >>
  impl_tac >- simp[] >> strip_tac >>
  `v' = v /\ gas_path_mem ctx func s 0 (OK u)` by
    (drule exprSimMemorySourceTheory.read_result_gas_obs >> strip_tac >>
     qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gasSummaryTheory.gas_marked_exec_def, fragGasModeTheory.gas_marked_path_def]) >>
  qpat_x_assum `v' = v` SUBST_ALL_TAC >>
  `eval_operand dst u = SOME w` by
    (metis_tac[assign_materialized_destination_frame]) >>
  `stmt_state_rel ctx func cenv cx ee u /\ expr_val_rel cx dty v op u /\
   (!x z. not_fresh_at sm x /\ lookup_var x s = SOME z ==>
          lookup_var x u = SOME z)` by
    (qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     pure_rewrite_tac[expr_post_def] >> strip_tac >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- gvs[] >> rpt strip_tac >>
     first_x_assum irule >> gvs[not_fresh_at_def]) >>
  `~u.vs_halted` by
    (drule fragGasPathMemTheory.gas_path_mem_exec >>
     simp[fragExecTheory.exit_result_def]) >>
  `place_ptr_rel cenv cx u (PlaceR p) w (SOME loc) (Type dty)` by
    (irule assign_place_ptr_rel_forward_frame >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all assign_place_word_continuation_mem >> strip_tac >>
  qexists_tac `t` >> simp[] >>
  qpat_x_assum `gas_path_mem ctx func s 0 (OK u)` mp_tac >>
  disch_then (mp_then Any mp_tac fragGasPathMemTheory.gas_path_mem_then) >> simp[]
QED
Resume assign_place_nonempty_continuation_mem_site[stack]:
  rename1 `StackValue vt src` >>
  `is_bytestring_type (expr_type e) /\
   is_bytestring_type (lowered_value_type cenv e) /\ is_bytestring_type dty` by
    (Cases_on `(?ann bi args. e = Builtin ann bi args) \/
       (?ann tb dst args. e = TypeBuiltin ann tb dst args) \/
       (?ann ct args drv. e = Call ann ct args drv)`
     >- (drule_all assign_site_dispatch_stack_shape >> simp[]) >>
     `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
       fs[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def] >>
     drule assign_site_core_stack_word >> simp[] >> metis_tac[]) >>
  `op = src /\ sn = sm` by gvs[unwrap_value_def, comp_return_def] >>
  qpat_x_assum `op = src` SUBST_ALL_TAC >>
  qpat_x_assum `sn = sm` SUBST_ALL_TAC >>
  `?sw. eval_operand src s = SOME sw /\
     val_in_memory stv v (w2n sw) s.vs_memory /\
     w2n sw + type_memory_size stv <= s.vs_alloca_next` by
    (drule assign_original_memory_source_capacity >>
     simp[vv_operand_def] >> metis_tac[]) >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `val_wf stv v /\ val_wf dtv v` by
    metis_tac[cj 1 valueEncodingTypingTheory.value_has_type_val_wf] >>
  Cases_on `loc = LocMemory`
  >- (`w2n sw + val_store_size stv v <= s.vs_alloca_next` by
        (qpat_assum `val_wf stv v` (mp_tac o MATCH_MP exprSimPropsTheory.val_store_size_le) >> decide_tac) >>
      gns[vv_location_def, vv_operand_def] >>
      drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)
        assign_place_bytestring_continuation_mem >>
      disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
      disch_then (drule_at (Pat `write_place _ _ _ _ = _`)) >>
      disch_then (drule_at (Pat `eval_operand _ _ = SOME _`)) >>
      disch_then (qspecl_then [`w`, `stv`, `env`, `dtv`] mp_tac) >>
      impl_tac >- (simp[] >> metis_tac[]) >>
      strip_tac >> qexists_tac `t` >> simp[] >> metis_tac[]) >>
  suspend "stack_backend"
QED
Resume assign_place_nonempty_continuation_mem_site[stack_backend]:
  `?tr. loc = if tr then LocTransient else LocStorage` by
    (qexists_tac `loc = LocTransient` >> Cases_on `p` >> Cases_on `loc` >>
     gvs[place_ptr_rel_def, slot_loc_def, AllCaseEqs()]) >>
  `p = StoragePlace tr w dtv` by
    (Cases_on `p` >> Cases_on `tr` >> gvs[place_ptr_rel_def, slot_loc_def] >>
     rename1 `StoragePlace b slot tv` >> Cases_on `b` >> gvs[]) >>
  `well_formed_type_value dtv` by
    metis_tac[cj 1 vyperTypingTheory.evaluate_type_well_formed] >>
  gnvs[vyperStateTheory.write_place_def, vv_location_def, vv_operand_def] >>
  once_rewrite_tac[GSYM (SIMP_RULE (srw_ss()) []
    (Q.SPEC `T` fragGasModeTheory.gas_marked_path_def))] >>
  qsuff_tac `?z. gas_marked_path T ctx func s 0 (OK z) /\
    stmt_state_rel ctx func cenv cx ff z /\
    (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x s) /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts`
  >- metis_tac[] >>
  irule backend_direct_mem >> simp[] >> metis_tac[]
QED
Resume assign_place_nonempty_continuation_mem_site[memory]:
  `~is_word_type vt` by
    (fs[vv_holds_def] >> metis_tac[valueCopyBytesTheory.is_bytestring_word_type]) >>
  `op = srcp.ptr_operand /\ sn = sm` by
    gvs[unwrap_value_def, comp_return_def] >>
  qpat_x_assum `op = srcp.ptr_operand` SUBST_ALL_TAC >>
  qpat_x_assum `sn = sm` SUBST_ALL_TAC >>
  `?sw. eval_operand srcp.ptr_operand s = SOME sw /\
     val_in_memory stv v (w2n sw) s.vs_memory /\
     w2n sw + type_memory_size stv <= s.vs_alloca_next` by
    (drule assign_original_memory_source_capacity >>
     simp[vv_operand_def] >> metis_tac[]) >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  Cases_on `loc = LocMemory`
  >- (`acyclic_struct_metadata cenv.ce_struct_fields` by fs[body_inv_def] >>
      gns[vv_location_def, vv_operand_def] >>
      qsuff_tac `?z. gas_path_mem ctx func s 0 (OK z) /\
        stmt_state_rel ctx func cenv cx ff z /\
        (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x s) /\
        ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
        z.vs_inst_idx = LENGTH sb.cs_current_insts`
      >- metis_tac[] >>
      irule assign_place_memory_continuation_mem >> simp[] >>
      goal_assum (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
      simp[] >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  suspend "memory_backend"
QED
Resume assign_place_nonempty_continuation_mem_site[memory_backend]:
  `?tr. loc = if tr then LocTransient else LocStorage` by
    (qexists_tac `loc = LocTransient` >> Cases_on `p` >> Cases_on `loc` >>
     gvs[place_ptr_rel_def, slot_loc_def, AllCaseEqs()]) >>
  `well_formed_type_value stv /\ well_formed_type_value dtv` by
    metis_tac[cj 1 vyperTypingTheory.evaluate_type_well_formed] >>
  `val_wf stv v /\ val_wf dtv v` by
    metis_tac[cj 1 valueEncodingTypingTheory.value_has_type_val_wf] >>
  `acyclic_struct_metadata cenv.ce_struct_fields` by fs[body_inv_def] >>
  `dty <> lowered_value_type cenv e /\
   ~(is_bytestring_type dty /\ is_bytestring_type (lowered_value_type cenv e)) ==>
   type_memory_size dtv < dimword (:256)` by
    metis_tac[assign_place_normalization_size_bound] >>
  Cases_on `lowered_value_type cenv e = expr_type e`
  >- suspend "memory_backend_equal" >>
  suspend "memory_backend_bytes"
QED
Resume assign_place_nonempty_continuation_mem_site[memory_backend_equal]:
  gnvs[vv_location_def, vv_operand_def] >>
  once_rewrite_tac[GSYM (SIMP_RULE (srw_ss()) []
    (Q.SPEC `T` fragGasModeTheory.gas_marked_path_def))] >>
  qsuff_tac `?z. gas_marked_path T ctx func s 0 (OK z) /\
    stmt_state_rel ctx func cenv cx ff z /\
    (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x s) /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts`
  >- metis_tac[] >>
  irule assign_place_backend_continuation_mem >> simp[] >>
  goal_assum (drule_at (Pat `vv_at _ _ _ _ _ _ _ _ _`)) >>
  simp[vv_operand_def, vv_location_def] >>
  goal_assum (drule_at (Pat `place_ptr_rel _ _ _ _ _ _ _`)) >>
  simp[] >> qexistsl_tac [`dst`,`env`] >> simp[] >> metis_tac[]
QED
Resume assign_place_nonempty_continuation_mem_site[memory_backend_bytes]:
  `is_bytestring_type (lowered_value_type cenv e) /\ is_bytestring_type dty` by
    metis_tac[typedMemoryCopyTheory.type_widens_from_bytestring] >>
  `p = StoragePlace tr w dtv` by
    (Cases_on `p` >> Cases_on `tr` >> gvs[place_ptr_rel_def, slot_loc_def] >>
     rename1 `StoragePlace b slot tv` >> Cases_on `b` >> gvs[]) >>
  gnvs[vyperStateTheory.write_place_def, vv_location_def, vv_operand_def] >>
  once_rewrite_tac[GSYM (SIMP_RULE (srw_ss()) []
    (Q.SPEC `T` fragGasModeTheory.gas_marked_path_def))] >>
  qsuff_tac `?z. gas_marked_path T ctx func s 0 (OK z) /\
    stmt_state_rel ctx func cenv cx ff z /\
    (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x s) /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts`
  >- metis_tac[] >>
  irule backend_direct_mem >> simp[] >> metis_tac[]
QED
Resume assign_place_nonempty_continuation_mem_site[materialized]:
  `vt = expr_type e /\ ~is_word_type vt` by
    (qpat_assum `vv_holds _ _ _ _ _ _ _` mp_tac >>
     Cases_on `srcp.ptr_location` >> gvs[vv_holds_def]) >>
  `vv_post ctx func cenv cx e es sa sm s0 ee (Value v)
     (LocatedValue vt srcp) s` by
    metis_tac[exprSimAggregateChildrenTheory.vv_post_materialise] >>
  `cs_extends sm sn /\ cs_extends sn sb` by
    (conj_tac >- metis_tac[exprSimUnwrapTheory.unwrap_value_extends] >>
     qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     qspec_then `cenv` mp_tac externalEntryShapeTheory.compile_assign_value_labels >>
     metis_tac[pairTheory.SND]) >>
  drule_all fragExecTheory.fn_has_code_split >> strip_tac >>
  `!tv. evaluate_type (get_tenv cx) vt = SOME tv ==>
     type_memory_bytes cenv vt = type_memory_size tv /\ type_memory_size tv < 2**64` by
    (rpt strip_tac >>
     `type_memory_bytes cenv vt = type_memory_size tv` by
       metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
     `type_alloc_ok cenv (expr_type e)` by
       (irule exprSimHypsTheory.alloc_limits_expr_type_alloc_ok >> fs[expr_body_pre_def]) >>
     gvs[allocLimitsTheory.type_alloc_ok_def]) >>
  suspend "materialized_run"
QED
Resume assign_place_nonempty_continuation_mem_site[materialized_run]:
  markerLib.RESUME_TAC >>
  `(!x. srcp.ptr_operand = Var x ==> not_fresh_at sm x) /\
   (!x. dst = Var x ==> not_fresh_at sm x)` by
    (qpat_x_assum `!x. vv_operand _ = Var x \/ _ ==> _` mp_tac >>
     simp[vv_operand_def] >> metis_tac[]) >>
  `?u sw tv. gas_path_mem ctx func s 0 (OK u) /\
    expr_post ctx func cenv cx e ee (sa with cs_next_var := sm.cs_next_var)
      sn s ee v op u /\
    evaluate_type (get_tenv cx) vt = SOME tv /\ eval_operand op u = SOME sw /\
    val_wf tv v /\ val_in_memory tv v (w2n sw) u.vs_memory /\
    w2n sw + type_memory_size tv < dimword (:256) /\
    w2n sw + type_memory_size tv <= u.vs_alloca_next /\
    (!name b len. local_region cenv ee.scopes u name b len ==>
      regions_disjoint (w2n sw) (type_memory_size tv) b len) /\
    ~u.vs_halted /\ u.vs_current_bb = sn.cs_current_bb /\
    u.vs_inst_idx = LENGTH sn.cs_current_insts /\ alloca_history func u /\
    eval_operand dst u = SOME w /\
    (!x w0. not_fresh_at sm x /\ lookup_var x s = SOME w0 ==>
      lookup_var x u = SOME w0)` by
    (qpat_x_assum `vt = expr_type e` SUBST_ALL_TAC >>
     Cases_on `srcp.ptr_location = LocCode`
     >- (irule assign_code_materialized_source_mem >>
         simp[vv_operand_def] >>
         goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
         simp[] >> metis_tac[]) >>
     `srcp.ptr_location = LocStorage \/ srcp.ptr_location = LocTransient` by
       (qpat_assum `vv_holds _ _ _ _ _ _ _` mp_tac >>
        Cases_on `srcp.ptr_location` >> gvs[vv_holds_def]) >>
     irule assign_storage_materialized_source_mem >> simp[vv_operand_def] >>
     goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     simp[] >> metis_tac[]) >>
  suspend "materialized_store"
QED
Resume assign_place_nonempty_continuation_mem_site[materialized_store]:
  markerLib.RESUME_TAC >>
  `stmt_state_rel ctx func cenv cx ee u` by
    metis_tac[expr_post_def] >>
  `place_ptr_rel cenv cx u (PlaceR p) w (SOME loc) (Type dty)` by
    (irule assign_place_ptr_rel_forward_frame >>
     goal_assum (drule_at (Pat `place_ptr_rel _ _ _ _ _ _ _`)) >>
     qexists_tac `sm` >> simp[] >>
     metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var]) >>
  `val_in_memory stv v (w2n sw) u.vs_memory /\
   w2n sw + type_memory_size stv <= u.vs_alloca_next /\
   w2n sw + type_memory_size stv < dimword (:256) /\
   (!name b len. local_region cenv ee.scopes u name b len ==>
      regions_disjoint (w2n sw) (type_memory_size stv) b len)` by
    (qpat_x_assum `vt = expr_type e` SUBST_ALL_TAC >>
     `tv = etv` by metis_tac[optionTheory.SOME_11] >>
     qpat_x_assum `tv = etv` SUBST_ALL_TAC >>
     drule_at (Pat `val_in_memory _ _ _ _`) assign_materialized_lowered_contents >>
     disch_then (qspecl_then [`stv`, `lowered_value_type cenv e`, `expr_type e`] mp_tac) >>
     disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
     disch_then (qspecl_then [`ee`, `cenv`] mp_tac) >>
     impl_tac >- (simp[] >> rpt gen_tac >> disch_tac >>
       first_assum irule >> metis_tac[]) >> simp[]) >>
  suspend "materialized_destination"
QED
Resume assign_place_nonempty_continuation_mem_site[materialized_destination]:
  markerLib.RESUME_TAC >>
  `sm.cs_next_var <= sn.cs_next_var` by
    (qpat_assum `unwrap_value _ _ _ = _` mp_tac >>
     qspecl_then [`cenv`, `LocatedValue vt srcp`, `sm`] mp_tac
       exprLoweringPropsTheory.ci_mono_unwrap_value >> simp[exprLoweringPropsTheory.ci_mono_def]) >>
  `local_ptrs_reserved cenv sn` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `(!x. op = Var x ==> not_fresh_at sn x) /\
   (!x. dst = Var x ==> not_fresh_at sn x)` by
    (conj_tac
     >- (drule exprOperandVarTheory.compiler_unwrap_value_var >> simp[]) >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `acyclic_struct_metadata cenv.ce_struct_fields` by fs[body_inv_def] >>
  suspend "materialized_route"
QED
Resume assign_place_nonempty_continuation_mem_site[materialized_route]:
  markerLib.RESUME_TAC >>
  `?z. gas_path_mem ctx func u 0 (OK z) /\
    stmt_state_rel ctx func cenv cx ff z /\
    (!x. not_fresh_at sn x ==> lookup_var x z = lookup_var x u) /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts` by
    (Cases_on `loc = LocMemory`
     >- (gns[vv_location_def] >>
         irule assign_place_memory_continuation_mem >> simp[] >>
         goal_assum (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
         simp[] >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
     suspend "materialized_backend") >>
  suspend "materialized_compose"
QED
Resume assign_place_nonempty_continuation_mem_site[materialized_compose]:
  markerLib.RESUME_TAC >>
  `gas_path_mem ctx func s 0 (OK z)` by
    metis_tac[fragGasPathMemTheory.gas_path_mem_then, arithmeticTheory.ADD_CLAUSES] >>
  qexists_tac `z` >> simp[] >>
  rpt strip_tac >>
  `not_fresh_at sn x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  metis_tac[]
QED
Resume assign_place_nonempty_continuation_mem_site[materialized_backend]:
  markerLib.RESUME_TAC >>
  `?tr. loc = if tr then LocTransient else LocStorage` by
    (qpat_x_assum `place_ptr_rel _ _ u _ _ _ _` mp_tac >>
     qpat_x_assum `loc <> LocMemory` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     Cases_on `p` >> Cases_on `loc` >>
     simp[place_ptr_rel_def, slot_loc_def, AllCaseEqs()] >>
     rpt strip_tac >> Cases_on `b` >> gvs[]) >>
  `well_formed_type_value stv /\ well_formed_type_value dtv` by
    metis_tac[cj 1 vyperTypingTheory.evaluate_type_well_formed] >>
  `val_wf stv v /\ val_wf dtv v` by
    metis_tac[cj 1 valueEncodingTypingTheory.value_has_type_val_wf] >>
  (Cases_on `lowered_value_type cenv e = expr_type e`
   >- suspend "materialized_backend_equal" >>
   suspend "materialized_backend_bytes")
QED
Resume assign_place_nonempty_continuation_mem_site[materialized_backend_equal]:
  markerLib.RESUME_TAC >>
  `vv_at cenv cx (expr_type e) (sa with cs_next_var := sm.cs_next_var) sn
    ee (Value v) (StackValue (expr_type e) op) u` by
    (qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     qpat_x_assum `post_value_type cenv e = expr_type e` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[vv_at_def, vyperStateTheory.read_result_def, expr_post_def,
          vyperStateTheory.return_def]) >>
  `compile_assign_value cenv dst (if tr then LocTransient else LocStorage)
     op F NONE dty (expr_type e)
     (case dty of ArrayT et (Dynamic _) =>
       SOME ((type_memory_bytes cenv et+31) DIV 32,type_memory_bytes cenv et)
       | _ => NONE) (type_memory_bytes cenv dty) sn = ((),sb)` by
    (qpat_x_assum `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     qpat_x_assum `loc = if tr then _ else _` mp_tac >>
     qpat_x_assum `lowered_value_type cenv e = expr_type e` mp_tac >>
     qpat_x_assum `~is_word_type dty` mp_tac >>
     qpat_x_assum `type_memory_bytes cenv dty = type_memory_size dtv` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     rpt strip_tac >> Cases_on `tr` >>
     gns[vv_location_def, compile_assign_value_def]) >>
  `dty <> expr_type e /\
   ~(is_bytestring_type dty /\ is_bytestring_type (expr_type e)) ==>
   type_memory_size dtv < dimword (:256)` by
    metis_tac[assign_place_normalization_size_bound] >>
  once_rewrite_tac[GSYM (SIMP_RULE (srw_ss()) []
    (Q.SPEC `T` fragGasModeTheory.gas_marked_path_def))] >>
  `stv = etv /\ tv = etv` by
    (qpat_x_assum `evaluate_type _ _ = SOME stv` mp_tac >>
     qpat_x_assum `evaluate_type _ _ = SOME tv` mp_tac >>
     qpat_x_assum `evaluate_type _ _ = SOME etv` mp_tac >>
     qpat_x_assum `lowered_value_type cenv e = expr_type e` mp_tac >>
     qpat_x_assum `vt = expr_type e` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[]) >>
  qpat_x_assum `loc = if tr then _ else _` SUBST_ALL_TAC >>
  irule assign_place_backend_continuation_mem >> simp[] >>
  goal_assum (drule_at (Pat `vv_at _ _ _ _ _ _ _ _ _`)) >>
  simp[vv_operand_def, vv_location_def, vyperStateTheory.read_result_def,
       vyperStateTheory.return_def] >>
  goal_assum (drule_at (Pat `place_ptr_rel _ _ _ _ _ _ _`)) >>
  simp[] >> qexistsl_tac [`dst`,`env`] >> gns[] >>
  rpt strip_tac >> simp[]
QED
Resume assign_place_nonempty_continuation_mem_site[materialized_backend_bytes]:
  markerLib.RESUME_TAC >>
  `is_bytestring_type (lowered_value_type cenv e) /\ is_bytestring_type dty` by
    (qpat_x_assum `_ \/ is_bytestring_type _ /\ _` mp_tac >>
     qpat_x_assum `lowered_value_type cenv e <> expr_type e` mp_tac >>
     qpat_x_assum `type_widens_to _ (lowered_value_type cenv e) dty` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     metis_tac[typedMemoryCopyTheory.type_widens_from_bytestring]) >>
  `p = StoragePlace tr w dtv` by
    (qpat_x_assum `place_ptr_rel _ _ u _ _ _ _` mp_tac >>
     qpat_x_assum `evaluate_type _ dty = SOME dtv` mp_tac >>
     qpat_x_assum `loc = if tr then _ else _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     Cases_on `p` >> Cases_on `tr` >>
     gvs[place_ptr_rel_def, slot_loc_def] >>
     Cases_on `b` >> gvs[]) >>
  gnvs[vyperStateTheory.write_place_def, vv_location_def, vv_operand_def] >>
  once_rewrite_tac[GSYM (SIMP_RULE (srw_ss()) []
    (Q.SPEC `T` fragGasModeTheory.gas_marked_path_def))] >>
  irule backend_direct_mem >> simp[] >>
  goal_assum (drule_at (Pat `write_storage_slot _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `val_in_memory _ _ _ _`)) >>
  goal_assum (drule_at (Pat `eval_operand _ _ = _`)) >>
  simp[] >> goal_assum (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
  qexistsl_tac [`dty`,`SOME srcp.ptr_location`,`op`,`lowered_value_type cenv e`] >>
  gns[] >> rpt strip_tac >> simp[]
QED
Finalise assign_place_nonempty_continuation_mem_site
