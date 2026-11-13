(* Direct joint execution of a word-field assignment. *)
Theory bodyFullAssignAttrStorage
Ancestors
  bodyFullAssignAttrStorageAddress bodyFullAssignAttrStorageStore
  bodyFullUnwrapWord bodySimFull gasOutcomeFullCompose gasOutcomeFull
  stmtSimAssignAttrStorage stmtSimAssignStorage stmtSimForced assignTuplePtrStorage
  stmtSimProps stmtSimDefs bodyMemoryDefs bodyPtrDefs
  gasShadowCompileStmtHelpers gasShadowState gasShadow gasExemptCert
  gasSummaryCompose gasContext gasSummary
  fragGasOriginPtr fragGasOrigin fragGasMode fragGasPath fragExec
  exprSimHyps exprSimHypsDefs exprSimVVFrame exprSimDefs exprSimSource loweringPosts
  exprSimMemDefs exprLoweringProps exprOperandVar bodyExprPreFacts
  exprSimMemorySource exprSimUnwrap exprSimFieldLayout exprSimTopLevelProps
  stmtLowering exprLowering compileEnv loweringStateRelDefs allocaHistory
  vyperStorageTrace vyperStorageFootprint vyperStoragePlaceRegion
  vyperStorageRegionWrite vyperStorageBackend accountsRelProps
  vyperEvalExprPreservesScopesDom vyperInterpreter vyperState vyperValue
  venomState venomInst ptrDiscipline context list finite_map pred_set
Libs monadsyntax

Theorem compile_assign_attr_storage_full:
  !DF lo d ctx shadow_ctx PG func shadow_func cx lctx RetQ cenv ty env
   src id fld sid fty fsz e es ts tr id_str slot.
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr (StructT sid),id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    cenv.ce_hashmap_info (src,id) = NONE /\
    cenv.ce_module_var_type (src,id) = SOME (StructT sid) /\
    ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld =
      SOME (fty,fsz) /\ is_word_type fty /\ expr_type e = fty /\
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e es /\
    expr_body_pre cenv cx env e es ==>
    stmt_frag_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ty
        (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src,id)) fld)) e))
      (stmt_env cenv lctx ty
        (gas_shadow_stmt
          (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src,id)) fld)) e)))
      (eval_stmt cx
        (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src,id)) fld)) e)) es
Proof
  rpt gen_tac >> strip_tac >> rewrite_tac[stmt_frag_full_def] >>
  rpt gen_tac >> strip_tac >>
  irule gas_outcome_full_initial_domain >>
  simp[evaluate_storage_trace_frame] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace)
     es.storage_trace` by fs[storage_trace_domain_def] >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace)
     ctx func cenv cx es s0` by metis_tac[] >>
  `FLOOKUP cenv.ce_module_vars (src,id) =
     SOME (if tr then TransientLoc (n2w slot) else StorageLoc (n2w slot))` by
    (irule toplevel_storage_ce_vars >>
     gvs[stmt_state_rel_def, state_rel_def] >> metis_tac[]) >>
  `is_word_type (expr_type e)` by simp[] >>
  drule_all assign_attr_storage_code_parts >> strip_tac >> gvs[] >>
  rename1 `emit_void _ _ su = ((),sb)` >>
  `ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn su /\ ci_mono su sb` by
    metis_tac[compile_expr_ci_mono, ci_mono_emit_op, ci_mono_unwrap_value,
              ci_mono_emit_void, pairTheory.SND] >>
  `fn_has_code sa sm func /\ fn_has_code sm sn func /\
   fn_has_code sn su func /\ fn_has_code su sb func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split, cs_extends_trans]) >>
  `?shadow_sm. compile_expr cenv (expr_type e) (gas_shadow_expr e) shadow_sa =
                (vv,shadow_sm) /\ gas_shadow_state sm shadow_sm` by
    (mp_tac (Q.INST [`cenv` |-> `cenv`, `ty` |-> `expr_type e`, `e` |-> `e`]
       gas_shadow_stmt_compile_expr) >>
     simp[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >> simp[] >>
     Cases_on `compile_expr cenv (expr_type e) (gas_shadow_expr e) shadow_sa` >>
     simp[]) >>
  `cs_extends shadow_sa shadow_sm /\ cs_extends shadow_sm shadow_sb` by
    (qpat_x_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _` mp_tac >>
     simp[gas_shadow_stmt_def, gas_shadow_assignment_def, gas_shadow_expr_def] >>
     strip_tac >>
     mp_tac (Q.SPECL [`cenv`, `lctx`, `ty`, `src`, `id`, `fld`,
       `gas_shadow_expr e`, `shadow_sa`, `cenv`, `shadow_sb`, `tr`,
       `n2w slot`, `sid`, `expr_type e`, `fsz`] assign_attr_storage_code_parts) >>
     simp[] >> strip_tac >> gvs[] >>
     rename1 `emit_op ADD _ shadow_sm = (shadow_dst,shadow_sn)` >>
     rename1 `unwrap_value cenv vv shadow_sn = (shadow_op,shadow_su)` >>
     `ci_mono shadow_sa shadow_sm /\ ci_mono shadow_sm shadow_sn /\
      ci_mono shadow_sn shadow_su /\ ci_mono shadow_su shadow_sb` by
       metis_tac[compile_expr_ci_mono, ci_mono_emit_op, ci_mono_unwrap_value,
                 ci_mono_emit_void, pairTheory.SND] >>
     fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code shadow_sa shadow_sm shadow_func` by
    metis_tac[fn_has_code_split] >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
          not_fresh_at sa x` by fs[ret_pc_ok_def] >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    metis_tac[expr_body_pre_vv_gas_admissible] >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_full_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `shadow_sa`, `shadow_sm`, `vv`,
                           `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
  rewrite_tac[eval_assign_attr_toplevel_action] >>
  irule gas_outcome_full_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_result >>
      qexistsl_tac [`mid`, `t`, `v`] >> RULE_ASSUM_TAC BETA_RULE >>
      BETA_TAC >> rpt conj_tac >> first_assum ACCEPT_TAC)
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_result >> simp[])
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`storage_trace_frame _`]
  >- (gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_read_result] >>
      gen_tac >> irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_write_place]) >>
  qexists_tac `\H res ee G tn t. childQ H res ee G tn t /\
                    ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac >- suspend "continue" >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  conj_tac >- simp[] >>
  simp[Abbr `childR`] >> rpt strip_tac >>
  Cases_on `res` >- fs[expr_exit_def] >>
  simp[stmt_exit_ptr_def] >>
  metis_tac[expr_exit_INR_type]
QED

Resume compile_assign_attr_storage_full[continue]:
  qx_genl_tac [`marks`, `res`, `mid`, `G1`, `tn1`, `t`] >>
  BETA_TAC >> strip_tac >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` kall_tac >>
  qunabbrev_tac `childQ` >> RULE_ASSUM_TAC BETA_RULE >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `res = INL _` SUBST_ALL_TAC >>
  gvs[] >>
  `mid with gas_obs := [] = mid` by
    simp[evaluation_state_component_equality] >>
  `eval_expr cx e
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL tv,mid)` by
    (qpat_assum `mid with gas_obs := [] = mid` (fn mt =>
       qpat_assum `!tail. eval_expr _ _ _ = _`
         (ACCEPT_TAC o SIMP_RULE (srw_ss()) [mt] o Q.SPEC `[]`))) >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (drule eval_expr_preserves_scopes_dom >> simp[]) >>
  `?rty. evaluate_type (get_tenv cx) (expr_type e) = SOME rty /\
     !v. read_result cx tv mid = (INL v,mid) ==> value_has_type rty v` by
    (drule_at (Pat `eval_expr _ _ _ = _`) expr_body_pre_runtime_typed >>
     simp[] >> metis_tac[]) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
   sm.cs_next_var <= sn.cs_next_var /\ sm.cs_next_id <= sn.cs_next_id` by
    fs[ci_mono_def] >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     vv_post H ctx func cenv cx e es sa sm s0 mid tv vv t /\
     ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `H` mp_tac) >> simp[]) >>
  mp_tac (Q.INST [`explicit` |-> `gas_explicit_sites ctx shadow_ctx`,
    `PG` |-> `PG`, `ty` |-> `expr_type e`, `s` |-> `t`,
    `G` |-> `G1`, `tn` |-> `tn1`, `raw` |-> `tv`, `ee` |-> `mid`,
    `Gi` |-> `G0`, `ti` |-> `tn0`, `root` |-> `n2w slot`,
    `off` |-> `struct_field_offset_slots
       (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld`]
    storage_field_address_full) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    metis_tac[cj 1 compiler_compile_var] >>
  `!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
          ptr_buf_ok cenv e p.ptr_operand HG q` by
    (rpt strip_tac >> gvs[] >>
     fs[ptr_buf_ok_def, vv_operand_def] >> rpt strip_tac >>
     Cases_on `p.ptr_operand` >>
     gvs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     metis_tac[]) >>
  `post_value_type cenv e = expr_type e` by simp[] >>
  `(is_word_type (post_value_type cenv e) ==> is_word_type (expr_type e)) /\
   (!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
     ~is_word_type (post_value_type cenv e) ==>
     type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
     type_memory_size rt < 2**64) /\
   (!t' op0. vv = StackValue t' op0 /\
     ~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op0 HG q) /\
   evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rty` by simp[] >>
  mp_tac (Q.INST [`explicit` |-> `gas_explicit_sites ctx shadow_ctx`,
    `PG` |-> `PG`, `ty` |-> `expr_type e`, `sb` |-> `sn`, `sc` |-> `su`,
    `s` |-> `q`, `ee` |-> `mid`, `G` |-> `HG`, `tn` |-> `tf`,
    `Gi` |-> `G0`, `ti` |-> `tn0`] unwrap_word_value_origin_ptr) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  rename1 `read_result cx tv mid = (INL v,mid)` >>
  rename1 `ptr_val_ok cx _ v op Gu tu z` >>
  qpat_assum `!H. valid_horizon cx st0 H mid.storage_trace ==>
       gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  mp_tac (Q.INST [`fty` |-> `expr_type e`, `raw` |-> `tv`, `ee` |-> `mid`,
    `gs` |-> `gas_explicit marks s0.vs_gas_readings`]
    assign_attr_storage_source_counted) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rename1 `write_storage_slot _ _ _ _ _ _ = (result,ff)` >>
  `type_slot_size ftv = 1` by metis_tac[word_type_slot_size] >>
  `well_formed_type_value ftv` by
    metis_tac[cj 1 vyperTypingTheory.evaluate_type_well_formed] >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace)
     ctx func cenv cx mid z` by fs[expr_post_def] >>
  `~z.vs_halted` by
    metis_tac[gas_origin_ptr_path_projections, gas_origin_path_erase,
              gas_marked_path_exec, gas_path_normal] >>
  `~z.vs_call_ctx.cc_static /\ ~cx.txn.is_static /\ alloca_inv z` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `result = INL ()` by
    (qpat_x_assum `write_storage_slot _ _ _ _ _ _ = _` mp_tac >>
     simp[write_storage_slot_eq]) >>
  pop_assum SUBST_ALL_TAC >>
  `ff.gas_obs = [] /\ ff.scopes = mid.scopes /\
   ff.storage_trace = mid.storage_trace ++ [StorageRoot tr slot (StructTV fs)]` by
    (qpat_x_assum `write_storage_slot _ _ _ _ _ _ = _` mp_tac >>
     simp[write_storage_slot_eq] >> Cases_on `tr` >>
     simp[set_storage_def] >> strip_tac >> gvs[]) >>
  `ff with gas_obs := [] = ff` by
    simp[evaluation_state_component_equality] >>
  `eval_operand op z = SOME (typed_val_to_w256 ftv v)` by
    (gvs[expr_post_def, expr_val_rel_def] >> metis_tac[]) >>
  `eval_operand dst z = SOME (n2w slot + n2w off) /\
   op_taint tu dst = {}` by
    (gvs[ptr_val_ok_def] >>
     qpat_assum `!x. not_fresh_at sn x ==> _`
       (qspec_then `out` mp_tac) >>
     simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     metis_tac[]) >>
  qabbrev_tac `u = if tr then tstore (n2w slot + n2w off)
      (typed_val_to_w256 ftv v) z
    else sstore (n2w slot + n2w off) (typed_val_to_w256 ftv v) z` >>
  qabbrev_tac `tnf = step_taint
    (mk_inst su.cs_next_id (if tr then TSTORE else SSTORE) [dst;op] []) z u tu` >>
  qabbrev_tac `stored_state = u with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  irule (Q.INST [`t` |-> `stored_state`, `G'` |-> `Gu`, `tn'` |-> `tnf`,
                 `ee` |-> `ff`, `res` |-> `INL ()`]
    (INST_TYPE [alpha |-> ``:unit``] gas_outcome_full_pure)) >> simp[] >>
  qexistsl_tac [`Gu`, `ff`, `stored_state`, `tnf`] >> simp[] >>
  qx_gen_tac `H` >> strip_tac >>
  `valid_horizon cx st0 H mid.storage_trace /\
   MEM (tr,n2w slot,StructTV fs) (FST H) /\ regions_consistent (FST H)` by
    fs[valid_horizon_def, storage_observations_ok_def,
       EVERY_APPEND, storage_trace_regions_def] >>
  `stmt_state_rel H ctx func cenv cx mid z /\
   storage_well_formed_on cx mid (FST H) /\
   ghost_inv_at (DF H) lo d cenv cx mid Gu tu z` by
    metis_tac[expr_post_def] >>
  `allocas_from lo z` by fs[ghost_inv_at_def] >>
  `op_taint tu op = {}` by fs[ptr_val_ok_def] >>
  `dead_lo_ok H (DF H) lo cenv cx` by metis_tac[] >>
  drule_all (Q.INST [`D` |-> `DF H`, `explicit` |-> `gas_explicit_sites ctx shadow_ctx`,
                    `PG` |-> `PG`, `root` |-> `n2w slot`,
                    `es` |-> `mid`, `es'` |-> `ff`, `G` |-> `Gu`, `tn` |-> `tu`]
    storage_field_store_origin_ptr) >>
  disch_then (qspecl_then [`shadow_ctx`, `PG`] strip_assume_tac) >>
  `!w st. storage_dead H tr (update_storage (n2w slot + n2w off) w st) =
           storage_dead H tr st` by
    (rpt gen_tac >> irule storage_dead_update_struct_word_field >> metis_tac[]) >>
  `stmt_state_rel H ctx func cenv cx ff stored_state` by
    (qspecl_then [`H`, `func`, `cenv`, `cx`,
       `mid with storage_trace := mid.storage_trace ++ [StorageRoot tr slot (StructTV fs)]`,
       `z`, `tr`, `n2w slot + n2w off`, `ftv`, `v`, `typed_val_to_w256 ftv v`,
       `INL ()`, `ff`, `ctx`] mp_tac stmt_state_rel_write_storage_word >>
     (impl_tac >- simp[]) >>
     simp[Abbr `stored_state`, Abbr `u`, stmt_state_rel_inst_idx]) >>
  `storage_well_formed_on cx ff (FST H)` by
    (qabbrev_tac `mid_root = mid with storage_trace :=
       mid.storage_trace ++ [StorageRoot tr slot (StructTV fs)]` >>
     `storage_well_formed_on cx mid_root (FST H)` by
       fs[Abbr `mid_root`, storage_well_formed_on_def] >>
     `storage_subregion (StructTV fs) [AttrSubscript fld] off ftv` by
       simp[storage_subregion_def] >>
     `w2n (n2w slot : bytes32) + type_slot_size (StructTV fs) <= dimword(:256)` by
       metis_tac[regions_consistent_def] >>
     drule storage_subregion_bounds >> strip_tac >>
     `w2n (n2w slot + n2w off : bytes32) = w2n (n2w slot : bytes32) + off` by
       (`w2n (n2w slot : bytes32) + off < dimword(:256)` by decide_tac >>
        Cases_on `(n2w slot : bytes32)` >> fs[wordsTheory.word_add_n2w]) >>
     `slots_in_range (get_storage cx mid_root tr)
        (w2n (n2w slot : bytes32)) (StructTV fs)` by
       metis_tac[storage_well_formed_on_def] >>
     `0 < type_slot_size ftv` by simp[] >>
     `slots_in_range (get_storage cx ff tr)
        (w2n (n2w slot : bytes32)) (StructTV fs)` by
       (drule_all storage_subregion_typed_write_preserves_root >> simp[]) >>
     irule contained_write_preserves_storage_well_formed_on >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >> simp[] >>
     qexistsl_tac [`v`, `n2w slot + n2w off`, `ftv`] >> simp[] >> decide_tac) >>
  `tnf.t_var = tu.t_var` by
    (simp[Abbr `tnf`] >> irule (cj 2 clean_storage_step_taint_ptr) >>
     Cases_on `tr` >> simp[Abbr `u`, tstore_def, sstore_def] >>
     qexists_tac `n2w slot + n2w off` >>
     qpat_assum `dst = Var out` (fn th => PURE_ONCE_REWRITE_TAC [GSYM th]) >>
     first_assum ACCEPT_TAC) >>
  `sa.cs_next_var <= sb.cs_next_var` by
    (fs[ci_mono_def] >> decide_tac) >>
  `return_buf_frame d cenv sb stored_state` by
    (irule (Q.SPECL [`d`, `cenv`, `cenv`, `sa`, `sb`, `s0`, `stored_state`]
       return_buf_frame_frame) >> simp[] >>
     qexistsl_tac [`s0`, `sa`] >>
     simp[Abbr `stored_state`, Abbr `u`] >> Cases_on `tr` >>
     fs[expr_post_def, tstore_def, sstore_def, lookup_var_def]) >>
  `gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (t,G1,tn1) [] (OK z,Gu,tu)` by
    (qpat_assum `!D. gas_origin_ptr_path _ _ _ _`
       (qspec_then `DF H` assume_tac) >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ _`
       (qspec_then `H` assume_tac) >>
     metis_tac[gas_origin_ptr_path_append, APPEND_NIL]) >>
  conj_tac
  >- (qunabbrev_tac `stored_state` >> qunabbrev_tac `tnf` >> qunabbrev_tac `u` >>
      qpat_assum `gas_origin_ptr_path _ (t,G1,tn1) [] (OK z,Gu,tu)` mp_tac >>
      qpat_assum `gas_origin_ptr_path _ (z,Gu,tu) [] _` mp_tac >>
      rpt (pop_assum kall_tac) >> rpt strip_tac >>
      metis_tac[gas_origin_ptr_path_append, APPEND_NIL]) >>
  simp[stmt_lands_def, cenv_top_ext_refl, Abbr `stored_state`, Abbr `tnf`, Abbr `u`] >>
  Cases_on `tr` >>
  fs[expr_post_def, ghost_kept_at_def, op_taint_def,
     tstore_def, sstore_def, lookup_var_def] >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`!x. not_fresh_at sa x ==> FLOOKUP Gu x = FLOOKUP G0 x /\ _`,
     `(step_taint _ _ _ _).t_var = tu.t_var`, `dst = Var out`,
     `ftv = rty`, `off = struct_field_offset_slots _ fld`] >>
  rpt (pop_assum kall_tac) >> rpt strip_tac >> gvs[]
QED

Finalise compile_assign_attr_storage_full
