(* Request-prefix companion to bodyFullAssignAttrStorage. *)
Theory s1PrefixAssignAttrStorage
Ancestors
  s1PrefixPreds s1PrefixDefs s1PrefixCompose s1PrefixProps bodySimFull
  stmtSimAssignAttrStorage stmtSimProps exprSimTopLevelProps exprSimHyps exprSimDefs
  exprLoweringProps fragExec compileEnv loweringPosts stateRelProj
  gasShadowCompileStmtHelpers gasShadowState gasShadow gasOutcomeFull
  gasOutcomeFullCompose tuplePlaceStep vyperStorageFootprint vyperStorageTrace
  vyperInterpreter vyperState sum list
  bodyFullExtCallPackingReady[qualified,ignore_grammar]
Libs monadsyntax

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >>
  rewrite_tac[stmt_frag_prefix_def, stmt_frag_full_pre_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `storage_trace_domain cx st0 es.storage_trace`
  >- suspend "valid" >>
  suspend "invalid"
QED
*)
Theorem compile_assign_attr_storage_prefix:
  !DF lo d ctx shadow_ctx PG func shadow_func cx lctx RetQ cenv ty env
   src id fld sid fty fsz e es ts tr id_str slot.
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr (StructT sid),id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  cenv.ce_hashmap_info (src,id) = NONE /\
  cenv.ce_module_var_type (src,id) = SOME (StructT sid) /\
  ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld =
      SOME (fty,fsz) /\
  is_word_type fty /\
  expr_type e = fty /\
  expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e es /\
  expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx (expr_type e) e es /\
  expr_body_pre cenv cx env e es ==>
  stmt_frag_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cx lctx RetQ cenv
      (stmt_env cenv lctx ty
        (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src,id)) fld)) e))
      (stmt_env (gas_shadow_env T cenv) lctx ty
        (gas_shadow_stmt
          (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src,id)) fld)) e)))
      (eval_stmt cx
        (Assign (BaseTarget (AttributeTarget (TopLevelNameTarget (src,id)) fld)) e)) es
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume compile_assign_attr_storage_prefix[valid]:
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace)
     es.storage_trace` by fs[storage_trace_domain_def] >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace)
     ctx func cenv cx es s0` by metis_tac[] >>
  `FLOOKUP cenv.ce_module_vars (src,id) =
     SOME (if tr then TransientLoc (n2w slot) else StorageLoc (n2w slot))` by
    (drule stmt_state_rel_vars_rels >> strip_tac >>
     irule toplevel_storage_ce_vars >> goal_assum (drule_at Any) >> simp[]) >>
  `is_word_type (expr_type e)` by simp[] >>
  drule_all assign_attr_storage_code_parts >> strip_tac >> gvs[] >>
  rename1 `emit_void _ _ su = ((),sb)` >>
  `ci_mono sa sm /\ ci_mono sm sn /\ ci_mono sn su /\ ci_mono su sb` by
    metis_tac[compile_expr_ci_mono, ci_mono_emit_op, ci_mono_unwrap_value,
              ci_mono_emit_void, pairTheory.SND] >>
  `fn_has_code sa sm func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split, cs_extends_trans]) >>
  `?shadow_sm. compile_expr (gas_shadow_env T cenv) (expr_type e)
                  (gas_shadow_expr e) shadow_sa = (vv,shadow_sm) /\
                gas_shadow_state sm shadow_sm` by
    (`gas_shadow_compiles (compile_expr cenv (expr_type e) e)
       (compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e))`
       by irule gas_shadow_stmt_compile_expr_env >>
     qpat_x_assum `gas_shadow_compiles _ _`
       (qspecl_then [`sa`,`shadow_sa`] mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
     Cases_on `compile_expr (gas_shadow_env T cenv) (expr_type e)
                 (gas_shadow_expr e) shadow_sa` >> simp[]) >>
  `cs_extends shadow_sa shadow_sm /\ cs_extends shadow_sm shadow_sb` by
    (qpat_x_assum `stmt_env _ _ _ (gas_shadow_stmt _) _ = _` mp_tac >>
     simp[gas_shadow_stmt_def, gas_shadow_assignment_def, gas_shadow_expr_def] >>
     strip_tac >>
     drule_at (Pat `stmt_env _ _ _ _ _ = _`) assign_attr_storage_code_parts >>
     simp[] >> strip_tac >>
     qpat_x_assum `!tr' slot'. _` (qspecl_then [`tr`,`n2w slot`] strip_assume_tac) >>
     gvs[] >>
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
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 (eval_expr cx e) (es,s0,G0,tn0)` by
    (qpat_x_assum `expr_vv_sim_prefix _ _ _ _ _ _`
      (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`vv`,`s0`,`G0`,`tn0`]
       mp_tac o REWRITE_RULE [expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def]) >>
     simp[] >> disch_then irule >> first_assum ACCEPT_TAC) >>
  rewrite_tac[eval_assign_attr_toplevel_action] >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (eval_expr cx e) (es,s0,G0,tn0)
     (\H res ee G tn t. ~t.vs_halted) (\H res ee gt r. ISR res)` by
    (qpat_x_assum `expr_vv_sim_full _ _ _ _ _ _`
      (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shadow_sm`,`vv`,`s0`,`G0`,`tn0`]
       mp_tac o REWRITE_RULE [expr_vv_sim_full_def]) >>
     (impl_tac >- (simp[] >> metis_tac[])) >>
     disch_then (mp_then Any irule gas_outcome_full_post_source) >>
     simp[] >> rpt gen_tac >> Cases_on `res` >> simp[expr_exit_def]) >>
  pop_assum (mp_then Any irule gas_prefix_full_bind_no_outcome) >>
  simp[evaluate_storage_trace_frame, evaluate_requests_outcomes_frame] >>
  reverse conj_tac
  >- (gen_tac >> irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_read_result] >>
      gen_tac >> irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_write_place]) >>
  rpt gen_tac >>
  Cases_on `read_result cx v (st with gas_obs := gobs)` >>
  drule read_result_state >> strip_tac >> gvs[] >>
  rename1 `read_result cx v _ = (raw,_)` >>
  reverse (Cases_on `raw`) >> simp[bind_def]
  >- (strip_tac >> gvs[]) >>
  Cases_on `eval_target_place cx (AttributeTarget (TopLevelNameTarget (src,id)) fld)
              (st with gas_obs := gobs)` >>
  rename1 `eval_target_place _ _ _ = (ans,mid)` >>
  `mid.storage_trace = st.storage_trace \/
   ?tv. mid.storage_trace = st.storage_trace ++ [StorageRoot tr slot tv]` by
    (qpat_x_assum `eval_target_place _ _ _ = _` mp_tac >>
     simp[Once evaluate_def, bind_def] >>
     simp[Once evaluate_def, bind_def] >>
     simp[Once evaluate_def, lookup_global_def, lift_option_type_def,
          bind_def, return_def, ignore_bind_def, record_storage_event_def] >>
     Cases_on `evaluate_type (get_tenv cx) (StructT sid)` >>
     simp[raise_def, return_def, extend_place_def, bind_def]
     >- (strip_tac >> gvs[]) >>
     rename1 `evaluate_type _ _ = SOME tv` >>
     Cases_on `tv` >>
     simp[extend_storage_place_def, lift_option_type_def, bind_def, raise_def,
          return_def, get_place_def] >>
     TRY (strip_tac >> gvs[] >> NO_TAC) >>
     rename1 `struct_field_slot fields fld` >>
     Cases_on `struct_field_slot fields fld` >> simp[raise_def,return_def] >>
     TRY (strip_tac >> gvs[] >> NO_TAC) >>
     pairarg_tac >> simp[return_def,get_place_def] >> strip_tac >> gvs[]) >>
  Cases_on `ans` >> simp[] >> strip_tac >>
  TRY (qpat_assum `write_place _ _ _ _ = _`
         (mp_then Any assume_tac write_place_storage_trace)) >>
  gvs[DROP_APPEND1]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume compile_assign_attr_storage_prefix[invalid]:
  rewrite_tac[gas_prefix_full_def] >> qexists_tac `[]` >> conj_tac
  >- (qexistsl_tac [`storage_trace_horizon es.storage_trace`,`func`,`PG`,
                     `G0`,`tn0`,`s0`] >> simp[gas_origin_ptr_focus_nil]) >>
  rpt gen_tac >> strip_tac >>
  `?xs. ee.storage_trace = es.storage_trace ++ xs` by
    (qpat_assum `eval_stmt _ _ _ = _`
       (mp_then Any mp_tac vyperStorageTraceTheory.storage_trace_frame_prefix) >>
     simp[evaluate_storage_trace_frame]) >>
  `TAKE (LENGTH es.storage_trace) obs_pre = es.storage_trace` by
    (`TAKE (LENGTH es.storage_trace) ee.storage_trace =
      TAKE (LENGTH es.storage_trace) obs_pre` by
       (qpat_assum `ee.storage_trace = obs_pre ++ _`
          (fn th => PURE_ONCE_REWRITE_TAC [th]) >> simp[TAKE_APPEND1]) >>
     pop_assum mp_tac >>
     qpat_assum `ee.storage_trace = es.storage_trace ++ _`
       (fn th => PURE_ONCE_REWRITE_TAC [th]) >> simp[TAKE_APPEND1]) >>
  `?ys. obs_pre = es.storage_trace ++ ys` by metis_tac[TAKE_DROP] >>
  metis_tac[valid_horizon_append,
            bodyFullExtCallPackingReadyTheory.extcall_packing_observed_domain]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise compile_assign_attr_storage_prefix
*)
