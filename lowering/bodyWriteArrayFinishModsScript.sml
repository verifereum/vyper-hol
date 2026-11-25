(* Finish an array target at the endpoint of its one bounds/address run. *)
Theory bodyWriteArrayFinishMods
Ancestors
  bodyWriteArrayPacketMods gasOutcomeFullPostMods bodyFullUnwrapRun
  bodyBinopFragMemory stmtReasonLitFragMemory exprSimWordArgs wordArgsPtr
  exprSimProps loweringSlice bodyWriteTargetStageMods bodyFullPostsMods
  bodyFullShadowBodyInv bodyInvSplit targetSubscriptSplit targetSubscriptContinuation
  vyperStorageTrace vyperStorageFootprint vyperEvalExprPreservesScopesDom
  exprLoweringProps loweringStateRelDefs allocaHistory venomState fragExec
  rich_list bodyPtrDefs ptrDiscipline exprSimDefs vyperState freshWrites
  vyperTypeEnv vyperTypeSystem exprLowering loweringPosts allocasBelowFmpUpdatesProps

Theorem array_finish_entry_horizon[local]:
  eval_base_place cx bt (es with gas_obs := base_gas) = (INL pv,mid1) /\
  bind (eval_expr cx e) (read_result cx) (mid1 with gas_obs := index_gas) =
    (INL v,mid2) /\
  valid_horizon cx st0 H mid2.storage_trace ==>
  valid_horizon cx st0 H es.storage_trace
Proof
  strip_tac >>
  `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
    (irule storage_trace_frame_bind_all >>
     simp[evaluate_storage_trace_frame,storage_trace_frame_read_result]) >>
  `valid_horizon cx st0 H mid1.storage_trace` by
    (drule_all valid_horizon_frame >> simp[]) >>
  `storage_trace_frame (eval_base_place cx bt)` by simp[evaluate_storage_trace_frame] >>
  drule_all valid_horizon_frame >> simp[]
QED

Theorem array_finish_prefix_frames[local]:
  stmt_state_rel (H : (bool # 256 word # type_value) list # num list) ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\ MAP FDOM es.scopes = MAP FDOM mid1.scopes /\ ci_mono sa sm /\
  write_target_post_mods H (DF H) lo d ctx func cenv cx bt
    es sa sm s0 mid1 pv bvt rb G0 tn0 G1 tn1 t1 /\
  expr_post_mods H ctx func cenv cx e mid1 sm sn t1 mid2 v iop t2 /\
  ghost_kept_at lo cenv mid1 sm G1 tn1 t1 G2 tn2 ==>
  wb_frame cenv es mid2 sa s0 t2 /\ ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2
Proof
  strip_tac >> drule write_target_post_view_mods >> strip_tac >>
  fs[expr_post_mods_def,ci_mono_def] >> drule_then assume_tac expr_post_frame >>
  `wb_frame cenv es mid2 sa s0 t2` by
    (irule (INST_TYPE [alpha |-> ``:256``] wb_frame_trans) >> simp[] >>
     conj_tac >- (qexistsl [`mid1`,`sm`,`t1`] >> simp[]) >>
     qexistsl [`H`,`ctx`,`cx`,`func`] >> simp[]) >>
  simp[] >> irule (INST_TYPE [beta |-> ``:256``] ghost_kept_at_wb_trans) >> simp[] >>
  conj_tac >- (qexistsl [`H`,`ctx`,`cx`,`func`] >> simp[]) >>
  qexistsl [`G1`,`mid1`,`mid1`,`t1`,`sm`,`tn1`] >> simp[]
QED

Theorem array_finish_vars[local]:
  local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  t = s with <|vs_vars := t.vs_vars; vs_inst_idx := t.vs_inst_idx|> /\
  stmt_state_rel H ctx func cenv cx es s /\ immutable_frame_mods func cenv cx es s ==>
  stmt_state_rel H ctx func cenv cx es t /\ immutable_frame_mods func cenv cx es t
Proof
  strip_tac >> conj_tac
  >- (`stmt_state_rel H ctx func cenv cx es (s with vs_vars := t.vs_vars)` by
        (irule stmt_state_rel_vars_frame >> simp[] >>
         fs[local_ptrs_reserved_def,lookup_var_def] >> metis_tac[]) >>
      `t = (s with vs_vars := t.vs_vars) with vs_inst_idx := t.vs_inst_idx` by
        (qpat_assum `t = s with <|vs_vars := _; vs_inst_idx := _|>` (mp_tac o REWRITE_RULE [venom_state_component_equality]) >> simp[]) >>
      pop_assum (fn th => once_rewrite_tac[th]) >> simp[stmt_state_rel_inst_idx]) >>
  `t.vs_data_section = s.vs_data_section /\ t.vs_memory = s.vs_memory /\
   t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    (qpat_assum `t = s with <|vs_vars := _; vs_inst_idx := _|>` (mp_tac o REWRITE_RULE [venom_state_component_equality]) >> simp[]) >>
  fs[immutable_frame_mods_def,immutables_rel_mods_def,immutable_alloca_sep_mods_def] >>
  conj_tac
  >- (rpt strip_tac >> irule immutables_rel_mem_agree >> qexists `s` >> simp[]) >>
  rpt strip_tac >> irule immutable_alloca_sep_fields >> qexistsl [`s`,`es`] >> simp[] >>
  rpt strip_tac >> qexists `id` >>
  fs[local_region_def,local_ptrs_reserved_def] >> metis_tac[]
QED

Theorem array_finish_ghost[local]:
  ghost_inv_at_mods D lo d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
         FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
  t.vs_memory = s.vs_memory /\ tn'.t_mem = tn.t_mem /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
  t.vs_transient = s.vs_transient /\ t.vs_immutables = s.vs_immutables /\
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm ==>
  ghost_inv_at_mods D lo d cenv cx es G' tn' t
Proof
  simp[ghost_inv_at_mods_def,local_ptrs_reserved_def,stor_taint_ok_at_def,
       allocas_from_def] >> rpt strip_tac
  >- (gvs[ptr_covers_def] >> metis_tac[])
  >- metis_tac[]
  >- (Cases_on `d` >- gvs[return_buf_ptr_def] >>
      PairCases_on `x` >> gvs[return_buf_ptr_def,ptr_covers_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem array_finish_alloca_history[local]:
  alloca_history func t2 /\ fn_has_code sn sb func /\
  t2.vs_current_bb = sn.cs_current_bb /\ t3.vs_current_bb = t2.vs_current_bb /\
  t2.vs_inst_idx = LENGTH sn.cs_current_insts /\
  t3.vs_inst_idx = LENGTH sb.cs_current_insts /\ t3.vs_allocas = t2.vs_allocas /\
  sb.cs_current_bb = sn.cs_current_bb /\ sb.cs_current_insts = sn.cs_current_insts ++ code /\
  EVERY (\i. i.inst_opcode <> ALLOCA) code ==>
  alloca_history func t3
Proof
  strip_tac >> drule_all fn_has_code_code >> strip_tac >>
  fs[IS_PREFIX_APPEND] >>
  `alloca_history func (t3 with vs_inst_idx := t2.vs_inst_idx + LENGTH code)` by
    (irule alloca_history_no_alloca_slice >> simp[] >>
     qexistsl [`bb`,`l`,`t2`] >> simp[]) >>
  `t3 with vs_inst_idx := t2.vs_inst_idx + LENGTH code = t3` by
    simp[venom_state_component_equality] >>
  fs[]
QED

Theorem array_finish_result_type[local]:
  type_place_target env bt = SOME (Type (ArrayT et bd)) /\
  type_place_target env (SubscriptTarget bt e) = SOME vt /\
  FST (SND rb) = SOME loc /\ SND (SND rb) = SOME (ValPT (ArrayT et bd)) /\
  target_subscript_suffix cenv e rb iop sn = (r,sb) ==>
  SND (SND r) = SOME (value_type_place vt)
Proof
  Cases_on `rb` >> rename1 `(_,rest)` >> Cases_on `rest` >>
  simp[type_place_target_SubscriptTarget,subscript_vtype_def,AllCaseEqs()] >>
  strip_tac >> gvs[target_subscript_suffix_array,value_type_place_def] >>
  gvs[subscript_vtype_def,AllCaseEqs(),value_type_place_def]
QED

Theorem write_array_finish_mods:
  write_array_reached_mods
    ((DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func),
     (mods,exps,cenv,cx,env,bt,e,et,bd,vt),
     (st0,es,sa,s0,G0,tn0),
     (sm,sn,sb,shadow_sa,shadow_sb,rb,iop,r),
     (base_gas,mid1,pv,t1,G1,tn1),
     (index_gas,mid2,v,t2,G2,tn2)) /\
  write_array_select_frame
    ((DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func),
     (mods,exps,cenv,cx,env,bt,e,et,bd,vt),
     (st0,es,sa,s0,G0,tn0),
     (sm,sn,sb,shadow_sa,shadow_sb,rb,iop,r),
     (base_gas,mid1,pv,t1,G1,tn1),
     (index_gas,mid2,v,t2,G2,tn2))
    (loc,b,iw,nw) (t3,G3,tn3) /\
  extend_place cx pv (ValueSubscript v) mid2 = (res,mid2) /\
  (if idx_in_range (is_signed_type (expr_type e)) iw nw then
     ?child. res = INL child /\
       (!H. valid_horizon cx st0 H mid2.storage_trace ==>
         target_ptr_ok cenv child r G3 tn3 t3 /\
         write_target_location_mods cenv cx (SubscriptTarget bt e) mid2 child vt r G3 t3)
   else ?msg. res = INR (Error (RuntimeError msg))) ==>
  write_array_suffix_mods
    ((DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func),
     (mods,exps,cenv,cx,env,bt,e,et,bd,vt),
     (st0,es,sa,s0,G0,tn0),
     (sm,sn,sb,shadow_sa,shadow_sb,rb,iop,r),
     (base_gas,mid1,pv,t1,G1,tn1),
     (index_gas,mid2,v,t2,G2,tn2))
Proof
  simp[write_array_reached_mods_def,write_array_select_frame_def,write_array_suffix_mods_def] >>
  strip_tac >>
  `!tail. extend_place cx pv (ValueSubscript v) (mid2 with gas_obs := tail) =
            (res,mid2 with gas_obs := tail)` by simp[target_subscript_extend_gas_obs] >>
  Cases_on `idx_in_range (is_signed_type (expr_type e)) iw nw`
  >- suspend "normal" >>
  gs[] >> irule gas_outcome_full_mods_exit >> simp[] >>
  qexistsl [`G3`,`mid2`,`Abort Revert_abort t3`,`INR (Error (RuntimeError msg))`,`tn3`] >>
  simp[exit_result_def,expr_exit_def,halt_exit_def]
QED

Resume write_array_finish_mods[normal]:
  gs[] >> irule gas_outcome_full_mods_pure >> simp[] >>
  qexistsl [`G3`,`mid2`,`INL child`,`t3`,`tn3`] >> simp[] >>
  gen_tac >> strip_tac >>
  `mid2 with gas_obs := [] = mid2` by simp[evaluation_state_component_equality] >>
  qpat_assum `!H. valid_horizon cx st0 H mid2.storage_trace ==>
               _ /\ expr_post_mods H ctx func cenv cx e mid1 sm sn t1 mid2 v iop t2 /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  simp[] >> suspend "post"
QED

Resume write_array_finish_mods[post]:
  qhdtm_x_assum `write_target_entry_mods`
    (strip_assume_tac o REWRITE_RULE [write_target_entry_mods_def]) >>
  `valid_horizon cx st0 H es.storage_trace` by
    (drule_all array_finish_entry_horizon >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx es s0` by
    (qpat_assum `!K. valid_horizon cx st0 K es.storage_trace ==> _` drule >> simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM mid1.scopes` by
    (drule eval_base_place_preserves_scopes_dom >> simp[]) >>
  drule_all array_finish_prefix_frames >> strip_tac >>
  `sa.cs_next_var <= sn.cs_next_var` by
    (fs[ci_mono_def] >> decide_tac) >>
  `!x. not_fresh_at sa x ==> lookup_var x t3 = lookup_var x t2 /\
       FLOOKUP G3 x = FLOOKUP G2 x /\ op_taint tn3 (Var x) = op_taint tn2 (Var x)` by
    (rpt strip_tac >> drule_all not_fresh_at_mono >>
     simp[lookup_var_def,op_taint_def]) >>
  `t3 = t2 with <|vs_vars := t3.vs_vars; vs_inst_idx := t3.vs_inst_idx|>` by
    (qpat_assum `t3 with <|vs_vars := _; vs_inst_idx := _|> = t2` mp_tac >>
     simp[venom_state_component_equality]) >>
  suspend "resources"
QED

Resume write_array_finish_mods[resources]:
  `stmt_state_rel H ctx func cenv cx mid2 t2 /\ storage_well_formed_on cx mid2 (FST H) /\
   immutable_frame_mods func cenv cx mid2 t2` by
    fs[expr_post_mods_def,expr_post_def] >>
  `stmt_state_rel H ctx func cenv cx mid2 t3 /\ immutable_frame_mods func cenv cx mid2 t3` by
    (irule array_finish_vars >> qexistsl [`t2`,`sa`] >> simp[]) >>
  qpat_assum `t3 with <|vs_vars := _; vs_inst_idx := _|> = t2`
    (strip_assume_tac o REWRITE_RULE [venom_state_component_equality,venom_state_accfupds]) >>
  `wb_frame cenv es mid2 sa s0 t3` by
    (irule wb_frame_readonly_tail >> qexistsl [`sa`,`t2`] >> simp[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G3 tn3` by
    (irule ghost_kept_at_clean_suffix >> qexistsl [`G2`,`tn2`] >> simp[]) >>
  `ghost_inv_at_mods (DF H) lo d cenv cx mid2 G3 tn3 t3` by
    (irule array_finish_ghost >> simp[] >> qexistsl [`G2`,`t2`,`sa`,`tn2`] >> simp[]) >>
  `alloca_history func t3` by
    (irule array_finish_alloca_history >> qexistsl [`code`,`sb`,`sn`,`t2`] >> simp[]) >>
  drule write_target_post_view_mods >> strip_tac >>
  `SND (SND rb) = SOME (ValPT (ArrayT et bd))` by simp[value_type_place_def] >>
  `SND (SND r) = SOME (value_type_place vt)` by
    (drule_all array_finish_result_type >> simp[]) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t3` by
    (`allocas_below_fmp t3 <=> allocas_below_fmp t2` by
       (irule allocas_below_fmp_fields >> simp[]) >> simp[]) >>
  `s0.vs_alloca_next <= t3.vs_alloca_next` by decide_tac >>
  qpat_assum `!K. valid_horizon cx st0 K mid2.storage_trace ==>
                  target_ptr_ok cenv child r G3 tn3 t3 /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  drule_then assume_tac target_subscript_suffix_var >>
  simp[write_target_post_mods_def]
QED

Finalise write_array_finish_mods
