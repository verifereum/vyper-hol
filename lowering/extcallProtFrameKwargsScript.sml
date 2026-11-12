Theory extcallProtFrameKwargs
Ancestors
  extcallProtFrameUnread extcallProtFrameJointUnwrap
  extcallProtFrameKwargMaterialize extcallProtFrameKwargPrepare
  exprExtRequestKwargCps exprExtRequestKwargSuffix exprExtRequestKwargs
  exprExtRequestGasBind exprExtRequestHistoryCompose exprSimHypsDefs
  exprExtRequestShape exprExtRequestUnreadCps exprExtRequestSourceFrame exprExtRequestReadProbe
  exprExtRequestStrongCapture exprExtRequestHistory exprExtRequestRetained
  exprLoweringProps exprSimProps exprSimDefs exprSimHyps loweringPosts compileEnv gasSummary
  gasOutcome stmtSimDeclGas stmtSimForRounds loweringHalt pair fragExec exprOperandVar exprSafeOperand context typedMemoryCopy exprSimAggregateSource
  fragGasPath fragGasMode exprLowering vyperInterpreter vyperState vyperTypeSystem allocLimits loweringStateRelDefs valueEncodingDefs
Libs
  monadsyntax

Theorem extcall_protframe_kwarg_retained_cps:
  expr_vv_case nocalls ctx func cenv cx e /\
  expr_body_pre cenv cx env e es /\ ~expr_has_effect e /\
  (nocalls ==> int_calls_expr e = []) /\
  expr_type e = ext_call_kw_type ret kw /\
  (kw = EKDefault ==> ret <> NoneT) /\
  compile_ext_call_kwarg compile_expr cenv ret kw e sa = ((op,dty),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  gas_admissible (bind (bind (eval_expr cx e) (read_result cx)) kont)
     expr_vv_res_ok es /\
  extrequest_strong_captures ctx func cenv cx old_es old_rs old_vvs
    (es with gas_obs := []) sa s0 /\
  (!e ee sm sn t ef r vv u ty p w tv.
    vv_post ctx func cenv cx e ee sm sn t ef r vv u /\
    ~expr_has_effect e /\ vv = LocatedValue ty p /\
    eval_operand p.ptr_operand u = SOME w /\
    evaluate_type (get_tenv cx) ty = SOME tv ==>
    (p.ptr_location = LocStorage ==>
      storage_read_live cx F (get_storage cx ef F) w tv) /\
    (p.ptr_location = LocTransient ==>
      storage_read_live cx T (get_storage cx ef T) w tv)) /\
  (!e ee sm sn t ef r vv u.
    vv_post ctx func cenv cx e ee sm sn t ef r vv u /\
    ~expr_has_effect e ==>
    (!n b sz. local_region cenv ee.scopes t n b sz ==>
      mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz t.vs_memory) /\
    (!off len.
      (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
        sm.cs_next_id <= inst.inst_id /\
        FLOOKUP u.vs_allocas inst.inst_id = SOME (b,sz) ==>
        loweringStateRelDefs$regions_disjoint off len b sz) ==>
      mem_bytes_at off len u.vs_memory = mem_bytes_at off len t.vs_memory)) /\
  (!pa pk. prot pa pk ==> pa + pk <= s0.vs_alloca_next /\
    mem_bytes_at pa pk s0.vs_memory = mem_bytes_at pa pk M /\
    !i b n. FLOOKUP s0.vs_allocas i = SOME (b,n) ==>
      loweringStateRelDefs$regions_disjoint pa pk b n) /\
  (!e ee sm sn t ef r vv u n.
    vv_post ctx func cenv cx e ee sm sn t ef r vv u /\
    ~expr_has_effect e /\ gas_marked_path F ctx func t n (OK u) /\
    (!pa pk. prot pa pk ==> pa + pk <= t.vs_alloca_next /\
      mem_bytes_at pa pk t.vs_memory = mem_bytes_at pa pk M /\
      !i b len. FLOOKUP t.vs_allocas i = SOME (b,len) ==>
        loweringStateRelDefs$regions_disjoint pa pk b len) ==>
    (!pa pk. prot pa pk ==> pa + pk <= u.vs_alloca_next /\
      mem_bytes_at pa pk u.vs_memory = mem_bytes_at pa pk M /\
      !i b len. FLOOKUP u.vs_allocas i = SOME (b,len) ==>
        loweringStateRelDefs$regions_disjoint pa pk b len)) /\
  (!v ee t.
    extrequest_kwarg_post ctx func cenv cx env ret kw e es sa s0 sb op dty
      old_es old_rs old_vvs v ee t /\
    extrequest_history_frame cenv cx (es with gas_obs := []) sa s0 ee sb t /\
    extrequest_retained_value cenv cx
      (if kw = EKDefault then dty else BaseT (UintT 256)) v op ee sb t /\
    (?used. !tail. (bind (eval_expr cx e) (read_result cx))
       (es with gas_obs := used ++ tail) = (INL v, ee with gas_obs := tail)) /\
    (!pa pk. prot pa pk ==> pa + pk <= t.vs_alloca_next /\
      mem_bytes_at pa pk t.vs_memory = mem_bytes_at pa pk M /\
      !i b n. FLOOKUP t.vs_allocas i = SOME (b,n) ==>
        loweringStateRelDefs$regions_disjoint pa pk b n) ==>
    gas_outcome F (cx_tops cx) (ctx,func) (kont v) (ee,t) Q
      (\res ee r. expr_exit res r)) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (bind (eval_expr cx e) (read_result cx)) kont) (es,s0) Q
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  qpat_x_assum `!e ee sm sn t ef r vv u n. _` (mk_asm "raw_frame") >>
  qpat_x_assum `!v ee t. _` (mk_asm "continuation") >>
  `?vv sm.
    compile_expr cenv (expr_type e) e sa = (vv,sm) /\
    (if kw = EKDefault /\ ~is_word_type ret then
       compile_materialize_vv cenv (lowered_value_type cenv e) vv sm = (op,sb)
     else unwrap_value cenv vv sm = (op,sb))` by
    (qpat_assum `compile_ext_call_kwarg _ _ _ _ _ _ = _` mp_tac >>
     qpat_assum `expr_type e = _` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     Cases_on `kw` >> Cases_on `is_word_type ret` >>
     simp[compile_ext_call_kwarg_def, lower_value_def, ext_call_kw_type_def,
          comp_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
     metis_tac[pairTheory.PAIR]) >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    (irule extrequest_results_head_admissible >>
     reverse conj_tac >- (qexistsl [`cenv`, `env`] >> simp[]) >>
     qexistsl [`[]`, `\rs. bind (read_result cx (HD rs)) kont`] >>
     fs[extrequest_results_cps_cons, Once evaluate_def, bind_return, bind_assoc]) >>
  `ci_mono sa sm` by
    (mp_tac (Q.SPECL [`cenv`, `expr_type e`, `e`, `sa`]
       (cj 1 compile_expr_ci_mono)) >> simp[]) >>
  suspend "raw_setup"
QED

Resume extcall_protframe_kwarg_retained_cps[raw_setup]:
  `ci_mono sm sb` by
    (qpat_assum `if _ then _ else _` mp_tac >> rpt (pop_assum kall_tac) >>
     Cases_on `kw = EKDefault /\ ~is_word_type ret` >> simp[] >>
     metis_tac[ci_mono_compile_materialize_vv, ci_mono_unwrap_value, SND]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (irule fn_has_code_split >> metis_tac[ci_mono_def]) >>
  `local_ptrs_reserved cenv sm` by (drule_all compiler_ci_mono_reserved >> simp[]) >>
  `expr_vv_sim ctx func cenv cx (expr_type e) e es` by
    (metis_tac[expr_vv_case_def]) >>
  `gas_outcome F (cx_tops cx) (ctx,func) (eval_expr cx e) (es,s0)
    (\res ee t. ?r. res = INL r /\
      vv_post ctx func cenv cx e es sa sm s0 ee r vv t /\
      t.vs_current_bb = sm.cs_current_bb /\
      t.vs_inst_idx = LENGTH sm.cs_current_insts)
    (\res ee r. expr_exit res r)` by
    (metis_tac[expr_vv_sim_def]) >>
  rewrite_tac[bind_assoc] >>
  drule (INST_TYPE [alpha |-> ``:eval_result``] extrequest_outcome_bind_result) >>
  disch_then (qspecl_then
    [`\r. bind (read_result cx r) kont`, `\res ee r. expr_exit res r`, `Q`] mp_tac) >>
  disch_then irule >> reverse conj_tac
  >- (rpt gen_tac >> Cases_on `rr` >> simp[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> gvs[] >> suspend "raw_landing"
QED

Resume extcall_protframe_kwarg_retained_cps[raw_landing]:
  `!tail. eval_expr cx e
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
     (INL r, mid with gas_obs := tail)` by gvs[gas_marked_exec_def] >>
  `!pa pk. prot pa pk ==> pa + pk <= t.vs_alloca_next /\
    mem_bytes_at pa pk t.vs_memory = mem_bytes_at pa pk M /\
    !i b n. FLOOKUP t.vs_allocas i = SOME (b,n) ==>
      loweringStateRelDefs$regions_disjoint pa pk b n` by
    (`gas_marked_path F ctx func s0 (LENGTH marks) (OK t)` by
       (gvs[gas_marked_exec_def]) >>
     asm "raw_frame" (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     disch_then (qspec_then `LENGTH marks` mp_tac) >>
     metis_tac[]) >>
  `~t.vs_halted` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [gas_marked_exec_def, gas_marked_path_def]) >>
     drule fragGasPathTheory.gas_path_normal >> simp[]) >>
  `stmt_state_rel ctx func cenv cx (mid with gas_obs := []) t /\
   vv_post ctx func cenv cx e (es with gas_obs := []) sa sm s0
     (mid with gas_obs := []) r vv t /\
   extrequest_read_frame cx (es with gas_obs := []) (mid with gas_obs := []) /\
   wb_frame cenv es mid sa s0 t /\
   extrequest_strong_capture ctx func cenv cx e r vv (mid with gas_obs := []) sm t /\
   extrequest_strong_captures ctx func cenv cx old_es old_rs old_vvs
     (mid with gas_obs := []) sm t` by
    (irule extcall_protframe_unread_head >>
     qpat_assum `vv_post _ _ _ _ e es _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `extrequest_strong_captures _ _ _ _ _ _ _ _ sa s0` (irule_at Any) >>
     qexistsl [`gas_explicit marks s0.vs_gas_readings`, `env`] >> simp[] >>
     qpat_assum `!e ee sm sn t ef r vv u. _` (drule_all_then strip_assume_tac) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     rpt strip_tac >> gvs[] >>
     qpat_x_assum `!e ee sm sn t ef r u ty p w tv. _`
       (drule_all_then strip_assume_tac) >> simp[]) >>
  suspend "suffix_prepare"
QED

Resume extcall_protframe_kwarg_retained_cps[suffix_prepare]:
  `!tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
         ~is_word_type (expr_type e) ==>
         type_memory_bytes cenv (expr_type e) = type_memory_size tv /\
         type_memory_size tv < 2**64` by
    (rpt strip_tac >>
     `type_memory_bytes cenv (expr_type e) = type_memory_size tv` by
       (irule typed_copy_memory_size >> qexists `get_tenv cx` >> simp[] >>
        qpat_assum `expr_body_pre _ _ _ e es` mp_tac >>
        simp[NoAsms, expr_body_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
     simp[] >> `alloc_limits_expr cenv e` by fs[expr_body_pre_def] >>
     drule alloc_limits_expr_type_alloc_ok >> simp[type_alloc_ok_def]) >>
  reverse (Cases_on `kw = EKDefault /\ ~is_word_type ret`)
  >- (gvs[] >>
      qpat_x_assum `extrequest_strong_capture _ _ _ _ e r vv _ sm t`
        (strip_assume_tac o REWRITE_RULE [extrequest_strong_capture_def]) >>
      drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)
        (SRULE [] extcall_joint_unwrap_read_protected) >>
      disch_then (qspecl_then [`t`, `sm`, `sb`, `prot`, `op`, `mid with gas_obs := []`, `M`] mp_tac) >>
      simp[] >> (impl_tac >- metis_tac[]) >> strip_tac >>
      suspend "unwrap_post") >>
  suspend "materialize_prepare"
QED

Resume extcall_protframe_kwarg_retained_cps[materialize_prepare]:
  gvs[] >>
  `expr_type e = ret` by fs[ext_call_kw_type_def] >>
  `dty = lowered_value_type cenv e` by
    (qpat_x_assum `compile_ext_call_kwarg _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_ext_call_kwarg_def, LET_THM, comp_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> gvs[]) >> metis_tac[]) >>
  `?v. read_result cx r (mid with gas_obs := []) =
    (INL v,mid with gas_obs := [])` by metis_tac[vv_post_materialises] >>
  `(bind (eval_expr cx e) (read_result cx))
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v,mid with gas_obs := [])` by
    (qpat_assum `!tail. eval_expr _ _ _ = _`
       (qspec_then `[]` assume_tac) >> fs[bind_def]) >>
  `expr_body_pre cenv cx env e
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  `(do r <- eval_expr cx e; read_result cx r od)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v,mid with gas_obs := [])` by
    (qpat_assum `!tail. eval_expr _ _ _ = _`
       (qspec_then `[]` assume_tac) >> fs[bind_def]) >>
  drule_all extcall_default_read_prepare >> strip_tac >>
  `!v' src z. read_result cx r (mid with gas_obs := []) =
      (INL v',mid with gas_obs := []) /\ expr_val_rel cx (expr_type e) v' src z ==>
    value_has_type dtv v' /\ val_wf dtv v' /\
    expr_val_rel cx (lowered_value_type cenv e) v' src z` by
    (rpt strip_tac >> `v' = v` by metis_tac[sumTheory.INL_11, pairTheory.PAIR_EQ] >>
     simp[] >> metis_tac[]) >>
  qpat_x_assum `extrequest_strong_capture _ _ _ _ e r vv _ sm t`
    (strip_assume_tac o REWRITE_RULE [extrequest_strong_capture_def]) >>
  drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)
    (SRULE [] extcall_materialize_read_protected) >>
  disch_then (qspecl_then [`t`, `sm`, `sb`, `prot`,
    `mid with gas_obs := []`, `lowered_value_type cenv e`, `dtv`, `op`, `M`] mp_tac) >>
  simp[] >> (impl_tac >- metis_tac[]) >> strip_tac >>
  suspend "materialize_post"
QED

Resume extcall_protframe_kwarg_retained_cps[unwrap_post]:
  `dty = ret` by
    (qpat_x_assum `compile_ext_call_kwarg _ _ _ _ _ _ = _` mp_tac >>
     Cases_on `kw` >> fs[compile_ext_call_kwarg_def, lower_value_def,
       comp_bind_def, comp_return_def, ext_call_kw_type_def]) >>
  `is_word_type (expr_type e) /\
   (if kw = EKDefault then dty else BaseT (UintT 256)) = expr_type e` by
    (Cases_on `kw` >> fs[ext_call_kw_type_def, is_word_type_def]) >>
  `read_result cx r (mid with gas_obs := []) =
    (INL v,mid with gas_obs := [])` by
    (qpat_assum `gas_marked_exec _ _ (read_result _ _) _ _ _ _ _` mp_tac >>
     simp[NoAsms, gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `(do r <- eval_expr cx e; read_result cx r od)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v,mid with gas_obs := [])` by
    (qpat_assum `!tail. eval_expr _ _ _ = _`
       (qspec_then `[]` assume_tac) >> fs[bind_def]) >>
  `expr_body_pre cenv cx env e
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
  drule_all extcall_read_runtime_prepare >> strip_tac >>
  `safe_operand sb op` by
    (irule unwrap_value_safe_operand >> goal_assum (drule_at Any) >>
     Cases_on `vv` >> fs[word_result_ok_def]
     >- (irule safe_operand_mono >> qexists `sc` >>
         fs[extrequest_history_frame_def]) >>
     rename1 `LocatedValue tag p` >>
     Cases_on `p.ptr_location = LocMemory`
     >- (simp[] >> disj2_tac >> irule safe_operand_mono >> qexists `sc` >>
         fs[extrequest_history_frame_def]) >>
     `tag = expr_type e` by fs[vv_post_def, vv_holds_def] >>
     gvs[safe_operand_mono]) >>
  `~u.vs_halted` by
    (qpat_assum `gas_marked_exec _ _ (read_result _ _) _ _ _ _ _` mp_tac >>
     simp[NoAsms,gas_marked_exec_def,gas_marked_path_def] >>
     metis_tac[gas_path_normal]) >>
  suspend "unwrap_finish"
QED

Resume extcall_protframe_kwarg_retained_cps[unwrap_finish]:
  `extrequest_kwarg_post ctx func cenv cx env ret kw e es sa s0 sb op dty
    old_es old_rs old_vvs v (mid with gas_obs := []) u` by
    (irule extrequest_kwarg_suffix_post >>
     goal_assum (drule_at Any) >> simp[] >>
     fs[expr_post_def, extrequest_read_frame_def] >>
     conj_tac >- (qexists `tv` >> metis_tac[]) >>
     conj_tac >- (Cases_on `kw = EKDefault` >> fs[ext_call_kw_type_def]) >>
     conj_tac >- (strip_tac >> qexists `tv` >> fs[ext_call_kw_type_def] >> metis_tac[]) >>
     conj_tac >- metis_tac[] >>
     qexistsl_tac [`r`, `sm`, `t`, `gas_explicit marks s0.vs_gas_readings`, `vv`] >>
     simp[] >> metis_tac[]) >>
  `extrequest_history_frame cenv cx (es with gas_obs := []) sa s0
     (mid with gas_obs := []) sb u` by
    (irule extrequest_history_frame_trans >>
     conj_tac >- (qexistsl_tac [`ctx`, `func`] >> simp[]) >>
     qexistsl_tac [`mid with gas_obs := []`, `sm`, `t`] >> simp[] >>
     irule extrequest_history_frame_extend >>
     qpat_assum `vv_post _ _ _ _ e (es with gas_obs := []) sa sm s0 _ _ _ t`
       (irule_at Any) >> simp[extrequest_history_frame_refl] >>
     qpat_assum `!e ee sm sn t ef r vv u. _` mp_tac >>
     disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     simp[] >> metis_tac[ci_mono_def]) >>
  `extrequest_retained_value cenv cx
     (if kw = EKDefault then dty else BaseT (UintT 256)) v op
     (mid with gas_obs := []) sb u` by
    (simp[extrequest_retained_value_def] >> fs[expr_post_def] >>
     metis_tac[]) >>
  irule extrequest_kwarg_suffix_cps >> simp[] >>
  qexistsl_tac [`v`, `u`] >> simp[] >>
  asm "continuation" irule >> simp[] >>
  conj_tac >- metis_tac[] >>
  qexists `gas_explicit marks s0.vs_gas_readings` >>
  irule extrequest_kwarg_counted_read >>
  goal_assum (drule_at Any) >> simp[]
QED

Resume extcall_protframe_kwarg_retained_cps[materialize_post]:
  markerLib.RESUME_TAC >> (
  `v' = v` by
    (qpat_assum `gas_marked_exec _ _ (read_result _ _) _ _ _ _ _` mp_tac >>
     simp[NoAsms,gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  gvs[] >>
  `extrequest_kwarg_post ctx func cenv cx env (expr_type e) EKDefault e es sa s0 sb op
    (lowered_value_type cenv e) old_es old_rs old_vvs v (mid with gas_obs := []) z` by
    (irule extrequest_kwarg_suffix_post >> goal_assum (drule_at Any) >>
     simp[ext_call_kw_type_def] >> fs[extrequest_read_frame_def] >>
     metis_tac[]) >>
  `extrequest_history_frame cenv cx (es with gas_obs := []) sa s0
     (mid with gas_obs := []) sb z` by
    (irule extrequest_history_frame_trans >>
     conj_tac >- (qexistsl_tac [`ctx`, `func`] >> simp[]) >>
     qexistsl_tac [`mid with gas_obs := []`, `sm`, `t`] >> simp[] >>
     irule extrequest_history_frame_extend >>
     qpat_assum `vv_post _ _ _ _ e (es with gas_obs := []) sa sm s0 _ _ _ t`
       (irule_at Any) >> simp[extrequest_history_frame_refl] >>
     qpat_assum `!e ee sm sn t ef r vv u. _` mp_tac >>
     disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     simp[] >> metis_tac[ci_mono_def]) >>
  `extrequest_retained_value cenv cx (lowered_value_type cenv e) v op
     (mid with gas_obs := []) sb z` by
    (simp[extrequest_retained_value_def] >>
     qexistsl_tac [`sm.cs_next_id`, `type_memory_bytes cenv (lowered_value_type cenv e)`] >>
     conj_tac >-
       (qpat_assum `compile_materialize_vv _ _ _ _ = _` mp_tac >>
        simp[NoAsms, compile_materialize_vv_def, comp_bind_def, comp_return_def] >>
        rpt (pairarg_tac >> gvs[]) >> strip_tac >>
        drule loweringHaltTheory.compile_alloc_buffer_parts >> strip_tac >>
        rename1 `unwrap_value cenv vv ca = (src,cu)` >>
        `ci_mono ca cu` by metis_tac[ci_mono_unwrap_value, SND] >>
        qpat_x_assum `do compile_store_memory _ _ _ _ _; _ od _ = _` mp_tac >>
        simp[NoAsms, comp_ignore_bind_def, comp_bind_def, comp_return_def] >>
        pairarg_tac >> gvs[] >> strip_tac >>
        `ci_mono cu sb` by metis_tac[ci_mono_compile_store_memory, SND] >>
        fs[ci_mono_def]) >>
     simp[] >> conj_tac >- (irule val_footprint_le >> simp[]) >>
     gvs[] >> metis_tac[]) >>
  irule extrequest_kwarg_suffix_cps >> simp[] >>
  qexistsl_tac [`v`, `z`] >> simp[] >>
  gvs[] >> asm "continuation" irule >> simp[] >>
  conj_tac >- metis_tac[] >>
  qexists `gas_explicit marks s0.vs_gas_readings` >>
  irule extrequest_kwarg_counted_read >> goal_assum (drule_at Any) >> simp[] )
QED

Finalise extcall_protframe_kwarg_retained_cps

Theorem extcall_protframe_kwargs_cps:
  !ks xs es sa sb value_op gas_op default_op s0 kont old_es old_rs old_vvs.
  LENGTH xs = LENGTH ks /\ exprs_case nocalls ctx func cenv cx xs /\
  EVERY2 (\kw e. expr_type e = ext_call_kw_type ret kw /\
    (kw = EKDefault ==> ret <> NoneT)) ks xs /\
  EVERY (\e. ~expr_has_effect e) xs /\
  EVERY (\e. nocalls ==> int_calls_expr e = []) xs /\
  (!i ee. i < LENGTH xs /\ extrequest_kwargs_reach cx xs es i ee ==>
    expr_body_pre cenv cx env (EL i xs) ee) /\
  compile_ext_call_kwargs compile_expr cenv ret ks xs sa =
    ((value_op,gas_op,default_op),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  gas_admissible (bind (eval_exprs cx xs) kont) expr_vv_res_ok es /\
  extrequest_strong_captures ctx func cenv cx old_es old_rs old_vvs
    (es with gas_obs := []) sa s0 /\
  (!e ee sm sn t ef r vv u ty p w tv.
    vv_post ctx func cenv cx e ee sm sn t ef r vv u /\
    ~expr_has_effect e /\ vv = LocatedValue ty p /\
    eval_operand p.ptr_operand u = SOME w /\
    evaluate_type (get_tenv cx) ty = SOME tv ==>
    (p.ptr_location = LocStorage ==>
      storage_read_live cx F (get_storage cx ef F) w tv) /\
    (p.ptr_location = LocTransient ==>
      storage_read_live cx T (get_storage cx ef T) w tv)) /\
  (!e ee sm sn t ef r vv u.
    vv_post ctx func cenv cx e ee sm sn t ef r vv u /\
    ~expr_has_effect e ==>
    (!n b sz. local_region cenv ee.scopes t n b sz ==>
      mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz t.vs_memory) /\
    (!off len.
      (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
        sm.cs_next_id <= inst.inst_id /\
        FLOOKUP u.vs_allocas inst.inst_id = SOME (b,sz) ==>
        loweringStateRelDefs$regions_disjoint off len b sz) ==>
      mem_bytes_at off len u.vs_memory = mem_bytes_at off len t.vs_memory)) /\
  (!e ee sm sn t ef r vv u n.
    vv_post ctx func cenv cx e ee sm sn t ef r vv u /\ ~expr_has_effect e /\
    gas_marked_path F ctx func t n (OK u) /\
    (!pa pk. prot pa pk ==> pa + pk <= t.vs_alloca_next /\
      mem_bytes_at pa pk t.vs_memory = mem_bytes_at pa pk M /\
      !i b len. FLOOKUP t.vs_allocas i = SOME (b,len) ==>
        loweringStateRelDefs$regions_disjoint pa pk b len) ==>
    !pa pk. prot pa pk ==> pa + pk <= u.vs_alloca_next /\
      mem_bytes_at pa pk u.vs_memory = mem_bytes_at pa pk M /\
      !i b len. FLOOKUP u.vs_allocas i = SOME (b,len) ==>
        loweringStateRelDefs$regions_disjoint pa pk b len) /\
  (!pa pk. prot pa pk ==> pa + pk <= s0.vs_alloca_next /\
    mem_bytes_at pa pk s0.vs_memory = mem_bytes_at pa pk M /\
    !i b len. FLOOKUP s0.vs_allocas i = SOME (b,len) ==>
      loweringStateRelDefs$regions_disjoint pa pk b len) /\
  (!vs ee t.
    extrequest_kwargs_post ctx func cenv cx ret ks xs es sa s0 sb
      value_op gas_op default_op old_es old_rs old_vvs vs ee t /\
    (!pa pk. prot pa pk ==> pa + pk <= t.vs_alloca_next /\
      mem_bytes_at pa pk t.vs_memory = mem_bytes_at pa pk M /\
      !i b len. FLOOKUP t.vs_allocas i = SOME (b,len) ==>
        loweringStateRelDefs$regions_disjoint pa pk b len) ==>
    gas_outcome F (cx_tops cx) (ctx,func) (kont vs) (ee,t) Q
      (\res ee r. expr_exit res r)) ==>
  gas_outcome F (cx_tops cx) (ctx,func) (bind (eval_exprs cx xs) kont)
    (es,s0) Q (\res ee r. expr_exit res r)
Proof
  Induct_on `ks` >> rpt gen_tac
  >- (Cases_on `xs` >> simp[compile_ext_call_kwargs_def, comp_return_def] >>
      rpt strip_tac >>
      qpat_x_assum `!e ee sm sn t ef r vv u n. _` kall_tac >>
      qpat_x_assum `!vs ee t. _` (mk_asm "nil_continuation") >> gvs[] >>
      `gas_outcome F (cx_tops cx) (ctx,func) (kont [])
        (es with gas_obs := [],s0) Q (\res ee r. expr_exit res r)` by
        (asm "nil_continuation" irule >> simp[] >>
         metis_tac[extrequest_kwargs_post_nil]) >>
      simp[Once evaluate_def, bind_return] >>
      qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
      rewrite_tac[gas_outcome_def] >> strip_tac
      >- (qexists `marks` >> disj1_tac >>
          gvs[gas_summary_at_def, gas_marked_exec_def] >> metis_tac[]) >>
      drule gas_exempt_cert_start_gas_obs >>
      disch_then (qspec_then `es.gas_obs` mp_tac) >> simp[] >> metis_tac[]) >>
  qpat_x_assum `!xs es sa sb value_op gas_op default_op s0 kont old_es old_rs old_vvs. _`
    (mk_asm "tail_ih") >>
  Cases_on `xs` >- simp[NoAsms] >>
  simp[NoAsms, Once compile_ext_call_kwargs_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >>
  qpat_x_assum `!e ee sm sn t ef r vv u n. _` (mk_asm "raw_frame") >>
  qpat_x_assum `!vs ee t. _` (mk_asm "continuation") >>
  rename1 `compile_ext_call_kwarg compile_expr cenv ret kw e sa = ((op,dty),sm)` >>
  rename1 `EVERY (\e. ~expr_has_effect e) xs` >>
  qpat_x_assum `comp_bind _ _ sm = _` mp_tac >>
  simp[comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[comp_return_def] >>
  rename1 `compile_ext_call_kwargs compile_expr cenv ret ks xs sm = ((vo,go,dopt),sb)` >>
  `ci_mono sa sm` by
    (mp_tac (Q.SPECL [`compile_expr`, `cenv`, `ret`, `kw`, `e`, `sa`]
      ci_mono_compile_ext_call_kwarg) >> simp[cj 1 compile_expr_ci_mono]) >>
  `ci_mono sm sb` by
    (mp_tac (Q.SPECL [`ks`, `xs`, `cenv`, `ret`, `sm`] extrequest_kwargs_mono) >> simp[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (irule fn_has_code_split >> fs[ci_mono_def]) >>
  `expr_body_pre cenv cx env e es` by
    (qpat_x_assum `!i ee. _` (qspecl_then [`0`, `es with gas_obs := []`] mp_tac) >> simp[]) >>
  `expr_vv_case nocalls ctx func cenv cx e` by fs[exprs_case_def] >>
  rewrite_tac[extrequest_kwargs_bind_cons] >>
  irule extcall_protframe_kwarg_retained_cps >>
  qpat_assum `compile_ext_call_kwarg _ _ _ _ _ _ = _` (irule_at Any) >> simp[] >>
  qpat_assum `extrequest_strong_captures _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qexistsl_tac [`prot`, `nocalls`, `env`, `M`] >>
  simp[GSYM extrequest_kwargs_bind_cons] >>
  suspend "head_continuation"
QED

Resume extcall_protframe_kwargs_cps[head_continuation]:
  conj_tac >- (asm "raw_frame" ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  rename1 `extrequest_kwarg_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ v mid tm` >>
  `mid.gas_obs = [] /\ stmt_state_rel ctx func cenv cx mid tm /\
   ~tm.vs_halted /\ tm.vs_current_bb = sm.cs_current_bb /\
   tm.vs_inst_idx = LENGTH sm.cs_current_insts /\ local_ptrs_reserved cenv sm /\
   extrequest_strong_captures ctx func cenv cx old_es old_rs old_vvs mid sm tm` by
    fs[extrequest_kwarg_post_def] >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  `gas_admissible (bind (eval_exprs cx xs) (\vs. kont (v::vs))) expr_vv_res_ok mid` by
    (qpat_assum `gas_admissible _ _ es` mp_tac >>
     rewrite_tac[extrequest_kwargs_bind_cons] >> strip_tac >>
     drule_all gas_admissible_bind_tail >> simp[]) >>
  `!i ee. i < LENGTH xs /\ extrequest_kwargs_reach cx xs mid i ee ==>
    expr_body_pre cenv cx env (EL i xs) ee` by
    (rpt strip_tac >>
     `extrequest_kwargs_reach cx (e::xs) es (SUC i) ee` by
       (irule extrequest_kwargs_reach_cons >> goal_assum (drule_at Any) >> simp[]) >>
     qpat_x_assum `!i ee. i < SUC _ /\ _ ==> _`
       (qspecl_then [`SUC i`, `ee`] mp_tac) >> simp[]) >>
  `exprs_case nocalls ctx func cenv cx xs` by
    (qpat_assum `exprs_case _ _ _ _ _ (e::xs)` mp_tac >>
     simp[NoAsms, exprs_case_def] >> strip_tac >> first_x_assum irule >>
     qpat_assum `!tail. bind (eval_expr cx e) _ _ = _` (qspec_then `[]` mp_tac) >>
     simp[NoAsms, bind_def, AllCaseEqs()] >> strip_tac >>
     goal_assum (drule_at Any) >> gvs[] >> goal_assum (drule_at Any)) >>
  asm "tail_ih" irule >>
  qpat_assum `compile_ext_call_kwargs _ _ _ _ _ _ = _` (irule_at Any) >>
  qexistsl_tac [`old_vvs`, `old_rs`, `old_es`] >> simp[] >>
  suspend "tail_continuation"
QED
Resume extcall_protframe_kwargs_cps[tail_continuation]:
  conj_tac >- (asm "raw_frame" ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  asm "continuation" irule >> simp[] >>
  drule_all extrequest_kwargs_post_cons >>
  Cases_on `kw` >> gvs[] >> metis_tac[]
QED
Finalise extcall_protframe_kwargs_cps
