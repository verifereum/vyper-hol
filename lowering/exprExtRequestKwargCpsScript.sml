(* One effect-free keyword: evaluate once, then read at the same source endpoint. *)
Theory exprExtRequestKwargCps
Ancestors
  exprExtRequestUnreadCps exprExtRequestMaterializeRead exprExtRequestJointUnwrap
  exprExtRequestDefaultProbe exprExtRequestShape exprExtRequestGasBind
  exprExtRequestStrongCapture exprExtRequestHistory exprExtRequestHistoryCompose
  exprExtRequestSourceFrame exprExtRequestReadProbe exprExtRequestOperandSafety
  exprSimHypsDefs exprSimHyps exprSimDefs exprSimProps exprOperandVar exprSafeOperand
  exprLowering exprLoweringProps loweringPosts compileEnv context freshWrites
  typedMemoryCopy allocLimits exprExtRequestKwargSuffix
  memoryLocalRhsProps valueEncodingTyping exprSimSource exprSimAggregateSource
  exprExtRequestTyping exprExtRequestRetained
  gasSummary gasSummaryCompose gasOutcome fragExec fragGasMode fragGasPath vyperCallOutcomeFrame
  vyperInterpreter vyperTypeSystem vyperState venomState list pair
Libs
  monadsyntax

Theorem extrequest_materialize_mono[local]:
  !cenv ty vv sa. ci_mono sa (SND (compile_materialize_vv cenv ty vv sa))
Proof
  rpt gen_tac >> rewrite_tac[compile_materialize_vv_def] >>
  ho_match_mp_tac ci_mono_bind >> conj_tac
  >- simp[ci_mono_compile_alloc_buffer] >>
  rpt strip_tac >>
  ho_match_mp_tac ci_mono_bind >> conj_tac >- simp[ci_mono_unwrap_value] >>
  rpt strip_tac >>
  ho_match_mp_tac ci_mono_ignore_bind >> conj_tac
  >- simp[ci_mono_compile_store_memory] >>
  simp[ci_mono_comp_return]
QED

Theorem extrequest_materialize_id[local]:
  compile_materialize_vv cenv ty vv sa = (op,sb) ==>
  sa.cs_next_id < sb.cs_next_id
Proof
  simp[compile_materialize_vv_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `unwrap_value cenv vv ca = (src,cb)` >>
  rename1 `compile_store_memory cenv src tmp.buf_operand ty ty cb = ((),cc)` >>
  drule loweringHaltTheory.compile_alloc_buffer_parts >> strip_tac >>
  `ci_mono ca cb` by metis_tac[ci_mono_unwrap_value, SND] >>
  `ci_mono cb cc` by metis_tac[ci_mono_compile_store_memory, SND] >>
  fs[ci_mono_def]
QED

Theorem extrequest_kwarg_retained_cps:
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
        compileEnv$regions_disjoint off len b sz) ==>
      mem_bytes_at off len u.vs_memory = mem_bytes_at off len t.vs_memory)) /\
  (!v ee t.
    extrequest_kwarg_post ctx func cenv cx env ret kw e es sa s0 sb op dty
      old_es old_rs old_vvs v ee t /\
    extrequest_history_frame cenv cx (es with gas_obs := []) sa s0 ee sb t /\
    extrequest_retained_value cenv cx
      (if kw = EKDefault then dty else BaseT (UintT 256)) v op ee sb t /\
    (?used. !tail. (bind (eval_expr cx e) (read_result cx))
       (es with gas_obs := used ++ tail) = (INL v, ee with gas_obs := tail)) ==>
    gas_outcome F (cx_tops cx) (ctx,func) (kont v) (ee,t) Q
      (\res ee r. expr_exit res r)) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (bind (eval_expr cx e) (read_result cx)) kont) (es,s0) Q
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `post_value_type cenv e = expr_type e` by
    (irule post_value_type_not_int_call >> metis_tac[expr_has_effect_thm]) >>
  `?vv sm.
    compile_expr cenv (expr_type e) e sa = (vv,sm) /\
    (if kw = EKDefault /\ ~is_word_type ret then
       compile_materialize_vv cenv (lowered_value_type cenv e) vv sm = (op,sb)
     else unwrap_value cenv vv sm = (op,sb))` by
    (qpat_x_assum `compile_ext_call_kwarg _ _ _ _ _ _ = _` mp_tac >>
     Cases_on `kw` >> Cases_on `is_word_type ret` >>
     simp[compile_ext_call_kwarg_def, lower_value_def, ext_call_kw_type_def,
          comp_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
     metis_tac[pairTheory.PAIR]) >>
  `gas_admissible (eval_expr cx e) expr_vv_res_ok es` by
    (irule extrequest_results_head_admissible >>
     reverse conj_tac >- (qexistsl_tac [`cenv`, `env`] >> simp[]) >>
     qexistsl_tac [`[]`, `\rs. bind (read_result cx (HD rs)) kont`] >>
     fs[extrequest_results_cps_cons, Once evaluate_def, bind_return,
          bind_assoc]) >>
  `ci_mono sa sm` by
    (mp_tac (Q.SPECL [`cenv`, `expr_type e`, `e`, `sa`]
       (cj 1 compile_expr_ci_mono)) >> simp[]) >>
  `ci_mono sm sb` by
    (Cases_on `kw = EKDefault /\ ~is_word_type ret` >> fs[]
     >- metis_tac[extrequest_materialize_mono, SND] >>
     metis_tac[ci_mono_unwrap_value, SND]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (irule fn_has_code_split >> gvs[ci_mono_def]) >>
  `local_ptrs_reserved cenv sm` by
    (drule_all compiler_ci_mono_reserved >> simp[]) >>
  `expr_vv_sim ctx func cenv cx (expr_type e) e es` by
    (gvs[expr_vv_case_def] >> first_x_assum irule >>
     qexists `env` >> simp[]) >>
  `gas_outcome F (cx_tops cx) (ctx,func) (eval_expr cx e) (es,s0)
    (\res ee t. ?r. res = INL r /\
      vv_post ctx func cenv cx e es sa sm s0 ee r vv t /\
      t.vs_current_bb = sm.cs_current_bb /\
      t.vs_inst_idx = LENGTH sm.cs_current_insts)
    (\res ee r. expr_exit res r)` by
    (gvs[expr_vv_sim_def] >> first_x_assum irule >> simp[]) >>
  rewrite_tac[bind_assoc] >>
  drule (INST_TYPE [alpha |-> ``:eval_result``]
    extrequest_outcome_bind_result) >>
  disch_then (qspecl_then
    [`\r. bind (read_result cx r) kont`,
     `\res ee r. expr_exit res r`, `Q`] mp_tac) >>
  disch_then irule >>
  reverse conj_tac
  >- (rpt gen_tac >> Cases_on `rr` >> simp[] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  `!tail. eval_expr cx e
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
     (INL r, mid with gas_obs := tail)` by gvs[gas_marked_exec_def] >>
  `!l. vv_operand vv <> Label l` by
    (irule (cj 1 extrequest_compiler_nonlabel) >>
     goal_assum (drule_at Any) >> qexists `env` >>
     qpat_assum `expr_body_pre _ _ _ e es` mp_tac >>
     simp[NoAsms, expr_body_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sm x` by
    metis_tac[CONJUNCT1 compiler_compile_var] >>
  `safe_operand sm (vv_operand vv)` by simp[safe_operand_def] >>
  `(case vv of StackValue ty op => safe_operand sm op
    | LocatedValue ty p => safe_operand sm p.ptr_operand)` by
    (Cases_on `vv` >> gvs[vv_operand_def]) >>
  `~t.vs_halted` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[NoAsms, gas_marked_exec_def, gas_marked_path_def] >> metis_tac[gas_path_normal]) >>
  `stmt_state_rel ctx func cenv cx (mid with gas_obs := []) t` by
    (qpat_assum `vv_post _ _ _ _ e _ _ _ _ _ _ _ _` mp_tac >>
     simp[NoAsms, vv_post_def] >> metis_tac[]) >>
  `extrequest_read_frame cx (es with gas_obs := [])
     (mid with gas_obs := [])` by
    (drule extrequest_pure_expr_read_frame >>
     rewrite_tac[state_rel_frame_result] >>
     disch_then (qspecl_then
       [`cx`, `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
        `INL r`, `mid with gas_obs := []`] mp_tac) >>
     qpat_assum `!tail. eval_expr _ _ _ = _`
       (qspec_then `[]` assume_tac) >> fs[extrequest_read_frame_def]) >>
  `vv_post ctx func cenv cx e (es with gas_obs := []) sa sm s0
     (mid with gas_obs := []) r vv t` by simp[vv_post_initial_gas] >>
  `extrequest_strong_captures ctx func cenv cx old_es old_rs old_vvs
     (mid with gas_obs := []) sm t` by
    (irule extrequest_strong_captures_extend >>
     qpat_assum `extrequest_strong_captures _ _ _ _ _ _ _ _ sa s0`
       (irule_at Any) >>
     qpat_assum `vv_post _ _ _ _ e (es with gas_obs := []) _ _ _ _ _ _ _`
       (irule_at Any) >> simp[] >>
     qpat_assum `!e ee sm sn t ef r vv u. _` (drule_all_then mp_tac) >>
     fs[ci_mono_def]) >>
  `extrequest_history_frame cenv cx (es with gas_obs := []) sa s0
     (es with gas_obs := []) sa s0` by simp[extrequest_history_frame_refl] >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) s0` by
    simp[] >>
  `extrequest_history_frame cenv cx (es with gas_obs := []) sa s0
     (mid with gas_obs := []) sm t` by
    (irule extrequest_history_frame_extend >>
     qpat_assum `vv_post _ _ _ _ e (es with gas_obs := []) _ _ _ _ _ _ _`
       (irule_at Any) >> simp[] >>
     qpat_assum `!e ee sm sn t ef r vv u. _` (drule_all_then mp_tac) >>
     fs[ci_mono_def]) >>
  `extrequest_history_frame cenv cx (mid with gas_obs := []) sm t
     (mid with gas_obs := []) sm t` by simp[extrequest_history_frame_refl] >>
  `!ty p tr w tv.
     vv = LocatedValue ty p /\ p.ptr_location = slot_loc tr /\
     eval_operand p.ptr_operand t = SOME w /\
     evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==>
     storage_read_live cx tr (get_storage cx (mid with gas_obs := []) tr) w tv` by
    (rpt strip_tac >>
     `p.ptr_location <> LocMemory` by
       (Cases_on `tr` >> fs[slot_loc_def]) >>
     `ty = expr_type e` by fs[vv_post_def, vv_holds_def] >>
     `vv_post ctx func cenv cx e es sa sm s0
        (mid with gas_obs := []) r (LocatedValue ty p) t` by metis_tac[] >>
     qpat_assum `!e ee sm sn t ef r u ty p w tv. _`
       (drule_then mp_tac) >>
     simp[] >> disch_then (qspec_then `tv` mp_tac) >>
     Cases_on `tr` >> gvs[slot_loc_def]) >>
  `!tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
         ~is_word_type (expr_type e) ==>
         type_memory_bytes cenv (expr_type e) = type_memory_size tv /\
         type_memory_size tv < 2**64` by
    (rpt strip_tac >>
     `type_memory_bytes cenv (expr_type e) = type_memory_size tv` by
       (irule typed_copy_memory_size >>
        qexists `get_tenv cx` >> simp[] >>
        qpat_assum `expr_body_pre _ _ _ e es` mp_tac >>
        simp[NoAsms, expr_body_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
     simp[] >>
     `alloc_limits_expr cenv e` by fs[expr_body_pre_def] >>
     drule alloc_limits_expr_type_alloc_ok >> simp[type_alloc_ok_def]) >>
  reverse (Cases_on `kw = EKDefault /\ ~is_word_type ret`)
  >- (`unwrap_value cenv vv sm = (op,sb)` by
       (qpat_assum `if _ then _ else _` mp_tac >>
        Cases_on `kw` >> gvs[]) >>
      `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id`
        by fs[ci_mono_def] >>
      drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)
        extrequest_joint_unwrap_read >> simp[] >>
      disch_then (qspecl_then [`t`, `sm`, `sb`, `op`, `mid with gas_obs := []`] mp_tac) >>
      simp[] >> strip_tac >>
      `dty = ret` by
        (qpat_assum `compile_ext_call_kwarg _ _ _ _ _ _ = _` mp_tac >>
         Cases_on `kw` >> fs[compile_ext_call_kwarg_def, lower_value_def,
           comp_bind_def, comp_return_def, ext_call_kw_type_def]) >>
      `read_result cx r (mid with gas_obs := []) =
         (INL v, mid with gas_obs := [])` by
        (qpat_assum `gas_marked_exec _ _ (read_result _ _) _ _ _ _ _` mp_tac >>
         simp[NoAsms, gas_marked_exec_def] >> strip_tac >>
         first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
      `(bind (eval_expr cx e) (read_result cx))
         (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
         (INL v, mid with gas_obs := [])` by
        (qpat_assum `!tail. eval_expr _ _ _ = _`
           (qspec_then `[]` assume_tac) >> fs[bind_def]) >>
      `value_runtime_typed env (expr_type e) v` by
        (irule memory_rhs_read_annotation_typed >>
         qexistsl_tac [`cenv`, `cx`,
           `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
           `mid with gas_obs := []`] >> simp[ETA_THM, bind_def] >>
         qpat_assum `!tail. eval_expr _ _ _ = _`
           (qspec_then `[]` strip_assume_tac) >> fs[]) >>
      `?tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
         value_has_type tv v /\ val_wf tv v` by
        (`expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
         drule_all memory_rhs_runtime_layout >> strip_tac >>
         metis_tac[value_has_type_val_wf]) >>
      `?used. !tail. (bind (eval_expr cx e) (read_result cx))
        (es with gas_obs := used ++ tail) =
        (INL v, mid with gas_obs := tail)` by
        (qexists `gas_explicit marks s0.vs_gas_readings` >>
         irule extrequest_kwarg_counted_read >>
         qpat_assum `gas_marked_exec _ _ (read_result _ _) _ _ _ _ _`
           (irule_at Any) >> simp[]) >>
      irule extrequest_kwarg_suffix_cps >> simp[] >>
      qexistsl_tac [`v`, `u`] >> simp[] >>
      first_x_assum irule >> simp[] >>
      (conj_tac >- (qexists `used` >> simp[])) >>
      once_rewrite_tac[CONJ_ASSOC] >> reverse conj_tac
      >- (irule extrequest_kwarg_suffix_post >>
      goal_assum (drule_at Any) >> simp[] >>
      `is_word_type (expr_type e) /\
       (if kw = EKDefault then ret else BaseT (UintT 256)) = expr_type e` by
        (Cases_on `kw` >> fs[ext_call_kw_type_def, is_word_type_def]) >>
      simp[] >>
      conj_tac >- (qexists `tv` >> metis_tac[]) >>
      conj_tac >- (fs[gas_marked_exec_def, gas_marked_path_def] >>
                     metis_tac[fragGasPathTheory.gas_path_normal]) >>
      conj_tac >- (strip_tac >> qexists `tv` >> fs[ext_call_kw_type_def]) >>
      conj_tac
      >- (irule unwrap_value_safe_operand >> goal_assum (drule_at Any) >>
          Cases_on `vv` >> fs[word_result_ok_def] >>
          rename1 `LocatedValue tag p` >>
          Cases_on `p.ptr_location = LocMemory` >- simp[] >>
          `tag = expr_type e` by fs[vv_post_def, vv_holds_def] >>
          gvs[]) >>
      conj_tac >- fs[extrequest_read_frame_def] >>
      conj_tac >- (fs[expr_post_def] >> metis_tac[]) >>
      conj_tac >- (fs[expr_post_def] >> metis_tac[]) >>
      qexistsl_tac [`r`, `sm`, `t`,
        `gas_explicit marks s0.vs_gas_readings`, `vv`] >> simp[]) >>
      suspend "word_history") >>
  gvs[] >>
  `expr_type e = ret` by fs[ext_call_kw_type_def] >>
  `dty = lowered_value_type cenv e` by
    (qpat_x_assum `compile_ext_call_kwarg _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_ext_call_kwarg_def, LET_THM, comp_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> gvs[]) >> metis_tac[]) >>
  `?v. read_result cx r (mid with gas_obs := []) =
       (INL v, mid with gas_obs := [])` by
    metis_tac[vv_post_materialises] >>
  `(bind (eval_expr cx e) (read_result cx))
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL v, mid with gas_obs := [])` by
    (qpat_assum `!tail. eval_expr _ _ _ = _`
       (qspec_then `[]` assume_tac) >> fs[bind_def]) >>
  `type_widens_to env.type_defs (expr_type e) ret` by
    fs[type_widens_to_def] >>
  `?dtv rtv.
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME dtv /\
    value_has_type dtv v /\ val_wf dtv v /\
    type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size dtv /\
    evaluate_type (get_tenv cx) ret = SOME rtv /\
    value_has_type rtv v /\ val_wf rtv v` by
    (irule extrequest_default_runtime_types >> simp[] >>
     qexistsl_tac [`mid with gas_obs := []`, `env`,
       `es with gas_obs := gas_explicit marks s0.vs_gas_readings`] >> simp[bind_def] >>
     qpat_assum `!tail. eval_expr _ _ _ = _`
       (qspec_then `[]` assume_tac) >> fs[]) >>
  `well_typed_expr env e` by fs[expr_body_pre_def] >>
  `lowered_value_type cenv e = ret \/
   is_bytestring_type (lowered_value_type cenv e) /\ is_bytestring_type ret` by
    (drule_all extrequest_lowered_type_compatible >> metis_tac[]) >>
  `~is_word_type (lowered_value_type cenv e)` by
    (Cases_on `lowered_value_type cenv e = ret` >- metis_tac[] >>
     `is_bytestring_type (lowered_value_type cenv e)` by metis_tac[] >>
     Cases_on `lowered_value_type cenv e` >>
     gvs[is_bytestring_type_def, is_word_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[is_bytestring_type_def, is_word_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     gvs[is_bytestring_type_def, is_word_type_def]) >>
  `type_memory_size dtv + 64 < dimword (:256)` by
    (drule_all extrequest_default_copy_capacity >> simp[]) >>
  `!v' src z. read_result cx r (mid with gas_obs := []) =
       (INL v',mid with gas_obs := []) /\
     expr_val_rel cx (expr_type e) v' src z ==>
     value_has_type dtv v' /\ val_wf dtv v' /\
     expr_val_rel cx (lowered_value_type cenv e) v' src z` by
    (rpt strip_tac >> `v' = v` by metis_tac[sumTheory.INL_11, pairTheory.PAIR_EQ] >>
     simp[] >>
     qpat_x_assum `expr_val_rel _ _ _ _ _` mp_tac >>
     simp[NoAsms, expr_val_rel_def] >> strip_tac >>
     `val_in_memory rtv v (w2n w) z.vs_memory` by metis_tac[] >>
     `?tv. evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv /\
       value_has_type tv v /\ val_wf tv v /\
       type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size tv /\
       val_in_memory tv v (w2n w) z.vs_memory` by
       (irule extrequest_default_lowered_memory >> simp[] >>
        qexistsl_tac [`mid with gas_obs := []`, `env`,
          `es with gas_obs := gas_explicit marks s0.vs_gas_readings`] >> simp[bind_def] >>
        qpat_assum `!tail. eval_expr _ _ _ = _`
          (qspec_then `[]` assume_tac) >> fs[]) >>
     simp[expr_val_rel_def] >> metis_tac[optionTheory.SOME_11]) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id`
    by fs[ci_mono_def] >>
  `?v' z w. gas_marked_exec F (ctx,func) (read_result cx r)
      (mid with gas_obs := [],t) [] (INL v') (mid with gas_obs := []) (OK z) /\
    stmt_state_rel ctx func cenv cx (mid with gas_obs := []) z /\
    extrequest_history_frame cenv cx (mid with gas_obs := []) sm t
      (mid with gas_obs := []) sb z /\
    ~z.vs_halted /\ z.vs_current_bb = sb.cs_current_bb /\
    z.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand op z = SOME w /\
    expr_val_rel cx (lowered_value_type cenv e) v' op z /\
    value_has_type dtv v' /\ val_wf dtv v' /\
    w2n w + val_footprint dtv v' <= z.vs_alloca_next /\
    FLOOKUP z.vs_allocas sm.cs_next_id =
      SOME (w2n w,type_memory_bytes cenv (lowered_value_type cenv e)) /\
    w2n w + type_memory_bytes cenv (lowered_value_type cenv e) < dimword (:256) /\
    safe_operand sb op /\
    (!aid b len. aid < sm.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,len) ==>
       regions_disjoint (w2n w) (type_memory_bytes cenv (lowered_value_type cenv e)) b len) /\
    (!name b len. local_region cenv (mid with gas_obs := []).scopes t name b len ==>
       regions_disjoint (w2n w) (type_memory_bytes cenv (lowered_value_type cenv e)) b len) /\
    (!name b len. local_region cenv (mid with gas_obs := []).scopes z name b len ==>
       regions_disjoint (w2n w) (type_memory_bytes cenv (lowered_value_type cenv e)) b len) /\
    (cenv.ce_is_ctor ==> !name tv v off.
       FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
       FLOOKUP (case ALOOKUP (mid with gas_obs := []).immutables cx.txn.target of
         NONE => FEMPTY | SOME imms => get_source_immutables cenv.ce_module imms)
         name = SOME (tv,v) ==>
       regions_disjoint (w2n w) (type_memory_bytes cenv (lowered_value_type cenv e))
         off (type_memory_size tv))` by
    (irule extrequest_materialize_read >>
     qpat_assum `compile_materialize_vv _ _ _ _ = _` (irule_at Any) >>
     simp[] >>
     qpat_assum `vv_post _ _ _ _ e es sa sm s0 _ r vv t` (irule_at Any) >>
     qpat_assum `extrequest_history_frame _ _ _ sm t _ sm t` (irule_at Any) >>
     simp[] >> rpt conj_tac >> rpt gen_tac >> rpt strip_tac >>
     fs[ext_call_kw_type_def] >> metis_tac[]) >>
  (`v' = v` by
    (qpat_assum `gas_marked_exec _ _ (read_result _ _) _ _ _ _ _` mp_tac >>
     simp[NoAsms, gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  qpat_x_assum `v' = v` SUBST_ALL_TAC >>
  `?used. !tail. (bind (eval_expr cx e) (read_result cx))
    (es with gas_obs := used ++ tail) =
    (INL v, mid with gas_obs := tail)` by
    (qexists `gas_explicit marks s0.vs_gas_readings` >>
     irule extrequest_kwarg_counted_read >>
     qpat_assum `gas_marked_exec _ _ (read_result _ _) _ _ _ _ _`
       (irule_at Any) >> simp[]) >>
  irule extrequest_kwarg_suffix_cps >> simp[] >>
  qexistsl_tac [`v`, `z`] >> simp[] >>
  first_x_assum irule >> simp[] >>
      (conj_tac >- (qexists `used` >> simp[])) >>
      once_rewrite_tac[CONJ_ASSOC] >> reverse conj_tac
  >- (irule extrequest_kwarg_suffix_post >>
  goal_assum (drule_at Any) >> simp[] >>
  gs[extrequest_read_frame_def] >>
  qexistsl_tac [`r`, `sm`, `t`,
    `gas_explicit marks s0.vs_gas_readings`, `vv`] >> simp[]) >>
  suspend "memory_history")
QED

Resume extrequest_kwarg_retained_cps[word_history]:
  conj_tac
  >- (irule extrequest_history_frame_trans >>
      conj_tac >- (qexistsl_tac [`ctx`, `func`] >> simp[]) >>
      qexistsl_tac [`mid with gas_obs := []`, `sm`, `t`] >> simp[]) >>
  `is_word_type (expr_type e) /\
   (if kw = EKDefault then dty else BaseT (UintT 256)) = expr_type e` by
    (Cases_on `kw` >> fs[ext_call_kw_type_def, is_word_type_def]) >>
  `safe_operand sb op` by
    (irule unwrap_value_safe_operand >> goal_assum (drule_at Any) >>
     Cases_on `vv` >> fs[word_result_ok_def] >>
     rename1 `LocatedValue tag p` >>
     Cases_on `p.ptr_location = LocMemory` >- simp[] >>
     `tag = expr_type e` by fs[vv_post_def, vv_holds_def] >>
     gvs[]) >>
  simp[extrequest_retained_value_def] >>
  conj_tac >- (gvs[expr_post_def]) >>
  qexists `tv` >> gvs[]
QED

Resume extrequest_kwarg_retained_cps[memory_history]:
  markerLib.RESUME_TAC >> (
  conj_tac
  >- (irule extrequest_history_frame_trans >>
      conj_tac >- (qexistsl_tac [`ctx`, `func`] >> simp[]) >>
      qexistsl_tac [`mid with gas_obs := []`, `sm`, `t`] >> simp[]) >>
  gvs[] >> simp[extrequest_retained_value_def] >>
  qexistsl_tac [`sm.cs_next_id`, `type_memory_bytes cenv (lowered_value_type cenv e)`] >>
  conj_tac >- (drule extrequest_materialize_id >> simp[]) >>
  simp[] >> conj_tac
  >- (drule val_footprint_le >> gvs[]) >>
  gvs[] >> metis_tac[])
QED

Finalise extrequest_kwarg_retained_cps


Theorem extrequest_kwarg_cps:
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
        compileEnv$regions_disjoint off len b sz) ==>
      mem_bytes_at off len u.vs_memory = mem_bytes_at off len t.vs_memory)) /\
  (!v ee t.
    extrequest_kwarg_post ctx func cenv cx env ret kw e es sa s0 sb op dty
      old_es old_rs old_vvs v ee t ==>
    gas_outcome F (cx_tops cx) (ctx,func) (kont v) (ee,t) Q
      (\res ee r. expr_exit res r)) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (bind (eval_expr cx e) (read_result cx)) kont) (es,s0) Q
    (\res ee r. expr_exit res r)
Proof
  strip_tac >> irule extrequest_kwarg_retained_cps >>
  qpat_assum `compile_ext_call_kwarg _ _ _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `expr_body_pre _ _ _ _ _` (irule_at Any) >>
  qpat_assum `extrequest_strong_captures _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `expr_vv_case _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!e ee sm sn t ef r vv u ty p w tv. _`
        (fn th => metis_tac[th])) >>
  first_assum ACCEPT_TAC
QED
