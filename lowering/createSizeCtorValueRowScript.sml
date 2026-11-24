Theory createSizeCtorValueRow
Ancestors
  gasShadowCompileBase
  abiEncoderProps e2eDefs exprSimFullBundleProps fragExec fragGasOrigin fragGasOriginPtr
  gasExplicitSites gasSummary s1PrefixDefs venomExecSemantics venomState vyperState relation
  list words createMarkedPath pair bodyFullIfExpReach arithmetic exprLowering
  stmtLoweringMono vfmConstants compileEnv exprLoweringProps exprSimSource vyperStorageTrace
  fragGasOriginPtrExec bodyMemoryDefs rich_list exprSimHypsDefs vyperTypeSystem exprSimHyps
  bodyPtrDefs loweringPosts context vyperAST vyperStorageFootprint vyperTyping vyperValue
  integer_word valueEncoding createCtorPrivateSnapshot createCtorSegmentArrival
  bodyFullExtCallPosList bodyFullExtCallPosAggregate abiEncodeArgsSim abiEncodeArgsCase
  exprSimMemorySource bodyFullHashKeccakFixed aggregateEvaluatedLayout
  exprSimIfExpWidenedPhysicalType exprSimSubscriptArrayCompose loweringStateRelDefs
  exprSimMemDefs ptrDiscipline bodySim createExprSizeExitDefs createSizePrefixReplay
  createSizeCopyReplay createSizeBlueprintKeywordReplay createSizeRawReplay

(* Visit the calls in the original suffix, while carrying their reached
   source states. The continuation is kept under its actual bind. *)
Theorem blueprint_ctor_source_walk:
  !n i p k.
    i + n = LENGTH es /\ P i p /\
    bind (eval_exprs cx (DROP i es)) k p = (res,out) /\
    (!vs. storage_trace_frame (k vs)) /\
    (!j q l. j < LENGTH es /\ P j q /\ (!v. storage_trace_frame (l v)) /\
       bind (bind (eval_expr cx (EL j es)) (read_result cx)) l q = (res,out) ==>
       (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
       ?v q'. bind (eval_expr cx (EL j es)) (read_result cx) q = (INL v,q') /\
              l v q' = (res,out) /\ P (SUC j) q') ==>
    (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
    ?vs E. E i = p /\ LENGTH vs = n /\
       eval_exprs cx (DROP i es) p = (INL vs,E (LENGTH es)) /\
       k vs (E (LENGTH es)) = (res,out) /\
       (!j. i <= j /\ j <= LENGTH es ==> P j (E j)) /\
       (!j. i <= j /\ j < LENGTH es ==>
         bind (eval_expr cx (EL j es)) (read_result cx) (E j) =
           (INL (EL (j-i) vs),E (SUC j)))
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >> gvs[cj 49 vyperInterpreterTheory.evaluate_def, bind_return] >>
      disj2_tac >> qexists_tac `\j. p` >> simp[return_def] >>
      metis_tac[LESS_EQUAL_ANTISYM]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `i < LENGTH es /\ SUC i + n = LENGTH es` by decide_tac >>
  `DROP i es = EL i es :: DROP (SUC i) es` by metis_tac[DROP_CONS_EL] >>
  qabbrev_tac `l = \v. bind (eval_exprs cx (DROP (SUC i) es)) (\vs. k (v::vs))` >>
  `!v. storage_trace_frame (l v)` by simp[Abbr `l`, blueprint_read_list_frame] >>
  `bind (bind (eval_expr cx (EL i es)) (read_result cx)) l p = (res,out)` by
    (qpat_x_assum `bind (eval_exprs cx (DROP i es)) k p = _` mp_tac >>
     simp[create_copy_source_cons, Abbr `l`]) >>
  first_assum (qspecl_then [`i`,`p`,`l`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >- metis_tac[] >>
  rename1 `l v q = (res,out)` >>
  first_x_assum (qspecl_then [`SUC i`,`q`,`\vs. k (v::vs)`] mp_tac) >>
  (impl_tac >- fs[Abbr `l`]) >> strip_tac >- metis_tac[] >>
  rename1 `E (SUC i) = q` >>
  disj2_tac >> qexistsl [`v::vs`,`\j. if j = i then p else E j`] >>
  simp[] >> rpt conj_tac
  >- (irule blueprint_eval_join_cons >> metis_tac[])
  >- gvs[]
  >- (rpt strip_tac >> Cases_on `j = i` >> simp[] >> first_assum irule >> decide_tac) >>
  rpt strip_tac >> Cases_on `j = i` >> gvs[] >>
  `?z. j-i = SUC z /\ j-SUC i = z` by (qexists_tac `j - SUC i` >> decide_tac) >>
  `SUC j <> i /\ SUC i <= j` by decide_tac >>
  qpat_assum `!j. SUC i <= j /\ j < LENGTH es ==> _` (qspec_then `j` mp_tac) >> simp[]
QED

(* Apply the completed-operand judgment to a source state that already
   carries the full residual stream, without changing the input of its post. *)
Theorem blueprint_ctor_complete:
  gas_completed_operand (DF,lo,explicit,ctx,func,PG)
    tops cx st0 a b source (p,s,G,tn) Q /\
  create_expr_prefix a b explicit ctx func s marks t /\
  t.vs_current_bb = b.cs_current_bb /\ t.vs_inst_idx = LENGTH b.cs_current_insts /\
  source p = (rr,q) /\ valid_horizon cx st0 H q.storage_trace /\
  p.gas_obs = gas_explicit marks s.vs_gas_readings ++ suffix ==>
  (?err. rr = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  ?G' tn'. q.gas_obs = suffix /\
    !h. valid_horizon cx st0 h q.storage_trace ==>
      gas_origin_ptr_path (DF h,lo,explicit,ctx,func,PG) (s,G,tn) marks (OK t,G',tn') /\
      Q h rr (q with gas_obs := []) G' tn' t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `p with gas_obs := gas_explicit marks s.vs_gas_readings ++ suffix = p` by
    (qpat_assum `p.gas_obs = _` (once_rewrite_tac o single o SYM) >> simp[]) >>
  qhdtm_x_assum `gas_completed_operand`
    (qspecl_then [`H`,`marks`,`t`,`suffix`,`rr`,`q`] mp_tac o
     REWRITE_RULE [gas_completed_operand_def]) >>
  asm_rewrite_tac[] >> metis_tac[]
QED

Theorem blueprint_ctor_segment_rtc:
  create_expr_prefix m b explicit ctx func mid snap t ==>
  RTC (\u r. (u.vs_current_bb,u.vs_inst_idx) <>
                (b.cs_current_bb,LENGTH b.cs_current_insts) /\
       ?i ms. ctor_segment_fetch func u = SOME i /\
              m.cs_next_id <= i.inst_id /\ i.inst_id < b.cs_next_id /\
              gas_origin_edge F explicit ctx func u ms (OK r)) mid t
Proof
  strip_tac >> drule_then irule create_expr_prefix_rtc_project >>
  simp[create_prefix_step_def, ctor_segment_fetch_def] >>
  rpt strip_tac >> fs[frag_ids_def] >> metis_tac[]
QED

(* The value-view post is at the expression cut, not at the private copy's
   return. Only the next row's entry uses the copy's new ghosts. *)
Theorem blueprint_ctor_vv_row_at:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shctx /\
  expr_body_pre ce cx env e p /\
  (expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG:(num # num) option list,func,shfunc)
     ce cx (expr_type e) e p (st0,a,m,sha,shm,vv,s,G,tn) ==>
   gas_completed_operand (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
     tops cx st0 a m (eval_expr cx e) (p,s,G,tn)
     (\H res ee G' tn' t. ?tv. res = INL tv /\
        vv_post H ctx func ce cx e p a m s ee tv vv t /\
        vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee tv vv t /\
        alloca_history func t /\
        (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
        s.vs_alloca_next <= t.vs_alloca_next /\
        ghost_inv_at (DF H) lo d ce cx ee G' tn' t /\
        ptr_vv_ok cx (post_value_type ce e) tv vv ee G' tn' t /\
        (!v. tv = Value v /\ ~is_word_type (post_value_type ce e) /\
           ~is_bytestring_type (post_value_type ce e) ==>
           vv_own ce cx (post_value_type ce e) a m ee tv vv t /\
           (!t' p. vv = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
        (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
         ?val. read_result cx tv ee = (INL val,ee) /\
           !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
             eval_operand (vv_operand vv) t = SOME w ==>
             w2n w + type_memory_size rt <= lo /\
             (!mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
                val_in_memory rt val (w2n w) mem)) /\
        (!tag op. vv = StackValue tag op /\ ~is_word_type (post_value_type ce e) ==>
           ptr_buf_ok ce e op G' t) /\
        (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
           ptr_buf_ok ce e p.ptr_operand G' t) /\
        ghost_kept_at lo ce p a G tn s G' tn')) /\
  ~is_word_type (lowered_value_type ce e) /\
  compile_expr ce (expr_type e) e a = (vv,m) /\
  compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) sha = (vv,shm) /\
  expr_sim_full_code (ctx,shctx,func,shfunc) (a,m,sha,shm) /\
  compile_snapshot_vv ce (exprs_can_mutate ce xs)
    (ext_call_arg_value (lowered_value_type ce e) vv) m = (saved,b) /\
  local_ptrs_reserved ce a /\ (!h. dead_lo_ok h (DF h) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  return_buf_frame d ce a s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!f i z. frag_reachable ctx func s f i z ==> dalloca_fmp_headroom i z) /\
  (!h. valid_horizon cx st0 h p.storage_trace ==>
     stmt_state_rel h ctx func ce cx p s /\ storage_well_formed_on cx p (FST h) /\
     ghost_inv_at (DF h) lo d ce cx p G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  create_expr_prefix a m (gas_explicit_sites ctx shctx) ctx func s chunk mid /\
  mid.vs_current_bb = m.cs_current_bb /\ mid.vs_inst_idx = LENGTH m.cs_current_insts /\
  create_expr_prefix m b (gas_explicit_sites ctx shctx) ctx func mid snap t /\
  t.vs_current_bb = b.cs_current_bb /\ t.vs_inst_idx = LENGTH b.cs_current_insts /\
  (exprs_can_mutate ce xs ==>
    fn_has_code m b func /\
    (?j. ctor_segment_fetch func t = SOME j /\ j.inst_opcode <> PHI /\
         b.cs_next_id <= j.inst_id) /\
    (gas_origin_path T (gas_explicit_sites ctx shctx) ctx func mid [] (OK t) ==> snap = [])) /\
  bind (eval_expr cx e) (read_result cx) p = (rr,q) /\
  valid_horizon cx st0 H q.storage_trace /\
  p.gas_obs = gas_explicit (chunk ++ (snap ++ rest)) s.vs_gas_readings ++ tail ==>
  (?err. rr = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  ?v raw Gm tm tv ann Gt tt.
    rr = INL v /\ eval_expr cx e p = (INL raw,q) /\ read_result cx raw q = (INL v,q) /\
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME ann /\
    arg_type_fits (lowered_value_type ce e) (expr_type e) /\
    value_has_type tv v /\ value_has_type ann v /\
    (!h. valid_horizon cx st0 h q.storage_trace ==>
       vv_post h ctx func ce cx e p a m s (q with gas_obs := []) raw vv mid /\
       vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e)
         (q with gas_obs := []) raw vv mid /\
       ptr_vv_ok cx (post_value_type ce e) raw vv (q with gas_obs := []) Gm tm mid /\
       alloca_history func mid /\ s.vs_alloca_next <= mid.vs_alloca_next /\
       ghost_inv_at (DF h) lo d ce cx (q with gas_obs := []) Gm tm mid /\
       ghost_kept_at lo ce p a G tn s Gm tm /\
       (!tag op. vv = StackValue tag op /\ ~is_word_type (post_value_type ce e) ==>
         ptr_buf_ok ce e op Gm mid) /\
       (!tag p0. vv = LocatedValue tag p0 /\ p0.ptr_location = LocMemory ==>
         ptr_buf_ok ce e p0.ptr_operand Gm mid) /\
       (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
         ?val. read_result cx raw (q with gas_obs := []) = (INL val,q with gas_obs := []) /\
           !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
             eval_operand (vv_operand vv) mid = SOME w ==>
             w2n w + type_memory_size rt <= lo /\
             (!mem. mem_agree_outside tm.t_mem mid.vs_memory mem ==>
                val_in_memory rt val (w2n w) mem))) /\
    q.gas_obs = gas_explicit rest t.vs_gas_readings ++ tail /\
    expr_sim_inv ce cx env q /\ return_buf_frame d ce b t /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!f i z. frag_reachable ctx func t f i z ==> dalloca_fmp_headroom i z) /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts /\
    (!h. valid_horizon cx st0 h q.storage_trace ==>
      stmt_state_rel h ctx func ce cx q t /\ storage_well_formed_on cx q (FST h) /\
      ghost_inv_at (DF h) lo d ce cx q Gt tt t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG:(num # num) option list,func,shfunc)
     ce cx (expr_type e) e p (st0,a,m,sha,shm,vv,s,G,tn)` by
    (fs[expr_vv_sim_full_pre_def, expr_sim_full_code_def] >>
     metis_tac[expr_body_pre_vv_gas_admissible]) >>
  qpat_x_assum `expr_vv_sim_full_pre _ _ _ _ _ _ _ ==> _`
    (drule_then assume_tac) >>
  Cases_on `eval_expr cx e p` >>
  qmatch_asmsub_rename_tac `eval_expr cx e p = (rv,rq)` >>
  `rq = q` by (Cases_on `rv` >> fs[bind_def] >> metis_tac[read_result_state]) >>
  qpat_x_assum `rq = q` SUBST_ALL_TAC >>
  `p.gas_obs = gas_explicit chunk s.vs_gas_readings ++
     (gas_explicit (snap ++ rest) mid.vs_gas_readings ++ tail)` by
    (qpat_assum `create_expr_prefix a m _ _ _ s chunk mid`
       (assume_tac o MATCH_MP create_prefix_readings) >>
     qpat_assum `p.gas_obs = gas_explicit (chunk ++ (snap ++ rest)) _ ++ _`
       (pure_once_rewrite_tac o single) >>
     CONV_TAC (LAND_CONV (LAND_CONV (REWR_CONV gas_explicit_append))) >>
     simp[APPEND_ASSOC]) >>
  drule_all blueprint_ctor_complete >> strip_tac
  >- (disj1_tac >> qexists_tac `err` >> fs[bind_def]) >>
  suspend "read"
QED

Resume blueprint_ctor_vv_row_at[read]:
  qpat_x_assum `!h. _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (assume_tac o BETA_RULE) >>
  qpat_assum `!h. _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  qpat_x_assum `rv = INL _` SUBST_ALL_TAC >>
  rename1 `eval_expr cx e p = (INL raw,q)` >>
  drule abi_args_vv_post_read >> strip_tac >>
  `read_result cx raw q = (INL v,q)` by
    (drule read_result_gas_obs >> disch_then (qspec_then `q.gas_obs` mp_tac) >>
     simp[IgnAsm `q.gas_obs = _`]) >>
  `rr = INL v` by fs[bind_def] >>
  qpat_x_assum `rr = INL v` SUBST_ALL_TAC >>
  disj2_tac >> qexistsl [`v`,`raw`,`G'`,`tn'`] >> simp[] >>
  `arg_type_fits (lowered_value_type ce e) (expr_type e)` by metis_tac[expr_body_pre_lowered_fits] >>
  `~is_word_type (expr_type e)` by metis_tac[arg_type_fits_word_type] >>
  drule_all (REWRITE_RULE [ETA_AX] abi_args_success_ready) >> simp[] >> strip_tac >>
  drule_all expr_body_pre_runtime_typed >> strip_tac >>
  rename1 `evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv` >>
  rename1 `evaluate_type (get_tenv cx) (expr_type e) = SOME ann` >>
  qexistsl [`tv`,`ann`] >> simp[] >>
  suspend "advance"
QED
Resume blueprint_ctor_vv_row_at[advance]:
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (fs[expr_sim_full_code_def] >> metis_tac[body_inv_no_phi]) >>
  `!f i z. frag_reachable ctx func mid f i z ==> dalloca_fmp_headroom i z` by
    (drule gas_origin_ptr_path_dalloca_fmp_headroom >> simp[] >> metis_tac[]) >>
  `~mid.vs_halted` by (drule gas_origin_ptr_path_exec >> simp[exit_result_def]) >>
  Cases_on `exprs_can_mutate ce xs`
  >- suspend "copy" >>
  suspend "retain"
QED
Resume blueprint_ctor_vv_row_at[retain]:
  `vv_type (ext_call_arg_value (lowered_value_type ce e) vv) = lowered_value_type ce e`
     by metis_tac[extcall_operand_snapshot_type] >>
  `b = m` by
    (qpat_x_assum `compile_snapshot_vv _ _ _ _ = _` mp_tac >>
     simp[compile_snapshot_vv_def,comp_return_def]) >>
  qpat_x_assum `b = m` SUBST_ALL_TAC >>
  drule_all create_copy_empty_cut >> strip_tac >>
  `a.cs_next_var <= m.cs_next_var` by
    metis_tac[ci_mono_compile_expr_sa,SND,ci_mono_def] >>
  `return_buf_frame d ce m mid` by
    (irule return_buf_frame_frame >>
     qexistsl [`ce`,`s`,`a`] >> fs[vv_post_def]) >>
  qexistsl [`G'`,`tn'`] >> gvs[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qx_gen_tac `h` >> disch_tac >>
  qpat_assum `!h. _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `h` (drule_then strip_assume_tac)) >>
  fs[vv_post_def] >> conj_tac
  >- (irule (iffLR storage_well_formed_on_backends) >>
      qexists_tac `q with gas_obs := []` >> simp[]) >>
  qpat_x_assum `ghost_inv_at (DF h) _ _ _ _ _ _ _ _` mp_tac >>
  simp_tac (srw_ss()) [ghost_inv_at_def,ghost_inv_def,local_region_def] >>
  strip_tac >> first_assum ACCEPT_TAC
QED
Resume blueprint_ctor_vv_row_at[copy]:
  qpat_x_assum `exprs_can_mutate ce xs ==> _` (drule_then strip_assume_tac) >>
  qpat_assum `create_expr_prefix m b _ _ _ mid snap t`
    (assume_tac o MATCH_MP blueprint_ctor_segment_rtc) >>
  `storage_trace_domain cx st0 q.storage_trace` by
    (qpat_assum `valid_horizon cx st0 H q.storage_trace`
       (ACCEPT_TAC o MATCH_MP bodyFullExtCallPackingReadyTheory.extcall_packing_observed_domain)) >>
  `!h. valid_horizon cx st0 h q.storage_trace ==>
    vv_post h ctx func ce cx e p a m s q raw vv mid /\
    ghost_inv_at (DF h) lo d ce cx q G' tn' mid` by
    (rpt strip_tac >>
     qpat_assum `!h. _ ==> gas_origin_ptr_path _ _ _ _ /\ _` (drule_then strip_assume_tac) >>
     gvs[vv_post_final_gas,ghost_inv_at_def,ghost_inv_def,local_region_def] >>
     first_assum ACCEPT_TAC) >>
  `vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) q raw vv mid /\
   ptr_vv_ok cx (post_value_type ce e) raw vv q G' tn' mid` by
    (qpat_assum `vv_store_bound _ _ _ _ _ _ _` mp_tac >>
     qpat_assum `ptr_vv_ok _ _ _ _ _ _ _ _` mp_tac >> Cases_on `vv` >>
     simp_tac (srw_ss()) [vv_store_bound_def, ptr_vv_ok_def, read_result_success_gas_iff] >>
     disch_then strip_assume_tac >> disch_then strip_assume_tac >>
     simp[]) >>
  `~is_word_type (post_value_type ce e)` by metis_tac[post_value_type_nonword] >>
  `!tag op. vv = StackValue tag op ==> ptr_buf_ok ce e op G' mid` by simp[] >>
  `compile_snapshot_vv ce T (ext_call_arg_value (lowered_value_type ce e) vv) m = (saved,b)` by fs[] >>
  `eval_expr cx e (p with gas_obs := p.gas_obs) = (INL raw,q)` by
    simp[IgnAsm `p.gas_obs = _`] >>
  `ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
     ?val. read_result cx raw q = (INL val,q) /\
       !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
         eval_operand (vv_operand vv) mid = SOME w ==>
         w2n w + type_memory_size rt <= lo /\
         (!mem. mem_agree_outside tn'.t_mem mid.vs_memory mem ==>
                val_in_memory rt val (w2n w) mem)` by fs[read_result_success_gas_iff] >>
  `fn_inst_ids_distinct func` by fs[expr_sim_full_code_def] >>
  drule_all (INST_TYPE [alpha |-> ``:exception``] ctor_private_snapshot_actual) >>
  disch_then (strip_assume_tac o SPEC_ALL) >>
  suspend "copied_entry"
QED
Resume blueprint_ctor_vv_row_at[copied_entry]:
  qmatch_asmsub_rename_tac `gas_origin_ptr_path _ (mid,G',tn') [] (OK t,Gout,tout)` >>
  qpat_assum `!h. _ ==> gas_origin_ptr_path _ (mid,_,_) [] _ /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  `snap = []` by
    (qpat_assum `gas_origin_ptr_path _ (mid,_,_) [] _`
       (strip_assume_tac o MATCH_MP gas_origin_ptr_path_projections) >>
     first_assum (drule_then ACCEPT_TAC)) >>
  `mid.vs_gas_readings = t.vs_gas_readings` by
    (qpat_assum `create_expr_prefix m b _ _ _ mid snap t`
       (mp_tac o MATCH_MP create_prefix_readings) >> simp[]) >>
  `!f i z. frag_reachable ctx func t f i z ==> dalloca_fmp_headroom i z` by
    (qpat_assum `gas_origin_ptr_path _ (mid,_,_) [] _` mp_tac >>
     qpat_assum `!f i z. frag_reachable ctx func mid f i z ==> _` mp_tac >>
     qpat_assum `!bb. MEM bb func.fn_blocks ==> _` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[gas_origin_ptr_path_dalloca_fmp_headroom]) >>
  `!h. valid_horizon cx st0 h q.storage_trace ==>
      stmt_state_rel h ctx func ce cx q t /\ storage_well_formed_on cx q (FST h) /\
      ghost_inv_at (DF h) lo d ce cx q Gout tout t /\ return_buf_frame d ce b t /\
      alloca_history func t /\ ~t.vs_halted` by
    (qx_gen_tac `h` >> disch_tac >>
     qpat_assum `!h. _ ==> gas_origin_ptr_path _ (mid,_,_) [] _ /\ _`
       (qspec_then `h` (drule_then strip_assume_tac)) >>
     qpat_x_assum `!kw. extcall_positional_post T _ _ _ _ _ _ _ _ kw [e] _ _ _ _ _ _ _ h _ q _ _ t`
       (qspec_then `[]` (strip_assume_tac o SIMP_RULE (srw_ss())
          [extcall_positional_post_def])) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `!h. _ ==> stmt_state_rel h _ _ _ _ _ t /\ _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    metis_tac[stmt_state_rel_allocas_below_fmp] >>
  qexistsl [`Gout`,`tout`] >> simp[] >> conj_tac
  >- (rpt gen_tac >> disch_tac >>
      qpat_assum `!h. _ ==> gas_origin_ptr_path _ (s,_,_) _ _ /\ _`
        (drule_then strip_assume_tac) >> gvs[]) >>
  first_assum ACCEPT_TAC
QED
Finalise blueprint_ctor_vv_row_at

Theorem blueprint_ctor_vv_row:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shctx /\
  expr_body_pre ce cx env e p /\ create_operand_completed_ok cx e /\
  ~is_word_type (lowered_value_type ce e) /\
  compile_expr ce (expr_type e) e a = (vv,m) /\
  compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) sha = (vv,shm) /\
  expr_sim_full_code (ctx,shctx,func,shfunc) (a,m,sha,shm) /\
  compile_snapshot_vv ce (exprs_can_mutate ce xs)
    (ext_call_arg_value (lowered_value_type ce e) vv) m = (saved,b) /\
  local_ptrs_reserved ce a /\ (!h. dead_lo_ok h (DF h) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  return_buf_frame d ce a s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!f i z. frag_reachable ctx func s f i z ==> dalloca_fmp_headroom i z) /\
  (!h. valid_horizon cx st0 h p.storage_trace ==>
     stmt_state_rel h ctx func ce cx p s /\ storage_well_formed_on cx p (FST h) /\
     ghost_inv_at (DF h) lo d ce cx p G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  create_expr_prefix a m (gas_explicit_sites ctx shctx) ctx func s chunk mid /\
  mid.vs_current_bb = m.cs_current_bb /\ mid.vs_inst_idx = LENGTH m.cs_current_insts /\
  create_expr_prefix m b (gas_explicit_sites ctx shctx) ctx func mid snap t /\
  t.vs_current_bb = b.cs_current_bb /\ t.vs_inst_idx = LENGTH b.cs_current_insts /\
  (exprs_can_mutate ce xs ==>
    fn_has_code m b func /\
    (?j. ctor_segment_fetch func t = SOME j /\ j.inst_opcode <> PHI /\
         b.cs_next_id <= j.inst_id) /\
    (gas_origin_path T (gas_explicit_sites ctx shctx) ctx func mid [] (OK t) ==> snap = [])) /\
  bind (eval_expr cx e) (read_result cx) p = (rr,q) /\
  valid_horizon cx st0 H q.storage_trace /\
  p.gas_obs = gas_explicit (chunk ++ (snap ++ rest)) s.vs_gas_readings ++ tail ==>
  (?err. rr = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  ?v raw Gm tm tv ann Gt tt.
    rr = INL v /\ eval_expr cx e p = (INL raw,q) /\ read_result cx raw q = (INL v,q) /\
    evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME ann /\
    arg_type_fits (lowered_value_type ce e) (expr_type e) /\
    value_has_type tv v /\ value_has_type ann v /\
    (!h. valid_horizon cx st0 h q.storage_trace ==>
       vv_post h ctx func ce cx e p a m s (q with gas_obs := []) raw vv mid /\
       vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e)
         (q with gas_obs := []) raw vv mid /\
       ptr_vv_ok cx (post_value_type ce e) raw vv (q with gas_obs := []) Gm tm mid /\
       alloca_history func mid /\ s.vs_alloca_next <= mid.vs_alloca_next /\
       ghost_inv_at (DF h) lo d ce cx (q with gas_obs := []) Gm tm mid /\
       ghost_kept_at lo ce p a G tn s Gm tm /\
       (!tag op. vv = StackValue tag op /\ ~is_word_type (post_value_type ce e) ==>
         ptr_buf_ok ce e op Gm mid) /\
       (!tag p0. vv = LocatedValue tag p0 /\ p0.ptr_location = LocMemory ==>
         ptr_buf_ok ce e p0.ptr_operand Gm mid) /\
       (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
         ?val. read_result cx raw (q with gas_obs := []) = (INL val,q with gas_obs := []) /\
           !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
             eval_operand (vv_operand vv) mid = SOME w ==>
             w2n w + type_memory_size rt <= lo /\
             (!mem. mem_agree_outside tm.t_mem mid.vs_memory mem ==>
                val_in_memory rt val (w2n w) mem))) /\
    q.gas_obs = gas_explicit rest t.vs_gas_readings ++ tail /\
    expr_sim_inv ce cx env q /\ return_buf_frame d ce b t /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!f i z. frag_reachable ctx func t f i z ==> dalloca_fmp_headroom i z) /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts /\
    (!h. valid_horizon cx st0 h q.storage_trace ==>
      stmt_state_rel h ctx func ce cx q t /\ storage_well_formed_on cx q (FST h) /\
      ghost_inv_at (DF h) lo d ce cx q Gt tt t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (SPEC_ALL blueprint_ctor_vv_row_at) >>
  (impl_tac >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
                strip_tac >> drule_all_then ACCEPT_TAC create_size_replay_vv_cut)) >>
  disch_then ACCEPT_TAC
QED
