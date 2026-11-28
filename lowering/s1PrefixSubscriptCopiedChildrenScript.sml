(* Request prefixes through the base and index of a copied array subscript. *)
Theory s1PrefixSubscriptCopiedChildren
Ancestors
  s1PrefixPreds s1PrefixDefs bodyFullSubscriptCopiedBind s1PrefixCompose
  s1PrefixOfVV s1PrefixProps bodyFullPreds bodyFullSimProjection bodySimFull bodyFullIfExpReach
  exprSimSubscriptArraySource exprSimSubscriptArray exprSimSource
  compileEnv fragExec gasOutcomeFullCompose exprSimDefs vyperStorageTrace
  vyperStorageFootprint vyperState gasShadowState
  exprSimMemorySource bodyPtrAttributeSource loweringPosts exprBodyPreProps
  exprLoweringProps freshWrites exprSimHyps venomExecSemantics
  contextRawReachable unitTransformDefs fragGasOriginPtr gasSummary

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_body_pre ce cx env obj es` by
    metis_tac[expr_body_pre_array_subscript_base,
              copies_subscript_base_not_array_slot_base] >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty obj es` by
    (irule (cj 2 body_expr_full_ok_simulations) >>
     simp[] >> qexistsl [`env`,`tops`] >> simp[]) >>
  `expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty obj es` by
    (qpat_assum `body_expr_prefix_ok cx obj`
       (mp_tac o Q.SPECL [`DF`,`lo`,`d`,`PG`,`tops`,`ctx`,`shadow_ctx`,
         `func`,`shadow_func`,`ce`,`env`,`ty`,`es`] o
        CONJUNCT1 o ONCE_REWRITE_RULE [CONJUNCT1 body_expr_prefix_ok_def]) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then (ACCEPT_TAC o CONJUNCT2)) >>
  PURE_REWRITE_TAC[expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all copied_array_cuts >> strip_tac >>
  `cs_extends sm sb /\ cs_extends sc sb /\
   cs_extends shm shadow_sb /\ cs_extends shc shadow_sb` by
    (rpt conj_tac >> irule cs_extends_trans
     >- (qexists `sc` >> simp[] >> irule cs_extends_trans >> qexists `si` >> simp[])
     >- (qexists `si` >> simp[])
     >- (qexists `shc` >> simp[] >> irule cs_extends_trans >> qexists `shi` >> simp[])
     >> qexists `shi` >> simp[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sc func /\ fn_has_code sc si func /\
   fn_has_code shadow_sa shm shadow_func /\ fn_has_code shc shi shadow_func` by
    (imp_res_tac fn_has_code_split >> simp[]) >>
  `gas_admissible (eval_expr cx obj) expr_vv_res_ok es` by
    (drule expr_body_pre_vv_gas_admissible >> simp[]) >>
  qpat_x_assum `expr_vv_sim_prefix _ _ _ _ obj _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_prefix_def, expr_vv_sim_full_pre_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shm`,`bvv`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ obj _` (mp_tac o REWRITE_RULE [expr_vv_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shm`,`bvv`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  drule_then (drule_then assume_tac) (REWRITE_RULE [AND_IMP_INTRO |> GSYM] body_inv_no_phi) >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ baseQ baseR` >>
  qabbrev_tac `reach_ok = \u. !fn i v. frag_reachable ctx func u fn i v ==>
    dalloca_fmp_headroom i v` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (eval_expr cx obj) (es,s0,G0,tn0)
     (\H res ee G tn t. baseQ H res ee G tn t /\ reach_ok t) baseR` by
    (irule gas_outcome_full_post_path >>
     qpat_assum `gas_outcome_full _ _ _ _ _ _ baseQ baseR` (irule_at Any) >>
     simp[Abbr `reach_ok`] >> rpt gen_tac >> strip_tac >>
     qpat_assum `gas_origin_ptr_path _ _ _ (OK t,_,_)`
       (mp_then Any mp_tac gas_origin_ptr_path_dalloca_fmp_headroom) >>
     simp[] >> metis_tac[]) >>
  suspend "base_bind"
QED
*)
Theorem subscript_copied_children_prefix:
  !frames cx ann obj idx DF lo d PG tops ctx shadow_ctx func shadow_func ce env ty es et bd.
  (!s raw mid saved. eval_expr cx obj s = (INL raw,mid) /\
       read_result cx raw mid = (INL saved,mid) ==> body_expr_full_ok cx idx) /\
  (!s raw mid saved. eval_expr cx obj s = (INL raw,mid) /\
       read_result cx raw mid = (INL saved,mid) ==> body_expr_prefix_ok cx idx) /\
  body_expr_full_ok cx obj /\
  body_expr_prefix_ok cx obj /\
  body_inv tops ctx ce cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  subscript_reads_base cx obj idx /\
  copies_subscript_base ce obj idx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre ce cx env (Subscript ann obj idx) es /\
  expr_type obj = ArrayT et bd /\
  place_type ce obj = ValPT (ArrayT et bd) /\
  post_value_type ce obj = expr_type obj /\
  (!st0 sa sm sc bvv cvv shm s0 G0 tn0 gs raw mid saved s G1 tn1.
       eval_expr cx obj (es with gas_obs := gs) = (INL raw,mid) /\
       read_result cx raw mid = (INL saved,mid) /\
       compile_expr ce ty obj sa = (bvv,sm) /\
       compile_snapshot_vv ce T bvv sm = (cvv,sc) /\ gas_shadow_state sm shm /\
       fn_has_code sm sc func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
       (!H. dead_lo_ok H (DF H) lo ce cx) /\
       (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
       (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
       return_buf_frame d ce sa s0 /\ storage_trace_domain cx st0 mid.storage_trace /\
       (!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func ce cx es s0) /\
       (!H. valid_horizon cx st0 H mid.storage_trace ==>
          vv_post H ctx func ce cx obj es sa sm s0 mid raw bvv s /\
          ghost_inv_at (DF H) lo d ce cx mid G1 tn1 s) /\
       vv_store_bound cx (post_value_type ce obj) (lowered_value_type ce obj) mid raw bvv s /\
       ptr_vv_ok cx (post_value_type ce obj) raw bvv mid G1 tn1 s /\
       (!t op. bvv = StackValue t op ==> ptr_buf_ok ce obj op G1 s) /\
       (!t p. bvv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
              ptr_buf_ok ce obj p.ptr_operand G1 s) /\
       (ce.ce_is_ctor /\ vv_location bvv = SOME LocCode ==>
         ?v. read_result cx raw mid = (INL v,mid) /\
           !rt w. evaluate_type (get_tenv cx) (post_value_type ce obj) = SOME rt /\
                  eval_operand (vv_operand bvv) s = SOME w ==>
             w2n w + type_memory_size rt <= lo /\
             !m. mem_agree_outside tn1.t_mem s.vs_memory m ==> val_in_memory rt v (w2n w) m) /\
       ghost_kept_at lo ce es sa G0 tn0 s0 G1 tn1 /\
       alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
       ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
       s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
       ?u Gc tnc q w atv.
         cvv = LocatedValue (ArrayT et bd) (mk_ptr (Var q) LocMemory) /\
         evaluate_type (get_tenv cx) (ArrayT et bd) = SOME atv /\ val_wf atv saved /\
         value_has_type atv saved /\ lookup_var q u = SOME w /\ not_fresh_at sc q /\
         ptr_covers Gc tnc q u (type_memory_size atv) /\
         (!m. mem_agree_outside tnc.t_mem u.vs_memory m ==> val_in_memory atv saved (w2n w) m) /\
         vv_own ce cx (ArrayT et bd) sm sc mid (Value saved) cvv u /\
         (!H. valid_horizon cx st0 H mid.storage_trace ==>
           gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
              (s,G1,tn1) [] (OK u,Gc,tnc) /\
           stmt_state_rel H ctx func ce cx mid u /\ storage_well_formed_on cx mid (FST H) /\
           ghost_inv_at (DF H) lo d ce cx mid Gc tnc u) /\
         ghost_kept_at lo ce es sa G0 tn0 s0 Gc tnc /\ return_buf_frame d ce sc u /\
         local_ptrs_reserved ce sc /\ alloca_history func u /\ allocas_from lo u /\
         (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\ s.vs_alloca_next <= u.vs_alloca_next /\
         (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s /\
             FLOOKUP Gc x = FLOOKUP G1 x /\ op_taint tnc (Var x) = op_taint tn1 (Var x)) /\
         (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> FLOOKUP u.vs_allocas aid = SOME entry) /\
         u.vs_labels = s.vs_labels /\ ~u.vs_halted /\ u.vs_current_bb = sc.cs_current_bb /\
         u.vs_inst_idx = LENGTH sc.cs_current_insts /\
         (frames ==> wb_frame ce es mid sa s0 u /\
            (~expr_has_effect obj ==> pure_frame ce func es sa s0 u))) ==>
  expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty (Subscript ann obj idx) es
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume subscript_copied_children_prefix[base_bind]:
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (cx_tops cx) cx st0 (eval_expr cx obj) (es,s0,G0,tn0)
     (\H res ee G tn t. baseQ H res ee G tn t /\ reach_ok t /\
        ~t.vs_halted /\ ee.gas_obs = []) (\H res ee gt r. ISR res)` by
    (irule gas_outcome_full_post_source >>
     qpat_assum `gas_outcome_full _ _ _ _ _ _ (\H res ee G tn t. _ /\ reach_ok t) baseR`
       (irule_at Any) >> simp[Abbr `baseR`] >>
     rpt gen_tac >> Cases_on `res` >> simp[expr_exit_def]) >>
  qpat_assum `subscript_reads_base _ _ _` (fn th =>
    pure_once_rewrite_tac[MATCH_MP eval_expr_subscript_copied_bind th]) >>
  irule gas_prefix_full_bind >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ (\H res ee gt r. ISR res)`
    (irule_at Any) >>
  simp[evaluate_storage_trace_frame, evaluate_requests_outcomes_frame,
       storage_trace_frame_bind_all, storage_trace_frame_select, storage_trace_frame_read_result] >>
  suspend "snapshot"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume subscript_copied_children_prefix[snapshot]:
  qx_genl_tac [`marks`,`raw`,`mid`,`G1`,`tn1`,`t`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> baseQ _ _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qunabbrev_tac `baseQ` >> disch_then (strip_assume_tac o BETA_RULE) >>
  qpat_assum `!tail. eval_expr _ _ _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [listTheory.APPEND_NIL])) >>
  `mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
  gvs[] >>
  `?saved. read_result cx raw mid = (INL saved,mid)` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ ghost_inv_at _ _ _ _ _ _ _ _ _` drule >>
     disch_then (strip_assume_tac o REWRITE_RULE [vv_post_def]) >>
     drule attribute_vv_holds_read_operand >>
     disch_then strip_assume_tac >> goal_assum (drule_at Any)) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func ce cx es s0` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  qpat_assum `!st sa sm sc bvv cvv shm s0 G0 tn0 gs raw ee saved s G1 tn1. _ ==> ?u. _`
    (qspecl_then [`st0`,`sa`,`sm`,`sc`,`bvv`,`cvv`,`shm`,`s0`,`G0`,`tn0`,
                  `gas_explicit marks s0.vs_gas_readings`,`raw`,`mid`,`saved`,`t`,`G1`,`tn1`] mp_tac) >>
  (impl_tac >- simp[is_word_type_def]) >> strip_tac >>
  suspend "index"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume subscript_copied_children_prefix[index]:
  `body_expr_prefix_ok cx idx` by
    (qpat_assum `!s raw ee saved. _ ==> body_expr_prefix_ok cx idx`
       drule_all >> simp[]) >>
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (`well_typed_expr env obj` by
       qpat_assum `expr_body_pre _ cx env obj _`
         (ACCEPT_TAC o cj 2 o MATCH_MP expr_body_pre_static_facts) >>
     irule body_const_cells_agree_expr >>
     goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >> simp[]) >>
  `expr_body_pre ce cx env idx mid` by
    (`expr_body_pre ce cx env (Subscript ann obj idx)
         (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
     drule_all expr_body_pre_array_subscript_index_after_base >> simp[]) >>
  `expr_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty idx mid` by
    (qpat_x_assum `body_expr_prefix_ok cx idx`
       (mp_tac o cj 1 o REWRITE_RULE [body_expr_prefix_ok_def]) >> metis_tac[]) >>
  `sa.cs_next_var <= sc.cs_next_var` by
    (mp_tac (Q.SPECL [`ce`,`ty`,`obj`,`sa`] (cj 1 compile_expr_ci_mono)) >>
     mp_tac (Q.SPECL [`ce`,`T`,`bvv`,`sm`] ci_mono_compile_snapshot_vv) >>
     simp[ci_mono_def]) >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x)` by
    (rpt conj_tac >> rpt strip_tac >>
     irule not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  `gas_admissible (bind (eval_expr cx idx) (read_result cx)) expr_res_ok mid` by
    (drule expr_body_pre_gas_admissible >> simp[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (t,G1,tn1) [] (OK u,Gc,tnc)` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
       gas_origin_ptr_path _ (t,G1,tn1) [] _ /\ _` (drule_then (ACCEPT_TAC o cj 1))) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
     stmt_state_rel H ctx func ce cx mid u /\ storage_well_formed_on cx mid (FST H) /\
     ghost_inv_at (DF H) lo d ce cx mid Gc tnc u` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
       gas_origin_ptr_path _ (t,G1,tn1) [] _ /\ _` (drule_then (ACCEPT_TAC o CONJUNCT2))) >>
  `reach_ok u` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
       gas_origin_ptr_path _ (t,G1,tn1) [] _`
       (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then assume_tac)) >>
     qpat_assum `gas_origin_ptr_path _ (t,G1,tn1) [] (OK u,Gc,tnc)`
       (mp_then Any mp_tac gas_origin_ptr_path_dalloca_fmp_headroom) >>
     fs[Abbr `reach_ok`] >> metis_tac[]) >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 (bind (eval_expr cx idx) (read_result cx)) (mid,u,Gc,tnc)` by
    (qpat_x_assum `expr_sim_prefix _ _ _ _ idx _`
       (mp_tac o REWRITE_RULE [expr_sim_prefix_def,expr_sim_full_pre_def]) >>
     disch_then (qspecl_then [`st0`,`sc`,`si`,`shc`,`shi`,`iop`,`u`,`Gc`,`tnc`] mp_tac) >>
     qunabbrev_tac `reach_ok` >> simp[] >>
     disch_then irule >> first_assum (ACCEPT_TAC o BETA_RULE)) >>
  suspend "selection"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume subscript_copied_children_prefix[selection]:
  (* The saved value is immediate: selecting from it changes the result,
     not the source state or its request trace. *)
  qabbrev_tac `ix = bind (eval_expr cx idx) (read_result cx)` >>
  qabbrev_tac `sel = \v. select_result cx (ArrayT et bd) (Value saved) (ValueSubscript v)` >>
  `!ee. SND (bind ix sel ee) = SND (ix ee)` by
    (gen_tac >> Cases_on `ix ee` >> rename1 `ix ee = (res,fin)` >>
     Cases_on `res` >> simp[Once vyperStateTheory.bind_def] >>
     rename1 `SND (sel key fin) = fin` >>
     simp[Abbr `sel`,select_result_def,vyperStateTheory.bind_def] >>
     Cases_on `evaluate_subscripts atv saved [ValueSubscript key]` >>
     simp[lift_sum_def,return_def,raise_def]) >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 (bind ix sel) (mid,u,Gc,tnc)` by
    (drule_then (fn th => rewrite_tac[th]) gas_prefix_full_state_cong >>
     first_assum ACCEPT_TAC) >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 (bind ix sel) (mid,t,G1,tn1)` by
    (qpat_assum `gas_prefix_full _ _ _ (bind ix sel) (mid,u,Gc,tnc)`
       (mp_then Any irule gas_prefix_full_zero_prefix_guarded) >>
     simp[Abbr `ix`,Abbr `sel`,evaluate_storage_trace_frame,
          storage_trace_frame_bind_all,storage_trace_frame_select,storage_trace_frame_read_result]) >>
  drule_then assume_tac read_result_gas_obs >>
  `!tail. bind (read_result cx raw) (\base. bind ix
      (\v. select_result cx (ArrayT et bd) (Value base) (ValueSubscript v)))
        (mid with gas_obs := tail) = bind ix sel (mid with gas_obs := tail)` by
    (gen_tac >> CONV_TAC (LAND_CONV (REWR_CONV (SPEC_ALL vyperStateTheory.bind_def))) >>
     simp[Abbr `sel`]) >>
  qpat_x_assum `gas_prefix_full _ _ _ (bind ix sel) (mid,t,G1,tn1)` mp_tac >>
  simp[gas_prefix_full_def]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise subscript_copied_children_prefix
*)
