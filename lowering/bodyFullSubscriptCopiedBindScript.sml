(* The copied array arm: read/snapshot before evaluating the index. *)
Theory bodyFullSubscriptCopiedBind
Ancestors
  bodyFullShadowBodyInv
  bodyFullPreds bodyFullSimProjection bodySimFull bodyFullShared bodyFullSubscriptCapturedPlace
  gasOutcomeFullCompose gasOutcomeFullGuarded gasShadowCompile
  gasShadowCompileConvert gasShadowCompileStmtHelpers
  exprSimSubscriptArray exprSimSubscriptArraySource
  exprSimUnwrap exprOperandVar exprLoweringProps exprSimMemorySource
  abiEncodeArgsSim stateRelProj wordArgsPtr bodyPtrAttributeSource
  bodyFullBuiltinConcatScratch bodyPtrBytestringBuiltinsWindowGhost
  bodyPtrDefs loweringPosts exprSimWordArgs ptrDiscipline
  exprLowering compileEnv vyperAST gasShadowState gasShadow
  fragExec exprSimHyps gasExemptCert vyperStorageTrace
  vyperTyping[qualified,ignore_grammar]
  bodyFullIfExpReach
  contextRawReachable[qualified,ignore_grammar]
  unitTransformDefs[qualified,ignore_grammar]

Theorem compile_expr_copied_array_subscript[local]:
  compile_expr cenv ty (Subscript ann obj idx) sa = (vv,sb) /\
  place_type cenv obj = ValPT (ArrayT et bd) /\
  copies_subscript_base cenv obj idx ==>
  ?bvv sm cvv sc iop si dst loc.
    compile_expr cenv ty obj sa = (bvv,sm) /\
    compile_snapshot_vv cenv T bvv sm = (cvv,sc) /\
    lower_value compile_expr cenv ty idx sc = (iop,si) /\
    loc = (case vv_location cvv of SOME l => l | NONE => LocMemory) /\
    compile_array_subscript (vv_operand cvv) iop
      (case bd of Fixed _ => F | Dynamic _ => T)
      (case bd of Fixed n => n | Dynamic _ => 0)
      (word_scale loc) (elem_size_in_location cenv loc et)
      (is_signed_type (expr_type idx))
      (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc)
      si = (dst,sb) /\
    vv = LocatedValue ann (mk_ptr dst loc)
Proof
  strip_tac >>
  qpat_x_assum `compile_expr _ _ (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once (cj 1 compile_expr_raw_def), compile_expr_body_def,
       compile_subscript_def, lower_value_def,
       exprCallBoundsTheory.expr_child_callback_def,
       comp_bind_def, comp_return_def, expr_size_def, expr_type_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem copied_array_suffix_extends[local]:
  compile_array_subscript bop iop dyn cnt scale elem_bytes signed
    (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca loc) si = (dst,sb) ==>
  cs_extends si sb
Proof
  strip_tac >> `ci_mono si sb` suffices_by simp[ci_mono_def] >>
  qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _`
    (SUBST1_TAC o SYM o PURE_REWRITE_RULE [pairTheory.SND] o Q.AP_TERM `SND`) >>
  simp[ci_mono_compile_array_subscript, ci_mono_compile_ptr_load]
QED

Theorem copied_array_cuts[local]:
  compile_expr ce ty (Subscript ann obj idx) sa = (vv,sb) /\
  compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr (Subscript ann obj idx)) sha = (vv,shb) /\
  gas_shadow_state sa sha /\
  place_type ce obj = ValPT (ArrayT et bd) /\
  copies_subscript_base ce obj idx ==>
  ?bvv sm cvv sc iop si dst loc shm shc shi.
    compile_expr ce ty obj sa = (bvv,sm) /\
    compile_snapshot_vv ce T bvv sm = (cvv,sc) /\
    lower_value compile_expr ce ty idx sc = (iop,si) /\
    loc = (case vv_location cvv of SOME l => l | NONE => LocMemory) /\
    compile_array_subscript (vv_operand cvv) iop
      (case bd of Fixed _ => F | Dynamic _ => T)
      (case bd of Fixed n => n | Dynamic _ => 0)
      (word_scale loc) (elem_size_in_location ce loc et)
      (is_signed_type (expr_type idx))
      (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca loc)
      si = (dst,sb) /\
    vv = LocatedValue ann (mk_ptr dst loc) /\
    compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr obj) sha = (bvv,shm) /\
    compile_snapshot_vv ce T bvv shm = (cvv,shc) /\
    lower_value compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr idx) shc = (iop,shi) /\
    gas_shadow_state sm shm /\ gas_shadow_state sc shc /\ gas_shadow_state si shi /\
    cs_extends sa sm /\ cs_extends sm sc /\ cs_extends sc si /\ cs_extends si sb /\
    cs_extends sha shm /\ cs_extends shm shc /\ cs_extends shc shi /\ cs_extends shi shb
Proof
  strip_tac >> drule_all compile_expr_copied_array_subscript >> strip_tac >>
  `copies_subscript_base (gas_shadow_env T ce) (gas_shadow_expr obj) (gas_shadow_expr idx) /\
   place_type (gas_shadow_env T ce) (gas_shadow_expr obj) = ValPT (ArrayT et bd)` by
    gvs[copies_subscript_base_def] >>
  qpat_x_assum `compile_expr _ _ (gas_shadow_expr (Subscript _ _ _)) _ = _` mp_tac >>
  simp[gas_shadow_expr_def] >> strip_tac >>
  drule_all compile_expr_copied_array_subscript >> strip_tac >>
  `gas_shadow_compiles (compile_expr ce ty obj)
     (compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr obj))` by
    irule gas_shadow_stmt_compile_expr_env >>
  drule_all_then strip_assume_tac gas_shadow_step >> gvs[] >>
  `gas_shadow_compiles (compile_snapshot_vv ce T bvv)
     (compile_snapshot_vv ce T bvv)` by irule gas_shadow_compiles_snapshot_vv >>
  drule_all_then strip_assume_tac gas_shadow_step >> gvs[] >>
  `gas_shadow_compiles (lower_value compile_expr ce ty idx)
     (lower_value compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr idx))` by
    irule gas_shadow_stmt_lower_value_env >>
  drule_all_then strip_assume_tac gas_shadow_step >> gvs[] >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  metis_tac[compile_expr_extends, cj 2 compile_expr_grows,
    ci_mono_compile_snapshot_vv, ci_mono_def, pairTheory.SND, copied_array_suffix_extends]
QED

(* The snapshot allocation is old at the index entry cut, even though it
   is fresh relative to the entire subscript expression. *)
Theorem copied_array_index_frame[local]:
  expr_post H ctx func ce cx idx mid sc si s fin key iop u /\
  ghost_kept_at lo ce mid sc G tn s Gi tni /\
  stmt_state_rel H ctx func ce cx mid s /\
  MAP FDOM mid.scopes = MAP FDOM fin.scopes /\
  local_ptrs_reserved ce sc /\ not_fresh_at sc p /\
  lookup_var p s = SOME w /\ ptr_covers G tn p s (type_memory_size tv) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  vv_own ce cx ty sm sc mid (Value saved) (LocatedValue ty (mk_ptr (Var p) LocMemory)) s /\
  val_wf tv saved /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv saved (w2n w) m) ==>
  lookup_var p u = SOME w /\ ptr_covers Gi tni p u (type_memory_size tv) /\
  vv_own ce cx ty sm sc fin (Value saved) (LocatedValue ty (mk_ptr (Var p) LocMemory)) u /\
  (!m. mem_agree_outside tni.t_mem u.vs_memory m ==> val_in_memory tv saved (w2n w) m)
Proof
  strip_tac >>
  `!x y. not_fresh_at sc x /\ lookup_var x s = SOME y ==> lookup_var x u = SOME y` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_post_def]) >> first_assum ACCEPT_TAC) >>
  `lookup_var p u = SOME w` by simp[] >>
  `ptr_covers Gi tni p u (type_memory_size tv)` by
    (qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ _ _` mp_tac >>
     qpat_x_assum `ptr_covers G _ _ _ _` mp_tac >>
     simp[ptr_covers_def, ghost_kept_at_def] >> metis_tac[]) >>
  simp[vv_own_def, contextTheory.mk_ptr_def, venomStateTheory.eval_operand_def,
       vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
  qpat_x_assum `vv_own _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[vv_own_def, contextTheory.mk_ptr_def, venomStateTheory.eval_operand_def,
       vyperStateTheory.read_result_def, vyperStateTheory.return_def] >>
  strip_tac
  >- (rename1 `FLOOKUP s.vs_allocas aid = SOME (b,n)` >>
      drule_all_then strip_assume_tac concat_scratch_child_frame >>
      conj_tac
      >- (disj1_tac >> qexistsl_tac [`aid`,`b`,`n`] >> simp[] >>
          qx_genl_tac [`n'`,`lb`,`lsz`] >> strip_tac >>
          `local_region ce mid.scopes s n' lb lsz` by
            (irule exprSimPropsTheory.local_region_frame >>
             first_assum (irule_at Any) >> qexistsl_tac [`sc`,`func`] >> simp[] >>
             metis_tac[cj 1 stmt_state_rel_local_ptrs_alloca]) >>
          metis_tac[]) >>
      `mem_bytes_at (w2n w) (val_footprint tv saved) u.vs_memory =
       mem_bytes_at (w2n w) (val_footprint tv saved) s.vs_memory` by
        (qpat_assum `mem_bytes_at b n _ = _`
           (mp_then Any mp_tac valueEncodingPropsTheory.mem_bytes_at_translated_window) >>
         disch_then (qspecl_then [`w2n w - b`,`val_footprint tv saved`] mp_tac) >>
         `b + (w2n w - b) = w2n w` by decide_tac >> simp[] >> decide_tac) >>
      `!i. w2n w <= i /\ i < w2n w + val_footprint tv saved /\ i IN tni.t_mem ==>
           i IN tn.t_mem` by (rpt strip_tac >> first_assum irule >> simp[] >> decide_tac) >>
      (rpt strip_tac >> irule robust_val_in_memory_window_transport >>
       conj_tac >- simp[] >>
       qexistsl_tac [`tn.t_mem`, `tni.t_mem`, `val_footprint tv saved`,
                     `s.vs_memory`, `u.vs_memory`] >> simp[])) >>
  `mem_bytes_at (w2n w) (val_footprint tv saved) u.vs_memory =
   mem_bytes_at (w2n w) (val_footprint tv saved) s.vs_memory` by
    simp[valueEncodingDefsTheory.mem_bytes_at_def] >>
  `!i. w2n w <= i /\ i < w2n w + val_footprint tv saved /\ i IN tni.t_mem ==>
       i IN tn.t_mem` by (simp[] >> decide_tac) >>
  conj_tac >- simp[] >>
  (rpt strip_tac >> irule robust_val_in_memory_window_transport >>
       conj_tac >- simp[] >>
       qexistsl_tac [`tn.t_mem`, `tni.t_mem`, `val_footprint tv saved`,
                     `s.vs_memory`, `u.vs_memory`] >> simp[])
QED

(* The two continuation interfaces are kept explicit: the snapshot runs at
   the pre-index read, and the array selection uses its saved Value.
   The frames flag lets the selector request the caller's composed frames. *)
Theorem subscript_copied_bind_caller_frames:
  !frames cx ann obj idx DF lo d PG tops ctx shadow_ctx func shadow_func ce env ty es et bd.
    (!s raw mid saved. eval_expr cx obj s = (INL raw,mid) /\
       read_result cx raw mid = (INL saved,mid) ==> body_expr_full_ok cx idx) /\
    body_expr_full_ok cx obj /\ body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shadow_ctx /\
    subscript_reads_base cx obj idx /\ copies_subscript_base ce obj idx /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_body_pre ce cx env (Subscript ann obj idx) es /\
    expr_type obj = ArrayT et bd /\ place_type ce obj = ValPT (ArrayT et bd) /\
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
            (~expr_has_effect obj ==> pure_frame ce func es sa s0 u))) /\
    (!st0 sa sm sc si sb bvv cvv vv iop dst s0 G0 tn0 gs raw mid saved s gc ic u
       key fin z Gi tni q w atv.
       eval_expr cx obj (es with gas_obs := gs) = (INL raw,mid) /\
       read_result cx raw mid = (INL saved,mid) /\
       bind (eval_expr cx idx) (read_result cx) (mid with gas_obs := ic) = (INL key,fin) /\
       compile_expr ce ty obj sa = (bvv,sm) /\
       compile_snapshot_vv ce T bvv sm = (cvv,sc) /\
       lower_value compile_expr ce ty idx sc = (iop,si) /\
       compile_expr ce ty (Subscript ann obj idx) sa = (vv,sb) /\
       cvv = LocatedValue (ArrayT et bd) (mk_ptr (Var q) LocMemory) /\
       vv = LocatedValue ann (mk_ptr dst LocMemory) /\
       compile_array_subscript (Var q) iop
         (case bd of Fixed _ => F | Dynamic _ => T)
         (case bd of Fixed n => n | Dynamic _ => 0)
         (word_scale LocMemory) (elem_size_in_location ce LocMemory et)
         (is_signed_type (expr_type idx))
         (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca LocMemory) si = (dst,sb) /\
       fn_has_code si sb func /\ fn_inst_ids_distinct func /\
       cs_extends sa sm /\ cs_extends sm sc /\ cs_extends sc si /\ cs_extends si sb /\
       local_ptrs_reserved ce si /\ local_ptrs_reserved ce sa /\
       (frames ==> wb_frame ce es fin sa s0 z /\
          (~expr_has_effect (Subscript ann obj idx) ==> pure_frame ce func es sa s0 z)) /\
       (!H. dead_lo_ok H (DF H) lo ce cx) /\
       (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
       (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
       return_buf_frame d ce sa s0 /\ storage_trace_domain cx st0 fin.storage_trace /\
       fin.gas_obs = [] /\ ~z.vs_halted /\ z.vs_current_bb = si.cs_current_bb /\
       z.vs_inst_idx = LENGTH si.cs_current_insts /\ alloca_history func z /\
       s0.vs_alloca_next <= z.vs_alloca_next /\
       (!H. valid_horizon cx st0 H fin.storage_trace ==>
          stmt_state_rel H ctx func ce cx es s0 /\
          vv_post H ctx func ce cx obj es sa sm s0 mid raw bvv s /\
          expr_post H ctx func ce cx idx mid sc si u fin key iop z /\
          ghost_inv_at (DF H) lo d ce cx fin Gi tni z) /\
       ghost_kept_at lo ce es sa G0 tn0 s0 Gi tni /\
       ptr_val_ok cx (post_value_type ce idx) key iop Gi tni z /\
       evaluate_type (get_tenv cx) (ArrayT et bd) = SOME atv /\
       val_wf atv saved /\ value_has_type atv saved /\
       lookup_var q z = SOME w /\ not_fresh_at si q /\ ptr_covers Gi tni q z (type_memory_size atv) /\
       (!m. mem_agree_outside tni.t_mem z.vs_memory m ==> val_in_memory atv saved (w2n w) m) /\
       vv_own ce cx (ArrayT et bd) sm sc fin (Value saved) cvv z ==>
       gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (cx_tops cx) cx st0
         (select_result cx (ArrayT et bd) (Value saved) (ValueSubscript key)) (fin,z,Gi,tni)
         (\H res ee G tn t. ?tv. res = INL tv /\
           vv_post H ctx func ce cx (Subscript ann obj idx) es sa sb s0 ee tv vv t /\
           vv_store_bound cx (post_value_type ce (Subscript ann obj idx))
             (lowered_value_type ce (Subscript ann obj idx)) ee tv vv t /\
           t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
           alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
           s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at (DF H) lo d ce cx ee G tn t /\
           ptr_vv_ok cx (post_value_type ce (Subscript ann obj idx)) tv vv ee G tn t /\
           (!v. tv = Value v /\ ~is_word_type (post_value_type ce (Subscript ann obj idx)) /\
             ~is_bytestring_type (post_value_type ce (Subscript ann obj idx)) ==>
             vv_own ce cx (post_value_type ce (Subscript ann obj idx)) sa sb ee tv vv t /\
             (!t' p. vv = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
           (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
             ?v. read_result cx tv ee = (INL v,ee) /\
              !rt base. evaluate_type (get_tenv cx) (post_value_type ce (Subscript ann obj idx)) = SOME rt /\
                        eval_operand (vv_operand vv) t = SOME base ==>
                w2n base + type_memory_size rt <= lo /\
                (!m. mem_agree_outside tn.t_mem t.vs_memory m ==> val_in_memory rt v (w2n base) m)) /\
           (!t' op. vv = StackValue t' op /\ ~is_word_type (post_value_type ce (Subscript ann obj idx)) ==>
             ptr_buf_ok ce (Subscript ann obj idx) op G t) /\
           (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
             ptr_buf_ok ce (Subscript ann obj idx) p.ptr_operand G t) /\
           ghost_kept_at lo ce es sa G0 tn0 s0 G tn)
         (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
           (ctx_has_dalloca ctx ==> !t. r = Halt t ==> allocas_below_fmp t))) ==>
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty (Subscript ann obj idx) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_body_pre ce cx env obj es` by
    metis_tac[exprSimSubscriptArraySourceTheory.expr_body_pre_array_subscript_base,
              exprSimSubscriptArraySourceTheory.copies_subscript_base_not_array_slot_base] >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty obj es` by
    (drule_all body_expr_full_ok_simulations >> simp[]) >>
  simp[expr_vv_sim_full_def] >> rpt gen_tac >> strip_tac >>
  drule_all copied_array_cuts >> strip_tac >>
  `cs_extends sm sb /\ cs_extends sc sb /\
   cs_extends shm shadow_sb /\ cs_extends shc shadow_sb` by
    (rpt (qpat_x_assum `!x y z w v. _ ==> _` kall_tac) >>
     rpt conj_tac >> irule cs_extends_trans
     >- (qexists `sc` >> simp[] >> irule cs_extends_trans >> qexists `si` >> simp[])
     >- (qexists `si` >> simp[])
     >- (qexists `shc` >> simp[] >> irule cs_extends_trans >> qexists `shi` >> simp[])
     >> qexists `shi` >> simp[]) >>
  `fn_has_code sa sm func /\ fn_has_code sm sc func /\ fn_has_code sc si func /\
   fn_has_code si sb func /\ fn_has_code shadow_sa shm shadow_func /\
   fn_has_code shc shi shadow_func` by
    (imp_res_tac fn_has_code_split >> simp[]) >>
  `gas_admissible (eval_expr cx obj) expr_vv_res_ok es` by
    (drule expr_body_pre_vv_gas_admissible >> simp[]) >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ obj _` (mp_tac o REWRITE_RULE [expr_vv_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`shm`,`bvv`,`s0`,`G0`,`tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ baseQ baseR` >>
  qpat_assum `subscript_reads_base _ _ _` (fn th =>
    pure_once_rewrite_tac[MATCH_MP eval_expr_subscript_copied_bind th]) >>
  irule gas_outcome_full_bind_all_path >>
  `!res : eval_result + exception. !r.
     (?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) r) <=> expr_exit res r` by
    (Cases >> simp[]) >> simp[] >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_result >>
      qexistsl [`mid`,`t`,`v`] >> simp[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_result >> simp[])
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[cj 5 evaluate_storage_trace_frame]
  >- (gen_tac >> simp[storage_trace_frame_bind_all, storage_trace_frame_select,
          cj 5 evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
  qexists `\H res ee G tn t. baseQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac >~ [`storage_trace_domain _ _ _`] >- suspend "base_success" >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[Abbr `baseQ`, Abbr `baseR`] >>
  rpt gen_tac >> Cases_on `res` >> simp[exprSimDefsTheory.expr_exit_def]
QED

Resume subscript_copied_bind_caller_frames[base_success]:
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`t`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> baseQ _ _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  qunabbrev_tac `baseQ` >> disch_then (strip_assume_tac o BETA_RULE) >>
  qpat_assum `!tail. eval_expr _ _ _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [listTheory.APPEND_NIL])) >>
  `mid with gas_obs := [] = mid` by simp[vyperStateTheory.evaluation_state_component_equality] >>
  gvs[] >>
  `?saved. read_result cx tv mid = (INL saved,mid)` by
    (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _ /\ ghost_inv_at _ _ _ _ _ _ _ _ _` drule >>
     disch_then (strip_assume_tac o REWRITE_RULE [vv_post_def]) >>
     drule bodyPtrAttributeSourceTheory.attribute_vv_holds_read_operand >>
     disch_then strip_assume_tac >> goal_assum (drule_at Any)) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==> stmt_state_rel H ctx func ce cx es s0` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
       vv_post H ctx func ce cx obj es sa sm s0 mid tv bvv t /\
       ghost_inv_at (DF H) lo d ce cx mid G1 tn1 t` by
    (rpt strip_tac >> first_x_assum drule >> simp[]) >>
  qpat_assum `!st sa sm sc bvv cvv shm s0 G0 tn0 gs raw ee saved s G1 tn1. _ ==> ?u. _`
    (qspecl_then [`st0`,`sa`,`sm`,`sc`,`bvv`,`cvv`,`shm`,`s0`,`G0`,`tn0`,
                  `gas_explicit marks s0.vs_gas_readings`,`tv`,`mid`,`saved`,`t`,`G1`,`tn1`] mp_tac) >>
  impl_tac >- simp[is_word_type_def] >> strip_tac >>
  `body_expr_full_ok cx idx` by
    (qpat_assum `!s raw ee saved. eval_expr _ _ _ = _ /\ read_result _ _ _ = _ ==> _`
       drule_all >> simp[]) >>
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (`well_typed_expr env obj` by
       qpat_assum `expr_body_pre _ cx env obj _`
         (ACCEPT_TAC o cj 2 o MATCH_MP exprBodyPrePropsTheory.expr_body_pre_static_facts) >>
     irule body_const_cells_agree_expr >>
     goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >> simp[]) >>
  `expr_body_pre ce cx env idx mid` by
    (`expr_body_pre ce cx env (Subscript ann obj idx)
         (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by simp[] >>
     drule_all expr_body_pre_array_subscript_index_after_base >> simp[]) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty idx mid` by
    (drule_all body_expr_full_ok_simulations >> simp[]) >>
  `sa.cs_next_var <= sc.cs_next_var /\ sc.cs_next_var <= si.cs_next_var` by
    (mp_tac (Q.SPECL [`ce`,`ty`,`obj`,`sa`] (cj 1 compile_expr_ci_mono)) >>
     mp_tac (Q.SPECL [`ce`,`T`,`bvv`,`sm`] ci_mono_compile_snapshot_vv) >>
     mp_tac (Q.SPECL [`ce`,`ty`,`idx`,`sc`] ci_mono_lower_value_compile_expr) >>
     simp[ci_mono_def]) >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x)` by
    (rpt conj_tac >> rpt strip_tac >>
     irule freshWritesTheory.not_fresh_at_mono >> qexists `sa` >> simp[]) >>
  `gas_admissible (bind (eval_expr cx idx) (read_result cx)) expr_res_ok mid` by
    (drule exprSimSourceTheory.expr_body_pre_gas_admissible >> simp[]) >>
  qpat_x_assum `expr_sim_full _ _ _ _ idx _` (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`sc`,`si`,`shc`,`shi`,`iop`,`u`,`Gc`,`tnc`] mp_tac) >>
  (impl_tac >-
    (`!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
       (qpat_assum `body_inv tops ctx ce cx` (fn inv =>
          qpat_assum `MEM func ctx.ctx_functions`
            (ACCEPT_TAC o MATCH_MP bodyFullIfExpReachTheory.body_inv_no_phi o CONJ inv))) >>
     qabbrev_tac `H0 = storage_trace_horizon mid.storage_trace` >>
     `gas_origin_ptr_path (DF H0,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s0,G0,tn0) marks (OK t,G1,tn1)` by
       (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _`
          (qspec_then `H0` mp_tac) >> simp[Abbr `H0`]) >>
     `gas_origin_ptr_path (DF H0,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (t,G1,tn1) [] (OK u,Gc,tnc)` by
       (qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
            gas_origin_ptr_path _ (t,G1,tn1) [] _ /\ _`
          (qspec_then `H0` mp_tac) >> simp[Abbr `H0`]) >>
     `gas_origin_ptr_path (DF H0,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (s0,G0,tn0) marks (OK u,Gc,tnc)` by
       metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append, listTheory.APPEND_NIL] >>
     `!fn i v. frag_reachable ctx func u fn i v ==> dalloca_fmp_headroom i v` by
       (qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) marks (OK u,Gc,tnc)` (fn path =>
        qpat_assum `!bb. MEM bb func.fn_blocks ==> phi_prefix_length _ = _` (fn no_phi =>
        qpat_assum `!fn i v. frag_reachable ctx func s0 fn i v ==> _`
          (ACCEPT_TAC o MATCH_MP bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom o
           CONJ path o CONJ no_phi)))) >>
     simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qpat_x_assum `cvv = LocatedValue _ _` SUBST_ALL_TAC >>
  fs[contextTheory.vv_location_def, contextTheory.vv_operand_def, contextTheory.mk_ptr_def] >>
  irule gas_outcome_full_bind >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
            qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` (irule_at Any) >> gvs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[])
  >~ [`storage_trace_frame (read_result _ _)`]
  >- simp[storage_trace_frame_read_result]
  >- (gen_tac >> simp[storage_trace_frame_bind_all, storage_trace_frame_select,
          cj 5 evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
  irule gas_outcome_full_pure >> simp[] >>
  qexistsl [`Gc`, `mid`, `INL saved`, `u`, `tnc`] >>
  simp[exprSimMemorySourceTheory.read_result_gas_obs] >>
  rpt strip_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ (bind (eval_expr cx idx) _) _ indexQ indexR` >>
  irule gas_outcome_full_bind_all >> simp[] >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
      qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` (irule_at Any) >> gvs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[])
  >~ [`storage_trace_frame (bind _ _)`]
  >- simp[storage_trace_frame_bind_all, cj 5 evaluate_storage_trace_frame,
          storage_trace_frame_read_result]
  >~ [`storage_trace_frame (select_result _ _ _ _)`]
  >- simp[storage_trace_frame_select] >>
  qexists `\H res ee G tn t. indexQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ indexQ indexR` (irule_at Any) >>
      simp[Abbr `indexQ`, Abbr `indexR`, Abbr `baseR`] >>
      gen_tac >> Cases >> simp[exprSimDefsTheory.expr_exit_def] >>
      rpt strip_tac
      >~ [`expr_exit (INR _) _`]
      >- (qpat_assum `expr_exit (INR _) _`
            (mp_then Any MATCH_ACCEPT_TAC bodyFullTargetSubscriptTheory.expr_exit_INR_retype)) >>
      fs[exprSimDefsTheory.halt_exit_def]) >>
  suspend "index_success"
QED

Resume subscript_copied_bind_caller_frames[index_success]:
  qx_genl_tac [`imarks`, `ires`, `fin`, `Gi`, `tni`, `it`] >>
  BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) fin.storage_trace` by
    gvs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `indexQ (storage_trace_horizon fin.storage_trace) ires fin Gi tni it /\
   ~it.vs_halted /\ fin.gas_obs = []` by
    (qpat_assum `!H. valid_horizon cx st0 H fin.storage_trace ==>
        indexQ H ires fin Gi tni it /\ ~it.vs_halted /\ fin.gas_obs = []`
       (qspec_then `storage_trace_horizon fin.storage_trace`
         (fn post => qpat_assum
           `valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) fin.storage_trace`
           (ACCEPT_TAC o MATCH_MP post)))) >>
  qpat_x_assum `indexQ _ _ _ _ _ _` mp_tac >>
  simp[Abbr `indexQ`, NoAsms] >> strip_tac >> gvs[] >>
  `bind (eval_expr cx idx) (read_result cx)
       (mid with gas_obs := gas_explicit imarks u.vs_gas_readings) = (INL v,fin)` by
    (qpat_assum `!tail. bind (eval_expr cx idx) _ _ = _`
       (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [listTheory.APPEND_NIL])) >>
     `fin with gas_obs := [] = fin` by simp[vyperStateTheory.evaluation_state_component_equality] >>
     metis_tac[]) >>
  `MAP FDOM mid.scopes = MAP FDOM fin.scopes` by
    (drule (SRULE [SF ETA_ss] exprSimWordArgsTheory.forced_eval_expr_preserves_scopes_dom) >> simp[]) >>
  `!H'. valid_horizon cx st0 H' fin.storage_trace ==>
         valid_horizon cx st0 H' mid.storage_trace` by
    (gen_tac >> strip_tac >>
     qpat_assum `bind (eval_expr cx idx) _ _ = _`
       (mp_then (Pos (el 2)) mp_tac vyperStorageFootprintTheory.valid_horizon_frame) >>
     simp[storage_trace_frame_bind_all, cj 5 evaluate_storage_trace_frame,
          storage_trace_frame_read_result]) >>
  `lookup_var q it = SOME w /\ ptr_covers Gi tni q it (type_memory_size atv) /\
   vv_own ce cx (ArrayT et bd) sm sc fin (Value saved)
     (LocatedValue (ArrayT et bd) (mk_ptr (Var q) LocMemory)) it /\
   (!m. mem_agree_outside tni.t_mem it.vs_memory m ==> val_in_memory atv saved (w2n w) m)` by
    (irule (INST_TYPE [alpha |-> ``:256``] copied_array_index_frame) >> simp[] >>
     qexistsl [`Gc`,`storage_trace_horizon fin.storage_trace`,`ctx`,`func`,`idx`,
               `iop`,`v`,`lo`,`mid`,`u`,`si`,`tnc`] >>
     simp[contextTheory.mk_ptr_def] >> metis_tac[]) >>
  `!H'. valid_horizon cx st0 H' mid.storage_trace ==>
         valid_horizon cx st0 H' es.storage_trace` by
    (gen_tac >> strip_tac >>
     qpat_assum `eval_expr cx obj _ = _`
       (mp_then (Pos (el 2)) mp_tac vyperStorageFootprintTheory.valid_horizon_frame) >>
     simp[cj 5 evaluate_storage_trace_frame]) >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (qpat_assum `eval_expr cx obj _ = _`
       (mp_then Any mp_tac vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom) >>
     simp[]) >>
  `sa.cs_next_id <= sc.cs_next_id` by
    (mp_tac (Q.SPECL [`ce`,`ty`,`obj`,`sa`] (cj 1 compile_expr_ci_mono)) >>
     mp_tac (Q.SPECL [`ce`,`T`,`bvv`,`sm`] ci_mono_compile_snapshot_vv) >>
     simp[ci_mono_def]) >>
  qabbrev_tac `Hmid = storage_trace_horizon mid.storage_trace` >>
  `stmt_state_rel Hmid ctx func ce cx es s0 /\
   vv_post Hmid ctx func ce cx obj es sa sm s0 mid tv bvv t` by simp[] >>
  `wb_frame ce es mid sa s0 t` by
    (qpat_assum `vv_post Hmid _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [vv_post_def]) >>
     pure_rewrite_tac[wb_frame_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
               FLOOKUP u.vs_allocas aid = SOME entry` by
    (qpat_assum `wb_frame _ _ _ _ _ _`
       (assume_tac o cj 2 o REWRITE_RULE [wb_frame_def]) >>
     rpt strip_tac >> first_assum irule >> first_assum irule >> simp[]) >>
  `!n b sz. local_region ce es.scopes s0 n b sz <=>
            local_region ce mid.scopes t n b sz` by
    (drule_all wb_frame_local_regions >> simp[]) >>
  `local_ptrs_reserved ce sm /\ local_ptrs_reserved ce si` by
    (mp_tac (Q.SPECL [`ce`,`ty`,`obj`,`sa`] (cj 1 compile_expr_ci_mono)) >>
     simp[ci_mono_def] >> metis_tac[local_ptrs_reserved_next_var]) >>
  `!n b sz. local_region ce mid.scopes u n b sz <=>
            local_region ce es.scopes s0 n b sz` by
    (rpt gen_tac >> qpat_assum `!n b sz. local_region _ es.scopes _ _ _ _ <=> _`
       (pure_once_rewrite_tac o single) >>
     irule exprSimCopyTheory.copy_buffer_local_region_frame >>
     qexists `sm` >> simp[]) >>
  `ghost_kept_at lo ce es sa G0 tn0 s0 Gi tni` by
    (irule ghost_kept_at_trans >> qexistsl [`Gc`,`mid`,`u`,`sc`,`tnc`] >> simp[]) >>
  `s0.vs_alloca_next <= it.vs_alloca_next` by decide_tac >>
  `not_fresh_at si q` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists `sc` >> simp[]) >>
  `frames ==> wb_frame ce es fin sa s0 it /\
      (~expr_has_effect obj /\ ~expr_has_effect idx ==> pure_frame ce func es sa s0 it)` by
    (strip_tac >>
     qpat_assum `frames ==> wb_frame _ _ _ _ _ _ /\ _` drule >> strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon fin.storage_trace` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
     `wb_frame ce mid fin sc u it` by
       (pure_rewrite_tac[wb_frame_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     conj_tac
     >- (irule (INST_TYPE [alpha |-> ``:256``] exprSimWordArgsTheory.wb_frame_trans) >>
         simp[] >> conj_tac
         >- (qexistsl [`mid`,`sc`,`u`] >> simp[]) >>
         qexistsl [`Hmid`,`ctx`,`cx`,`func`] >> simp[]) >>
     strip_tac >>
     qpat_assum `wb_frame ce es mid sa s0 u`
       (assume_tac o cj 1 o REWRITE_RULE [wb_frame_def]) >>
     irule exprSimPropsTheory.pure_frame_trans >> simp[] >>
     qexistsl [`mid`,`sc`,`u`] >> simp[]) >>
  first_assum irule >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  goal_assum (drule_at (Pat `compile_expr ce ty obj sa = _`)) >>
  goal_assum (drule_at (Pat `compile_snapshot_vv ce T bvv sm = _`)) >>
  rpt (goal_assum (drule_at Any)) >> simp[contextTheory.mk_ptr_def] >>
  qexistsl [`t`,`u`] >> simp[contextTheory.mk_ptr_def] >>
  qpat_assum `vv_own _ _ _ _ _ _ _ (LocatedValue _ (mk_ptr _ _)) _`
    (ACCEPT_TAC o REWRITE_RULE [contextTheory.mk_ptr_def])
QED

Finalise subscript_copied_bind_caller_frames

Theorem subscript_copied_bind_full:
  !cx ann obj idx DF lo d PG tops ctx shadow_ctx func shadow_func ce env ty es et bd.
    (!s raw mid saved. eval_expr cx obj s = (INL raw,mid) /\
       read_result cx raw mid = (INL saved,mid) ==> body_expr_full_ok cx idx) /\
    body_expr_full_ok cx obj /\ body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shadow_ctx /\
    subscript_reads_base cx obj idx /\ copies_subscript_base ce obj idx /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_body_pre ce cx env (Subscript ann obj idx) es /\
    expr_type obj = ArrayT et bd /\ place_type ce obj = ValPT (ArrayT et bd) /\
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
         u.vs_inst_idx = LENGTH sc.cs_current_insts) /\
    (!st0 sa sm sc si sb bvv cvv vv iop dst s0 G0 tn0 gs raw mid saved s gc ic u
       key fin z Gi tni q w atv.
       eval_expr cx obj (es with gas_obs := gs) = (INL raw,mid) /\
       read_result cx raw mid = (INL saved,mid) /\
       bind (eval_expr cx idx) (read_result cx) (mid with gas_obs := ic) = (INL key,fin) /\
       compile_expr ce ty obj sa = (bvv,sm) /\
       compile_snapshot_vv ce T bvv sm = (cvv,sc) /\
       lower_value compile_expr ce ty idx sc = (iop,si) /\
       compile_expr ce ty (Subscript ann obj idx) sa = (vv,sb) /\
       cvv = LocatedValue (ArrayT et bd) (mk_ptr (Var q) LocMemory) /\
       vv = LocatedValue ann (mk_ptr dst LocMemory) /\
       compile_array_subscript (Var q) iop
         (case bd of Fixed _ => F | Dynamic _ => T)
         (case bd of Fixed n => n | Dynamic _ => 0)
         (word_scale LocMemory) (elem_size_in_location ce LocMemory et)
         (is_signed_type (expr_type idx))
         (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca LocMemory) si = (dst,sb) /\
       fn_has_code si sb func /\ fn_inst_ids_distinct func /\
       cs_extends sa sm /\ cs_extends sm sc /\ cs_extends sc si /\ cs_extends si sb /\
       local_ptrs_reserved ce si /\
       (!H. dead_lo_ok H (DF H) lo ce cx) /\
       (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
       (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
       return_buf_frame d ce sa s0 /\ storage_trace_domain cx st0 fin.storage_trace /\
       fin.gas_obs = [] /\ ~z.vs_halted /\ z.vs_current_bb = si.cs_current_bb /\
       z.vs_inst_idx = LENGTH si.cs_current_insts /\ alloca_history func z /\
       s0.vs_alloca_next <= z.vs_alloca_next /\
       (!H. valid_horizon cx st0 H fin.storage_trace ==>
          stmt_state_rel H ctx func ce cx es s0 /\
          vv_post H ctx func ce cx obj es sa sm s0 mid raw bvv s /\
          expr_post H ctx func ce cx idx mid sc si u fin key iop z /\
          ghost_inv_at (DF H) lo d ce cx fin Gi tni z) /\
       ghost_kept_at lo ce es sa G0 tn0 s0 Gi tni /\
       ptr_val_ok cx (post_value_type ce idx) key iop Gi tni z /\
       evaluate_type (get_tenv cx) (ArrayT et bd) = SOME atv /\
       val_wf atv saved /\ value_has_type atv saved /\
       lookup_var q z = SOME w /\ not_fresh_at si q /\ ptr_covers Gi tni q z (type_memory_size atv) /\
       (!m. mem_agree_outside tni.t_mem z.vs_memory m ==> val_in_memory atv saved (w2n w) m) /\
       vv_own ce cx (ArrayT et bd) sm sc fin (Value saved) cvv z ==>
       gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (cx_tops cx) cx st0
         (select_result cx (ArrayT et bd) (Value saved) (ValueSubscript key)) (fin,z,Gi,tni)
         (\H res ee G tn t. ?tv. res = INL tv /\
           vv_post H ctx func ce cx (Subscript ann obj idx) es sa sb s0 ee tv vv t /\
           vv_store_bound cx (post_value_type ce (Subscript ann obj idx))
             (lowered_value_type ce (Subscript ann obj idx)) ee tv vv t /\
           t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
           alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
           s0.vs_alloca_next <= t.vs_alloca_next /\ ghost_inv_at (DF H) lo d ce cx ee G tn t /\
           ptr_vv_ok cx (post_value_type ce (Subscript ann obj idx)) tv vv ee G tn t /\
           (!v. tv = Value v /\ ~is_word_type (post_value_type ce (Subscript ann obj idx)) /\
             ~is_bytestring_type (post_value_type ce (Subscript ann obj idx)) ==>
             vv_own ce cx (post_value_type ce (Subscript ann obj idx)) sa sb ee tv vv t /\
             (!t' p. vv = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
           (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
             ?v. read_result cx tv ee = (INL v,ee) /\
              !rt base. evaluate_type (get_tenv cx) (post_value_type ce (Subscript ann obj idx)) = SOME rt /\
                        eval_operand (vv_operand vv) t = SOME base ==>
                w2n base + type_memory_size rt <= lo /\
                (!m. mem_agree_outside tn.t_mem t.vs_memory m ==> val_in_memory rt v (w2n base) m)) /\
           (!t' op. vv = StackValue t' op /\ ~is_word_type (post_value_type ce (Subscript ann obj idx)) ==>
             ptr_buf_ok ce (Subscript ann obj idx) op G t) /\
           (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
             ptr_buf_ok ce (Subscript ann obj idx) p.ptr_operand G t) /\
           ghost_kept_at lo ce es sa G0 tn0 s0 G tn)
         (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
           (ctx_has_dalloca ctx ==> !t. r = Halt t ==> allocas_below_fmp t))) ==>
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) ce cx ty (Subscript ann obj idx) es
Proof
  rpt gen_tac >> strip_tac >>
  MATCH_MP_TAC (REWRITE_RULE [boolTheory.F_IMP, boolTheory.AND_CLAUSES]
                 (Q.SPEC `F` subscript_copied_bind_caller_frames)) >>
  qexistsl [`tops`,`env`,`et`,`bd`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >> first_assum MATCH_MP_TAC >>
  rpt (goal_assum (drule_at Any)) >> simp[]
QED
