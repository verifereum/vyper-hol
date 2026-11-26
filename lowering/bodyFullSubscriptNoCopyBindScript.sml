(* The no-copy prefix reaches selection without assuming a base location
   or that the index preserves the source's scopes or immutables. *)
Theory bodyFullSubscriptNoCopyBind
Ancestors option[qualified,ignore_grammar] vyperTypeValues[qualified,ignore_grammar] vyperTyping[qualified,ignore_grammar] vyperValueOperation[qualified,ignore_grammar]
  bodyFullShadowBodyInv bodyFullToplevelVVStorage
  bodyFullPreds bodyFullSimProjection bodySimFull gasOutcomeFullCompose bodyFullSubscriptCapturedPlace
  stateRelProj exprSimSubscriptArraySuffix
  gasShadowCompileStmtHelpers bodyFullBuiltinWordPowCompose
  exprSimSubscriptArrayFramed exprSimSubscriptArrayOrigin exprSimSubscriptArraySource exprSimHyps exprSimSource
  exprOperandVar exprLoweringProps exprSimUnwrap fragExec
  exprSimVVFrame exprSimProps exprSimExtract32Post
  gasShadowCompile gasShadowState gasShadow gasExemptCert
  vyperStorageTrace vyperStorageFootprint
  bodyPtrDefs loweringPosts compileEnv vyperInterpreter vyperState vyperAST
  bodyFullIfExpReach

Theorem subscript_nocopy_bind_full:
  !cx ann e1 e2 DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es et bd.
    (!s raw t. eval_expr cx e1 s = (INL raw,t) ==> body_expr_full_ok cx e2) /\
    body_expr_full_ok cx e1 /\ body_inv tops ctx cenv cx /\ shadow_body_inv tops ctx shadow_ctx /\
    ~subscript_reads_base cx e1 e2 /\ ~copies_subscript_base cenv e1 e2 /\
    body_const_cells_agree [(NONE,tops)] cx env es /\
    expr_body_pre cenv cx env (Subscript ann e1 e2) es /\
    expr_type e1 = ArrayT et bd /\ place_type cenv e1 = ValPT (ArrayT et bd) /\
    post_value_type cenv e1 = expr_type e1 /\
    (!st0 sa sm st2 sb bvv iop dst loc s0 G0 tn0
       mid raw s G1 tn1 gs1 fin key it Gi tni gs2.
      ~(?n id path. bd = Fixed n /\ raw = PlaceR (MemoryPlace id path) /\ base_from_pop e1) /\
      compile_expr cenv ty e1 sa = (bvv,sm) /\
      lower_value compile_expr cenv ty e2 sm = (iop,st2) /\
      loc = (case vv_location bvv of SOME l => l | NONE => LocMemory) /\
      compile_array_subscript (vv_operand bvv) iop
        (case bd of Fixed _ => F | Dynamic _ => T)
        (case bd of Fixed n => n | Dynamic _ => 0)
        (word_scale loc) (elem_size_in_location cenv loc et)
        (is_signed_type (expr_type e2))
        (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca loc) st2 = (dst,sb) /\
      fn_has_code sa sb func /\ fn_has_code st2 sb func /\
      fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
      local_ptrs_reserved cenv st2 /\
      sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
      sm.cs_next_var <= st2.cs_next_var /\ sm.cs_next_id <= st2.cs_next_id /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
      eval_expr cx e1 (es with gas_obs := gs1) = (INL raw,mid) /\
      bind (eval_expr cx e2) (read_result cx) (mid with gas_obs := gs2) = (INL key,fin) /\
      storage_trace_domain cx st0 fin.storage_trace /\ mid.gas_obs = [] /\ fin.gas_obs = [] /\
      ~s.vs_halted /\ ~it.vs_halted /\
      s.vs_current_bb = sm.cs_current_bb /\ s.vs_inst_idx = LENGTH sm.cs_current_insts /\
      it.vs_current_bb = st2.cs_current_bb /\ it.vs_inst_idx = LENGTH st2.cs_current_insts /\
      alloca_history func s /\ alloca_history func it /\
      s0.vs_alloca_next <= s.vs_alloca_next /\ s.vs_alloca_next <= it.vs_alloca_next /\
      vv_store_bound cx (post_value_type cenv e1) (lowered_value_type cenv e1) mid raw bvv s /\
      ptr_vv_ok cx (post_value_type cenv e1) raw bvv mid G1 tn1 s /\
      (!v. raw = Value v /\ ~is_word_type (post_value_type cenv e1) /\
           ~is_bytestring_type (post_value_type cenv e1) ==>
           vv_own cenv cx (post_value_type cenv e1) sa sm mid raw bvv s /\
           (!t p. bvv = LocatedValue t p ==> p.ptr_location = LocMemory)) /\
      (cenv.ce_is_ctor /\ vv_location bvv = SOME LocCode ==>
       ?v. read_result cx raw mid = (INL v,mid) /\
           !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e1) = SOME rt /\
                  eval_operand (vv_operand bvv) s = SOME w ==>
                  w2n w + type_memory_size rt <= lo /\
                  (!mem. mem_agree_outside tn1.t_mem s.vs_memory mem ==>
                         val_in_memory rt v (w2n w) mem)) /\
      (!t op. bvv = StackValue t op /\ ~is_word_type (post_value_type cenv e1) ==>
              ptr_buf_ok cenv e1 op G1 s) /\
      (!t p. bvv = LocatedValue t p /\ p.ptr_location = LocMemory ==>
             ptr_buf_ok cenv e1 p.ptr_operand G1 s) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
      expr_store_bound cx (post_value_type cenv e2) key iop it /\
      ptr_val_ok cx (post_value_type cenv e2) key iop Gi tni it /\
      (~is_word_type (post_value_type cenv e2) ==> ptr_buf_ok cenv e2 iop Gi it) /\
      ghost_kept_at lo cenv mid sm G1 tn1 s Gi tni /\
      (!H. dead_lo_ok H (DF H) lo cenv cx) /\
      (!H. valid_horizon cx st0 H fin.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es s0 /\
        storage_well_formed_on cx es (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0 /\
        vv_post H ctx func cenv cx e1 es sa sm s0 mid raw bvv s /\
        ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 s /\
        expr_post H ctx func cenv cx e2 mid sm st2 s fin key iop it /\
        ghost_inv_at (DF H) lo d cenv cx fin Gi tni it) ==>
      gas_outcome_full
        (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG) (cx_tops cx) cx st0
        (select_result cx (ArrayT et bd) raw (ValueSubscript key)) (fin,it,Gi,tni)
        (\H res ee G tn t. ?tv. res = INL tv /\
          vv_post H ctx func cenv cx (Subscript ann e1 e2) es sa sb s0 ee tv (LocatedValue ann (mk_ptr dst loc)) t /\
          vv_store_bound cx (post_value_type cenv (Subscript ann e1 e2))
            (lowered_value_type cenv (Subscript ann e1 e2)) ee tv (LocatedValue ann (mk_ptr dst loc)) t /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          alloca_history func t /\
          (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
          s0.vs_alloca_next <= t.vs_alloca_next /\
          ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
          ptr_vv_ok cx (post_value_type cenv (Subscript ann e1 e2)) tv (LocatedValue ann (mk_ptr dst loc)) ee G tn t /\
          (!v. tv = Value v /\ ~is_word_type (post_value_type cenv (Subscript ann e1 e2)) /\
               ~is_bytestring_type (post_value_type cenv (Subscript ann e1 e2)) ==>
               vv_own cenv cx (post_value_type cenv (Subscript ann e1 e2)) sa sb ee tv (LocatedValue ann (mk_ptr dst loc)) t /\
               (!t' p. (LocatedValue ann (mk_ptr dst loc)) = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
          (cenv.ce_is_ctor /\ vv_location (LocatedValue ann (mk_ptr dst loc)) = SOME LocCode ==>
           ?val. read_result cx tv ee = (INL val,ee) /\
                 !rt w. evaluate_type (get_tenv cx) (post_value_type cenv (Subscript ann e1 e2)) =
                        SOME rt /\ eval_operand (vv_operand (LocatedValue ann (mk_ptr dst loc))) t = SOME w ==>
                        w2n w + type_memory_size rt <= lo /\
                        (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
                               val_in_memory rt val (w2n w) mem)) /\
          (!t' op. (LocatedValue ann (mk_ptr dst loc)) = StackValue t' op /\
                   ~is_word_type (post_value_type cenv (Subscript ann e1 e2)) ==>
                   ptr_buf_ok cenv (Subscript ann e1 e2) op G t) /\
          (!t' p. (LocatedValue ann (mk_ptr dst loc)) = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
                  ptr_buf_ok cenv (Subscript ann e1 e2) p.ptr_operand G t) /\
          ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
        (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
           (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))) ==>
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Subscript ann e1 e2) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac expr_body_pre_array_subscript_base_typed >>
  drule_all_then strip_assume_tac expr_body_pre_array_subscript_base_admissible >>
  `~array_slot_base cenv e1 ==> expr_body_pre cenv cx env e1 es` by
    metis_tac[expr_body_pre_array_subscript_base] >>
  (* A storage or transient array base has no precondition of its own: its
     simulation needs only the invariant and typing. *)
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty e1 es` by
    (Cases_on `array_slot_base cenv e1`
     >- metis_tac[toplevel_slot_base_vv_full,
                  expr_body_pre_array_subscript_slot_base] >>
     `expr_body_pre cenv cx env e1 es` by fs[] >>
     irule (cj 2 body_expr_full_ok_simulations) >>
     simp[] >> qexistsl_tac [`env`, `tops`] >> simp[]) >>
  simp[expr_vv_sim_full_def] >> rpt gen_tac >> strip_tac >>
  drule_all compile_expr_array_subscript >> strip_tac >>
  rename1 `compile_expr cenv ty e1 sa = (bvv,sm)` >>
  drule compile_expr_extends >> strip_tac >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  `cs_extends st2 sb` by
    (`ci_mono st2 sb` suffices_by simp[ci_mono_def] >>
     qpat_assum `compile_array_subscript _ _ _ _ _ _ _ _ st2 = _`
       (SUBST1_TAC o SYM o PURE_REWRITE_RULE [pairTheory.SND] o Q.AP_TERM `SND`) >>
     irule ci_mono_compile_array_subscript >> simp[ci_mono_compile_ptr_load]) >>
  `cs_extends sm sb` by
    (irule cs_extends_trans >> qexists_tac `st2` >> simp[]) >>
  drule_all fn_has_code_split >> strip_tac >>
  `?shadow_sm. compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e1) shadow_sa =
      (bvv,shadow_sm) /\ gas_shadow_state sm shadow_sm` by
    (`gas_shadow_compiles (compile_expr cenv ty e1)
         (compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e1))` by
       irule gas_shadow_stmt_compile_expr_env >>
     pop_assum (qspecl_then [`sa`, `shadow_sa`] mp_tac o
       REWRITE_RULE [gas_shadow_compiles_def]) >>
     Cases_on `compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e1) shadow_sa` >>
     simp[]) >>
  `cs_extends shadow_sa shadow_sm /\ cs_extends shadow_sm shadow_sb` by
    suspend "shadow_extends" >>
  `fn_has_code shadow_sa shadow_sm shadow_func` by
    (drule_all fn_has_code_split >> simp[]) >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ e1 _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_full_def]) >>
  disch_then (qspecl_then [`st0`, `sa`, `sm`, `shadow_sa`, `shadow_sm`,
                          `bvv`, `s0`, `G0`, `tn0`] mp_tac) >>
  (impl_tac >- (simp[] >> gvs[])) >> strip_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ baseQ baseR` >>
  suspend "bind_base"
QED

Resume subscript_nocopy_bind_full[shadow_extends]:
  reverse conj_tac
  >- (qpat_x_assum `compile_expr _ _ (gas_shadow_expr (Subscript _ _ _)) _ = _` mp_tac >>
      simp[gas_shadow_expr_def] >> strip_tac >>
      qpat_x_assum `compile_expr _ _ (Subscript _ (gas_shadow_expr e1) _) _ = _`
        (mp_then Any mp_tac compile_expr_array_subscript) >>
      fs[exprLoweringTheory.copies_subscript_base_def] >> strip_tac >> gvs[] >>
      rename1 `lower_value _ _ _ (gas_shadow_expr e2) shadow_sm = (_,shadow_st2)` >>
      qpat_assum `lower_value _ _ _ (gas_shadow_expr e2) _ = _`
        (mp_then Any strip_assume_tac (cj 2 compile_expr_grows)) >>
      `cs_extends shadow_st2 shadow_sb` by
        (`ci_mono shadow_st2 shadow_sb` suffices_by simp[ci_mono_def] >>
         qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ shadow_st2 = _`
           (SUBST1_TAC o SYM o PURE_REWRITE_RULE [pairTheory.SND] o Q.AP_TERM `SND`) >>
         irule ci_mono_compile_array_subscript >> simp[ci_mono_compile_ptr_load]) >>
      irule cs_extends_trans >> goal_assum (drule_at Any) >> simp[]) >>
  drule compile_expr_extends >> simp[]
QED

Resume subscript_nocopy_bind_full[bind_base]:
  qpat_assum `~subscript_reads_base _ _ _` (fn th =>
    pure_once_rewrite_tac[MATCH_MP eval_expr_subscript_bind th]) >>
  irule gas_outcome_full_bind_all_path >>
  `!res : eval_result + exception. !r.
     (?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) r) <=> expr_exit res r` by
    (Cases >> simp[]) >> simp[] >>
  rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_result >>
      qexistsl_tac [`mid`, `t`, `v`] >> fs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_result >> simp[])
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[(cj 5 evaluate_storage_trace_frame)]
  >- (gen_tac >> irule storage_trace_frame_bind_all >>
      simp[storage_trace_frame_select] >> irule storage_trace_frame_bind_all >>
      simp[(cj 5 evaluate_storage_trace_frame), storage_trace_frame_read_result]) >>
  qexists_tac `\H res ee G tn t. baseQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac >~ [`storage_trace_domain _ _ _`] >- suspend "after_base" >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  conj_tac >- simp[Abbr `baseR`] >>
  simp[Abbr `baseQ`, Abbr `baseR`] >> metis_tac[]
QED

Resume subscript_nocopy_bind_full[after_base]:
  qx_genl_tac [`marks`, `res`, `mid`, `G1`, `tn1`, `s`] >>
  strip_tac >> fs[] >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    gvs[storage_trace_domain_def] >>
  qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then assume_tac)) >>
  `baseQ (storage_trace_horizon mid.storage_trace) res mid G1 tn1 s` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> baseQ H _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >> simp[]) >>
  qpat_x_assum `baseQ _ _ _ _ _ _` mp_tac >>
  simp[Abbr `baseQ`, NoAsms] >> strip_tac >> gvs[] >>
  `~s.vs_halted /\ mid.gas_obs = []` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _` drule >> simp[]) >>
  `eval_expr cx e1 (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL tv,mid)` by
    (`mid with gas_obs := [] = mid` by simp[evaluation_state_component_equality] >>
     qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` mp_tac) >>
     qpat_assum `mid with gas_obs := [] = mid` (fn th => simp[NoAsms, th])) >>
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (irule body_const_cells_agree_expr >>
     goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >> simp[]) >>
  `expr_body_pre cenv cx env e2 mid` by
    (irule expr_body_pre_array_subscript_index_after_base >>
     goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >> simp[] >>
     qexists_tac `ann` >> simp[]) >>
  `body_expr_full_ok cx e2` by metis_tac[] >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty e2 mid` by
    (irule (cj 1 body_expr_full_ok_simulations) >>
     simp[] >> qexistsl_tac [`env`, `tops`] >> simp[]) >>
  `?shadow_st2. lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e2)
      shadow_sm = (iop,shadow_st2) /\ gas_shadow_state st2 shadow_st2` by
    (`gas_shadow_compiles (lower_value compile_expr cenv ty e2)
       (lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e2))` by
       irule gas_shadow_stmt_lower_value_env >>
     pop_assum (qspecl_then [`sm`, `shadow_sm`] mp_tac o
       REWRITE_RULE [gas_shadow_compiles_def]) >>
     Cases_on `lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e2) shadow_sm` >>
     simp[]) >>
  `cs_extends shadow_sm shadow_st2 /\ cs_extends shadow_st2 shadow_sb` by
    (`cs_extends shadow_sm shadow_st2` by
       (qpat_assum `lower_value _ _ _ _ shadow_sm = _`
          (mp_then Any mp_tac (cj 2 compile_expr_grows)) >> simp[]) >>
     qpat_assum `compile_expr _ _ (gas_shadow_expr (Subscript _ _ _)) _ = _` mp_tac >>
     simp[gas_shadow_expr_def, NoAsms] >> strip_tac >>
     drule compile_expr_array_subscript >>
     fs[exprLoweringTheory.copies_subscript_base_def] >> strip_tac >> gvs[] >>
     `ci_mono shadow_st2 shadow_sb` suffices_by simp[ci_mono_def] >>
     qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ shadow_st2 = _`
       (SUBST1_TAC o SYM o PURE_REWRITE_RULE [pairTheory.SND] o Q.AP_TERM `SND`) >>
     irule ci_mono_compile_array_subscript >> simp[ci_mono_compile_ptr_load]) >>
  `fn_has_code sm st2 func /\ fn_has_code shadow_sm shadow_st2 shadow_func` by
    metis_tac[fn_has_code_split] >>
  `vv_post (storage_trace_horizon mid.storage_trace) ctx func cenv cx e1
      es sa sm s0 mid tv bvv s` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _`
       (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >> simp[]) >>
  `return_buf_frame d cenv sm s` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`cenv`, `s0`, `sa`] >> fs[vv_post_def]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  qpat_x_assum `expr_sim_full _ _ _ _ e2 _`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`, `sm`, `st2`, `shadow_sm`, `shadow_st2`,
                          `iop`, `s`, `G1`, `tn1`] mp_tac) >>
  (impl_tac >-
    (simp[] >> rpt conj_tac
     >~ [`local_ptrs_reserved _ _`] >- metis_tac[local_ptrs_reserved_next_var]
     >~ [`gas_admissible _ _ _`] >- metis_tac[expr_body_pre_gas_admissible]
     >- (`!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
           metis_tac[bodyFullIfExpReachTheory.body_inv_no_phi] >>
         qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) marks (OK s,G1,tn1)` (fn path =>
           qpat_assum `!bb. MEM bb func.fn_blocks ==> phi_prefix_length _ = _` (fn no_phi =>
           qpat_assum `!fn i v. frag_reachable ctx func s0 fn i v ==> _`
             (ACCEPT_TAC o MATCH_MP bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom o
              CONJ path o CONJ no_phi))))
     >> rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (drule_then strip_assume_tac) >> fs[vv_post_def])) >>
  strip_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ indexQ indexR` >>
  irule gas_outcome_full_bind_all >> simp[] >> rpt conj_tac
  >~ [`storage_trace_frame (bind _ _)`]
  >- simp[storage_trace_frame_bind_all, (cj 5 evaluate_storage_trace_frame), storage_trace_frame_read_result]
  >~ [`storage_trace_frame (select_result _ _ _ _)`]
  >- simp[storage_trace_frame_select]
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
      qexistsl_tac [`mid'`, `t`, `v`] >> fs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[]) >>
  qexists_tac `\H res ee G tn t. indexQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac >- suspend "selection" >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ indexQ indexR` (irule_at Any) >>
  conj_tac >- simp[Abbr `indexR`, Abbr `baseR`] >>
  simp[Abbr `indexQ`, Abbr `indexR`, Abbr `baseR`] >>
  rpt gen_tac >> Cases_on `res` >> simp[exprSimDefsTheory.expr_exit_def] >>
  strip_tac >> conj_tac
  >- (irule exprSimHashTheory.expr_exit_INR_cast >> first_assum ACCEPT_TAC) >>
  gvs[exprSimDefsTheory.halt_exit_def]
QED

Resume subscript_nocopy_bind_full[selection]:
  qx_genl_tac [`imarks`, `ires`, `fin`, `Gi`, `tni`, `it`] >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) fin.storage_trace` by
    gvs[storage_trace_domain_def] >>
  `indexQ (storage_trace_horizon fin.storage_trace) ires fin Gi tni it /\
   ~it.vs_halted /\ fin.gas_obs = []` by metis_tac[] >>
  qpat_x_assum `indexQ _ _ _ _ _ _` mp_tac >>
  simp[Abbr `indexQ`, NoAsms] >> strip_tac >> gvs[] >>
  `bind (eval_expr cx e2) (read_result cx)
      (mid with gas_obs := gas_explicit imarks s.vs_gas_readings) = (INL v,fin)` by
    (`fin with gas_obs := [] = fin` by simp[evaluation_state_component_equality] >>
     qpat_assum `!tail. bind _ _ _ = _` (qspec_then `[]` mp_tac) >>
     qpat_assum `fin with gas_obs := [] = fin` (fn th => simp[NoAsms, th])) >>
  `?X. mid.storage_trace = es.storage_trace ++ X` by
    (qpat_assum `eval_expr cx e1 _ = (INL tv,mid)`
       (mp_then Any mp_tac storage_trace_frame_prefix) >>
     simp[(cj 5 evaluate_storage_trace_frame)]) >>
  `?Y. fin.storage_trace = mid.storage_trace ++ Y` by
    (qpat_assum `bind _ _ _ = (INL v,fin)`
       (mp_then Any mp_tac storage_trace_frame_prefix) >>
     simp[storage_trace_frame_bind_all, (cj 5 evaluate_storage_trace_frame),
          storage_trace_frame_read_result]) >>
  `!H. valid_horizon cx st0 H fin.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es s0 /\
       storage_well_formed_on cx es (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0 /\
       vv_post H ctx func cenv cx e1 es sa sm s0 mid tv bvv s /\
       ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 s /\
       expr_post H ctx func cenv cx e2 mid sm st2 s fin v iop it /\
       ghost_inv_at (DF H) lo d cenv cx fin Gi tni it` by
    suspend "horizon" >>
  Cases_on `?n id path. bd = Fixed n /\ tv = PlaceR (MemoryPlace id path) /\ base_from_pop e1`
  >- suspend "fixed_pop" >>
  suspend "other_selection"
QED

Resume subscript_nocopy_bind_full[horizon]:
  qx_gen_tac `H` >> strip_tac >>
  `valid_horizon cx st0 H mid.storage_trace` by
    (irule gasOutcomeFullTheory.valid_horizon_append >>
     qexists_tac `Y` >> metis_tac[]) >>
  `valid_horizon cx st0 H es.storage_trace` by
    (irule gasOutcomeFullTheory.valid_horizon_append >>
     qexists_tac `X` >> metis_tac[]) >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  (metis_tac[Abbr `indexQ`])
QED

Resume subscript_nocopy_bind_full[other_selection]:
  `local_ptrs_reserved cenv sm /\ local_ptrs_reserved cenv st2` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `fn_has_code st2 sb func` by metis_tac[fn_has_code_split] >>
  first_x_assum (irule o REWRITE_RULE [LET_THM]) >> simp[] >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`G1`, `gas_explicit marks s0.vs_gas_readings`,
    `gas_explicit imarks s.vs_gas_readings`, `mid`, `s`, `tn1`] >>
  simp[] >> rpt strip_tac >> metis_tac[]
QED

Resume subscript_nocopy_bind_full[fixed_pop]:
  qpat_x_assum `?n id path. _` strip_assume_tac >> gvs[] >>
  `expr_body_pre cenv cx env e1 es` by
    metis_tac[base_from_pop_not_array_slot_base] >>
  `ann = et` by
    (`well_typed_expr env (Subscript ann e1 e2) /\ well_typed_expr env e1` by
       metis_tac[exprSimHypsDefsTheory.expr_body_pre_def] >>
     drule_all vyperTypeConstantFoldTheory.constant_subscript_type_ok >>
     simp[vyperTypeSystemTheory.subscript_type_ok_def]) >>
  `?p t. bvv = LocatedValue t p /\ p.ptr_location = LocMemory` by
    (`vv_post (storage_trace_horizon mid.storage_trace) ctx func cenv cx e1
         es sa sm s0 mid (PlaceR (MemoryPlace id path)) bvv s` by metis_tac[] >>
     pop_assum (strip_assume_tac o REWRITE_RULE [vv_post_def]) >>
     Cases_on `bvv`
     >- gvs[vv_at_def, is_word_type_def] >>
     gvs[vv_place_ptr_def]) >>
  gvs[contextTheory.vv_location_def, contextTheory.vv_operand_def] >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sm x` by
    (qpat_assum `compile_expr cenv ty e1 sa = _`
       (mp_then Any mp_tac (cj 1 exprOperandVarTheory.compiler_compile_var)) >>
     simp[contextTheory.vv_operand_def]) >>
  `!l. p.ptr_operand <> Label l` by
    (qpat_assum `compile_expr cenv ty e1 sa = _`
       (mp_then Any mp_tac compile_array_pointer_not_label) >>
     disch_then irule >> simp[] >> qexists_tac `env` >>
     metis_tac[exprSimHypsDefsTheory.expr_body_pre_def, exprSimHypsDefsTheory.expr_sim_inv_def]) >>
  `?etv. evaluate_type (get_tenv cx) (ArrayT ann (Fixed n)) = SOME (ArrayTV etv (Fixed n))` by
    ((qpat_assum `expr_body_pre cenv cx env e1 es`
       (mp_then Any mp_tac expr_body_pre_type_evaluates) >>
     simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
     drule vyperTypeValuesTheory.evaluate_type_ArrayT_cases >> simp[] >> (metis_tac[optionTheory.IS_SOME_EXISTS, expr_body_pre_type_evaluates, vyperTypeValuesTheory.evaluate_type_ArrayT_cases]))) >>
  `local_ptrs_reserved cenv sm /\ fn_has_code st2 sb func` by
    metis_tac[local_ptrs_reserved_next_var, fn_has_code_split] >>
  simp[Abbr `baseR`, expr_type_def, contextTheory.mk_ptr_def, contextTheory.vv_location_def] >>
  irule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
  irule_at Any (SRULE [contextTheory.mk_ptr_def, contextTheory.vv_location_def,
    contextTheory.vv_operand_def, post_value_type_def, expr_type_def]
    subscript_captured_fixed_outcome) >>
  qpat_assum `eval_expr cx e1 (_ with gas_obs := _) = (INL _,mid)` (irule_at Any) >>
  qpat_assum `bind (eval_expr cx e2) _ (_ with gas_obs := _) = (INL v,fin)` (irule_at Any) >>
  simp[expr_body_pre_gas_obs, elem_size_in_location_def,
       stmt_state_rel_start_gas_obs, vv_post_initial_gas,
       extract32_expr_post_start_gas_obs] >>
  qexistsl [`word_scale LocMemory`, `ty`, `tn0`, `tn1`, `t`, `st2`, `sm`, `sb`,
    `sa`, `s`, `s0`, `p`, `compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory`,
    `iop`, `env`, `dst`, `d`, `cenv`, `G0`, `G1`] >>
  simp[] >>
  qpat_assum `compile_array_subscript _ _ _ _ _ _ _ _ st2 = _`
    (mp_tac o SRULE [elem_size_in_location_def, is_slot_addressed_def]) >>
  simp[] >>
  rpt strip_tac >> first_assum (drule_then strip_assume_tac)
  >- (qpat_assum `ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> simp[ghost_kept_at_def] >> metis_tac[])
  >- (qpat_assum `ghost_kept_at lo cenv mid sm G1 tn1 s Gi tni` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> simp[ghost_kept_at_def] >> metis_tac[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G' tn'` by
    (qpat_assum `ghost_kept_at lo cenv (es with gas_obs := _) sa G0 tn0 s0 G' tn'` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[ghost_kept_at_def] >> metis_tac[]) >>
  qexists_tac `r` >> simp[]
QED

Finalise subscript_nocopy_bind_full
