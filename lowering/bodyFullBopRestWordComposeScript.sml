Theory bodyFullBopRestWordCompose
Ancestors
  bodyFullShadowBodyInv bodyFullSimProjection
  bodyFullBopRestWordLayout bodyFullBopRestWordEntry bodyFullBopRestWordPost
  bodyFullBopRestWordTail bodyFullPreds bodySimFull bodySim
  exprBopSimProps exprSimSource exprSimHypsDefs
  gasOutcomeFullCompose gasExemptCert gasStorage gasSummary vyperStorageTrace
  exprLowering loweringPosts bodyPtrDefs compileEnv vyperInterpreter
  vyperAST vyperState vyperStorageFootprint stmtSimProps
  bodyFullIfExpReach contextRawReachable unitMemInv

Theorem compile_rest_word_membership_full:
  !DF lo d PG tops ctx shadow_ctx func shadow_func cenv cx env ty ann bop e1 e2 bd es.
  (bop = In \/ bop = NotIn) /\ is_word_type (expr_type e1) /\
  expr_type e2 = ArrayT (expr_type e1) bd /\
  (!a t n elems. e2 <> Builtin a (MakeArray t n) elems) /\
  body_exprs_full_ok cx [e1;e2] /\ body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1;e2]) es ==>
  expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin ann (Bop bop) [e1;e2]) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_body_pre cenv cx env e1 es` by
    (irule expr_body_pre_builtin_arg >>
     conj_tac >- fs[expr_body_pre_def] >>
     qexistsl [`ann`, `[e1;e2]`, `Bop bop`, `es`] >> simp[]) >>
  `body_expr_full_ok cx e1` by
    (qpat_assum `body_exprs_full_ok cx [e1;e2]` mp_tac >>
     pure_once_rewrite_tac[body_exprs_full_ok_def] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e1) e1 es` by
    metis_tac[body_expr_full_ok_simulations] >>
  rewrite_tac[expr_sim_full_def] >> rpt gen_tac >> strip_tac >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    (mp_tac (Q.INST [`fn` |-> `func`, `ctx` |-> `ctx`, `tops` |-> `tops`,
        `cenv` |-> `cenv`, `cx` |-> `cx`] bodyFullIfExpReachTheory.body_inv_no_phi) >>
     simp[]) >>
  drule_all rest_word_full_compile_layout >> strip_tac >>
  `gas_admissible (bind (eval_expr cx e1) (read_result cx)) expr_res_ok es` by
    metis_tac[bop_first_admissible] >>
  qpat_x_assum `expr_sim_full _ _ _ _ e1 _` mp_tac >>
  rewrite_tac[expr_sim_full_def] >> disch_then drule_all >> strip_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ needleQ needleR` >>
  pure_once_rewrite_tac[REWRITE_RULE [ETA_AX] eval_expr_bop_bind] >>
  irule gas_outcome_full_bind_all_path >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
      qexistsl [`mid`, `t`, `v`] >> gvs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[])
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result])
  >~ [`storage_trace_frame _`]
  >- (gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >>
      conj_tac >- (fs[storage_trace_frame_def, exprBopSimDefsTheory.bop_result_def]) >>
      irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
  qexists `\H res ee G tn t. needleQ H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac
  >~ [`storage_trace_domain _ _ _`]
  >- suspend "after_needle" >>
  irule gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
  conj_tac >- simp[] >> simp[Abbr `needleR`] >>
  rpt strip_tac >> Cases_on `res` >- fs[exprSimDefsTheory.expr_exit_def] >>
  metis_tac[]
QED

Resume compile_rest_word_membership_full[after_needle]:
  rpt gen_tac >> strip_tac >> BETA_TAC >>
  Cases_on `res`
  >- (disj1_tac >> qexists `x` >> simp[] >>
      drule_all rest_word_full_second_entry >> strip_tac >>
      `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
        fs[storage_trace_domain_def] >>
      `needleQ (storage_trace_horizon mid.storage_trace) (INL x) mid G1 tn1 t /\
       ~t.vs_halted /\ mid.gas_obs = []` by metis_tac[] >>
      `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
        cenv cx (expr_type e2) e2 mid` by
        (`mid with gas_obs := [] = mid` by
           simp[evaluation_state_component_equality] >>
         metis_tac[body_expr_full_ok_simulations]) >>
      `gas_admissible (eval_expr cx e2) expr_vv_res_ok mid` by
        (qpat_assum `expr_body_pre _ _ _ e2 _`
           (mp_tac o MATCH_MP exprSimHypsTheory.expr_body_pre_vv_gas_admissible) >>
         simp[GSYM evaluation_state_component_equality]) >>
      `return_buf_frame d cenv s1 t` by
        (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
         qexistsl [`cenv`, `s0`, `sa`] >>
         fs[Abbr `needleQ`, expr_post_def]) >>
      `!H. valid_horizon cx st0 H mid.storage_trace ==>
        stmt_state_rel H ctx func cenv cx mid t /\
        storage_well_formed_on cx mid (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t` by
        (rpt strip_tac >>
         qpat_assum `!H. valid_horizon _ _ H _ ==> (_ H _ _ _ _ t)`
           (qspec_then `H` (drule_then (mp_tac o BETA_RULE))) >>
         simp[Abbr `needleQ`, expr_post_def]) >>
      `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
        (qpat_assum `needleQ (storage_trace_horizon _) _ _ _ _ t` mp_tac >>
         simp_tac bool_ss [Abbr `needleQ`] >>
         strip_tac >> first_assum ACCEPT_TAC) >>
      `!fn inst u. frag_reachable ctx func t fn inst u ==> dalloca_fmp_headroom inst u` by
        (qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _`
           (qspec_then `storage_trace_horizon mid.storage_trace`
             (drule_then assume_tac)) >>
         qpat_assum `gas_origin_ptr_path _ (s0,G0,tn0) marks (OK t,G1,tn1)`
           (fn path => ASSUME_TAC (MATCH_MP (REWRITE_RULE[GSYM AND_IMP_INTRO]
              bodyFullIfExpReachTheory.gas_origin_ptr_path_dalloca_fmp_headroom) path)) >>
         qpat_x_assum `(!bb. MEM bb func.fn_blocks ==> _) ==> _`
           (fn th => mp_tac th) >>
         impl_tac >- first_assum ACCEPT_TAC >>
         impl_tac >- first_assum ACCEPT_TAC >>
         disch_then ACCEPT_TAC) >>
      qpat_x_assum `expr_vv_sim_full _ _ _ _ _ _` mp_tac >>
      rewrite_tac[expr_vv_sim_full_def] >>
      disch_then (qspecl_then [`st0`, `s1`, `sm`, `sh1`, `shm`, `vv`, `t`, `G1`, `tn1`] mp_tac) >>
      (impl_tac >- (fs[Abbr `needleQ`] >> metis_tac[])) >> strip_tac >>
      qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ (eval_expr cx e2) _ arrayQ arrayR` >>
      pure_rewrite_tac[bind_assoc] >>
      irule gas_outcome_full_bind_all >> rpt conj_tac
      >~ [`gas_marked_exec _ _ _ _ _ _ _`]
      >- (rpt strip_tac >> irule gas_exempt_cert_bind_result >>
          qexistsl [`mid'`, `t'`, `v`] >> gvs[])
      >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
      >- (rpt strip_tac >> irule gas_exempt_cert_error_result >> simp[])
      >~ [`storage_trace_frame (eval_expr _ _)`]
      >- simp[evaluate_storage_trace_frame]
      >~ [`storage_trace_frame _`]
      >- (gen_tac >> BETA_TAC >> irule storage_trace_frame_bind_all >>
          simp[storage_trace_frame_read_result, storage_trace_frame_def,
               exprBopSimDefsTheory.bop_result_def] >> fs[]) >>
      qexists `\H res ee G tn u. arrayQ H res ee G tn u /\ ~u.vs_halted /\ ee.gas_obs = []` >>
      conj_tac
      >~ [`storage_trace_domain _ _ _`]
      >- suspend "after_array" >>
      irule gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ (eval_expr cx e2) _ _ _` (irule_at Any) >>
      conj_tac >- simp[] >> simp[Abbr `arrayR`, Abbr `needleR`] >>
      rpt strip_tac >> Cases_on `res` >- fs[exprSimDefsTheory.expr_exit_def] >>
      qexists `y` >> simp[] >>
      qpat_x_assum `expr_exit (INR y) r` mp_tac >>
      qpat_x_assum `halt_exit H cx ee (INR y) r` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >>
      simp[exprSimDefsTheory.halt_exit_def] >>
      metis_tac[stmtSimPropsTheory.expr_exit_INR_type]) >>
  disj2_tac >> qexists `y` >> simp[] >>
  rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> (_ H _ _ _ _ t)`
    (qspec_then `H` (drule_then (mp_tac o BETA_RULE))) >>
  simp[Abbr `needleQ`]
QED

Resume compile_rest_word_membership_full[after_array]:
  rpt gen_tac >> strip_tac >> BETA_TAC >>
  `valid_horizon cx st0 (storage_trace_horizon mid'.storage_trace) mid'.storage_trace` by
    fs[storage_trace_domain_def] >>
  `arrayQ (storage_trace_horizon mid'.storage_trace) res mid' G1' tn1' t' /\
   ~t'.vs_halted /\ mid'.gas_obs = []` by metis_tac[] >>
  `mid' with gas_obs := [] = mid'` by
    simp[evaluation_state_component_equality] >>
  Cases_on `res`
  >- (disj1_tac >> qexists `x'` >> simp[] >>
      `vv_holds cenv cx (post_value_type cenv e2) x' vv (mid' with gas_obs := []) t'` by
        (fs[Abbr `arrayQ`, vv_post_def] >>
         simp[GSYM evaluation_state_component_equality]) >>
      `ctx_has_dalloca ctx ==> allocas_below_fmp t'` by
        (qpat_assum `arrayQ (storage_trace_horizon _) _ _ _ _ _` mp_tac >>
         simp_tac bool_ss [Abbr `arrayQ`] >> strip_tac >>
         first_assum ACCEPT_TAC) >>
      drule_all rest_word_full_array_read >> strip_tac >>
      `!H. valid_horizon cx st0 H mid'.storage_trace ==>
        needleQ H (INL x) mid G1 tn1 t` by
        (rpt strip_tac >>
         `valid_horizon cx st0 H mid.storage_trace` by
           (qpat_assum `!tail. eval_expr cx e2 _ = _`
              (qspec_then `[]` mp_tac) >> strip_tac >>
            drule_at (Pos (el 2)) valid_horizon_frame >>
            simp[evaluate_storage_trace_frame]) >> metis_tac[]) >>
      `post_value_type cenv e1 = expr_type e1` by metis_tac[post_value_type_word] >>
      `eval_operand needle t = SOME (typed_val_to_w256 et x)` by
        (irule exprSimBopInLiteralWordTheory.literal_word_operand >>
         qexistsl [`cx`, `expr_type e1`] >>
         fs[Abbr `needleQ`, expr_post_def]) >>
      `(!z. needle = Var z ==> not_fresh_at s1 z) /\ (!l. needle <> Label l)` by
        metis_tac[expr_body_pre_lower_value_word_shape] >>
      `eval_operand needle t' = SOME (typed_val_to_w256 et x)` by
        (qpat_assum `arrayQ (storage_trace_horizon _) _ _ _ _ _` mp_tac >>
         simp_tac bool_ss [Abbr `arrayQ`, vv_post_def] >> strip_tac >>
         qpat_assum `!z. needle = Var z ==> _` mp_tac >>
         qpat_assum `!l. needle <> Label l` mp_tac >>
         qpat_assum `eval_operand needle t = _` mp_tac >>
         qpat_assum `!z w. not_fresh_at s1 z /\ _ ==> _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
         Cases_on `needle` >> fs[venomStateTheory.eval_operand_def] >> metis_tac[]) >>
      `op_prov G1 needle = NONE /\ op_taint tn1 needle = {}` by
        (qpat_assum `needleQ (storage_trace_horizon _) _ _ _ _ _` mp_tac >>
         simp_tac bool_ss [Abbr `needleQ`] >> strip_tac >>
         fs[ptr_val_ok_def]) >>
      `op_prov G1' needle = NONE /\ op_taint tn1' needle = {}` by
        (qpat_assum `arrayQ (storage_trace_horizon _) _ _ _ _ _` mp_tac >>
         simp_tac bool_ss [Abbr `arrayQ`] >> strip_tac >>
         qpat_assum `ghost_kept_at lo cenv mid s1 _ _ _ _ _` mp_tac >>
         qpat_assum `!z. needle = Var z ==> _` mp_tac >>
         qpat_assum `op_prov G1 needle = NONE` mp_tac >>
         qpat_assum `op_taint tn1 needle = {}` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         Cases_on `needle` >> simp[ghost_kept_at_def,
           ptrDisciplineTheory.op_prov_def, ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
      `?q Gt Tt. !H. valid_horizon cx st0 H mid'.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
          (t',G1',tn1') [] (OK q,Gt,Tt) /\
        membership_loop_frame sm G1' tn1' t' (Gt) (Tt) q /\
        ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
        q.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func q /\ t.vs_alloca_next <= q.vs_alloca_next /\
        vv_post H ctx func cenv cx e2 mid s1 sm t mid' x' vv q /\
        vv_store_bound cx (post_value_type cenv e2) (lowered_value_type cenv e2) mid' x' vv q /\
        ghost_inv_at (DF H) lo d cenv cx mid' (Gt) (Tt) q /\
        ptr_vv_ok cx (post_value_type cenv e2) x' vv mid' (Gt) (Tt) q /\
        (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
          ?val. read_result cx x' mid' = (INL val,mid') /\
            !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e2) = SOME rt /\
              eval_operand (vv_operand vv) q = SOME w ==>
              w2n w + type_memory_size rt <= lo /\
              (!mem. mem_agree_outside (Tt).t_mem q.vs_memory mem ==>
                val_in_memory rt val (w2n w) mem)) /\
        (!ty op. vv = StackValue ty op /\ ~is_word_type (post_value_type cenv e2) ==>
          ptr_buf_ok cenv e2 op (Gt) q) /\
        (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
          ptr_buf_ok cenv e2 p.ptr_operand (Gt) q) /\
        ghost_kept_at lo cenv mid s1 G1 tn1 t (Gt) (Tt) /\
        eval_operand needle q = SOME (typed_val_to_w256 et x) /\
        op_prov (Gt) needle = NONE /\ op_taint (Tt) needle = {} /\
        eval_operand op q = SOME (bool_to_word
          (if bop = In then evaluate_in_array (ArrayTV et bd) x av
           else ~evaluate_in_array (ArrayTV et bd) x av)) /\
        op_prov (Gt) op = NONE /\ op_taint (Tt) op = {}` by
        (ho_match_mp_tac rest_word_membership_tail_const_full >>
         qexistsl [`expr_type e1`, `pbd`] >>
         `t'.vs_current_bb = sm.cs_current_bb /\
          t'.vs_inst_idx = LENGTH sm.cs_current_insts` by
           (qpat_assum `arrayQ (storage_trace_horizon _) _ _ _ _ _` mp_tac >>
            simp_tac bool_ss [Abbr `arrayQ`] >> metis_tac[]) >>
         simp[] >>
         (conj_tac >- metis_tac[]) >> gen_tac >> disch_tac >>
         `arrayQ H (INL x') mid' G1' tn1' t'` by metis_tac[] >>
         qpat_x_assum `arrayQ H _ _ _ _ _` mp_tac >>
         simp_tac bool_ss [Abbr `arrayQ`] >> strip_tac >>
         qpat_x_assum `INL x' = INL tv`
           (SUBST_ALL_TAC o REWRITE_RULE [sumTheory.INL_11]) >>
         (conj_tac >-
           (qpat_assum `!tail. read_result cx x' _ = _` (qspec_then `[]` mp_tac) >>
            qpat_assum `mid' with gas_obs := [] = mid'`
              (fn th => rewrite_tac [th]))) >>
         rpt conj_tac >> metis_tac[arithmeticTheory.ADD_COMM]) >>
      `ann = BaseT BoolT` by
        (qpat_assum `expr_body_pre _ _ _ (Builtin _ _ _) _` mp_tac >>
         qpat_assum `bop = In \/ bop = NotIn` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[expr_body_pre_def, vyperTypeSystemTheory.well_typed_expr_def,
              vyperTypeSystemTheory.well_typed_builtin_app_def] >>
         Cases_on `bop` >> simp[vyperTypeSystemTheory.well_typed_binop_def] >> metis_tac[]) >>
      qmatch_asmsub_abbrev_tac `eval_operand op q = SOME (bool_to_word answer)` >>
      `evaluate_type (get_tenv cx) (ArrayT (expr_type e1) bd) = SOME (ArrayTV et bd)` by
        (qpat_assum `expr_body_pre _ _ _ e2 _`
           (mp_tac o MATCH_MP exprSimHypsTheory.expr_body_pre_type_evaluates) >>
         simp[vyperValueTheory.evaluate_type_def, AllCaseEqs()]) >>
      `!ee. bop_result cx ann bop [expr_type e1; ArrayT (expr_type e1) bd]
        x (ArrayV av) ee = INL (BoolV answer)` by
        (Cases_on `bop = In` >>
         gvs[exprBopSimDefsTheory.bop_result_def, Abbr `answer`,
             vyperContextTheory.evaluate_builtin_def, LET_THM,
         vyperValueOperationTheory.evaluate_binop_def,
         vyperValueOperationTheory.binop_negate_def]) >>
      irule gas_outcome_full_intro >>
      qexistsl [`Gt'`, `mid'`, `[]`, `OK q`, `INL (BoolV answer)`, `Tt`] >>
      conj_tac
      >- (gen_tac >> pure_rewrite_tac[gas_explicit_def, listTheory.MAP, listTheory.FLAT, listTheory.APPEND, bind_def] >>
          qpat_assum `!tail. read_result cx x' _ = _`
            (qspec_then `tail` (fn th => rewrite_tac [th])) >>
          qpat_assum `!ee. bop_result _ _ _ _ _ _ _ = _`
            (qspec_then `mid' with gas_obs := tail` (fn th => rewrite_tac [th])) >> simp[]) >>
      simp[] >> gen_tac >> disch_tac >> disj1_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
        (qspec_then `H` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
      `needleQ H (INL x) mid G1 tn1 t` by metis_tac[] >>
      qpat_x_assum `needleQ H _ _ _ _ _` mp_tac >>
      simp_tac bool_ss [Abbr `needleQ`] >> strip_tac >>
      `valid_horizon cx st0 H mid.storage_trace` by
        (qpat_assum `!tail. eval_expr cx e2 _ = _` (qspec_then `[]` mp_tac) >>
         strip_tac >> drule_at (Pos (el 2)) valid_horizon_frame >>
         simp[evaluate_storage_trace_frame]) >>
      `valid_horizon cx st0 H es.storage_trace` by
        (`storage_trace_frame (bind (eval_expr cx e1) (read_result cx))` by
           (irule storage_trace_frame_bind_all >>
            simp[evaluate_storage_trace_frame, storage_trace_frame_read_result]) >>
         qpat_assum `!tail. monad_bind (eval_expr cx e1) _ _ = _`
           (qspec_then `[]` mp_tac) >>
         strip_tac >> drule_at (Pos (el 2)) valid_horizon_frame >> simp[]) >>
      `stmt_state_rel H ctx func cenv cx es s0` by metis_tac[] >>
      qpat_x_assum `INL x = INL v`
        (SUBST_ALL_TAC o REWRITE_RULE [sumTheory.INL_11]) >>
      `ctx_has_dalloca ctx ==> allocas_below_fmp q` by
        (`allocas_below_fmp q <=> allocas_below_fmp t'` by
           (qpat_assum `membership_loop_frame sm _ _ t' _ _ q`
              (assume_tac o List.last o CONJUNCTS o
               REWRITE_RULE [bodyPtrBopInLoopContractTheory.membership_loop_frame_def]) >>
            qpat_x_assum `q = _`
              (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [th]))) >>
            simp[ptrDisciplineTheory.allocas_below_fmp_def]) >>
         PURE_ASM_REWRITE_TAC [] >> first_assum ACCEPT_TAC) >>
      qunabbrev_tac `answer` >>
      drule_all (SIMP_RULE bool_ss [post_value_type_def, expr_type_def] rest_word_full_parent_post) >>
      simp[post_value_type_def, expr_type_def]) >>
  fs[Abbr `arrayQ`]
QED

Finalise compile_rest_word_membership_full
