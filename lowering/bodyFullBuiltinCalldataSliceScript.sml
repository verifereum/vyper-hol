(* The calldata slice uses its scalar child's joint execution. *)
Theory bodyFullBuiltinCalldataSlice
Ancestors exprSimDefs[qualified,ignore_grammar]
  bodyFullBuiltinBytestringCalldataCase bodyFullBuiltinBytestringCalldataRun
  bodyFullBuiltinBytestringCalldataAbort
  bodyPtrBytestringBuiltinsExternalSlice bodyFullPreds bodySimFull
  bodyPtrBytestringBuiltinsWindowGhost wordArgsPtr ptrDiscipline localPtrsProps
  reasonCodeResourcesPtr bodyPtrAttributeFields
  valueEncodingDefs vyperValue vyperTypeInvariants exprSimProps exprSimMemDefs
  vyperEvalExprPreservesScopesDom
  bodyFullOfVV bodyFullExprGeneric exprSimCalldataSlice exprSimSource exprSimHyps exprSimHypsDefs exprSimHash
  exprSimUnopComposeProps gasOutcomeFullCompose gasOutcomeFull gasExemptCert
  gasShadowCompileStmtHelpers gasShadowState gasShadow
  exprLowering exprLoweringProps exprSimWordArgs compileEnv context fragExec
  vyperStorageTrace vyperStorageFootprint loweringPosts bodyPtrDefs loweringStateRelDefs
  venomInst venomState
  vyperInterpreter vyperState vyperAST vyperContext list words arithmetic
Libs
  pairLib

Theorem calldata_slice_vv_sim_full:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty ann n args es.
    (builtin_args_length_ok (CalldataSlice n) (LENGTH args) ==>
      body_exprs_full_ok cx args) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin ann (CalldataSlice n) args) es ==>
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin ann (CalldataSlice n) args) es
Proof
  rpt gen_tac >> strip_tac >>
  drule_all calldata_slice_body_operand_full >>
  disch_then (qspecl_then [`shadow_func`,`shadow_ctx`,`lo`,`func`,`d`,`PG`,`DF`]
    strip_assume_tac) >> gvs[] >>
  `post_value_type cenv e = expr_type e` by
    (irule post_value_type_word >> simp[is_word_type_def]) >>
  rewrite_tac[expr_vv_sim_full_def] >> rpt gen_tac >> strip_tac >>
  `?x sm out.
    lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
    compile_slice_calldata x (Lit (n2w n))
      (type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))) sm = (out,sb) /\
    vv = LocatedValue (BaseT (BytesT (Dynamic n))) (mk_ptr out LocMemory)` by
    (qpat_x_assum `compile_expr _ _ (Builtin _ (CalldataSlice n) _) sa = _` mp_tac >>
     simp[compile_calldata_slice_parts] >>
     Cases_on `lower_value compile_expr cenv (expr_type e) e sa` >>
     rename1 `lower_value compile_expr cenv (expr_type e) e sa = (x,sm)` >>
     Cases_on `compile_slice_calldata x (Lit (n2w n))
       (type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))) sm` >>
     gvs[as_ptr_val_def,comp_return_def]) >>
  qpat_x_assum `vv = _` SUBST_ALL_TAC >>
  `?sx ss. lower_value compile_expr cenv (expr_type e)
     (gas_shadow_expr e) shadow_sa = (sx,ss)` by metis_tac[pairTheory.PAIR] >>
  `sx = x /\ gas_shadow_state sm ss` by
    (mp_tac (Q.INST [`cenv` |-> `cenv`, `ty` |-> `expr_type e`, `e` |-> `e`]
      gas_shadow_stmt_lower_value) >> rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> simp[]) >>
  qpat_x_assum `sx = x` SUBST_ALL_TAC >>
  `compile_slice_calldata x (Lit (n2w n))
      (type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))) ss = (out,shadow_sb)` by
    (qpat_x_assum `compile_expr _ _ (gas_shadow_expr (Builtin _ _ _)) _ = _` mp_tac >>
     simp[gas_shadow_expr_def,gas_shadow_builtin_def,compile_calldata_slice_parts] >>
     Cases_on `compile_slice_calldata x (Lit (n2w n))
       (type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))) ss` >>
     gvs[as_ptr_val_def,comp_return_def,contextTheory.mk_ptr_def]) >>
  `cs_extends sm sb` by
    (qpat_assum `compile_slice_calldata _ _ _ sm = _`
       (mp_then Any strip_assume_tac compile_slice_calldata_stages) >>
     metis_tac[cs_extends_trans]) >>
  `cs_extends ss shadow_sb` by
    (qpat_assum `compile_slice_calldata _ _ _ ss = _`
       (mp_then Any strip_assume_tac compile_slice_calldata_stages) >>
     metis_tac[cs_extends_trans]) >>
  `cs_extends sa sm /\ cs_extends shadow_sa ss` by
    metis_tac[cj 2 compile_expr_grows] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func /\
   fn_has_code shadow_sa ss shadow_func` by
    metis_tac[fn_has_code_split] >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  `lower_value compile_expr cenv (BaseT (UintT 256)) e sa = (x,sm)` by
    (qpat_assum `expr_type e = _` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  `lower_value compile_expr cenv (BaseT (UintT 256))
     (gas_shadow_expr e) shadow_sa = (x,ss)` by
    (qpat_assum `expr_type e = _` (SUBST1_TAC o SYM) >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `expr_sim_full _ _ _ _ e es`
    (mp_tac o REWRITE_RULE [expr_sim_full_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`ss`,`x`,`s0`,`G0`,`tn0`]
    mp_tac) >>
  (impl_tac >- fs[]) >> disch_tac >>
  `eval_expr cx (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e]) =
    bind (bind (eval_expr cx e) (read_result cx))
      (\v mid. ((case builtin_result cx mid.accounts (BaseT (BytesT (Dynamic n)))
                    (CalldataSlice n) [expr_type e] [v] of
                  INL r => INL (Value r) | INR ex => INR ex),mid))` by
    (irule eval_expr_unary_builtin_action >>
     simp[precompile_builtin_def,builtin_args_length_ok_def]) >>
  pop_assum SUBST1_TAC >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ childQ childR` >>
  irule gas_outcome_full_bind_all >> rpt conj_tac
  >- simp[storage_trace_frame_def]
  >~ [`storage_trace_frame (bind _ _)`]
  >- (irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame,storage_trace_frame_read_result])
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
      qexistsl_tac [`mid`,`t`,`v`] >> gvs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[]) >>
  qexists_tac `\H res ee G' tn' t. childQ H res ee G' tn' t /\ ~t.vs_halted /\ ee.gas_obs = []` >>
  reverse conj_tac
  >- (irule gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
      conj_tac >- simp[] >>
      simp[Abbr `childR`] >> rpt strip_tac >> Cases_on `res` >>
      gvs[exprSimDefsTheory.expr_exit_def,stmtSimPropsTheory.expr_exit_INR_type]) >>
  qx_genl_tac [`marks`,`res`,`mid`,`G1`,`tn1`,`t`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     mid.storage_trace` by gvs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> childQ H res mid G1 tn1 t /\ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  simp_tac (srw_ss()) [Abbr `childQ`] >> strip_tac >>
  disj1_tac >> goal_assum (drule_at Any) >> simp[] >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    expr_post H ctx func cenv cx e es sa sm s0 mid v x t /\
    expr_store_bound cx (expr_type e) v x t /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
    ghost_inv_at (DF H) lo d cenv cx mid G1 tn1 t /\
    ptr_val_ok cx (post_value_type cenv e) v x G1 tn1 t /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> childQ H res mid G1 tn1 t /\ _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> BETA_TAC >> strip_tac >> gvs[]) >>
  qpat_x_assum `expr_vv_sim_full _ _ _ _ e es` kall_tac >>
  qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` kall_tac >>
  `mid with gas_obs := [] = mid` by
    (qpat_assum `mid.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,mid)` by
    (qpat_assum `!tail. bind (eval_expr cx e) _ _ = _`
       (qspec_then `[]` mp_tac) >>
     qpat_assum `res = INL v` mp_tac >>
     qpat_assum `mid with gas_obs := [] = mid` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rw[]) >>
  `expr_body_pre cenv cx env e
     (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by fs[] >>
  `expr_sim_inv cenv cx env mid /\ value_has_type (BaseTV (UintT 256)) v` by
    (drule_at (Pat `bind _ _ _ = _`)
      (CONV_RULE (DEPTH_CONV ETA_CONV) expr_body_pre_base_result) >>
     disch_then (qspecl_then [`env`,`cenv`] mp_tac) >> fs[]) >>
  `?a. v = IntV (&a) /\ a < 2 ** 256` by
    (Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def] >>
     `?m. i = &m` by (qexists_tac `Num i` >> intLib.COOPER_TAC) >> gvs[]) >>
  qpat_x_assum `v = IntV _` SUBST_ALL_TAC >>
  `is_word_type (expr_type e)` by fs[is_word_type_def] >>
  mp_tac (Q.SPECL [`cenv`,`cx`,`env`,`e`,`es`,`expr_type e`,`sa`,`x`,`sm`]
    expr_body_pre_lower_value_word_shape) >>
  (impl_tac >- fs[]) >> strip_tac >>
  `eval_operand x t = SOME (n2w a)` by
    (drule expr_post_word_operand >>
     simp[vyperValueTheory.evaluate_type_def,is_word_type_def,
          loweringSliceTheory.word_value_def,
          valueEncodingTheory.val_to_w256_def,integer_wordTheory.i2w_pos]) >>
  `op_prov G1 x = NONE /\ op_taint tn1 x = {}` by
    fs[ptr_val_ok_def] >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx mid t /\
   storage_well_formed_on cx mid (FST (storage_trace_horizon mid.storage_trace))` by
    fs[expr_post_def] >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by fs[ghost_inv_at_def] >>
  `context_well_typed cx` by fs[expr_sim_inv_def] >>
  `local_ptrs_reserved cenv sm` by
    (fs[local_ptrs_reserved_def] >> rpt strip_tac >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `(!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
      not_fresh_at sm x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
      not_fresh_at sm x)` by
    (conj_tac >> rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> fs[cs_extends_def] >> metis_tac[]) >>
  `32+32*word_size n < 2 ** 64` by
    fs[expr_body_pre_def,allocLimitsTheory.alloc_limits_expr_def] >>
  `type_memory_bytes cenv (BaseT (BytesT (Dynamic n))) = 32+32*word_size n` by
    (POP_ASSUM_LIST (K all_tac) >>
     simp_tac bool_ss [type_memory_bytes_def,vfmConstantsTheory.word_size_def] >>
     decide_tac) >>
  `n <= 32*word_size n` by simp[valueTypingMemoryPropsTheory.word_size_capacity] >>
  `32+32*word_size n < dimword (:256)` by
    (qpat_assum `32+32*word_size n < 2 ** 64` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[dimword_def] >> decide_tac) >>
  `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
    (irule storage_trace_frame_bind_all >>
     simp[evaluate_storage_trace_frame,storage_trace_frame_read_result]) >>
  `?observations. mid.storage_trace = es.storage_trace ++ observations` by
    (drule_all storage_trace_frame_prefix >> simp[]) >>
  `!H. valid_horizon cx st0 H mid.storage_trace ==>
    valid_horizon cx st0 H es.storage_trace` by
    (rpt strip_tac >> pop_assum mp_tac >>
     qpat_assum `mid.storage_trace = es.storage_trace ++ observations` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rw[] >>
     metis_tac[valid_horizon_append]) >>
  Cases_on `a+n < dimword (:256) /\ a+n <= LENGTH cx.txn.calldata`
  >- ((fn (asl,w) =>
      qpat_assum `stmt_state_rel (storage_trace_horizon mid.storage_trace) ctx func cenv cx mid t`
        (fn th =>
          let
            val provider = bytestring_calldata_full_run_resources
            val actual = hd (snd (strip_comb (concl th)))
            val formal = first (fn v => fst (dest_var v) = "H0")
              (free_vars (concl provider))
            val post = fst (dest_forall (find_term (fn tm => is_forall tm andalso
              fst (dest_var (fst (dest_forall tm))) = "H'") (concl provider)))
            val tys = match_type (type_of (pairSyntax.mk_pair (formal,post)))
              (type_of (pairSyntax.mk_pair (actual,actual)))
            val typed = INST [inst tys formal |-> actual] (INST_TYPE tys provider)
          in mp_tac (Q.INST [`start` |-> `x`,`sa` |-> `sm`,`es` |-> `mid`,
             `s` |-> `t`,`G` |-> `G1`,`tn` |-> `tn1`,
             `N` |-> `32+32*word_size n`,
             `explicit` |-> `gas_explicit_sites ctx shadow_ctx`] typed) end) (asl,w)) >>
      (impl_tac >- (fs[dimword_def] >> decide_tac)) >>
      disch_then (qx_choose_then `p` (qx_choose_then `w` (qx_choose_then `z`
        (qx_choose_then `HG` (qx_choose_then `tm` strip_assume_tac))))) >>
      qpat_x_assum `out = Var p` SUBST_ALL_TAC >>
      `!H. valid_horizon cx st0 H mid.storage_trace ==>
        ghost_inv_at (DF H) lo d cenv cx mid HG tm z` by
        (rpt strip_tac >>
         qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
           expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
           (qspec_then `H` mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
         `stmt_state_rel H ctx func cenv cx mid t` by fs[expr_post_def] >>
         `local_ptrs_rel func cenv mid.scopes t` by
           fs[stmt_state_rel_def,state_rel_def] >>
         `stor_taint_ok_at (DF H) tn1 t` by fs[ghost_inv_at_def] >>
         `stor_taint_ok_at (DF H) tm z` by fs[stor_taint_ok_at_def] >>
         `!i. i < lo /\ i IN tm.t_mem ==> i IN tn1.t_mem` by
           (qpat_assum `ghost_kept_at lo cenv mid sm G1 tn1 t HG tm`
             (ACCEPT_TAC o last o CONJUNCTS o REWRITE_RULE[ghost_kept_at_def])) >>
         (fn (asl,w) =>
           let val actualD = hd (snd (strip_comb w))
               val provider = ghost_inv_at_local_window_transport
               val dv = first (fn v => fst (dest_var v) = "D")
                 (free_vars (concl provider))
           in mp_tac (Q.INST [`sa` |-> `sm`,`G` |-> `G1`,`tn` |-> `tn1`,
             `s` |-> `t`,`es` |-> `mid`,`fn` |-> `func`,
             `es'` |-> `mid`,`s'` |-> `z`] (INST [dv |-> actualD] provider))
             (asl,w) end) >>
         (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
         disch_then ACCEPT_TAC) >>
      irule gas_outcome_full_pure >> reverse conj_tac >- simp[] >>
      qexistsl_tac [`HG`,`mid`,
        `INL (Value (BytesV (TAKE n (DROP a cx.txn.calldata))))`,`z`,`tm`] >>
      simp[builtin_result_def,vyperContextTheory.evaluate_builtin_def,
           evaluate_calldata_slice_uint,GSYM dimword_def] >>
      conj_tac >- (Cases_on `2 ** 256 <= a+n` >> gvs[dimword_def]) >>
      qx_gen_tac `H` >> strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==>
        expr_post H _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
        (qspec_then `H` mp_tac) >>
      (impl_tac >- simp[]) >> strip_tac >>
      `stmt_state_rel H ctx func cenv cx mid t /\
       storage_well_formed_on cx mid (FST H)` by fs[expr_post_def] >>
      `stmt_state_rel H ctx func cenv cx mid z` by
        (qpat_assum `!H'. stmt_state_rel H' ctx func cenv cx mid t ==> _`
          (qspec_then `H` match_mp_tac) >> first_assum ACCEPT_TAC) >>
      `alloca_inv z /\ local_ptrs_rel func cenv mid.scopes z` by
        fs[stmt_state_rel_def,state_rel_def] >>
      qpat_assum `compile_slice_calldata _ _ _ sm = _`
        (mp_then Any strip_assume_tac slice_calldata_shape) >>
      qabbrev_tac `ai = mk_inst (sm.cs_next_id+7) ALLOCA
        [Lit (n2w (32+32*word_size n))]
        [STRING #"%" (toString (sm.cs_next_var+6))]` >>
      `MEM ai (fn_insts func)` by
        (qpat_assum `fn_has_code sm sb func`
           (strip_assume_tac o REWRITE_RULE[fn_has_code_def]) >>
         rename1 `lookup_block sb.cs_current_bb func.fn_blocks = SOME code` >>
         qspecl_then [`sb.cs_current_bb`,`func`,`code`,`ai`]
           match_mp_tac lookup_block_fn_insts >> simp[] >>
         qpat_assum `isPREFIX sb.cs_current_insts code.bb_instructions`
           (strip_assume_tac o REWRITE_RULE[rich_listTheory.IS_PREFIX_APPEND]) >>
         fs[Abbr `ai`,MEM_APPEND] >> metis_tac[]) >>
      `!nm lb len. local_region cenv mid.scopes z nm lb len ==>
        regions_disjoint (w2n w) (32+32*word_size n) lb len` by
        (rpt strip_tac >>
         qspecl_then [`func`,`cenv`,`mid.scopes`,`z`,`ai`,
           `STRING #"%" (toString (sm.cs_next_var+6))`,`w2n w`,
           `32+32*word_size n`,`nm`,`lb`,`len`]
           match_mp_tac local_ptrs_rel_alloca_disjoint >>
         simp[Abbr `ai`,mk_inst_def] >>
         irule local_ptrs_reserved_fresh >> qexists_tac `sm` >> simp[]) >>
      `vv_post H ctx func cenv cx
         (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e])
         mid sm sb t mid (Value (BytesV (TAKE n (DROP a cx.txn.calldata))))
         (LocatedValue (BaseT (BytesT (Dynamic n)))
           (mk_ptr (Var p) LocMemory)) z` by
        (`z = z with vs_inst_idx := z.vs_inst_idx` by
           simp[venom_state_component_equality] >>
         pop_assum (fn th => ONCE_REWRITE_TAC [th]) >>
         irule (SIMP_RULE (srw_ss()) [expr_type_def]
           (Q.SPECL [`func`,`cenv`,`cx`,
             `Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e]`]
             slice_calldata_vv_post)) >>
         simp[expr_type_def,mk_ptr_def,eval_operand_def] >>
         conj_tac
         >- (rpt strip_tac >> first_x_assum irule >>
             qexists_tac `aid` >> simp[]) >>
         qexists_tac `sm.cs_next_id+7` >> simp[] >>
         rpt strip_tac >>
         qpat_assum `local_region cenv mid.scopes z nm lb len` mp_tac >>
         qpat_assum `!nm lb len. local_region cenv mid.scopes z nm lb len ==> _`
           (qspecl_then [`nm`,`lb`,`len`] mp_tac) >>
         POP_ASSUM_LIST (K all_tac) >>
         rewrite_tac[Q.SPECL [`32*word_size n`,`32`] ADD_COMM] >> simp[]) >>
      `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
        (qpat_assum `bind (eval_expr cx e) (read_result cx)
           (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = _`
           (mp_then Any mp_tac (CONV_RULE (DEPTH_CONV ETA_CONV)
             forced_eval_expr_preserves_scopes_dom)) >> simp[]) >>
      `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by
        (qpat_assum `lower_value compile_expr cenv (expr_type e) e sa = _`
          (mp_then Any strip_assume_tac (cj 2 compile_expr_grows)) >> simp[]) >>
      `stmt_state_rel H ctx func cenv cx es s0` by
        (qpat_assum `!H. valid_horizon cx st0 H es.storage_trace ==> _`
          (qspec_then `H` mp_tac) >>
         (impl_tac >- metis_tac[]) >> simp[]) >>
      `wb_frame cenv es mid sa s0 t` by
        (qpat_assum `expr_post _ _ _ _ _ e es sa sm s0 mid _ x t`
          (mp_then Any ACCEPT_TAC expr_post_frame)) >>
      `(~expr_has_effect
          (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e]) ==>
        pure_frame cenv func es sa s0 t)` by
        (simp[expr_has_effect_thm] >> strip_tac >>
         qpat_assum `expr_post _ _ _ _ _ e es sa sm s0 mid _ x t`
           (mp_then Any mp_tac expr_post_pure_frame) >> simp[]) >>
      `vv_post H ctx func cenv cx
         (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e])
         es sa sb s0 mid (Value (BytesV (TAKE n (DROP a cx.txn.calldata))))
         (LocatedValue (BaseT (BytesT (Dynamic n)))
           (mk_ptr (Var p) LocMemory)) z` by
        ((fn (asl,w) =>
           let val actualH = hd (snd (strip_comb w))
               val provider = vv_post_prefix_frame
               val formalH = first (fn v => fst (dest_var v) = "H")
                 (free_vars (concl provider))
               val tys = match_type (type_of formalH) (type_of actualH)
               val typed = INST [inst tys formalH |-> actualH] (INST_TYPE tys provider)
           in mp_tac (Q.INST [`ctx` |-> `ctx`,`func` |-> `func`,
             `cenv` |-> `cenv`,`cx` |-> `cx`,
             `e` |-> `Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e]`,
             `es` |-> `es`,`s0` |-> `s0`,`sa` |-> `sa`,`sb` |-> `sb`,
             `es1` |-> `mid`,`sm` |-> `sm`,`t` |-> `t`,`es2` |-> `mid`,
             `tv` |-> `Value (BytesV (TAKE n (DROP a cx.txn.calldata)))`,
             `vv` |-> `LocatedValue (BaseT (BytesT (Dynamic n)))
               (mk_ptr (Var p) LocMemory)`,`u` |-> `z`] typed) (asl,w) end) >>
         (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
         disch_then ACCEPT_TAC) >>
      `LENGTH (TAKE n (DROP a cx.txn.calldata)) = n` by simp[LENGTH_TAKE_EQ] >>
      `val_wf (BaseTV (BytesT (Dynamic n)))
        (BytesV (TAKE n (DROP a cx.txn.calldata)))` by
        (simp[val_wf_def,valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
      `val_store_size (BaseTV (BytesT (Dynamic n)))
         (BytesV (TAKE n (DROP a cx.txn.calldata))) = 32+32*word_size n` by
        simp[val_store_size_def] >>
      `evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic n))) =
         SOME (BaseTV (BytesT (Dynamic n)))` by
        (qpat_assum `32+32*word_size n < dimword(:256)` mp_tac >>
         qpat_assum `n < _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[evaluate_type_def,type_slot_size_def,dimword_def] >> decide_tac) >>
      `ptr_mem_ok cx (BaseT (BytesT (Dynamic n)))
        (BytesV (TAKE n (DROP a cx.txn.calldata))) (Var p) HG tm z` by
        (mp_tac (Q.INST [`ty` |-> `BaseT (BytesT (Dynamic n))`,
           `vt` |-> `BaseTV (BytesT (Dynamic n))`,
           `v` |-> `BytesV (TAKE n (DROP a cx.txn.calldata))`,
           `b` |-> `w`,`root` |-> `p`,`s` |-> `z`,`G` |-> `HG`,`tn` |-> `tm`,
           `capacity` |-> `32+32*word_size n`] clean_memory_representation_ptr) >>
         (impl_tac >- (simp[val_footprint_def] >> rpt strip_tac >>
           qpat_assum `!i. w2n w <= i /\ i < w2n w+32+n ==> _` irule >> simp[])) >>
         disch_then ACCEPT_TAC) >>
      `op_taint tm (Var p) = {}` by
        (qpat_assum `ptr_covers HG tm p z _`
          (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE[ptr_covers_def])) >>
      `ptr_vv_ok cx (BaseT (BytesT (Dynamic n)))
         (Value (BytesV (TAKE n (DROP a cx.txn.calldata))))
         (LocatedValue (BaseT (BytesT (Dynamic n))) (mk_ptr (Var p) LocMemory))
         mid HG tm z` by
        (qspecl_then [`cx`,`BaseT (BytesT (Dynamic n))`,
           `Value (BytesV (TAKE n (DROP a cx.txn.calldata)))`,
           `BaseT (BytesT (Dynamic n))`,`mk_ptr (Var p) LocMemory`,
           `mid`,`HG`,`tm`,`z`,`BytesV (TAKE n (DROP a cx.txn.calldata))`]
           match_mp_tac ptr_vv_ok_memory >>
         simp[mk_ptr_def,read_result_def,return_def]) >>
      `ptr_buf_ok cenv
         (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e]) (Var p) HG z` by
        (qpat_assum `ptr_covers HG tm p z _` mp_tac >>
         qpat_assum `type_memory_bytes cenv (BaseT (BytesT (Dynamic n))) = _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         rw[ptr_covers_def,ptr_buf_ok_def,eval_operand_def,
           lowered_value_type_def,expr_type_def] >> gvs[] >>
         qexistsl_tac [`b`,`sz'`] >> simp[] >> decide_tac) >>
      `vv_store_bound cx (BaseT (BytesT (Dynamic n))) (BaseT (BytesT (Dynamic n)))
         mid (Value (BytesV (TAKE n (DROP a cx.txn.calldata))))
         (LocatedValue (BaseT (BytesT (Dynamic n))) (mk_ptr (Var p) LocMemory)) z` by
        (qpat_assum `evaluate_type (get_tenv cx) (BaseT (BytesT (Dynamic n))) = _` mp_tac >>
         qpat_assum `w2n w+(32+32*word_size n) <= z.vs_alloca_next` mp_tac >>
         qpat_assum `lookup_var p z = SOME w` mp_tac >>
         qpat_assum `LENGTH (TAKE n (DROP a cx.txn.calldata)) = n` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         rw[vv_store_bound_def,mk_ptr_def,read_result_def,return_def,
           eval_operand_def,val_store_size_def,
           valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
      `ghost_kept_at lo cenv es sa G0 tn0 s0 HG tm` by
        (qspecl_then [`lo`,`cenv`,`es`,`sa`,`G0`,`tn0`,`s0`,`G1`,`tn1`,
           `mid`,`sm`,`HG`,`tm`,`t`,`H`,`ctx`,`func`,`cx`,`mid`]
           mp_tac ghost_kept_at_wb_trans >>
         (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
         disch_then ACCEPT_TAC) >>
      fs[expr_type_def,post_value_type_def,lowered_value_type_def,mk_ptr_def,vv_location_def]) >>
  `alloca_inv t /\ t.vs_call_ctx.cc_calldata = cx.txn.calldata` by
    fs[stmt_state_rel_def,state_rel_def,call_ctx_rel_def] >>
  `LENGTH t.vs_call_ctx.cc_calldata < dimword (:256)` by
    fs[context_well_typed_def,dimword_def] >>
  `dimword (:256) <= a+n \/ LENGTH cx.txn.calldata < a+n` by decide_tac >>
  `dimword (:256) <= a+n \/ LENGTH t.vs_call_ctx.cc_calldata < a+n` by
    metis_tac[] >>
  mp_tac (Q.INST [`start` |-> `x`,`sa` |-> `sm`,`s` |-> `t`,
    `G` |-> `G1`,`tn` |-> `tn1`,`N` |-> `32+32*word_size n`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    bytestring_calldata_full_abort) >>
  (impl_tac >- (fs[dimword_def,context_well_typed_def] >> decide_tac)) >>
  disch_then (qx_choose_then `u` (qx_choose_then `HG`
    (qx_choose_then `tm` assume_tac))) >>
  (* u,HG,tm are now fixed ONCE, before the final horizon binder. *)
  `?errstr. builtin_result cx mid.accounts (BaseT (BytesT (Dynamic n)))
      (CalldataSlice n) [BaseT (UintT 256)] [IntV (&a)] =
      INR (Error (RuntimeError errstr))` by
    (Cases_on `2 ** 256 <= a+n`
     >- (qexists_tac `"calldata slice overflow"` >>
         simp[builtin_result_def,vyperContextTheory.evaluate_builtin_def,
           evaluate_calldata_slice_uint]) >>
     qexists_tac `"evaluate_slice range"` >>
     simp[builtin_result_def,vyperContextTheory.evaluate_builtin_def,
       evaluate_calldata_slice_uint] >> gvs[dimword_def] >> decide_tac) >>
  (* The by-existential already introduces errstr; no extra CHOOSE. *)
  irule (Q.INST [`r` |-> `Abort Revert_abort u`,
    `res` |-> `INR (Error (RuntimeError errstr))`,`ee` |-> `mid`,
    `G'` |-> `HG`,`tn'` |-> `tm`] gas_outcome_full_exit) >>
  simp[exit_result_def,exprSimDefsTheory.expr_exit_def] >>
  qexistsl_tac [`HG`,`errstr`,`mid`,`tm`,`u`] >> simp[]
QED

Theorem calldata_slice_expr_sim_full:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty ann n args es.
    (builtin_args_length_ok (CalldataSlice n) (LENGTH args) ==>
      body_exprs_full_ok cx args) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin ann (CalldataSlice n) args) es ==>
    expr_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin ann (CalldataSlice n) args) es
Proof
  rpt gen_tac >> strip_tac >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin ann (CalldataSlice n) args) es` by
    (irule calldata_slice_vv_sim_full >> simp[] >> conj_tac
     >- (qexists_tac `tops` >> simp[]) >>
     qexists_tac `env` >> simp[]) >>
  irule bodyFullOfVVTheory.expr_sim_full_of_vv >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      drule_all exprSimHypsTheory.expr_body_pre_copy_ok >> simp[]) >>
  qpat_assum `expr_body_pre _ _ _ (Builtin _ (CalldataSlice _) _) _`
    (mp_tac o MATCH_MP exprSimHypsTheory.expr_body_pre_type_evaluates) >>
  simp[optionTheory.IS_SOME_EXISTS] >>
  disch_then (qx_choose_then `rty` assume_tac) >>
  qexists_tac `rty` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env (Builtin ann (CalldataSlice n) args)
      (es with gas_obs := gs)` by simp[] >>
  drule_all exprSimSourceTheory.expr_body_pre_runtime_typed >>
  strip_tac >> gvs[] >> metis_tac[]
QED
