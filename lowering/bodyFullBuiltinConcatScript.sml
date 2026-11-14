(* Concat on the joint finite-horizon body contract. *)
Theory bodyFullBuiltinConcat
Ancestors
  bodyFullBuiltinConcatLoop bodyFullBuiltinConcatFrame bodyFullOfVV
  bodyFullPreds bodySimFull gasOutcomeFullCompose gasOutcomeFullGuarded
  exprSimConcatResult exprSimConcatSource exprSimHyps exprSimSource
  exprSimHypsDefs exprLowering loweringPosts allocLimits vyperTypeInvariants
  vyperTypeSystem vyperContext compileEnv emitHelperProps fragExec
  gasShadowCompile gasShadowCompileHelpers gasShadowState
  reasonCodeResourcesPtr bodyPtrAttributeFields
  vyperTypeConversions valueEncoding valueEncodingDefs valueEncodingProps vfmConstants
  vyperAST words arithmetic list

Theorem concat_sim_full:
  !DF lo d ctx shadow_ctx PG tops func shadow_func cenv env cx ty a n args es.
    (builtin_args_length_ok (Concat n) (LENGTH args) ==>
      body_exprs_full_ok cx args) /\
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (Builtin a (Concat n) args) es ==>
    expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a (Concat n) args) es /\
    expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
      cenv cx ty (Builtin a (Concat n) args) es
Proof
  rpt gen_tac >> strip_tac >>
  `expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx ty (Builtin a (Concat n) args) es` by suspend "vv" >>
  reverse conj_tac >- first_assum ACCEPT_TAC >>
  irule bodyFullOfVVTheory.expr_sim_full_of_vv >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> drule_all exprSimHypsTheory.expr_body_pre_copy_ok >> simp[]) >>
  qpat_assum `expr_body_pre _ _ _ (Builtin a (Concat n) args) _`
    (mp_tac o MATCH_MP exprSimHypsTheory.expr_body_pre_type_evaluates) >>
  simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  qexists_tac `x` >> simp[] >>
  rpt gen_tac >> strip_tac >>
  `expr_body_pre cenv cx env (Builtin a (Concat n) args)
     (es with gas_obs := gs)` by simp[] >>
  drule_all exprSimSourceTheory.expr_body_pre_runtime_typed >>
  strip_tac >> gvs[] >> metis_tac[]
QED

Resume concat_sim_full[vv]:
  `!e st. MEM e args /\ expr_sim_inv cenv cx env st ==>
          expr_body_pre cenv cx env e st` by
    (rpt gen_tac >> strip_tac >>
     qspecl_then [`cenv`,`cx`,`env`,`a`,`Concat n`,`args`,`e`,`es`,`st`]
       mp_tac exprSimSourceTheory.expr_body_pre_builtin_arg >> simp[]) >>
  `expr_sim_inv cenv cx env es /\ well_typed_expr env (Builtin a (Concat n) args) /\
   alloc_limits_expr cenv (Builtin a (Concat n) args)` by fs[expr_body_pre_def] >>
  `env.type_defs = get_tenv cx` by
    (qpat_assum `expr_sim_inv cenv cx env es` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[expr_sim_inv_def,env_consistent_def,env_context_consistent_def]) >>
  `2 <= LENGTH args /\ SUM (MAP bytelike_type_bound (MAP expr_type args)) <= n /\
   well_formed_type env.type_defs a` by
    (qpat_assum `well_typed_expr _ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[Once well_typed_expr_def,well_typed_builtin_app_def] >>
     rpt strip_tac >> fs[]) >>
  `body_exprs_full_ok cx args` by
    (qpat_assum `builtin_args_length_ok (Concat n) (LENGTH args) ==> _` irule >>
     simp[builtin_args_length_ok_def]) >>
  Q.SUBGOAL_THEN
    `(a = BaseT (BytesT (Dynamic n)) /\
      EVERY (\t. ?bd. t = BaseT (BytesT bd)) (MAP expr_type args)) \/
     (a = BaseT (StringT n) /\
      EVERY (\t. ?m. t = BaseT (StringT m)) (MAP expr_type args))` assume_tac
  >- (qpat_assum `well_typed_expr _ _` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >>
      simp[Once well_typed_expr_def,well_typed_builtin_app_def] >>
      rpt strip_tac >> fs[]) >>
  `?tvr. evaluate_type (get_tenv cx) a = SOME tvr` by
    (qpat_x_assum `well_formed_type _ _` mp_tac >>
     qpat_assum `env.type_defs = _`
       (fn th => simp[th,well_formed_type_def,optionTheory.IS_SOME_EXISTS])) >>
  `concat_alloc_size (MAP expr_type args) < 2 ** 64` by
    (qpat_x_assum `alloc_limits_expr _ _` mp_tac >> simp[alloc_limits_expr_def]) >>
  rewrite_tac[expr_vv_sim_full_def] >> rpt gen_tac >> strip_tac >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_initial_domain >>
  conj_tac >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  conj_tac >- first_assum ACCEPT_TAC >> disch_tac >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel H _ _ _ _ _ s0 /\ _`
    (qspec_then `storage_trace_horizon es.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_assum `compile_expr cenv ty (Builtin a (Concat n) args) sa = _`
    (strip_assume_tac o MATCH_MP exprSimConcatResultTheory.concat_compile_shape) >>
  rename1 `emit_op ADD [buf.buf_operand; Lit 32w] s1 = (dataop,s2)` >>
  qabbrev_tac `bsz = concat_alloc_size (MAP expr_type args)` >>
  `bsz < dimword (:256)` by
    (mp_tac (Q.ASSUME `bsz < 2 ** 64`) >> POP_ASSUM_LIST (K all_tac) >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  `32 + SUM (MAP concat_payload_capacity (MAP expr_type args)) <= bsz /\
   32 + concat_data_bound 0 (MAP expr_type args) <= bsz` by
    simp[Abbr `bsz`,exprSimHypsTheory.concat_alloc_size_bounds] >>
  `32 <= bsz` by
    (qpat_assum `32 + SUM _ <= bsz` mp_tac >> POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  qspecl_then [`bsz`,`sa`,`buf`,`s1`,`dataop`,`s2`,`ob`,`s3`,`u`,`s4`]
    mp_tac exprSimConcatResultTheory.concat_prefix_code >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `cs_extends sa s4` by
    (irule compileEnvTheory.cs_extends_same_block >>
     qpat_assum `s4.cs_current_insts = _` (fn th => simp[th])) >>
  `ci_mono s4 s5` by
    (qpat_assum `compile_concat _ _ _ _ _ _ s4 = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >>
     metis_tac[exprLoweringPropsTheory.ci_mono_compile_concat_cfn,
       cj 1 exprLoweringPropsTheory.compile_expr_ci_mono,pairTheory.SND]) >>
  `cs_extends s4 s5` by fs[exprLoweringPropsTheory.ci_mono_def] >>
  qspecl_then [`STRING #"%" (toString (sa.cs_next_var+2))`,
    `STRING #"%" (toString sa.cs_next_var)`,`s5`,`fo`,`s6`,`u'`,`sb`]
    mp_tac exprSimConcatResultTheory.concat_suffix_code >>
  (impl_tac >-
    (qpat_assum `emit_op MLOAD [ob.buf_operand] s5 = _` mp_tac >>
     qpat_assum `emit_void MSTORE [buf.buf_operand;fo] s6 = _` mp_tac >>
     qpat_assum `buf.buf_operand = _` mp_tac >>
     qpat_assum `ob.buf_operand = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> Cases_on `u'` >> metis_tac[])) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `cs_extends s5 sb` by
    (irule compileEnvTheory.cs_extends_same_block >>
     qpat_assum `sb.cs_current_insts = _` (fn th => simp[th])) >>
  `cs_extends s4 sb` by
    (qspecl_then [`s4`,`s5`,`sb`] mp_tac compileEnvTheory.cs_extends_trans >> simp[]) >>
  `fn_has_code sa s4 func /\ fn_has_code s4 sb func` by
    (qspecl_then [`sa`,`s4`,`sb`,`func`] mp_tac fragExecTheory.fn_has_code_split >> simp[]) >>
  `allocas_from lo s0 /\ lo <= s0.vs_alloca_next` by
    (qpat_assum `ghost_inv_at _ _ _ _ _ es G0 tn0 s0` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[bodyPtrDefsTheory.ghost_inv_at_def]) >>
  drule_all bodyFullBuiltinConcatFrameTheory.concat_prefix_full >>
  disch_then (qspecl_then [`tn0`,`gas_explicit_sites ctx shadow_ctx`,`PG`,`G0`]
    (qx_choosel_then [`t4`,`G4`,`tn4`,`bv`,`dp`,`ov`,`B`,`ow`]
      (map_every assume_tac o CONJUNCTS))) >>
  qpat_assum `compile_expr cenv ty (gas_shadow_expr (Builtin a (Concat n) args)) shadow_sa = _`
    (mp_tac o SIMP_RULE (srw_ss())
      [gasShadowTheory.gas_shadow_expr_def,gasShadowTheory.gas_shadow_builtin_def]) >>
  disch_then (mp_tac o MATCH_MP exprSimConcatResultTheory.concat_compile_shape) >>
  simp_tac bool_ss [listTheory.MAP_MAP_o,combinTheory.o_DEF,gasShadowTheory.gas_shadow_expr_type] >>
  disch_then (qx_choosel_then [`shadow_buf`,`shadow_s1`,`shadow_data`,`shadow_s2`,
    `shadow_ob`,`shadow_s3`,`shadow_unit`,`shadow_s4`,`shadow_s5`,`shadow_fo`,
    `shadow_s6`,`shadow_unit'`] (map_every assume_tac o CONJUNCTS)) >>
  `buf = shadow_buf /\ gas_shadow_state s1 shadow_s1` by
    (mp_tac (Q.INST [`nbytes` |-> `bsz`]
       gasShadowCompileContextTheory.gas_shadow_compiles_alloc_buffer) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >>
     qpat_assum `compile_alloc_buffer _ shadow_sa = _`
       (mp_tac o CONV_RULE (DEPTH_CONV ETA_CONV)) >>
     simp_tac bool_ss [Abbr `bsz`] >> strip_tac >> simp[]) >>
  qpat_x_assum `buf = shadow_buf` (SUBST_ALL_TAC o SYM) >>
  `dataop = shadow_data /\ gas_shadow_state s2 shadow_s2` by
    (mp_tac (Q.INST [`opc` |-> `ADD`, `ops` |-> `[buf.buf_operand; Lit 32w]`]
       gasShadowCompileContextTheory.gas_shadow_compiles_emit_op_same) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`s1`,`shadow_s1`] mp_tac) >> simp[]) >>
  qpat_x_assum `dataop = shadow_data` (SUBST_ALL_TAC o SYM) >>
  `ob = shadow_ob /\ gas_shadow_state s3 shadow_s3` by
    (mp_tac (Q.INST [`nbytes` |-> `64`]
       gasShadowCompileContextTheory.gas_shadow_compiles_alloc_buffer) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`s2`,`shadow_s2`] mp_tac) >> simp[]) >>
  qpat_x_assum `ob = shadow_ob` (SUBST_ALL_TAC o SYM) >>
  `gas_shadow_state s4 shadow_s4` by
    (mp_tac (Q.INST [`opc` |-> `MSTORE`, `ops` |-> `[ob.buf_operand; Lit 0w]`]
       gasShadowStateTheory.gas_shadow_compiles_emit_void) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`s3`,`shadow_s3`] mp_tac) >> simp[]) >>
  qpat_x_assum `compile_concat _ _ args dataop _ _ s4 = _`
    (assume_tac o SIMP_RULE bool_ss [LET_THM]) >>
  qpat_x_assum `compile_concat _ _ (MAP gas_shadow_expr args) dataop _ _ shadow_s4 = _`
    (assume_tac o SIMP_RULE bool_ss [LET_THM]) >>
  qmatch_assum_abbrev_tac
    `compile_concat compile_expr cenv args dataop infos ob.buf_operand s4 = ((),s5)` >>
  `gas_shadow_state s5 shadow_s5` by
    (mp_tac (Q.INST [`sh` |-> `T`,`cenv` |-> `cenv`,
       `data_ptr` |-> `dataop`,`off_ptr` |-> `ob.buf_operand`]
       (MATCH_MP gasShadowCompileHelpersTheory.gas_shadow_compiles_concat
         (cj 1 gasShadowCompileTheory.gas_shadow_compile_expr))) >>
     disch_then (qspecl_then [`args`,`infos`] mp_tac) >>
     simp_tac bool_ss [] >> rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`s4`,`shadow_s4`] mp_tac) >> simp[]) >>
  `ci_mono shadow_s4 shadow_s5` by
    (qpat_assum `compile_concat _ _ _ _ _ _ shadow_s4 = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >>
     metis_tac[exprLoweringPropsTheory.ci_mono_compile_concat_cfn,
       cj 1 exprLoweringPropsTheory.compile_expr_ci_mono,pairTheory.SND]) >>
  `cs_extends shadow_s4 shadow_s5` by fs[exprLoweringPropsTheory.ci_mono_def] >>
  qspecl_then [`bsz`,`shadow_sa`,`buf`,`shadow_s1`,`dataop`,`shadow_s2`,
    `ob`,`shadow_s3`,`shadow_unit`,`shadow_s4`]
    mp_tac exprSimConcatResultTheory.concat_prefix_code >>
  (impl_tac >-
    (qpat_assum `compile_alloc_buffer _ shadow_sa = _`
       (mp_tac o CONV_RULE (DEPTH_CONV ETA_CONV)) >>
     simp[Abbr `bsz`])) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `cs_extends shadow_sa shadow_s4` by
    (irule compileEnvTheory.cs_extends_same_block >>
     qpat_assum `shadow_s4.cs_current_insts = _` (fn th => simp[th])) >>
  qspecl_then [`ov`,`bv`,`shadow_s5`,`shadow_fo`,`shadow_s6`,
    `shadow_unit'`,`shadow_sb`] mp_tac exprSimConcatResultTheory.concat_suffix_code >>
  (impl_tac >-
    (qpat_assum `emit_op MLOAD [ob.buf_operand] shadow_s5 = _` mp_tac >>
     qpat_assum `emit_void MSTORE [buf.buf_operand;shadow_fo] shadow_s6 = _` mp_tac >>
     qpat_assum `buf.buf_operand = Var bv` mp_tac >>
     qpat_assum `ob.buf_operand = Var ov` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     Cases_on `shadow_unit'` >> metis_tac[])) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `cs_extends shadow_s5 shadow_sb` by
    (irule compileEnvTheory.cs_extends_same_block >>
     qpat_assum `shadow_sb.cs_current_insts = _` (fn th => simp[th])) >>
  `cs_extends shadow_s4 shadow_sb` by
    (qspecl_then [`shadow_s4`,`shadow_s5`,`shadow_sb`]
      mp_tac compileEnvTheory.cs_extends_trans >> simp[]) >>
  `fn_has_code shadow_sa shadow_s4 shadow_func /\
   fn_has_code shadow_s4 shadow_sb shadow_func` by
    (qspecl_then [`shadow_sa`,`shadow_s4`,`shadow_sb`,`shadow_func`]
      mp_tac fragExecTheory.fn_has_code_split >> simp[]) >>
  `fn_has_code s4 s5 func /\ fn_has_code s5 sb func` by
    (qspecl_then [`s4`,`s5`,`sb`,`func`]
      mp_tac fragExecTheory.fn_has_code_split >> simp[]) >>
  `fn_has_code shadow_s4 shadow_s5 shadow_func /\
   fn_has_code shadow_s5 shadow_sb shadow_func` by
    (qspecl_then [`shadow_s4`,`shadow_s5`,`shadow_sb`,`shadow_func`]
      mp_tac fragExecTheory.fn_has_code_split >> simp[]) >>
  `local_ptrs_reserved cenv s4` by
    (qspecl_then [`cenv`,`sa`,`s4`]
      mp_tac exprLoweringPropsTheory.local_ptrs_reserved_next_var >> simp[]) >>
  `ptr_covers G4 tn4 ov t4 32` by
    (irule reasonCopySourcePtrTheory.ptr_covers_mono >> qexists_tac `64` >> simp[]) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es t4 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G4 tn4 t4` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _`
       (qspec_then `H` mp_tac) >> simp[]) >>
  `!name lb lsz. local_region cenv es.scopes t4 name lb lsz ==>
     local_region cenv es.scopes s0 name lb lsz` by
    (rpt gen_tac >> disch_tac >>
     qspecl_then [`func`,`cenv`,`es.scopes`,`s0`,`sa`,`es.scopes`,`t4`,
       `name`,`lb`,`lsz`] mp_tac exprSimPropsTheory.local_region_frame >>
     (impl_tac >-
       (rpt conj_tac >> simp[] >-
         (qpat_assum `stmt_state_rel _ _ _ _ _ es s0` mp_tac >>
          POP_ASSUM_LIST (K all_tac) >>
          simp[exprLoweringPropsTheory.stmt_state_rel_def,
            loweringStateRelDefsTheory.state_rel_def]))) >> simp[]) >>
  `EVERY (\e. is_bytestring_type (expr_type e) \/
              ?m. expr_type e = BaseT (BytesT (Fixed m))) args` by
    (qpat_assum `(a = _ /\ _) \/ (a = _ /\ _)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> strip_tac >>
     fs[listTheory.EVERY_MEM,listTheory.MEM_MAP,PULL_EXISTS] >>
     rpt strip_tac >> res_tac >> fs[compileEnvTheory.is_bytestring_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >> fs[compileEnvTheory.is_bytestring_type_def]) >>
  qabbrev_tac `binst = mk_inst sa.cs_next_id ALLOCA [Lit (n2w bsz)]
    [STRING #"%" (toString sa.cs_next_var)]` >>
  qabbrev_tac `oinst = mk_inst (sa.cs_next_id+2) ALLOCA [Lit 64w]
    [STRING #"%" (toString (sa.cs_next_var+2))]` >>
  `MEM binst (fn_insts func)` by
    (qspecl_then [`func`,`sa`,`s4`,`binst`]
      mp_tac exprSimConcatResultTheory.concat_code_mem >>
     (impl_tac >- simp[Abbr `binst`]) >> simp[]) >>
  `MEM oinst (fn_insts func)` by
    (qspecl_then [`func`,`sa`,`s4`,`oinst`]
      mp_tac exprSimConcatResultTheory.concat_code_mem >>
     (impl_tac >- simp[Abbr `oinst`]) >> simp[]) >>
  `!name lb lsz. local_region cenv es.scopes t4 name lb lsz ==>
    (B+bsz <= lb \/ lb+lsz <= B) /\
    (w2n ow+64 <= lb \/ lb+lsz <= w2n ow)` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!name lb lsz. local_region cenv es.scopes s0 name lb lsz ==> _`
       (qspecl_then [`name`,`lb`,`lsz`] mp_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  `!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at s4 z` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at s4 z` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  qunabbrev_tac `infos` >>
  qspecl_then [`args`,`0`,`0`,`DF`,`lo`,`d`,`ctx`,`shadow_ctx`,`PG`,`tops`,
    `func`,`shadow_func`,`cenv`,`cx`,`env`,`st0`,`es`,`s4`,`s5`,
    `shadow_s4`,`shadow_s5`,`t4`,`G4`,`tn4`,`dp`,`ov`,`ow`,`binst`,`B`,`bsz`,`oinst`]
    mp_tac bodyFullBuiltinConcatLoopTheory.concat_args_sim_full >>
  (impl_tac >-
    (simp[Abbr `binst`,Abbr `oinst`,venomInstTheory.mk_inst_def,
       loweringStateRelDefsTheory.regions_disjoint_def] >>
     rpt conj_tac >| [
       qpat_assum `compile_concat _ _ xs _ (MAP _ xs) _ _ = _` mp_tac >>
       map_every mp_tac [Q.ASSUME `dataop = Var dp`,
         Q.ASSUME `ob.buf_operand = Var ov`] >>
       POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> metis_tac[],
       qpat_assum `compile_concat _ _ (MAP gas_shadow_expr _) _ _ _ _ = _` mp_tac >>
       map_every mp_tac [Q.ASSUME `dataop = Var dp`,
         Q.ASSUME `ob.buf_operand = Var ov`] >>
       POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> metis_tac[],
       first_assum ACCEPT_TAC,
       mp_tac (Q.ASSUME `regions_disjoint B bsz (w2n (ow:bytes32)) 64`) >>
       POP_ASSUM_LIST (K all_tac) >>
       simp[loweringStateRelDefsTheory.regions_disjoint_def]
     ])) >>
  disch_tac >>
  qmatch_assum_abbrev_tac `gas_outcome_full _ _ _ _ _ _ loopQ loopR` >>
  qmatch_goalsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ finalQ finalR` >>
  `storage_trace_frame (eval_expr cx (Builtin a (Concat n) args))` by
    simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (s0,G0,tn0) [] (OK t4,G4,tn4)` by simp[] >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (eval_expr cx (Builtin a (Concat n) args))
    (es,t4,G4,tn4) finalQ finalR` by suspend "finish" >>
  mp_tac (Q.INST [`DF` |-> `DF`,`lo` |-> `lo`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`,`ctx` |-> `ctx`,
    `func` |-> `func`,`PG` |-> `PG`,`tops` |-> `cx_tops cx`,
    `cx` |-> `cx`,`st0` |-> `st0`,`es` |-> `es`,
    `s0` |-> `s0`,`G0` |-> `G0`,`tn0` |-> `tn0`,
    `s1` |-> `t4`,`G1` |-> `G4`,`tn1` |-> `tn4`,
    `Q` |-> `finalQ`,`R` |-> `finalR`]
    (Q.ISPEC `eval_expr cx (Builtin a (Concat n) args)`
      (Q.GEN `source`
        gasOutcomeFullGuardedTheory.gas_outcome_full_zero_prefix_guarded))) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED

Resume concat_sim_full[finish]:
  qspecl_then [`cx`,`a`,`n`,`args`] mp_tac exprSimHypsTheory.eval_expr_concat_bind >>
  (impl_tac >- first_assum ACCEPT_TAC) >> disch_then (fn th => rewrite_tac[th]) >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_bind_all >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_values >>
      qexistsl_tac [`mid`,`t`,`v`] >> fs[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_values >> simp[])
  >~ [`storage_trace_frame (eval_exprs _ _)`]
  >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]
  >- (gen_tac >> BETA_TAC >> simp[vyperStorageTraceTheory.storage_trace_frame_def]) >>
  qexists_tac `\H res ee G tn t. loopQ H res ee G tn t /\
    ~t.vs_halted /\ ee.gas_obs = []` >>
  conj_tac
  >~ [`storage_trace_domain _ _ _`]
  >- suspend "continuation" >>
  irule gasOutcomeFullComposeTheory.gas_outcome_full_post_source >>
  qpat_assum `gas_outcome_full _ _ _ _ _ _ loopQ loopR` (irule_at Any) >>
  conj_tac >- simp[] >> simp[Abbr `loopR`,Abbr `finalR`] >>
  rpt strip_tac >> Cases_on `res`
  >- (qpat_assum `expr_exit (INL _) _` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> simp[exprSimDefsTheory.expr_exit_def]) >>
  rename1 `expr_exit (INR ex) r` >> simp[] >>
  qspecl_then [`\vs:value list. Value (BytesV [])`,`INR ex : value list + exception`]
    (fn th => rewrite_tac[SIMP_RULE (srw_ss()) [] th])
    exprSimDefsTheory.expr_exit_success_map >> first_assum ACCEPT_TAC
QED

Resume concat_sim_full[continuation]:
  qx_genl_tac [`marks`,`res`,`ee`,`G5`,`tn5`,`t5`] >> BETA_TAC >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _ /\ _`
    (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qunabbrev_tac `loopQ` >> disch_then (strip_assume_tac o BETA_RULE) >>
  rename1 `res = INL vs` >> qpat_x_assum `res = INL vs` SUBST_ALL_TAC >>
  qspecl_then [`a`,`n`,`MAP expr_type args`,`vs`,`get_tenv cx`,`tvr`]
    mp_tac exprSimConcatResultTheory.concat_typed_result >>
  (impl_tac >-
    (rpt conj_tac >> asm_rewrite_tac[] >>
     simp[listTheory.LIST_REL_MAP1,combinTheory.o_DEF] >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `v` (map_every assume_tac o CONJUNCTS)) >>
  qabbrev_tac `payload = FLAT (MAP (\v. case v of BytesV bs => bs
    | StringV str => MAP (n2w o ORD) str | _ => []) vs)` >>
  `LENGTH payload < dimword (:256)` by
    (map_every mp_tac [Q.ASSUME `LENGTH (payload:word8 list) <=
       SUM (MAP concat_payload_capacity (MAP expr_type args))`,
       Q.ASSUME `32 + SUM (MAP concat_payload_capacity (MAP expr_type args)) <= bsz`,
       Q.ASSUME `bsz < dimword (:256)`] >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  `lookup_var bv t5 = SOME (n2w B)` by
    (qpat_assum `!z w. not_fresh_at s4 z /\ _ ==> _` irule >> simp[]) >>
  map_every assume_tac (CONJUNCTS (MATCH_MP
       (Q.SPEC `bv` (CONJUNCT1 (REWRITE_RULE [bodyPtrDefsTheory.ghost_kept_at_def]
         (Q.ASSUME `ghost_kept_at lo cenv es s4
           (G4:(string,num#num)fmap) tn4 t4 G5 tn5`))))
       (Q.ASSUME `not_fresh_at s4 bv`))) >>
  `ptr_covers G5 tn5 bv t5 bsz` by
    (map_every mp_tac [Q.ASSUME `ptr_covers G4 tn4 bv t4 bsz`,
       Q.ASSUME `lookup_var bv t4 = SOME (n2w B:bytes32)`,
       Q.ASSUME `lookup_var bv t5 = SOME (n2w B:bytes32)`,
       Q.ASSUME `FLOOKUP (G5:(string,num#num)fmap) bv = FLOOKUP G4 bv`,
       Q.ASSUME `op_taint tn5 (Var bv) = op_taint tn4 (Var bv)`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[bodyPtrDefsTheory.ptr_covers_def]) >>
  `s4.cs_next_var <= s5.cs_next_var` by
    (mp_tac (Q.ASSUME `ci_mono s4 s5`) >>
     POP_ASSUM_LIST (K all_tac) >> simp[exprLoweringPropsTheory.ci_mono_def]) >>
  `local_ptrs_reserved cenv s5` by
    (qspecl_then [`cenv`,`s4`,`s5`]
      mp_tac exprLoweringPropsTheory.local_ptrs_reserved_next_var >> simp[]) >>
  `not_fresh_at s5 bv /\ not_fresh_at s5 ov` by
    (conj_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `s4` >> simp[]) >>
  `!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at s5 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `s4` >> simp[]) >>
  `!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at s5 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `s4` >> simp[]) >>
  `!name lb lsz. local_region cenv ee.scopes t5 name lb lsz ==>
    regions_disjoint B 32 lb lsz` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!name lb lsz. local_region cenv ee.scopes t5 name lb lsz <=> _`
       (qspecl_then [`name`,`lb`,`lsz`] mp_tac) >>
     qpat_assum `!name lb lsz. local_region cenv es.scopes t4 name lb lsz ==> _ /\ _`
       (qspecl_then [`name`,`lb`,`lsz`] mp_tac) >>
     mp_tac (Q.ASSUME `local_region cenv ee.scopes t5 name lb lsz`) >>
     mp_tac (Q.ASSUME `32 <= bsz`) >>
     POP_ASSUM_LIST (K all_tac) >> simp[loweringStateRelDefsTheory.regions_disjoint_def] >>
     decide_tac) >>
  `!name lb lsz. local_region cenv es.scopes t4 name lb lsz ==>
    regions_disjoint B 32 lb lsz` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!name lb lsz. local_region cenv es.scopes t4 name lb lsz ==> _ /\ _`
       (qspecl_then [`name`,`lb`,`lsz`] mp_tac) >>
     map_every mp_tac [Q.ASSUME `local_region cenv es.scopes t4 name lb lsz`,
       Q.ASSUME `32 <= bsz`] >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `emit_op MLOAD [Var ov] s5 = (fo,s6)` by
    (map_every mp_tac [Q.ASSUME `emit_op MLOAD [ob.buf_operand] s5 = (fo,s6)`,
       Q.ASSUME `ob.buf_operand = Var ov`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> metis_tac[]) >>
  `emit_void MSTORE [Var bv;fo] s6 = (u',sb)` by
    (map_every mp_tac [Q.ASSUME `emit_void MSTORE [buf.buf_operand;fo] s6 = (u',sb)`,
       Q.ASSUME `buf.buf_operand = Var bv`] >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> metis_tac[]) >>
  mp_tac (Q.INST [`ov` |-> `ov`,`bv` |-> `bv`,`sa` |-> `s5`,`fo` |-> `fo`,
    `sm` |-> `s6`,`u` |-> `u'`,`sb` |-> `sb`,`func` |-> `func`,
    `cenv` |-> `cenv`,`ctx` |-> `ctx`,`s` |-> `t5`,`ow` |-> `ow`,
    `B` |-> `B`,`G` |-> `G5`,`tn` |-> `tn5`,`bsz` |-> `bsz`,
    `inst` |-> `binst`,`k` |-> `LENGTH (payload:word8 list)`,
    `H0` |-> `storage_trace_horizon ee.storage_trace`,`cx` |-> `cx`,`es` |-> `ee`,
    `lo` |-> `lo`,`d` |-> `d`,`explicit` |-> `gas_explicit_sites ctx shadow_ctx`,
    `PG` |-> `PG`] bodyFullBuiltinConcatFrameTheory.concat_suffix_full) >>
  (impl_tac >-
    (simp[Abbr `binst`,venomInstTheory.mk_inst_def] >>
     first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`t6`,`G6`,`tn6`] (map_every assume_tac o CONJUNCTS)) >>
  disj1_tac >> qexists_tac `vs` >> conj_tac >- REFL_TAC >>
  mp_tac (Q.INST [`DF` |-> `DF`,`lo` |-> `lo`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`,`ctx` |-> `ctx`,
    `func` |-> `func`,`PG` |-> `PG`,`tops` |-> `cx_tops cx`,
    `cx` |-> `cx`,`st0` |-> `st0`,`es` |-> `ee`,`ee` |-> `ee`,
    `s` |-> `t5`,`G` |-> `G5`,`tn` |-> `tn5`,
    `t` |-> `t6`,`G'` |-> `G6`,`tn'` |-> `tn6`,
    `res` |-> `INL (Value v):eval_result + exception`,
    `Q` |-> `finalQ`,`R` |-> `finalR`]
    (Q.ISPEC `\st:evaluation_state.
      ((case evaluate_concat n vs of INL v => INL (Value v)
        | INR err => INR (Error err)),st)`
      (Q.GEN `source` gasOutcomeFullComposeTheory.gas_outcome_full_pure))) >>
  (impl_tac >-
    (conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- simp[] >> qx_gen_tac `H` >> disch_tac >> conj_tac
     >- first_assum MATCH_ACCEPT_TAC >> suspend "post")) >>
  disch_then ACCEPT_TAC
QED

Resume concat_sim_full[post]:
  `ee with gas_obs := [] = ee` by
    (qpat_assum `ee.gas_obs = []` (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _ /\ _`
    (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (strip_assume_tac o BETA_RULE) >>
  qpat_x_assum `INL vs = INL _`
    (SUBST_ALL_TAC o SIMP_RULE (srw_ss()) []) >>
  qpat_x_assum `t6 = _` kall_tac >>
  `stmt_state_rel H ctx func cenv cx ee t6` by
    (qpat_assum `!H. stmt_state_rel H ctx func cenv cx ee t5 ==> _`
       (qspec_then `H` mp_tac) >> simp[]) >>
  `ghost_inv_at (DF H) lo d cenv cx ee G6 tn6 t6` by
    (qpat_assum `!D. ghost_inv_at D lo d cenv cx ee G5 tn5 t5 ==> _`
       (qspec_then `DF H` mp_tac) >> simp[]) >>
  `lookup_var bv t6 = SOME (n2w B)` by
    (qpat_assum `!x. not_fresh_at s5 x ==> _ /\ _ /\ _`
       (qspec_then `bv` mp_tac) >> simp[]) >>
  `mem_bytes_at (B+32) (LENGTH payload) t5.vs_memory = payload` by
    (qpat_assum `mem_bytes_at (B+32) _ t5.vs_memory = _` mp_tac >>
     qunabbrev_tac `payload` >> POP_ASSUM_LIST (K all_tac) >>
     simp[valueEncodingDefsTheory.mem_bytes_at_def]) >>
  `mem_bytes_at (B+32) (LENGTH payload) t6.vs_memory = payload` by
    (qpat_assum `!p n. _ ==> mem_bytes_at p n t6.vs_memory = _`
       (qspecl_then [`B+32`,`LENGTH payload`] mp_tac) >> simp[]) >>
  `val_in_memory tvr v B t6.vs_memory` by
    (qpat_assum `!off mem. val_in_memory tvr v off mem <=> _`
       (qspecl_then [`B`,`t6.vs_memory`] mp_tac) >>
     simp[valueEncodingPropsTheory.mem_word_at_eq_mload]) >>
  `!i. B+32 <= i /\ i < B+32+LENGTH payload ==> i NOTIN tn6.t_mem` by
    (rpt gen_tac >> strip_tac >>
     `i NOTIN tn5.t_mem` by
       (qpat_assum `!i. B+32 <= i /\ _ ==> i NOTIN tn5.t_mem`
          (qspec_then `i` mp_tac) >> simp[Abbr `payload`]) >>
     map_every mp_tac [Q.ASSUME `i NOTIN tn5.t_mem`,
       Q.ASSUME `tn6.t_mem SUBSET tn5.t_mem`] >>
     POP_ASSUM_LIST (K all_tac) >> simp[pred_setTheory.SUBSET_DEF] >> metis_tac[]) >>
  Q.SUBGOAL_THEN `a = BaseT (BytesT (Dynamic n)) \/ a = BaseT (StringT n)` ASSUME_TAC
  >- (qpat_assum `a = BaseT (BytesT (Dynamic n)) /\ _ \/
       a = BaseT (StringT n) /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `val_footprint tvr v <= 32 + SUM (MAP concat_payload_capacity (MAP expr_type args))` by
    (map_every mp_tac [Q.ASSUME `val_footprint tvr v = 32 + LENGTH (payload:word8 list)`,
       Q.ASSUME `LENGTH (payload:word8 list) <=
         SUM (MAP concat_payload_capacity (MAP expr_type args))`] >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  `val_store_size tvr v <= bsz` by
    (map_every mp_tac [Q.ASSUME `a = BaseT (BytesT (Dynamic n)) \/ a = BaseT (StringT n)`,
       Q.ASSUME `evaluate_type (get_tenv cx) a = SOME tvr`,
       Q.ASSUME `val_footprint tvr v <=
         32 + SUM (MAP concat_payload_capacity (MAP expr_type args))`] >>
     qunabbrev_tac `bsz` >> POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[] >>
     drule vyperTypeConversionsTheory.evaluate_type_BaseT_SOME >> strip_tac >> gvs[] >>
     Cases_on `v` >>
     gvs[loweringPostsTheory.val_footprint_def,exprSimPropsTheory.val_store_size_def,
       valueEncodingTheory.type_memory_size_def] >>
     drule exprSimPropsTheory.word_size_monotone >>
     simp[exprLoweringTheory.concat_alloc_size_def,vfmConstantsTheory.word_size_def,
       arithmeticTheory.MAX_DEF] >> decide_tac) >>
  `type_memory_bytes cenv (lowered_value_type cenv (Builtin a (Concat n) args)) <= bsz` by
    (mp_tac (Q.ASSUME `a = BaseT (BytesT (Dynamic n)) \/ a = BaseT (StringT n)`) >>
     qunabbrev_tac `bsz` >> POP_ASSUM_LIST (K all_tac) >> strip_tac >>
     gvs[exprLoweringTheory.lowered_value_type_def,exprLoweringTheory.concat_buffer_type_def,
       compileEnvTheory.type_memory_bytes_def,exprLoweringTheory.concat_alloc_size_def,
       listTheory.MAP_MAP_o,combinTheory.o_DEF,vfmConstantsTheory.word_size_def] >>
     simp[arithmeticTheory.MAX_DEF]) >>
  `B < dimword (:256)` by
    (mp_tac (Q.ASSUME `B+bsz < dimword (:256)`) >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  `!i. B <= i /\ i < B+val_footprint tvr v ==> i NOTIN tn6.t_mem` by
    (rewrite_tac[Q.ASSUME `val_footprint tvr v = 32+LENGTH (payload:word8 list)`] >>
     rpt gen_tac >> strip_tac >> Cases_on `i < B+32`
     >- (qpat_assum `!i. B <= i /\ i < B+32 ==> i NOTIN tn6.t_mem`
          (qspec_then `i` mp_tac) >> simp[]) >>
     qpat_assum `!i. B+32 <= i /\ _ ==> i NOTIN tn6.t_mem`
       (qspec_then `i` mp_tac) >>
     (impl_tac >- decide_tac) >> disch_then ACCEPT_TAC) >>
  mp_tac (SIMP_RULE (srw_ss()) [Q.ASSUME `B < dimword (:256)`]
    (Q.INST [`cx` |-> `cx`,`ty` |-> `a`,`vt` |-> `tvr`,`v` |-> `v`,
    `b` |-> `n2w B:bytes32`,`s` |-> `t6`,`root` |-> `bv`,
    `G` |-> `G6`,`tn` |-> `tn6`,`capacity` |-> `bsz`]
    reasonCodeResourcesPtrTheory.clean_memory_representation_ptr)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_tac >>
  assume_tac (CONJUNCT1 (REWRITE_RULE [bodyPtrDefsTheory.ptr_covers_def]
    (Q.ASSUME `ptr_covers G6 tn6 bv t6 bsz`))) >>
  qspecl_then [`cx`,`a`,`Value v`,`a`,`base_ptr buf`,`ee`,`G6`,`tn6`,`t6`,`v`]
    mp_tac bodyPtrAttributeFieldsTheory.ptr_vv_ok_memory >>
  (impl_tac >-
    (simp[NoAsms,contextTheory.base_ptr_def,Q.ASSUME `buf.buf_operand = Var bv`,
       vyperStateTheory.read_result_def,vyperStateTheory.return_def] >>
     conj_tac >> first_assum ACCEPT_TAC)) >> disch_tac >>
  `ptr_buf_ok cenv (Builtin a (Concat n) args) (Var bv) G6 t6` by
    (map_every mp_tac [Q.ASSUME `ptr_covers G6 tn6 bv t6 bsz`,
       Q.ASSUME `type_memory_bytes cenv
         (lowered_value_type cenv (Builtin a (Concat n) args)) <= bsz`] >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[bodyPtrDefsTheory.ptr_covers_def,bodyPtrDefsTheory.ptr_buf_ok_def,
       venomStateTheory.eval_operand_def] >> rpt strip_tac >> gvs[] >>
     goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
  `s0.vs_alloca_next <= t6.vs_alloca_next` by
    (map_every mp_tac [Q.ASSUME `s0.vs_alloca_next <= t4.vs_alloca_next`,
       Q.ASSUME `t4.vs_alloca_next <= t5.vs_alloca_next`,
       Q.ASSUME `t6.vs_alloca_next = t5.vs_alloca_next`] >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  qunabbrev_tac `finalQ` >> BETA_TAC >>
  qexists_tac `Value v` >>
  simp[NoAsms,Q.ASSUME `ee with gas_obs := [] = ee`,
    Q.ASSUME `vv = LocatedValue a (base_ptr buf)`,
    Q.ASSUME `t6.vs_current_bb = sb.cs_current_bb`,
    Q.ASSUME `t6.vs_inst_idx = LENGTH sb.cs_current_insts`,
    Q.ASSUME `alloca_history func t6`,
    Q.ASSUME `s0.vs_alloca_next <= t6.vs_alloca_next`,
    Q.ASSUME `ghost_inv_at (DF H) lo d cenv cx ee G6 tn6 t6`,
    SIMP_RULE (srw_ss()) [contextTheory.base_ptr_def,Q.ASSUME `buf.buf_operand = Var bv`]
      (Q.ASSUME `ptr_vv_ok cx a (Value v) (LocatedValue a (base_ptr buf)) ee G6 tn6 t6`),
    Q.ASSUME `ptr_buf_ok cenv (Builtin a (Concat n) args) (Var bv) G6 t6`,
    contextTheory.base_ptr_def,Q.ASSUME `buf.buf_operand = Var bv`,
    contextTheory.vv_location_def,contextTheory.vv_operand_def,
    vyperASTTheory.expr_type_def] >>
  rpt conj_tac
  >~ [`vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`]
  >- suspend "vvpost"
  >~ [`vv_store_bound _ _ _ _ _ _ _`]
  >- suspend "storebound"
  >~ [`ghost_inv_at _ _ _ _ _ _ _ _ _`]
  >- first_assum ACCEPT_TAC >>
  suspend "kept"
QED

Resume concat_sim_full[vvpost]:
  `sa.cs_next_id < s5.cs_next_id+2` by
    (map_every mp_tac [Q.ASSUME `ci_mono s4 s5`,
       Q.ASSUME `s4.cs_next_id = sa.cs_next_id+4`] >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
  `!name lb lsz. local_region cenv ee.scopes t6 name lb lsz <=>
    local_region cenv ee.scopes t5 name lb lsz` by
    (rpt gen_tac >>
     qspecl_then [`cenv`,`s5`,`ee.scopes`,`t5`,`t6`,`name`,`lb`,`lsz`]
       mp_tac exprSimConcatResultTheory.concat_local_region_vars >>
     (impl_tac >-
       (conj_tac >- first_assum ACCEPT_TAC >> rpt gen_tac >> disch_tac >>
        qpat_assum `!x. not_fresh_at s5 x ==> _ /\ _ /\ _`
          (qspec_then `x` mp_tac) >> simp[])) >> disch_then ACCEPT_TAC) >>
  `!name lb lsz. local_region cenv ee.scopes t6 name lb lsz ==>
    B+bsz <= lb \/ lb+lsz <= B` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!name lb lsz. local_region cenv ee.scopes t6 name lb lsz <=> _`
       (qspecl_then [`name`,`lb`,`lsz`] mp_tac) >>
     qpat_assum `!name lb lsz. local_region cenv ee.scopes t5 name lb lsz <=> _`
       (qspecl_then [`name`,`lb`,`lsz`] mp_tac) >>
     qpat_assum `!name lb lsz. local_region cenv es.scopes t4 name lb lsz ==> _ /\ _`
       (qspecl_then [`name`,`lb`,`lsz`] mp_tac) >>
     mp_tac (Q.ASSUME `local_region cenv ee.scopes t6 name lb lsz`) >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  `wb_frame cenv es ee sa s0 t6` by suspend "wb" >>
  `EVERY ($~ o expr_has_effect) args ==> pure_frame cenv func es sa s0 t6` by
    suspend "pure" >>
  mp_tac (SIMP_RULE (srw_ss()) [vyperASTTheory.expr_type_def,
    contextTheory.base_ptr_def,Q.ASSUME `buf.buf_operand = Var bv`]
    (Q.INST [`e` |-> `Builtin a (Concat n) args`,`cenv` |-> `cenv`,
      `cx` |-> `cx`,
      `ctx` |-> `ctx`,`func` |-> `func`,
      `tv` |-> `tvr`,`v` |-> `v`,`w` |-> `n2w B:bytes32`,
      `s` |-> `t6`,`p` |-> `base_ptr buf`,`aid` |-> `sa.cs_next_id`,
      `b` |-> `B`,`sz` |-> `bsz`,`sa` |-> `sa`,`sb` |-> `sb`,
      `es` |-> `es`,`es'` |-> `ee`,`s0` |-> `s0`]
      (Q.ISPEC `(H:(bool # bytes32 # type_value) list # num list)`
        (Q.GEN `H` exprSimHashTheory.vv_post_allocated_memory_intro)))) >>
  (impl_tac >-
    (simp[valueEncodingPropsTheory.mem_word_at_eq_mload,venomStateTheory.eval_operand_def] >>
     qx_genl_tac [`name`,`lb`,`lsz`] >> disch_tac >>
     qpat_assum `!name lb lsz. local_region cenv es.scopes t4 name lb lsz ==> _ /\ _`
       (qspecl_then [`name`,`lb`,`lsz`] mp_tac) >> simp[])) >>
  disch_then ACCEPT_TAC
QED

Resume concat_sim_full[storebound]:
  map_every mp_tac [Q.ASSUME `B < dimword (:256)`,
    Q.ASSUME `lookup_var bv t6 = SOME (n2w B)`,
    Q.ASSUME `val_store_size tvr v <= bsz`,
    Q.ASSUME `type_memory_bytes cenv
      (lowered_value_type cenv (Builtin a (Concat n) args)) <= bsz`,
    Q.ASSUME `evaluate_type (get_tenv cx) a = SOME tvr`,
    Q.ASSUME `B+bsz <= t4.vs_alloca_next`,
    Q.ASSUME `t4.vs_alloca_next <= t5.vs_alloca_next`,
    Q.ASSUME `t6.vs_alloca_next = t5.vs_alloca_next`,
    Q.ASSUME `a = BaseT (BytesT (Dynamic n)) \/ a = BaseT (StringT n)`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[] >>
  simp[exprSimMemDefsTheory.vv_store_bound_def,
    venomStateTheory.eval_operand_def,vyperStateTheory.read_result_def,
    vyperStateTheory.return_def] >> rpt strip_tac >> gvs[] >>
  drule vyperTypeConversionsTheory.evaluate_type_BaseT_SOME >>
  strip_tac >> gvs[exprLoweringTheory.lowered_value_type_def,
    exprLoweringTheory.concat_buffer_type_def,compileEnvTheory.type_memory_bytes_def,
    vyperValueTheory.evaluate_type_def,valueEncodingTheory.type_memory_size_def,
    vfmConstantsTheory.word_size_def] >> decide_tac
QED

Resume concat_sim_full[kept]:
  `!name lb lsz. local_region cenv es.scopes t4 name lb lsz <=>
    local_region cenv es.scopes s0 name lb lsz` by
    (rpt gen_tac >>
     qspecl_then [`cenv`,`sa`,`es.scopes`,`s0`,`t4`,`name`,`lb`,`lsz`]
       mp_tac exprSimConcatResultTheory.concat_local_region_vars >>
     (impl_tac >-
       (conj_tac >- first_assum ACCEPT_TAC >> rpt gen_tac >> disch_tac >>
        qpat_assum `!x. not_fresh_at sa x ==> _ /\ _ /\ _`
          (qspec_then `x` mp_tac) >> simp[])) >> disch_then ACCEPT_TAC) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 G5 tn5` by
    (irule wordArgsPtrTheory.ghost_kept_at_trans >>
     qexistsl_tac [`G4`,`es`,`t4`,`s4`,`tn4`] >>
     simp[NoAsms,Q.ASSUME `s4.cs_next_var = sa.cs_next_var+3`,
       Q.ASSUME `s4.cs_next_id = sa.cs_next_id+4`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `sa.cs_next_var <= s5.cs_next_var` by
    (map_every mp_tac [Q.ASSUME `s4.cs_next_var = sa.cs_next_var+3`,
       Q.ASSUME `s4.cs_next_var <= s5.cs_next_var`] >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  irule bodyFullUnwrapRunTheory.ghost_kept_at_clean_suffix >>
  qexistsl_tac [`G5`,`tn5`] >>
  rpt conj_tac >| [
    qx_gen_tac `x` >> disch_tac >>
      `not_fresh_at s5 x` by
        (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
      qpat_assum `!x. not_fresh_at s5 x ==> _ /\ _ /\ _`
        (qspec_then `x` mp_tac) >> simp[],
    first_assum ACCEPT_TAC,
    first_assum ACCEPT_TAC
  ]
QED

Resume concat_sim_full[wb]:
  `sa.cs_next_var <= s4.cs_next_var /\ sa.cs_next_var <= s5.cs_next_var` by
    (map_every mp_tac [Q.ASSUME `s4.cs_next_var = sa.cs_next_var+3`,
       Q.ASSUME `s4.cs_next_var <= s5.cs_next_var`] >>
     POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
  rewrite_tac[loweringPostsTheory.wb_frame_def] >> rpt conj_tac
  >- (qx_genl_tac [`x`,`w`] >> strip_tac >>
      `not_fresh_at s4 x /\ not_fresh_at s5 x` by
        (conj_tac >> irule freshWritesTheory.not_fresh_at_mono >>
         qexists_tac `sa` >> simp[]) >>
      `lookup_var x t4 = SOME w` by
        (qpat_assum `!x. not_fresh_at sa x ==> _ /\ _ /\ _`
           (qspec_then `x` mp_tac) >> simp[]) >>
      `lookup_var x t5 = SOME w` by
        (qpat_assum `!z w. not_fresh_at s4 z /\ _ ==> _` irule >> simp[]) >>
      qpat_assum `!x. not_fresh_at s5 x ==> _ /\ _ /\ _`
        (qspec_then `x` mp_tac) >> simp[])
  >- (qx_genl_tac [`aid`,`b`] >> disch_tac >>
      rewrite_tac[Q.ASSUME `t6.vs_allocas = t5.vs_allocas`] >>
      qpat_assum `!aid a. FLOOKUP t4.vs_allocas aid = SOME a ==> _` irule >>
      qpat_assum `!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==> _` irule >>
      first_assum ACCEPT_TAC)
  >- suspend "wbmem" >>
  suspend "wblocals"
QED

Resume concat_sim_full[wbmem]:
  qx_genl_tac [`aid`,`off`,`sz`] >> strip_tac >>
  `regions_disjoint B bsz off sz /\ regions_disjoint (w2n ow) 64 off sz` by
    (qpat_assum `!aid b len. aid < sa.cs_next_id /\ _ ==> _`
       (qspecl_then [`aid`,`off`,`sz`] mp_tac) >> simp[]) >>
  `FLOOKUP t4.vs_allocas aid = SOME (off,sz)` by
    (qpat_assum `!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==> _` irule >>
     first_assum ACCEPT_TAC) >>
  `!name lb lsz. local_region cenv es.scopes t4 name lb lsz <=>
    local_region cenv es.scopes s0 name lb lsz` by
    (rpt gen_tac >>
     qspecl_then [`cenv`,`sa`,`es.scopes`,`s0`,`t4`,`name`,`lb`,`lsz`]
       mp_tac exprSimConcatResultTheory.concat_local_region_vars >>
     (impl_tac >-
       (conj_tac >- first_assum ACCEPT_TAC >> rpt gen_tac >> disch_tac >>
        qpat_assum `!x. not_fresh_at sa x ==> _ /\ _ /\ _`
          (qspec_then `x` mp_tac) >> simp[])) >> disch_then ACCEPT_TAC) >>
  `mem_bytes_at off sz t4.vs_memory = mem_bytes_at off sz s0.vs_memory` by
    (qpat_assum `!p n. _ ==> mem_bytes_at p n t4.vs_memory = _` irule >>
     mp_tac (Q.ASSUME `regions_disjoint (w2n (ow:bytes32)) 64 off sz`) >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `mem_bytes_at off sz t5.vs_memory = mem_bytes_at off sz t4.vs_memory` by
    (qpat_assum `!aid p n. FLOOKUP t4.vs_allocas aid = SOME (p,n) /\ _ ==> _`
       (qspecl_then [`aid`,`off`,`sz`] mp_tac) >>
     (impl_tac >-
       (simp[NoAsms,Q.ASSUME `FLOOKUP t4.vs_allocas aid = SOME (off,sz)`] >>
        rpt conj_tac
        >- (map_every mp_tac [Q.ASSUME `aid < sa.cs_next_id`,
              Q.ASSUME `s4.cs_next_id = sa.cs_next_id+4`] >>
            POP_ASSUM_LIST (K all_tac) >> decide_tac)
        >- (mp_tac (Q.ASSUME `regions_disjoint B bsz off sz`) >>
            POP_ASSUM_LIST (K all_tac) >>
            simp[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[])
        >- (mp_tac (Q.ASSUME `regions_disjoint (w2n (ow:bytes32)) 64 off sz`) >>
            POP_ASSUM_LIST (K all_tac) >>
            simp[loweringStateRelDefsTheory.regions_disjoint_def] >> metis_tac[]) >>
        rewrite_tac[Q.ASSUME `!name lb lsz.
          local_region cenv es.scopes t4 name lb lsz <=>
          local_region cenv es.scopes s0 name lb lsz`] >>
        first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
  `mem_bytes_at off sz t6.vs_memory = mem_bytes_at off sz t5.vs_memory` by
    (qpat_assum `!p n. _ ==> mem_bytes_at p n t6.vs_memory = _` irule >>
     map_every mp_tac [Q.ASSUME `regions_disjoint B bsz off sz`,
       Q.ASSUME `32 <= bsz`] >> POP_ASSUM_LIST (K all_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  simp[]
QED

Resume concat_sim_full[wblocals]:
  `locals_kept cenv es es s0 t4` by
    (irule exprSimPropsTheory.locals_kept_regions >>
     qx_genl_tac [`name`,`lb`,`lsz`] >> disch_tac >>
     `regions_disjoint (w2n ow) 64 lb lsz` by
       (qpat_assum `!name b len. local_region cenv es.scopes s0 name b len ==> _ /\ _`
          (qspecl_then [`name`,`lb`,`lsz`] mp_tac) >> simp[]) >>
     qpat_assum `!p n. _ ==> mem_bytes_at p n t4.vs_memory = _` irule >>
     mp_tac (Q.ASSUME `regions_disjoint (w2n (ow:bytes32)) 64 lb lsz`) >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `locals_kept cenv es ee s0 t5` by
    (match_mp_tac (Q.SPECL [`cenv`,`es`,`es`,`ee`,`sa`,`s0`,`t4`,`t5`]
       exprBopSimPropsTheory.locals_kept_trans) >>
     rpt conj_tac >| [
       first_assum ACCEPT_TAC,
       qx_genl_tac [`x`,`w`] >> strip_tac >>
         qpat_assum `!x. not_fresh_at sa x ==> _ /\ _ /\ _`
           (qspec_then `x` mp_tac) >> simp[],
       first_assum ACCEPT_TAC,
       first_assum ACCEPT_TAC
     ]) >>
  match_mp_tac (Q.SPECL [`cenv`,`es`,`ee`,`s0`,`t5`,`t6`]
    exprSimPropsTheory.locals_kept_regions_tail) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qx_genl_tac [`name`,`lb`,`lsz`] >> disch_tac >>
  `regions_disjoint B bsz lb lsz` by
    (qpat_assum `!name b len. local_region cenv es.scopes s0 name b len ==> _ /\ _`
       (qspecl_then [`name`,`lb`,`lsz`] mp_tac) >> simp[]) >>
  qpat_assum `!p n. _ ==> mem_bytes_at p n t6.vs_memory = _` irule >>
  map_every mp_tac [Q.ASSUME `regions_disjoint B bsz lb lsz`,
    Q.ASSUME `32 <= bsz`] >> POP_ASSUM_LIST (K all_tac) >>
  simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac
QED

Resume concat_sim_full[pure]:
  disch_tac >>
  `~EXISTS expr_has_effect args` by
    (mp_tac (Q.ASSUME `EVERY ($~ o expr_has_effect) args`) >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[listTheory.EVERY_MEM,listTheory.EXISTS_MEM,combinTheory.o_DEF]) >>
  qpat_assum `~EXISTS expr_has_effect args ==> _ /\ _` mp_tac >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `!name lb lsz. local_region cenv es.scopes t4 name lb lsz <=>
    local_region cenv es.scopes s0 name lb lsz` by
    (rpt gen_tac >>
     qspecl_then [`cenv`,`sa`,`es.scopes`,`s0`,`t4`,`name`,`lb`,`lsz`]
       mp_tac exprSimConcatResultTheory.concat_local_region_vars >>
     (impl_tac >-
       (conj_tac >- first_assum ACCEPT_TAC >> rpt gen_tac >> disch_tac >>
        qpat_assum `!x. not_fresh_at sa x ==> _ /\ _ /\ _`
          (qspec_then `x` mp_tac) >> simp[])) >> disch_then ACCEPT_TAC) >>
  rewrite_tac[loweringPostsTheory.pure_frame_def] >>
  conj_tac >- suspend "purelocals" >> suspend "pureglobal"
QED

Resume concat_sim_full[purelocals]:
  qx_genl_tac [`name`,`lb`,`lsz`] >> disch_tac >>
  `regions_disjoint B bsz lb lsz /\ regions_disjoint (w2n ow) 64 lb lsz` by
    (qpat_assum `!name b len. local_region cenv es.scopes s0 name b len ==> _ /\ _`
       (qspecl_then [`name`,`lb`,`lsz`] mp_tac) >> simp[]) >>
  `mem_bytes_at lb lsz t4.vs_memory = mem_bytes_at lb lsz s0.vs_memory` by
    (qpat_assum `!p n. _ ==> mem_bytes_at p n t4.vs_memory = _` irule >>
     mp_tac (Q.ASSUME `regions_disjoint (w2n (ow:bytes32)) 64 lb lsz`) >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `mem_bytes_at lb lsz t5.vs_memory = mem_bytes_at lb lsz t4.vs_memory` by
    (qpat_assum `!name lb lsz. local_region cenv es.scopes t4 name lb lsz ==>
       mem_bytes_at lb lsz t5.vs_memory = _`
       (qspecl_then [`name`,`lb`,`lsz`] mp_tac) >> simp[]) >>
  `mem_bytes_at lb lsz t6.vs_memory = mem_bytes_at lb lsz t5.vs_memory` by
    (qpat_assum `!p n. _ ==> mem_bytes_at p n t6.vs_memory = _` irule >>
     map_every mp_tac [Q.ASSUME `regions_disjoint B bsz lb lsz`,
       Q.ASSUME `32 <= bsz`] >> POP_ASSUM_LIST (K all_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  simp[]
QED

Resume concat_sim_full[pureglobal]:
  qx_genl_tac [`off`,`len`] >> disch_tac >>
  `FLOOKUP t6.vs_allocas binst.inst_id = SOME (B,bsz) /\
   FLOOKUP t6.vs_allocas oinst.inst_id = SOME (w2n ow,64)` by
    simp[Q.ASSUME `t6.vs_allocas = t5.vs_allocas`] >>
  `regions_disjoint off len B bsz` by
    (qpat_assum `!inst b sz. MEM inst (fn_insts func) /\
       inst.inst_opcode = ALLOCA /\ sa.cs_next_id <= inst.inst_id /\ _ ==>
       regions_disjoint off len b sz`
       (qspecl_then [`binst`,`B`,`bsz`] mp_tac) >>
     simp[Abbr `binst`,venomInstTheory.mk_inst_def]) >>
  `regions_disjoint off len (w2n ow) 64` by
    (qpat_assum `!inst b sz. MEM inst (fn_insts func) /\
       inst.inst_opcode = ALLOCA /\ sa.cs_next_id <= inst.inst_id /\ _ ==>
       regions_disjoint off len b sz`
       (qspecl_then [`oinst`,`w2n ow`,`64`] mp_tac) >>
     simp[Abbr `oinst`,venomInstTheory.mk_inst_def]) >>
  `mem_bytes_at off len t4.vs_memory = mem_bytes_at off len s0.vs_memory` by
    (qpat_assum `!p n. _ ==> mem_bytes_at p n t4.vs_memory = _` irule >>
     mp_tac (Q.ASSUME `regions_disjoint off len (w2n (ow:bytes32)) 64`) >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  `mem_bytes_at off len t5.vs_memory = mem_bytes_at off len t4.vs_memory` by
    (qpat_assum `!p n. _ /\ _ /\ (!inst b sz. _ ==> _) ==>
       mem_bytes_at p n t5.vs_memory = _`
       (qspecl_then [`off`,`len`] mp_tac) >>
     (impl_tac >-
       (conj_tac
        >- (mp_tac (Q.ASSUME `regions_disjoint off len B bsz`) >>
            POP_ASSUM_LIST (K all_tac) >>
            simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
        conj_tac
        >- (mp_tac (Q.ASSUME `regions_disjoint off len (w2n (ow:bytes32)) 64`) >>
            POP_ASSUM_LIST (K all_tac) >>
            simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
        qx_genl_tac [`inst`,`b`,`sz`] >> strip_tac >>
        `sa.cs_next_id <= inst.inst_id` by
          (map_every mp_tac [Q.ASSUME `s4.cs_next_id = sa.cs_next_id+4`,
             Q.ASSUME `s4.cs_next_id <= inst.inst_id`] >>
           POP_ASSUM_LIST (K all_tac) >> decide_tac) >>
        qpat_assum `!inst b sz. MEM inst (fn_insts func) /\
          inst.inst_opcode = ALLOCA /\ sa.cs_next_id <= inst.inst_id /\ _ ==>
          regions_disjoint off len b sz`
          (qspecl_then [`inst`,`b`,`sz`] mp_tac) >>
        simp[Q.ASSUME `t6.vs_allocas = t5.vs_allocas`])) >>
     disch_then ACCEPT_TAC) >>
  `mem_bytes_at off len t6.vs_memory = mem_bytes_at off len t5.vs_memory` by
    (qpat_assum `!p n. _ ==> mem_bytes_at p n t6.vs_memory = _` irule >>
     map_every mp_tac [Q.ASSUME `regions_disjoint off len B bsz`,
       Q.ASSUME `32 <= bsz`] >> POP_ASSUM_LIST (K all_tac) >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  simp[]
QED

Finalise concat_sim_full
