(* Conditional linked simulation for the reached AddMod/MulMod operand prefix. *)
Theory bodyWordModOperandsMods
Ancestors
  bodyWordModSourceCutsMods bodyWordModPairedCutsMods bodyWordModReachedPrefixMods
  bodyWordModThirdEntryMods bodyWordModParentOutcomeMods
  bodyFullPredsMods bodyFullPostsMods bodyFullShadowBodyInv
  bodySimFull bodySim exprSimHypsDefs exprSimWordBuiltins exprSimSource exprLowering
  exprLoweringProps compileEnv gasShadowState gasShadow
  exprSimFullBundleProps loweringPosts builtinMath ptrDiscipline fragExec
  fragGasOriginPtr valueEncoding bodyPtrDefs gasContext
  vyperTypeSystem vyperTypeBuiltins vyperContext vyperInterpreter vyperState vyperAST
  vyperStorageTrace vyperStorageFootprint list finite_map

Theorem modular_sim_from_suffix_mods:
  (!DF lo explicit ctx func PG d cenv cx st0 ee sm sb bt x y z op t G1 tn1
      ann ts (va:bytes32) (vb:bytes32) (vc:bytes32).
    (bt = AddMod \/ bt = MulMod) /\
    (if bt = AddMod then compile_addmod else compile_mulmod) x y z sm = (op,sb) /\
    eval_operand x t = SOME va /\ eval_operand y t = SOME vb /\
    eval_operand z t = SOME vc /\
    op_taint tn1 x = {} /\ op_taint tn1 y = {} /\ op_taint tn1 z = {} /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\ local_ptrs_reserved cenv sm /\
    (!q sz. cenv.ce_return_buf = SOME (PtrVar (Var q) sz) ==> not_fresh_at sm q) /\
    (!q sz. cenv.ce_return_pc = SOME (PtrVar (Var q) sz) ==> not_fresh_at sm q) /\
    ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func t /\
    storage_trace_domain cx st0 ee.storage_trace /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func cenv cx ee t /\
      immutable_frame_mods func cenv cx ee t /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G1 tn1 t) ==>
    ?r t' G2 tn2.
      (vc = 0w ==>
        r = Abort Revert_abort t' /\ G2 = G1 /\ tn2 = tn1 /\
        builtin_result cx ee.accounts ann bt ts
          [IntV (&w2n va); IntV (&w2n vb); IntV (&w2n vc)] =
          INR (Error (RuntimeError (if bt = AddMod then
            "AddMod division by zero" else "MulMod division by zero"))) /\
        exit_result r /\
        expr_exit (builtin_result cx ee.accounts ann bt ts
          [IntV (&w2n va); IntV (&w2n vb); IntV (&w2n vc)]) r) /\
      (vc <> 0w ==>
        r = OK t' /\
        builtin_result cx ee.accounts ann bt ts
          [IntV (&w2n va); IntV (&w2n vb); IntV (&w2n vc)] =
          INL (IntV (&w2n ((if bt = AddMod then addmod else mulmod) va vb vc))) /\
        eval_operand op t' = SOME ((if bt = AddMod then addmod else mulmod) va vb vc) /\
        op_taint tn2 op = {} /\ op_prov G2 op = NONE /\
        ~t'.vs_halted /\ t'.vs_current_bb = sb.cs_current_bb /\
        t'.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history func t' /\
        t'.vs_alloca_next = t.vs_alloca_next /\ t'.vs_allocas = t.vs_allocas /\
        t'.vs_fmp = t.vs_fmp /\ t'.vs_memory = t.vs_memory /\
        t'.vs_call_ctx = t.vs_call_ctx /\ t'.vs_accounts = t.vs_accounts /\
        t'.vs_transient = t.vs_transient /\ t'.vs_immutables = t.vs_immutables /\
        t'.vs_data_section = t.vs_data_section /\
        t'.vs_gas_readings = t.vs_gas_readings /\
        (ctx_has_dalloca ctx ==> allocas_below_fmp t') /\
        tn2.t_mem = tn1.t_mem /\ tn2.t_stor = tn1.t_stor /\
        tn2.t_trans = tn1.t_trans /\ tn2.t_imm = tn1.t_imm /\
        (!q. not_fresh_at sm q ==>
          lookup_var q t' = lookup_var q t /\
          FLOOKUP G2 q = FLOOKUP G1 q /\
          op_taint tn2 (Var q) = op_taint tn1 (Var q)) /\
        ghost_kept_at lo cenv ee sm G1 tn1 t G2 tn2) /\
      (!H. valid_horizon cx st0 H ee.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
          (t,G1,tn1) [] (r,G2,tn2) /\
        (vc <> 0w ==>
          stmt_state_rel H ctx func cenv cx ee t' /\
          immutable_frame_mods func cenv cx ee t' /\
          ghost_inv_at_mods (DF H) lo d cenv cx ee G2 tn2 t'))) /\
  (!DF lo d ctx shadow_ctx PG func shadow_func cenv cx ty e es.
    is_word_type (post_value_type cenv e) /\
    expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty e es /\
    (!sa. ?t op sb. compile_expr cenv ty e sa = (StackValue t op,sb)) /\
    (!s tv s'. eval_expr cx e s = (INL tv,s') ==> ?v. tv = Value v) ==>
    expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty e es) /\
  (bt = AddMod \/ bt = MulMod) /\
  (builtin_args_length_ok bt (LENGTH args) ==>
     body_exprs_full_ok_mods mods exps cx args) /\
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env (Builtin ann bt args) es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin ann bt args) es /\
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (Builtin ann bt args) es
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac modular_source_shape_mods >>
  qpat_x_assum `args = [e1;e2;e3]` SUBST_ALL_TAC >>
  qpat_x_assum `ann = BaseT (UintT 256)` SUBST_ALL_TAC >>
  `expr_type e1 = BaseT (UintT 256) /\ expr_type e2 = BaseT (UintT 256) /\
   expr_type e3 = BaseT (UintT 256)` by fs[] >>
  `body_exprs_full_ok_mods mods exps cx [e1;e2;e3]` by
    (qpat_x_assum `builtin_args_length_ok _ _ ==> _` mp_tac >>
     qpat_assum `bt = AddMod \/ bt = MulMod` strip_assume_tac >>
     simp[builtin_args_length_ok_def]) >>
  conj_asm1_tac
  >- (pure_rewrite_tac[expr_sim_full_mods_def] >>
      qx_genl_tac [`st0`,`sa`,`sb`,`shadow_sa`,`shadow_sb`,`op`,`s0`,`G0`,`tn0`] >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      `expr_sim_full_code (ctx,shadow_ctx,func,shadow_func) (sa,sb,shadow_sa,shadow_sb)` by
        simp[expr_sim_full_code_def] >>
      `expr_body_pre_mods mods cenv cx env e1 es /\
       expr_body_pre_mods mods cenv cx env e2 es /\
       expr_body_pre_mods mods cenv cx env e3 es` by
        (rpt conj_tac >> qpat_assum `!e mid. _ ==> expr_body_pre_mods _ _ _ _ e mid`
           irule >> simp[]) >>
      drule_all_then strip_assume_tac modular_paired_cuts_mods >>
      irule (BETA_RULE modular_three_operands_cps_mods) >>
      BETA_TAC >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC ORELSE REFL_TAC) >>
      TRY (rpt gen_tac >> disch_tac >> first_assum ACCEPT_TAC >> NO_TAC) >>
      TRY (qexistsl_tac [`env`,`exps`,`mods`,`src`,`tops`] >>
           rpt conj_tac >> first_assum ACCEPT_TAC >> NO_TAC) >>
      qexistsl_tac [`d`,`s1`,`s2`,`s3`,`sa`,`sh1`,`sh2`,`sh3`,`shadow_sa`,`shadow_func`,`ty`,`x`,`y`,`z`] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      qx_genl_tac [`marks1`,`v1`,`mid1`,`G1`,`tn1`,`t1`,`marks2`,`v2`,`mid2`,`G2`,`tn2`,`t2`,
                   `marks3`,`v3`,`fin`,`G3`,`tn3`,`t3`] >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      `valid_horizon cx st0 (storage_trace_horizon mid1.storage_trace) mid1.storage_trace` by
        fs[storage_trace_domain_def] >>
      `valid_horizon cx st0 (storage_trace_horizon mid2.storage_trace) mid2.storage_trace` by
        fs[storage_trace_domain_def] >>
      `valid_horizon cx st0 (storage_trace_horizon fin.storage_trace) fin.storage_trace` by
        fs[storage_trace_domain_def] >>
      qpat_assum `!H. valid_horizon _ _ H mid1.storage_trace ==> _`
        (drule_then (map_every assume_tac o CONJUNCTS)) >>
      qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==> _`
        (drule_then (map_every assume_tac o CONJUNCTS)) >>
      qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> _`
        (drule_then (map_every assume_tac o CONJUNCTS)) >>
      `eval_operand x t3 = SOME (val_to_w256 v1) /\
       eval_operand y t3 = SOME (val_to_w256 v2) /\
       eval_operand z t3 = SOME (val_to_w256 v3) /\
       op_taint tn3 x = {} /\ op_taint tn3 y = {} /\ op_taint tn3 z = {}` by
        (irule modular_operands_at_third_cut_mods >>
         rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
         qpat_assum `expr_post_mods _ _ _ _ _ e1 _ _ _ _ _ _ _ _`
           (irule_at (Pat `expr_post_mods _ _ _ _ _ _ _ _ _ _ _ v1 _ _`)) >>
         qpat_assum `expr_post_mods _ _ _ _ _ e2 _ _ _ _ _ _ _ _`
           (irule_at (Pat `expr_post_mods _ _ _ _ _ _ _ _ _ _ _ v2 _ _`)) >>
         qpat_assum `expr_post_mods _ _ _ _ _ e3 _ _ _ _ _ _ _ _`
           (irule_at (Pat `expr_post_mods _ _ _ _ _ _ _ _ _ _ _ v3 _ _`)) >>
         qpat_assum `ptr_val_ok _ _ v1 _ _ _ _` (irule_at Any) >>
         qpat_assum `ptr_val_ok _ _ v2 _ _ _ _` (irule_at Any) >>
         qpat_assum `ptr_val_ok _ _ v3 _ _ _ _` (irule_at Any) >>
         qexists_tac `lo` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      irule modular_suffix_parent_outcome_mods >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      (rpt gen_tac >> disch_tac >>
       qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
         (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC
       ORELSE all_tac) >>
      qexistsl_tac [`G1`,`G2`,`marks1`,`mid1`,`mid2`,`s1`,`s2`,`s3`,`t1`,`t2`,
                    `tn1`,`tn2`,`x`,`y`,`z`] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >- (qx_gen_tac `H` >> disch_tac >>
          qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> _`
            (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
          strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC)
      >- (qx_gen_tac `H` >> disch_tac >>
          qpat_assum `!H. valid_horizon _ _ H mid1.storage_trace ==> _`
            (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
          strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC)
      >- (qx_gen_tac `H` >> disch_tac >>
          qpat_assum `!H. valid_horizon _ _ H mid2.storage_trace ==> _`
            (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
          strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      suspend "suffix") >>
  qpat_assum `!DF lo d ctx sh PG f sf cenv cx ty e es. _ ==> expr_vv_sim_full_mods _ _ _ _ _ _`
    irule >>
  simp[post_value_type_word,expr_type_def,is_word_type_def] >>
  conj_tac
  >- (qx_gen_tac `sa` >>
      Cases_on `compile_expr cenv ty (Builtin (BaseT (UintT 256)) bt [e1;e2;e3]) sa` >>
      drule_at Any compile_word_builtin_stack >>
      (impl_tac >- simp[]) >> strip_tac >> simp[]) >>
  rpt gen_tac >> disch_tac >> drule_then ACCEPT_TAC eval_expr_builtin_value
QED

(* Specialize the endpoint sequent at the actual third landing and retain
   the fields needed by modular_suffix_parent_outcome_mods. *)
Resume modular_sim_from_suffix_mods[suffix]:
  `sa.cs_next_var <= s3.cs_next_var` by decide_tac >>
  `local_ptrs_reserved cenv s3` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `!DF lo explicit ctx func PG d cenv cx st0 ee sm sb bt x y z op t G1 tn1 ann ts va vb vc. _ ==> _`
    (qspecl_then [`DF`,`lo`,`gas_explicit_sites ctx shadow_ctx`,`ctx`,`func`,`PG`,`d`,
                   `cenv`,`cx`,`st0`,`fin`,`s3`,`sb`,`bt`,`x`,`y`,`z`,`op`,`t3`,`G3`,`tn3`,
                   `BaseT (UintT 256)`,`[BaseT (UintT 256);BaseT (UintT 256);BaseT (UintT 256)]`,
                   `val_to_w256 v1`,`val_to_w256 v2`,`val_to_w256 v3`] mp_tac) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >- (qx_genl_tac [`q`,`sz`] >> disch_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
          qexists_tac `sa` >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
          qpat_assum `!q sz. cenv.ce_return_buf = SOME _ ==> _` irule >>
          qexists_tac `sz` >> first_assum ACCEPT_TAC)
      >- (qx_genl_tac [`q`,`sz`] >> disch_tac >> irule loweringShapeDefsTheory.not_fresh_at_mono >>
          qexists_tac `sa` >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
          qpat_assum `!q sz. cenv.ce_return_pc = SOME _ ==> _` irule >>
          qexists_tac `sz` >> first_assum ACCEPT_TAC) >>
      qx_gen_tac `H` >> disch_tac >>
      qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> _`
        (qspec_then `H` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
      strip_tac >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      qpat_assum `expr_post_mods H _ _ _ _ e3 _ _ _ _ _ _ _ _` mp_tac >>
      simp[NoAsms,expr_post_mods_def,expr_post_def]) >>
  disch_then (qx_choosel_then [`r`,`u`,`Gf`,`tnf`] (map_every assume_tac o CONJUNCTS)) >>
  qexistsl_tac [`r`,`u`,`Gf`,`tnf`] >> rpt conj_tac
  >- (disch_tac >>
      qpat_assum `val_to_w256 v3 = 0w ==> _` (drule_then strip_assume_tac) >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >- (disch_tac >>
      qpat_assum `val_to_w256 v3 <> 0w ==> _` (drule_then strip_assume_tac) >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      gen_tac >> disch_tac >>
      qpat_assum `!q. not_fresh_at s3 q ==> lookup_var q u = _ /\ _`
        (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED

Finalise modular_sim_from_suffix_mods
