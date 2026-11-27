(* Assemble ECMul's launch packet at the reached second-operand cut. *)
Theory bodyECMulReachedStageMods
Ancestors
  bodyECArithOperandsMods bodyECArithTailMods bodyECMulAllocEdgeMods
  bodyECMulPhysicalStageMods bodyECMulStageMods bodyECHeldPointMods
  bodyECMulScalarCutMods bodyECArithOperandReadyMods exprBodyPreProps
  bodyInvCodeProps bodyInvModuleProps exprSimHyps exprWordOperand
  gasShadowCompileBuiltinScalar stateRelProj vyperTypeEvalCaseProofs
  vyperTypeSystem exprLowering loweringPosts vyperStorageFootprint

val alloc_rule = fst (dest_imp (concl ecmul_physical_stage_given_alloc_mods));

Theorem ecmul_projected_alloc_mods[local]:
  ^alloc_rule
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (BETA_RULE (Q.INST
    [`P` |-> `\H. valid_horizon cx st0 H es2.storage_trace`,
     `es` |-> `es2`, `cenv` |-> `ce`, `sa` |-> `a`, `sb` |-> `b`]
    ecmul_alloc_edge_mods)) >>
  impl_tac
  >- (rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >>
      rpt strip_tac >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _`
        (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then [`dst`,`w`,`t`,`G'`,`tn'`]
    (map_every assume_tac o CONJUNCTS)) >>
  `t.vs_outcomes = s.vs_outcomes` by
    (qpat_assum `_ = s` (SUBST1_TAC o SYM) >> simp[]) >>
  `immutable_frame_mods func ce cx es2 t /\ local_ptrs_rel func ce es2.scopes t` by
    (qpat_assum `?H. valid_horizon _ _ H _` strip_assume_tac >>
     qpat_assum `!H. _ ==> stmt_state_rel H _ _ _ _ _ t /\ _`
       (drule_then strip_assume_tac) >>
     drule stmt_state_rel_local_ptrs_alloca >> simp[]) >>
  qexistsl_tac [`dst`,`w`,`t`,`G'`,`tn'`] >>
  rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >>
  rpt strip_tac >>
  qpat_assum `!H. _ ==> stmt_state_rel H _ _ _ _ _ t /\ _`
    (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC
QED

Theorem ecmul_point_post_type[local]:
  expr_sim_inv_mods mods cenv cx env es /\ well_typed_expr env e /\
  expr_type e = ArrayT (BaseT (UintT 256)) (Fixed 2) ==>
  post_value_type cenv e = expr_type e
Proof
  strip_tac >> Cases_on `?ty fid args drv. e = Call ty (IntCall fid) args drv`
  >- (gvs[] >> rename1 `IntCall fid` >> PairCases_on `fid` >>
      gvs[well_typed_expr_def,lowered_value_type_def,vyperASTTheory.expr_type_def,
          compileEnvTheory.is_word_type_def,compileEnvTheory.is_bytestring_type_def] >>
      drule_all expr_sim_inv_mods_return_type >> strip_tac >>
      drule type_widens_to_ec_point >> simp[]) >>
  irule post_value_type_not_int_call >> metis_tac[]
QED

(* Use the same cut and staging quotations as the terminal dispatch. *)
val (ambient, reached) =
  let
    val prems = strip_conj (fst (dest_imp (concl (BETA_RULE ec_arith_from_tail_mods))))
  in
    (list_mk_conj (List.take (prems, length prems - 1)), List.last prems)
  end;
val (cut_vars, reached_body) = strip_forall reached;
val (cut_input, _) = dest_imp reached_body;
val staged = subst [``addr:256 word`` |-> ``7w:256 word``,
                    ``an:256 word`` |-> ``96w:256 word``]
                 (rand (concl ec_arith_tail_from_staging_mods));
val launch = ``?p q. ^staged /\
  eval_operand x t2 = SOME p /\ eval_operand y t2 = SOME q /\
  expr_val_rel cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v1 x t2 /\
  expr_val_rel cx (BaseT (UintT 256)) v2 y t2``;
val staging = list_mk_forall (cut_vars, mk_imp (cut_input, launch));

Theorem ecmul_stage_from_reached_mods:
  ^ambient /\ bt = ECMul ==> ^staging
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_type e1 = ArrayT (BaseT (UintT 256)) (Fixed 2)` by simp[] >>
  `expr_type e2 = BaseT (UintT 256)` by simp[] >>
  `expr_body_pre_mods mods cenv cx env e1 es /\ expr_body_pre_mods mods cenv cx env e2 es1` by
    (drule_all ec_arith_operand_ready_mods >> strip_tac >> gvs[]) >>
  `well_typed_expr env e1 /\ well_typed_expr env e2 /\ expr_sim_inv_mods mods cenv cx env es` by
    metis_tac[expr_body_pre_mods_well_typed, expr_body_pre_mods_inv] >>
  `post_value_type cenv e1 = expr_type e1` by
    (irule ecmul_point_post_type >> asm_rewrite_tac[] >>
     qexistsl_tac [`cx`,`env`,`es`,`mods`] >> simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon es2.storage_trace) es2.storage_trace` by
    fs[storage_trace_domain_def] >>
  `valid_horizon cx st0 (storage_trace_horizon es2.storage_trace) es1.storage_trace` by
    (qpat_assum `!H. _ ==> valid_horizon _ _ H es1.storage_trace /\ _`
      (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  qpat_assum `!H. _ ==> expr_post_mods H _ _ _ _ e1 _ _ _ _ _ _ _ _ /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `!H. _ ==> expr_post_mods H _ _ _ _ e2 _ _ _ _ _ _ _ _ /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  drule_all_then (qx_choosel_then [`root`,`wp`,`point_cut`] strip_assume_tac)
    ec_held_point_at_second_cut_mods >>
  `!H. valid_horizon cx st0 H es2.storage_trace ==>
    expr_post_mods H ctx func cenv cx e2 es1 s1 s2 t1 es2 v2 y t2 /\
    expr_store_bound cx (post_value_type cenv e2) v2 y t2 /\
    ptr_val_ok cx (post_value_type cenv e2) v2 y G2 tn2 t2` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. _ ==> expr_post_mods H _ _ _ _ e2 _ _ _ _ _ _ _ _ /\ _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >> simp[]) >>
  drule_all_then (qx_choose_then `q` strip_assume_tac) ecmul_scalar_at_cut_mods >>
  suspend "compiler"
QED

Resume ecmul_stage_from_reached_mods[compiler]:
  qpat_assum `expr_sim_full_code _ (s2,sb,shadow_s2,shadow_sb)`
    (strip_assume_tac o MATCH_MP exprSimFullBundlePropsTheory.expr_sim_full_code_fields) >>
  qpat_x_assum `bt = ECMul` SUBST_ALL_TAC >>
  qpat_x_assum `x = Var root` SUBST_ALL_TAC >>
  qpat_x_assum `(if _ then _ else _) s2 = _` (assume_tac o SIMP_RULE (srw_ss()) []) >>
  qpat_x_assum `(if _ then _ else _) shadow_s2 = _` (assume_tac o SIMP_RULE (srw_ss()) []) >>
  `shadow_res = res` by
    (qspecl_then [`s2`,`shadow_s2`] mp_tac
       (REWRITE_RULE [gasShadowStateTheory.gas_shadow_compiles_def]
         (Q.INST [`p` |-> `Var root`, `scalar` |-> `y`] gas_shadow_compiles_ecmul_point)) >> simp[]) >>
  qpat_x_assum `shadow_res = res` SUBST_ALL_TAC >>
  `!i. MEM i (emitted_insts s2 sb) ==> MEM i (fn_insts func)` by
    (rpt strip_tac >> drule_all_then ACCEPT_TAC exprSimHashTheory.hash_emitted_inst_mem) >>
  drule_all_then (qx_choosel_then
    [`ib`,`ca`,`c1`,`c2`,`cpost`,`ob`,`sm`,`src_in`,`dst_out`,`gv`,`cv`]
    (map_every assume_tac o CONJUNCTS)) ecmul_stage_mods >>
  suspend "physical"
QED

Resume ecmul_stage_from_reached_mods[physical]:
  qpat_assum `!H. _ ==> stmt_state_rel H _ _ _ _ es2 t2 /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  `es2.outcomes = SOME t2.vs_outcomes` by
    (drule stmt_state_rel_state_rel >> simp[loweringStateRelDefsTheory.state_rel_def]) >>
  `allocas_from lo t2 /\ lo <= t2.vs_alloca_next` by
    (qpat_assum `ghost_inv_at_mods _ _ _ _ _ es2 _ _ t2`
       (map_every assume_tac o CONJUNCTS o REWRITE_RULE [bodyFullShadowBodyInvTheory.ghost_inv_at_mods_def]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H es2.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es2 t2 /\ ghost_inv_at_mods (DF H) lo d cenv cx es2 G2 tn2 t2` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. _ ==> stmt_state_rel H _ _ _ _ es2 t2 /\ _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >> simp[]) >>
  `ALOOKUP cenv.ce_modules cenv.ce_module = SOME tops` by
    (drule_then SUBST1_TAC contract_inv_cenv_modules >>
     qpat_assum `module_body_inv _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [bodyInvSplitTheory.module_body_inv_def]) >>
     simp[]) >>
  `cpost.cs_current_bb = ca.cs_current_bb` by
    fs[exprLoweringPropsTheory.same_blocks_def] >>
  `?H. valid_horizon cx st0 H es2.storage_trace` by
    (qexists_tac `storage_trace_horizon es2.storage_trace` >> first_assum ACCEPT_TAC) >>
  `is_word_type (expr_type e2)` by simp[compileEnvTheory.is_word_type_def] >>
  qpat_assum `expr_sim_inv_mods mods cenv cx env es1`
    (strip_assume_tac o MATCH_MP expr_sim_inv_mods_env) >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  `!id t. FLOOKUP env.var_types id = SOME t ==> well_formed_type env.type_defs t` by
    (simp[well_formed_type_def] >> rpt strip_tac >>
     drule_all_then ACCEPT_TAC exprSimSourceTheory.env_consistent_var_type_evaluates) >>
  qpat_assum `lower_value compile_expr cenv (expr_type e2) e2 s1 = (y,s2)`
    (mp_then Any (qspec_then `env` mp_tac) lower_value_word_shape) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  strip_tac >>
  mp_tac (Q.INST [`ce` |-> `cenv`, `scalar` |-> `y`,
                  `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    (MATCH_MP ecmul_physical_stage_given_alloc_mods ecmul_projected_alloc_mods)) >>
  impl_tac >- (rpt (first_assum ACCEPT_TAC ORELSE conj_tac) >>
    simp[venomStateTheory.eval_operand_def] >>
    HINT_EXISTS_TAC >> simp[]) >>
  disch_then (qx_choosel_then [`src_phy`,`dst_phy`,`wi`,`wo`,`u`,`Gu`,`tnu`]
    (map_every assume_tac o CONJUNCTS)) >>
  suspend "packet"
QED

Resume ecmul_stage_from_reached_mods[packet]:
  `src_phy = src_in /\ dst_phy = dst_out` by
    (conj_tac
     >- (qpat_assum `ib.buf_operand = Var src_phy` mp_tac >>
         qpat_assum `ib.buf_operand = Var src_in` (pure_rewrite_tac o single) >> simp[])
     >> qpat_assum `ob.buf_operand = Var dst_phy` mp_tac >>
     qpat_assum `ob.buf_operand = Var dst_out` (pure_rewrite_tac o single) >> simp[]) >>
  qpat_x_assum `src_phy = src_in` SUBST_ALL_TAC >>
  qpat_x_assum `dst_phy = dst_out` SUBST_ALL_TAC >>
  qpat_assum `!u. ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\ _ ==> _`
    (fn th => qspec_then `u` mp_tac th) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (CONJUNCTS_THEN2 assume_tac (qx_choose_then `bb` strip_assume_tac)) >>
  `cpost.cs_next_id < sb.cs_next_id` by
    (irule arithmeticTheory.LESS_TRANS >> qexists_tac `sm.cs_next_id` >> simp[]) >>
  qexistsl_tac [`wp`,`q`] >> reverse conj_tac
  >- simp[venomStateTheory.eval_operand_def] >>
  qexistsl_tac [`sm`,`res`,`cpost`, `mk_inst sm.cs_next_id GAS [] [gv]`,
    `mk_inst (sm.cs_next_id+1) STATICCALL
       [Var gv; Lit 7w; Var src_in; Lit 96w; Var dst_out; Lit 64w] [cv]`,
    `mk_inst (sm.cs_next_id+2) ASSERT [Var cv] []`,
    `gv`,`cv`,`src_in`,`dst_out`,`wi`,`wo`,`bb`,`u`,`Gu`,`tnu`] >>
  simp_tac bool_ss [EVAL ``ECMul = ECAdd``] >>
  rpt (first_assum ACCEPT_TAC ORELSE conj_tac)
  >- (qpat_assum `_ sm = (res,sb)` mp_tac >>
      qpat_assum `ib.buf_operand = Var src_in` (pure_rewrite_tac o single) >>
      qpat_assum `ob.buf_operand = Var dst_out` (pure_rewrite_tac o single) >> simp[])
  >- simp[as_stack_val_def]
  >- (qpat_assum `isPREFIX (emitted_insts sm sb) _` mp_tac >>
      qpat_assum `emitted_insts sm sb = _` (pure_rewrite_tac o single) >> simp[])
  >> simp[wordsTheory.dimword_def]
QED

Finalise ecmul_stage_from_reached_mods
