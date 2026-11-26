(* Join the reached copy operands, their common prefix, and the prepared dispatch. *)
Theory bodyCreateCopyRunMods
Ancestors
  bodyCreateCopyLayoutMods bodyCreateCopyTargetMods bodyCreateCopyScalarSuffixMods
  bodyCreateCopyPrepareMods bodyCreateCopyFinishMods bodyCreateDispatchMods
  bodyCreateOperandPreMods bodyFullPredsMods bodyFullPostsMods exprBodyPreProps
  exprLoweringProps loweringShapeDefs supportedExprTraverse loweringPosts
  vyperStorageTrace vyperStorageFootprint vyperValue exprSimHypsDefs vyperAST compileEnv

Theorem create_copy_forced_mods:
  body_exprs_full_ok_mods mods exps cx (create_operand_order CreateCopyOf salted args) /\
  contract_inv mods exps ctx cenv cx /\
  module_body_inv mods src tops cenv cx /\
  shadow_body_inv_mods mods exps ctx shadow_ctx /\
  body_const_cells_agree_mods mods cx env es /\
  expr_body_pre_mods mods cenv cx env
    (Call ann (CreateTarget CreateCopyOf salted rof ks) args dflt) es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func) cenv cx ty
    (Call ann (CreateTarget CreateCopyOf salted rof ks) args dflt) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rewrite_tac[expr_sim_full_mods_def] >>
  map_every qx_gen_tac [`st0`,`sa`,`sb`,`sha`,`shb`,`result`,`s0`,`G0`,`tn0`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac create_copy_layout_mods >>
  rename1 `args = target::amount::salts` >>
  qpat_x_assum `ann = _` SUBST_ALL_TAC >>
  `body_exprs_full_ok_mods mods exps cx (target::amount::salts)` by
    (qpat_assum `create_operand_order _ _ _ = _` (fs o single)) >>
  `expr_body_pre_mods mods cenv cx env target es` by
    (irule create_operand_pre_mods >>
     qpat_assum `expr_body_pre_mods _ _ _ _ (Call _ _ _ _) _` (irule_at Any) >>
     drule_then assume_tac expr_body_pre_mods_inv >> simp[]) >>
  qabbrev_tac `next = \vs. bind (eval_create_operands cx CreateCopyOf salted rof
    (MAP expr_type args) (blueprint_literal_offset cx salted args) vs) (read_result cx)` >>
  `!vs. storage_trace_frame (next vs)` by
    simp[Abbr `next`,storage_trace_frame_bind_all,storage_trace_frame_read_result,
         storage_trace_frame_create_operands] >>
  rewrite_tac[create_copy_eval_read_mods] >>
  qpat_assum `Abbrev (next = _)`
    (PURE_ONCE_REWRITE_TAC o single o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_assum `args = _` (PURE_ONCE_REWRITE_TAC o single) >>
  simp[post_value_type_def,expr_type_def,is_word_type_def] >>
  irule create_copy_target_cut_mods >> BETA_TAC >>
  suspend "target"
QED

Resume create_copy_forced_mods[target]:
  asm_rewrite_tac[] >>
  qexistsl_tac [`a`,`ha`,`d`,`env`,`exps`,`mods`,`sa`,`sha`,`shadow_func`,`src`,`tops`,`x`] >>
  asm_rewrite_tac[] >> reverse conj_tac
  >- (qpat_assum `expr_type target = _` (PURE_ONCE_REWRITE_TAC o single o SYM) >>
      asm_rewrite_tac[]) >>
  map_every qx_gen_tac [`bs`,`et`,`Gu`,`tu`,`u`,`mt`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!z. MEM z (amount::salts) ==> expr_body_pre_mods mods cenv cx env z et` by
    (rpt strip_tac >> irule create_operand_pre_mods >>
     qpat_assum `expr_body_pre_mods _ _ _ _ (Call _ _ _ _) _` (irule_at Any) >>
     qpat_assum `MEM z (amount::salts)` (mp_tac o REWRITE_RULE [listTheory.MEM]) >>
     strip_tac >> simp[]) >>
  `sa.cs_next_var <= a.cs_next_var` by fs[ci_mono_def] >>
  `local_ptrs_reserved cenv a` by drule_all_then ACCEPT_TAC local_ptrs_reserved_next_var >>
  `!z n. cenv.ce_return_buf = SOME (PtrVar (Var z) n) ==> not_fresh_at a z` by
    metis_tac[not_fresh_at_mono] >>
  `!z n. cenv.ce_return_pc = SOME (PtrVar (Var z) n) ==> not_fresh_at a z` by
    metis_tac[not_fresh_at_mono] >>
  irule create_copy_scalar_suffix_cut_mods >> BETA_TAC >> asm_rewrite_tac[] >>
  suspend "suffix"
QED

Resume create_copy_forced_mods[suffix]:
  `!ee z. MEM z salts /\ expr_sim_inv_mods mods cenv cx env ee ==>
      expr_body_pre_mods mods cenv cx env z ee` by
    (rpt strip_tac >> irule create_operand_pre_mods >>
     qpat_assum `expr_body_pre_mods _ _ _ _ (Call _ _ _ _) _` (irule_at Any) >> simp[]) >>
  `!H. valid_horizon cx st0 H et.storage_trace ==>
    stmt_state_rel H ctx func cenv cx et u /\ immutable_frame_mods func cenv cx et u /\
    storage_well_formed_on cx et (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx et Gu tu u` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H et.storage_trace ==> _`
       (drule_then strip_assume_tac) >> asm_rewrite_tac[]) >>
  qpat_assum `expr_type amount = _` (fn th =>
    map_every (fn p => qpat_assum p (assume_tac o PURE_REWRITE_RULE [th]))
      [`lower_value compile_expr cenv (expr_type amount) amount a = _`,
       `lower_value compile_expr (gas_shadow_env T cenv) (expr_type amount) (gas_shadow_expr amount) ha = _`]) >>
  qexistsl_tac [`d`,`env`,`exps`,`mods`,`a`,`salted`,`c`,`ha`,`shadow_func`,`hc`,`hb`,`b`,
               `sop`,`src`,`tops`,`y`] >>
  asm_rewrite_tac[] >> reverse conj_tac
  >- (qpat_assum `!z. MEM z (amount::salts) ==> _` irule >> simp[]) >>
  map_every qx_gen_tac [`av`,`sv`,`aw`,`sw`,`ee`,`G`,`tn`,`s`,`ms`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "prefix"
QED

Resume create_copy_forced_mods[prefix]:
  map_every (fn p => qpat_assum p (map_every assume_tac o CONJUNCTS o
      SIMP_RULE bool_ss [boolTheory.IMP_CONJ_THM,boolTheory.FORALL_AND_THM]))
    [`!H. valid_horizon cx st0 H es.storage_trace ==> _`,
     `!H. valid_horizon cx st0 H et.storage_trace ==> valid_horizon cx st0 H es.storage_trace /\ _`,
     `!H. valid_horizon cx st0 H ee.storage_trace ==> _`] >>
  `ci_mono a c` by drule_all_then ACCEPT_TAC ci_mono_trans >>
  qpat_assum `wb_frame cenv es et sa s0 u`
    (mp_then Any (drule_all_then strip_assume_tac) create_copy_prefix_frame_mods) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee s /\ immutable_frame_mods func cenv cx ee s /\
    storage_well_formed_on cx ee (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s` by
    (gen_tac >> disch_tac >> asm_rewrite_tac[] >> rpt conj_tac >>
     first_assum (drule_then ACCEPT_TAC)) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. _ ==> gas_origin_ptr_path _ _ (mt ++ ms) _`
    (drule_then assume_tac) >>
  `sa.cs_next_var <= c.cs_next_var` by fs[ci_mono_def] >>
  `local_ptrs_reserved cenv c` by drule_all_then ACCEPT_TAC local_ptrs_reserved_next_var >>
  `!z n. cenv.ce_return_buf = SOME (PtrVar (Var z) n) ==> not_fresh_at c z` by
    metis_tac[not_fresh_at_mono] >>
  `!z n. cenv.ce_return_pc = SOME (PtrVar (Var z) n) ==> not_fresh_at c z` by
    metis_tac[not_fresh_at_mono] >>
  suspend "finish"
QED

Resume create_copy_forced_mods[finish]:
  `accounts_well_typed ee.accounts /\ outcomes_accounts_typed ee.outcomes` by
    (qpat_assum `expr_sim_inv_mods _ _ _ _ ee` (mp_tac o REWRITE_RULE [expr_sim_inv_mods_def]) >> simp[]) >>
  `IS_SOME ee.outcomes` by
    (qpat_assum `expr_sim_inv_mods _ _ _ _ ee` (mp_tac o REWRITE_RULE [expr_sim_inv_mods_def]) >> simp[]) >>
  `(case sop of NONE => sw = NONE | SOME op =>
      ?w. sw = SOME w /\ eval_operand op s = SOME w /\ op_taint tn op = {})` by
    (qpat_assum `OPTREL _ sop sw` mp_tac >> Cases_on `sop` >> Cases_on `sw` >>
     simp[NoAsms,optionTheory.OPTREL_def]) >>
  `!z. x = Var z \/ y = Var z \/ sop = SOME (Var z) ==> not_fresh_at c z` by
    (rpt strip_tac
     >- qpat_assum `!z. x = Var z ==> not_fresh_at c z` (drule_then ACCEPT_TAC) >>
     qpat_assum `!z. y = Var z \/ sop = SOME (Var z) ==> _` irule >> simp[]) >>
  qabbrev_tac `code = (lookup_account (word_of_bytes_be bs) ee.accounts).code` >>
  `code = (lookup_account (word_of_bytes_be bs) ee.accounts).code` by simp[Abbr `code`] >>
  `post_value_type cenv (Call (BaseT AddressT) (CreateTarget CreateCopyOf salted rof ks)
      (target::amount::salts) dflt) = BaseT AddressT` by simp[post_value_type_def,expr_type_def] >>
  `expr_has_effect (Call (BaseT AddressT) (CreateTarget CreateCopyOf salted rof ks)
      (target::amount::salts) dflt)` by
    simp[expr_has_effect_def,supported_expr_exists_def,expr_effect_root_def] >>
  irule create_copy_finish_mods >> BETA_TAC >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexistsl_tac [`y`,`aw`,`bs`,`code`,`rof`,`c`,`sop`,`sw`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  FIRST [irule (INST_TYPE [alpha |-> ``:256``] create_copy_prepared_mods) >> suspend "prepared",
         rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
           irule create_dispatch_outcome_full_mods >> suspend "dispatch",
         suspend "source"]
QED

Resume create_copy_forced_mods[prepared]:
  asm_rewrite_tac[] >> conj_tac >- (qexistsl_tac [`bs`,`x`] >> asm_rewrite_tac[]) >>
  conj_tac
  >- (qexistsl_tac [`DF (storage_trace_horizon ee.storage_trace)`,
        `gas_explicit_sites ctx shadow_ctx`,`mt ++ ms`] >> first_assum ACCEPT_TAC) >>
  conj_tac >- (qexistsl_tac [`exps`,`mods`] >> first_assum ACCEPT_TAC) >>
  qexists_tac `storage_trace_horizon ee.storage_trace` >> first_assum ACCEPT_TAC
QED

Resume create_copy_forced_mods[dispatch]:
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qexistsl_tac [`y`,`aw`,`buf`,`create_copy_initcode code`,`len`,`pv`,`rof`,`sc`,`sop`,`sw`,`sz`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume create_copy_forced_mods[source]:
  gen_tac >> qpat_assum `Abbrev (next = _)`
    (PURE_ONCE_REWRITE_TAC o single o REWRITE_RULE [markerTheory.Abbrev_def]) >> BETA_TAC >>
  qpat_assum `IS_SOME sv = salted` (PURE_ONCE_REWRITE_TAC o single o SYM) >>
  irule create_copy_read_prepared_mods >>
  conj_tac >- (simp[NoAsms] >> first_assum ACCEPT_TAC) >>
  conj_tac
  >- (qpat_assum `IS_SOME sv = salted` (PURE_ONCE_REWRITE_TAC o single) >>
      qpat_assum `args = _` (PURE_ONCE_REWRITE_TAC o single) >>
      simp[NoAsms] >>
      qpat_assum `LENGTH salts = _` (PURE_ONCE_REWRITE_TAC o single) >>
      Cases_on `salted` >> simp[NoAsms]) >>
  conj_tac
  >- (qexists_tac `word_of_bytes_be bs` >> simp[NoAsms,dest_AddressV_def] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Finalise create_copy_forced_mods
