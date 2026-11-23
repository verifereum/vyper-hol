(* The zero-code prefix for a qualified immutable lookup. *)
Theory bodyQualifiedImmutableRawMods
Ancestors
  bodyFullPostsMods exprBodyPreProps exprSimTopLevelProps
  exprSimTopLevelImmutable exprSimMemorySource exprSimMemDefs
  exprSimHypsDefs exprSimProps loweringPosts bodyInvSplit bodyFullShadowBodyInv
  supportedExprTraverse vyperTypeInvariants vyperBareGlobalName
  vyperStorageFootprint bodyPtrDefs ptrDiscipline context words
  gasContext exprSimDefs exprLoweringProps vyperInterpreter vyperState
  vyperAST vyperTypeSystem venomState finite_map option

Theorem qualified_immutable_lookup_mods[local]:
  expr_body_pre_mods mods cenv cx env (TopLevelName ann (src,id)) es /\
  get_module_code cx src = SOME tops /\ find_var_decl_by_name id tops = NONE /\
  gas_admissible (eval_expr cx (TopLevelName ann (src,id))) expr_vv_res_ok es ==>
  ?off imms rt v.
    FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
    ALOOKUP es.immutables cx.txn.target = SOME imms /\
    FLOOKUP (get_source_immutables src imms) id = SOME (rt,v) /\
    lookup_immutable cx es src id = SOME (rt,v) /\
    evaluate_type (get_tenv cx) ann = SOME rt
Proof
  strip_tac >> drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_all_then assume_tac toplevel_find_NONE_bare_global >>
  `~cx_const_name_mods mods (src,id) /\ IS_SOME (FLOOKUP cenv.ce_module_vars (src,id))` by
    fs[expr_body_pre_mods_def, supported_expr_exists_def, const_name_root_mods_def,
       unallocated_bare_global_root_def, IS_SOME_EQ_NOT_NONE] >>
  `?off. FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off)` by
    (qpat_assum `expr_sim_inv_mods _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_sim_inv_mods_def]) >>
     qpat_assum `!src id ty. _ /\ (~cx_const_name_mods _ _ \/ _) ==> _`
       (qspecl_then [`src`,`id`,`ann`] mp_tac) >>
     (impl_tac >- simp[]) >> disch_then (drule_then strip_assume_tac o CONJUNCT2) >>
     goal_assum (drule_at Any)) >>
  qpat_x_assum `gas_admissible _ _ _` mp_tac >> simp[gas_admissible_def] >>
  disch_then (qspec_then `es.gas_obs` mp_tac) >>
  simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
       get_immutables_def, get_address_immutables_def, return_def, raise_def] >>
  Cases_on `ALOOKUP es.immutables cx.txn.target` >>
  simp[return_def, raise_def, expr_vv_res_ok_def] >>
  rename1 `ALOOKUP es.immutables cx.txn.target = SOME imms` >>
  Cases_on `FLOOKUP (get_source_immutables src imms) id` >>
  simp[return_def, raise_def, expr_vv_res_ok_def] >>
  rename1 `FLOOKUP _ id = SOME rv` >> PairCases_on `rv` >>
  fs[env_consistent_def, env_immutables_consistent_def, lookup_immutable_def] >>
  metis_tac[]
QED

Theorem qualified_immutable_eval_tail[local]:
  get_module_code cx src = SOME tops /\ find_var_decl_by_name id tops = NONE /\
  ALOOKUP es.immutables cx.txn.target = SOME imms /\
  FLOOKUP (get_source_immutables src imms) id = SOME (rt,v) ==>
  !tail. eval_expr cx (TopLevelName ann (src,id)) (es with gas_obs := tail) =
    (INL (PlaceR (ImmutablePlace src id [])),es with gas_obs := tail)
Proof
  strip_tac >> simp[Once evaluate_def, lookup_global_def, bind_def,
    get_immutables_def, get_address_immutables_def, lift_option_type_def,
    return_def, raise_def]
QED

Theorem immutable_prefix_gas_obs[local]:
  (immutable_frame_mods func cenv cx (es with gas_obs := tail) s <=>
   immutable_frame_mods func cenv cx es s) /\
  (ghost_inv_at_mods D lo d cenv cx (es with gas_obs := tail) G tn s <=>
   ghost_inv_at_mods D lo d cenv cx es G tn s)
Proof
  simp[immutable_frame_mods_def, immutables_rel_mods_def,
       loweringStateRelDefsTheory.immutables_rel_def, immutable_alloca_sep_mods_def,
       immutable_alloca_sep_def, ghost_inv_at_mods_def]
QED

Theorem immutable_prefix_vv_post[local]:
  stmt_state_rel H ctx func cenv cx es s /\
  immutable_frame_mods func cenv cx es s /\ storage_well_formed_on cx es (FST H) /\
  vv_holds_mods cenv cx ann (PlaceR (ImmutablePlace src id []))
    (LocatedValue ann (mk_ptr (Lit (n2w off)) LocCode)) es s /\
  vv_place_ptr_mods cenv cx es s (PlaceR (ImmutablePlace src id []))
    (LocatedValue ann (mk_ptr (Lit (n2w off)) LocCode)) ==>
  vv_post_mods H ctx func cenv cx (TopLevelName ann (src,id)) es sa sa s
    (es with gas_obs := []) (PlaceR (ImmutablePlace src id []))
    (LocatedValue ann (mk_ptr (Lit (n2w off)) LocCode)) s
Proof
  strip_tac >>
  `storage_well_formed_on cx (es with gas_obs := []) (FST H)` by
    (`(es with gas_obs := []).accounts = es.accounts /\
      (es with gas_obs := []).tStorage = es.tStorage` by simp[] >>
     metis_tac[storage_well_formed_on_backends]) >>
  simp[vv_post_mods_def, stmt_state_rel_start_gas_obs, immutable_prefix_gas_obs,
       expr_type_def, vv_at_def, mk_ptr_def, locals_kept_mem] >>
  conj_tac
  >- (qpat_x_assum `vv_holds_mods _ _ _ _ _ _ _` mp_tac >>
      simp[vv_holds_mods_def, mk_ptr_def, immutable_holds_mods_def, immutable_holds_def,
           eval_operand_def] >> strip_tac >>
      drule_then (qspec_then `[]` assume_tac) read_result_gas_obs >>
      goal_assum (drule_at Any) >> simp[] >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[]) >>
  qpat_x_assum `vv_place_ptr_mods _ _ _ _ _ _` mp_tac >>
  simp[vv_place_ptr_mods_def, mk_ptr_def, vv_place_ptr_def]
QED

(* The implementation of each quantified premise is supplied by the join.
   Neither premise changes the caller's compile environment. *)
val qualified_place =
  ``!mods exps ctx cenv cx env es src id tops func s off rt v ann.
    contract_inv mods exps ctx cenv cx /\
    expr_sim_inv_mods mods cenv cx env es /\
    get_module_code cx src = SOME tops /\
    immutable_frame_mods func cenv cx es s /\
    FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
    lookup_immutable cx es src id = SOME (rt,v) /\
    evaluate_type (get_tenv cx) ann = SOME rt ==>
    ALOOKUP cenv.ce_modules src = SOME tops /\
    off + type_memory_size rt < dimword (:256) /\
    read_result cx (PlaceR (ImmutablePlace src id [])) es = (INL v,es) /\
    vv_holds_mods cenv cx ann (PlaceR (ImmutablePlace src id []))
      (LocatedValue ann (mk_ptr (Lit (n2w off)) LocCode)) es s /\
    vv_place_ptr_mods cenv cx es s (PlaceR (ImmutablePlace src id []))
      (LocatedValue ann (mk_ptr (Lit (n2w off)) LocCode)) /\
    immutable_value_admissible rt v /\
    (~cenv.ce_is_ctor ==> off + type_memory_size rt <= LENGTH s.vs_data_section) /\
    val_in_memory rt v off (if cenv.ce_is_ctor then s.vs_memory else s.vs_data_section)``;

val qualified_ctor_frame =
  ``!mods exps ctx cenv cx env entry H D lo es src tops s d G tn id off imms rt v.
    contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env entry /\
    cenv.ce_is_ctor /\
    dead_lo_ok_mods (H : (bool # 256 word # type_value) list # num list) D lo cenv cx /\
    es.immutables = entry.immutables /\
    ALOOKUP cenv.ce_modules src = SOME tops /\
    immutables_rel_mods cenv cx.txn.target cenv.ce_is_ctor es s /\
    ghost_inv_at_mods D lo d cenv cx es G tn s /\
    FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
    ALOOKUP es.immutables cx.txn.target = SOME imms /\
    FLOOKUP (get_source_immutables src imms) id = SOME (rt,v) ==>
    off + type_memory_size rt <= lo /\
    !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory rt v off mem``;

Theorem qualified_immutable_raw_mods:
  ^qualified_place /\ ^qualified_ctor_frame /\
  contract_inv mods exps ctx cenv cx /\
  expr_body_pre_mods mods cenv cx env (TopLevelName ann (src,id)) es /\
  get_module_code cx src = SOME tops /\ find_var_decl_by_name id tops = NONE /\
  gas_admissible (eval_expr cx (TopLevelName ann (src,id))) expr_vv_res_ok es /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  alloca_history func s0 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?off rt v.
    let e = TopLevelName ann (src,id) in
    let tv = PlaceR (ImmutablePlace src id []) in
    let vv = LocatedValue ann (mk_ptr (Lit (n2w off)) LocCode) in
    let ee = es with gas_obs := [] in
    FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
    evaluate_type (get_tenv cx) ann = SOME rt /\
    compile_expr cenv ty e sa = (vv,sa) /\
    (!tail. eval_expr cx e (es with gas_obs := tail) = (INL tv,es with gas_obs := tail)) /\
    !H. valid_horizon cx st0 H ee.storage_trace ==>
      ALOOKUP cenv.ce_modules src = SOME tops /\
      off + type_memory_size rt < dimword (:256) /\
      read_result cx tv es = (INL v,es) /\ read_result cx tv ee = (INL v,ee) /\
      immutable_value_admissible rt v /\
      (~cenv.ce_is_ctor ==> off + type_memory_size rt <= LENGTH s0.vs_data_section) /\
      val_in_memory rt v off (if cenv.ce_is_ctor then s0.vs_memory else s0.vs_data_section) /\
      (cenv.ce_is_ctor ==> off + type_memory_size rt <= lo /\
        !mem. mem_agree_outside tn0.t_mem s0.vs_memory mem ==> val_in_memory rt v off mem) /\
      vv_post_mods H ctx func cenv cx e es sa sa s0 ee tv vv s0 /\
      vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv s0 /\
      s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
      alloca_history func s0 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G0 tn0 s0 /\
      ptr_vv_ok cx (post_value_type cenv e) tv vv ee G0 tn0 s0 /\
      (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
        ?val. read_result cx tv ee = (INL val,ee) /\
          !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
                 eval_operand (vv_operand vv) s0 = SOME w ==>
            w2n w + type_memory_size rt <= lo /\
            !mem. mem_agree_outside tn0.t_mem s0.vs_memory mem ==>
              val_in_memory rt val (w2n w) mem) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G0 tn0
Proof
  strip_tac >> drule_all_then strip_assume_tac qualified_immutable_lookup_mods >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  qexistsl [`off`,`rt`,`v`] >> simp[compile_toplevel_immutable_ptr] >>
  conj_tac >- (irule qualified_immutable_eval_tail >> simp[] >> goal_assum drule >> simp[]) >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  qpat_x_assum `!mods exps ctx cenv cx env es src id tops func s off rt v ann. _`
    (drule_all_then strip_assume_tac) >>
  `read_result cx (PlaceR (ImmutablePlace src id [])) (es with gas_obs := []) =
      (INL v,es with gas_obs := [])` by (drule read_result_gas_obs >> simp[]) >>
  `(cenv.ce_is_ctor ==> off + type_memory_size rt <= lo /\
      !mem. mem_agree_outside tn0.t_mem s0.vs_memory mem ==> val_in_memory rt v off mem)` by
    (strip_tac >>
     qpat_assum `!H. dead_lo_ok_mods _ _ _ _ _` (qspec_then `H` assume_tac) >>
     qpat_assum `immutable_frame_mods _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [immutable_frame_mods_def]) >>
     qpat_x_assum `!mods exps ctx cenv cx env entry H D lo es src tops s d G tn id off imms rt v. _`
       irule >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `off < dimword (:256)` by decide_tac >>
  simp[immutable_prefix_gas_obs, vv_store_bound_nonmem, mk_ptr_def,
       ptr_vv_ok_def, op_taint_def, op_prov_def, ghost_kept_at_def,
       expr_type_def, vv_location_def, vv_operand_def] >>
  conj_tac >- (simp[GSYM mk_ptr_def] >> irule immutable_prefix_vv_post >> simp[]) >>
  simp[eval_operand_def, w2n_n2w, arithmeticTheory.LESS_MOD] >>
  strip_tac >> qexists_tac `v` >> fs[arithmeticTheory.ADD_COMM]
QED
