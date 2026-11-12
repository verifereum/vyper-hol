(* Code-free top-level pointer views and their live storage boundary. *)
Theory exprSimPtrTopLevelViews
Ancestors
  sourceUnitExecution
  bodyPtrDefs ptrDiscipline compileEnv loweringStateRelDefs context vyperAST vyperState
  exprSimTopLevelProps exprSimHypsDefs exprSimTopLevelStorage exprSimTopLevelImmutable
  exprSimHyps exprSimDefs exprSimProps exprLowering exprLoweringProps
  gasSummary fragGasPathPtr gasContext loweringPosts
  vyperTypeGlobalLookupSoundness vyperStorageLayoutSafety vyperTypeSystem
  vyperInterpreter vyperLookupStorage vyperStorageFootprint vyperTypeValues
  vyperStorageBackend
  venomState accountsRelProps words pred_set finite_map list

Theorem toplevel_live_storage_taint:
  !tr cx tn s w tv k b.
  stor_taint_ok H cx tn s /\
  storage_read_live H tr
    (if tr then s.vs_transient s.vs_call_ctx.cc_address
     else (s.vs_accounts s.vs_call_ctx.cc_address).storage) w tv /\
  (k,b) IN (if tr then tn.t_trans else tn.t_stor) /\
  w2n w <= w2n k /\ w2n k < w2n w + type_slot_size tv ==>
  dead_bytes
    (if tr then s.vs_transient s.vs_call_ctx.cc_address
     else (s.vs_accounts s.vs_call_ctx.cc_address).storage)
    (w2n w) tv (w2n k) b
Proof
  Cases_on `tr` >>
  simp[stor_taint_ok_def, cx_dead_def, SUBSET_DEF, storage_read_live_def] >>
  rpt strip_tac >>
  Cases_on `s.vs_call_ctx.cc_address = cx.txn.target` >> gvs[] >>
  metis_tac[pairTheory.PAIR_EQ]
QED

Theorem toplevel_live_ptr_vv_ok:
  !cx tn s tr w t tv es G.
  stor_taint_ok H cx tn s /\
  (!ty. evaluate_type (get_tenv cx) t = SOME ty ==>
    storage_read_live H tr
      (if tr then s.vs_transient s.vs_call_ctx.cc_address
       else (s.vs_accounts s.vs_call_ctx.cc_address).storage) w ty) ==>
  ptr_vv_ok cx t tv
    (LocatedValue t (mk_ptr (Lit w) (if tr then LocTransient else LocStorage)))
    es G tn s
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `tr` >>
  simp[ptr_vv_ok_def, mk_ptr_def, op_taint_def, eval_operand_def] >>
  rpt strip_tac >> gvs[] >>
  metis_tac[SRULE [] (Q.SPEC `T` toplevel_live_storage_taint),
            SRULE [] (Q.SPEC `F` toplevel_live_storage_taint),
            arithmeticTheory.ADD_COMM]
QED

Theorem toplevel_code_ptr_vv_ok:
  !cx t tv t' off es G tn s.
  ptr_vv_ok cx t tv (LocatedValue t' (mk_ptr (Lit off) LocCode)) es G tn s
Proof
  simp[ptr_vv_ok_def, mk_ptr_def, op_taint_def]
QED

Theorem compile_toplevel_no_module_vv_sim_ptr:
  !d ctx PG func cenv cx ty ann src id es.
  get_module_code cx src = NONE ==>
  expr_vv_sim_ptr d ctx PG func cenv cx ty (TopLevelName ann (src,id)) es
Proof
  rw[expr_vv_sim_ptr_def] >>
  metis_tac[missing_module_not_gas_admissible]
QED

Theorem compile_toplevel_storage_undecodable_vv_sim_ptr:
  !d ctx PG func cenv cx env ty ann src id es ts tr typ id_str.
  expr_sim_pre cenv cx env (TopLevelName ann (src,id)) es /\
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
  ~(?slot tvt v. lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
                 evaluate_type (get_tenv cx) typ = SOME tvt /\
                 read_storage_slot cx tr (n2w slot) tvt es = (INL v, es)) ==>
  expr_vv_sim_ptr d ctx PG func cenv cx ty (TopLevelName ann (src,id)) es
Proof
  rw[expr_vv_sim_ptr_def] >>
  drule_all admissible_toplevel_storage_lookup >> strip_tac >>
  `gas_marked_exec F (ctx,func) (eval_expr cx (TopLevelName ann (src,id)))
     (es,s0) [] (INL (PlaceR (StoragePlace tr (n2w slot) tvt)))
     (es with storage_trace := es.storage_trace ++ [StorageRoot tr slot tvt])
     (OK s0)` by (irule toplevel_storage_marked_exec >> metis_tac[]) >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >>
  disj2_tac >> disj1_tac >> rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL (PlaceR (StoragePlace tr (n2w slot) tvt))`,
                `es with storage_trace := es.storage_trace ++ [StorageRoot tr slot tvt]`,
                `G0`, `tn0`, `OK s0`] >>
  conj_tac >- fs[gas_marked_exec_def] >>
  gen_tac >> strip_tac >> `F` suffices_by simp[] >>
  `valid_horizon cx st0 H es.storage_trace /\ MEM (tr,n2w slot,tvt) (FST H)` by
    gvs[vyperStorageFootprintTheory.valid_horizon_def,
        vyperStorageFootprintTheory.storage_observations_ok_def,
        vyperStorageFootprintTheory.storage_trace_regions_def] >>
  qpat_x_assum `!H. valid_horizon _ _ H es.storage_trace ==> _` drule >>
  strip_tac >>
  `slots_in_range (get_storage cx es tr) (w2n ((n2w slot):bytes32)) tvt` by
    gvs[vyperStorageFootprintTheory.storage_well_formed_on_def] >>
  drule vyperTypeValuesTheory.evaluate_type_well_formed_type_value >> strip_tac >>
  drule_all decode_value_from_slots_in_range >> strip_tac >>
  qpat_x_assum `!slot tvt v. _` (qspecl_then [`slot`, `tvt`, `v`] mp_tac) >>
  fs[read_storage_slot_def, vyperStorageBackendTheory.get_storage_backend_eq,
     bind_def, lift_option_def, return_def, wordsTheory.w2n_n2w]
QED

Theorem compile_toplevel_storage_vv_sim_ptr:
  !d ctx PG func cenv cx env ty ann src id es ts tr typ id_str slot tvt v.
  expr_sim_pre cenv cx env (TopLevelName ann (src,id)) es /\
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME tvt /\
  read_storage_slot cx tr (n2w slot) tvt es = (INL v,es) ==>
  expr_vv_sim_ptr d ctx PG func cenv cx ty (TopLevelName ann (src,id)) es
Proof
  rw[expr_vv_sim_ptr_def] >>
  `gas_marked_exec F (ctx,func) (eval_expr cx (TopLevelName ann (src,id)))
     (es,s0) [] (INL (PlaceR (StoragePlace tr (n2w slot) tvt)))
     (es with storage_trace := es.storage_trace ++ [StorageRoot tr slot tvt])
     (OK s0)` by (irule toplevel_storage_marked_exec >> metis_tac[]) >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >>
  disj2_tac >> disj1_tac >> rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL (PlaceR (StoragePlace tr (n2w slot) tvt))`,
                `es with storage_trace := es.storage_trace ++ [StorageRoot tr slot tvt]`,
                `G0`, `tn0`, `OK s0`] >>
  conj_tac >- fs[gas_marked_exec_def] >>
  gen_tac >> strip_tac >>
  `valid_horizon cx st0 H es.storage_trace /\ MEM (tr,n2w slot,tvt) (FST H)` by
    gvs[vyperStorageFootprintTheory.valid_horizon_def,
        vyperStorageFootprintTheory.storage_observations_ok_def,
        vyperStorageFootprintTheory.storage_trace_regions_def] >>
  qpat_x_assum `!H. valid_horizon _ _ H es.storage_trace ==> _` drule >>
  strip_tac >>
  `slots_in_range (get_storage cx es tr) (w2n ((n2w slot):bytes32)) tvt` by
    gvs[vyperStorageFootprintTheory.storage_well_formed_on_def] >>
  `w2n ((n2w slot):bytes32) + type_slot_size tvt <= dimword (:256)` by
    (gvs[vyperStorageFootprintTheory.valid_horizon_def,
         vyperStorageFootprintTheory.regions_consistent_def] >>
     qpat_x_assum `!b slot tv. MEM _ _ ==> _` (drule_then mp_tac) >> simp[]) >>
  `!st. storage_read_live H tr st (n2w slot) tvt` by
    metis_tac[observed_storage_region_read_live] >>
  `typ = ann` by
    (gvs[expr_sim_pre_def, expr_sim_inv_def] >>
     metis_tac[TopLevelName_storage_decl_type_eq]) >>
  gvs[] >>
  `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  fs[] >> drule_all toplevel_storage_ce_vars >> strip_tac >>
  `compile_expr cenv ty (TopLevelName ann (src,id)) sa =
     (LocatedValue ann (mk_ptr (Lit (n2w slot))
        (if tr then LocTransient else LocStorage)),sa)` by
    (Cases_on `tr` >> gvs[compile_expr_def, vyperASTTheory.expr_type_def]) >>
  gvs[] >>
  `es with <|gas_obs := []; storage_trace := es.storage_trace ++ [StorageRoot tr slot tvt]|> =
   es with <|storage_trace := es.storage_trace ++ [StorageRoot tr slot tvt]; gas_obs := []|>` by
    simp[evaluation_state_component_equality] >>
  conj_tac >- simp[gas_path_ptr_rules] >>
  pop_assum SUBST1_TAC >>
  conj_tac >- (irule toplevel_storage_value_post >> simp[]) >>
  `ptr_vv_ok cx ann (PlaceR (StoragePlace tr (n2w slot) tvt))
     (LocatedValue ann (mk_ptr (Lit (n2w slot))
       (if tr then LocTransient else LocStorage)))
     (es with <|storage_trace := es.storage_trace ++ [StorageRoot tr slot tvt];
                gas_obs := []|>) G0 tn0 s0` by
    (irule (INST_TYPE [alpha |-> ``:256``] toplevel_live_ptr_vv_ok) >>
     qexists_tac `H` >>
     gvs[ghost_inv_def] >> metis_tac[optionTheory.SOME_11]) >>
  Cases_on `tr` >>
  gvs[ghost_inv_def, ghost_kept_def, mk_ptr_def, vyperASTTheory.expr_type_def] >>
  metis_tac[]
QED

Theorem compile_toplevel_immutable_vv_sim_ptr:
  !d ctx PG func cenv cx env ty ann src id es ts.
  expr_sim_pre cenv cx env (TopLevelName ann (src,id)) es /\
  get_module_code cx src = SOME ts /\ find_var_decl_by_name id ts = NONE ==>
  expr_vv_sim_ptr d ctx PG func cenv cx ty (TopLevelName ann (src,id)) es
Proof
  rw[expr_vv_sim_ptr_def] >>
  drule_all toplevel_immutable_lookup >> strip_tac >>
  drule compile_toplevel_immutable_ptr >>
  disch_then (qspecl_then [`ty`, `sa`, `ann`] assume_tac) >> gvs[] >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >>
  disj2_tac >> disj1_tac >> rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL (PlaceR (ImmutablePlace cenv.ce_module id []))`,
                `es`, `G0`, `tn0`, `OK s0`] >>
  conj_tac
  >- simp[gas_explicit_def, Once evaluate_def, lookup_global_def, bind_def,
          lift_option_type_def, return_def, raise_def, get_immutables_def,
          get_address_immutables_def] >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!H. valid_horizon _ _ H es.storage_trace ==> _` drule >>
  strip_tac >> simp[gas_path_ptr_rules] >>
  conj_tac >- (irule toplevel_immutable_post >> simp[] >> metis_tac[]) >>
  simp[toplevel_code_ptr_vv_ok, vyperASTTheory.expr_type_def, mk_ptr_def] >>
  gvs[ghost_inv_def, ghost_kept_def] >> metis_tac[]
QED

Theorem compile_toplevel_name_vv_sim_ptr:
  !d ctx PG func cenv cx env ty ann nsid es.
  expr_sim_pre cenv cx env (TopLevelName ann nsid) es ==>
  expr_vv_sim_ptr d ctx PG func cenv cx ty (TopLevelName ann nsid) es
Proof
  rpt strip_tac >> PairCases_on `nsid` >>
  rename1 `TopLevelName ann (src,id)` >>
  Cases_on `get_module_code cx src`
  >- simp[compile_toplevel_no_module_vv_sim_ptr] >>
  rename1 `get_module_code cx src = SOME ts` >>
  Cases_on `find_var_decl_by_name id ts`
  >- (irule compile_toplevel_immutable_vv_sim_ptr >> metis_tac[]) >>
  rename1 `find_var_decl_by_name id ts = SOME di` >>
  PairCases_on `di` >> Cases_on `di0`
  >~ [`HashMapVarDecl`]
  >- (gvs[expr_sim_pre_def, expr_sim_inv_def] >>
      metis_tac[TopLevelName_Type_HashMapVarDecl_impossible]) >>
  rename1 `StorageVarDecl tr typ` >>
  Cases_on `?slot tvt v. lookup_var_slot_from_layout cx tr src di1 = SOME slot /\
                         evaluate_type (get_tenv cx) typ = SOME tvt /\
                         read_storage_slot cx tr (n2w slot) tvt es = (INL v,es)`
  >- (gvs[] >> irule compile_toplevel_storage_vv_sim_ptr >> metis_tac[]) >>
  irule compile_toplevel_storage_undecodable_vv_sim_ptr >> metis_tac[]
QED
