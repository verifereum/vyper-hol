(* Code-free top-level pointer views and their live storage boundary. *)
Theory exprSimPtrTopLevelViews
Ancestors
  bodyPtrDefs ptrDiscipline compileEnv context vyperAST vyperState
  exprSimTopLevelProps exprSimHypsDefs exprSimTopLevelStorage exprSimTopLevelImmutable
  exprSimHyps exprSimDefs exprSimProps exprLowering exprLoweringProps
  gasSummary fragGasPathPtr gasContext loweringPosts
  vyperTypeGlobalLookupSoundness vyperStorageLayoutSafety vyperTypeSystem
  vyperInterpreter vyperLookupStorage
  venomState accountsRelProps words pred_set finite_map list

Theorem toplevel_live_storage_taint:
  !tr cx tn s w tv k b.
  stor_taint_ok cx tn s /\
  storage_read_live cx tr
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
  stor_taint_ok cx tn s /\
  (!ty. evaluate_type (get_tenv cx) t = SOME ty ==>
    storage_read_live cx tr
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
  rpt strip_tac >> simp[expr_vv_sim_ptr_def] >> rpt gen_tac >> strip_tac >>
  `F` suffices_by simp[] >>
  drule_all admissible_toplevel_storage_lookup >> strip_tac >>
  `contract_storage_well_formed cx es` by
    gvs[expr_sim_pre_def, expr_sim_inv_def] >>
  drule_all toplevel_storage_read_decodes >> metis_tac[]
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
  `slots_in_range (get_storage cx es tr) (w2n ((n2w slot):bytes32)) tvt` by
    (irule toplevel_storage_slots_in_range >>
     gvs[expr_sim_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
  `declared_storage_region cx src id [] = SOME (tr,n2w slot,tvt)` by
    simp[declared_storage_region_def] >>
  `storage_layout_safe cx` by fs[expr_sim_pre_def, expr_sim_inv_def] >>
  `w2n ((n2w slot):bytes32) + type_slot_size tvt <= dimword (:256)` by
    (drule_all storage_layout_safe_region_nonoverflow >> simp[]) >>
  `typ = ann` by
    (gvs[expr_sim_pre_def, expr_sim_inv_def] >>
     metis_tac[TopLevelName_storage_decl_type_eq]) >>
  gvs[] >>
  `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  fs[] >> drule_all toplevel_storage_ce_vars >> strip_tac >>
  `!st. storage_read_live cx tr st (n2w slot) tvt` by
    (gen_tac >> irule declared_storage_region_read_live >>
     qexistsl [`src`, `id`, `[]`] >> simp[declared_storage_region_def]) >>
  `compile_expr cenv ty (TopLevelName ann (src,id)) sa =
     (LocatedValue ann (mk_ptr (Lit (n2w slot))
        (if tr then LocTransient else LocStorage)),sa)` by
    (Cases_on `tr` >> gvs[compile_expr_def, vyperASTTheory.expr_type_def]) >>
  gvs[] >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL (PlaceR (StoragePlace tr (n2w slot) tvt))`,
                `es`, `G0`, `tn0`, `OK s0`] >>
  simp[gas_explicit_def, gas_path_ptr_rules] >>
  conj_tac
  >- simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
          return_def, raise_def] >>
  conj_tac >- (irule toplevel_storage_value_post >> simp[]) >>
  `ptr_vv_ok cx ann (PlaceR (StoragePlace tr (n2w slot) tvt))
     (LocatedValue ann (mk_ptr (Lit (n2w slot))
       (if tr then LocTransient else LocStorage)))
     (es with gas_obs := []) G0 tn0 s0` by
    (irule toplevel_live_ptr_vv_ok >>
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
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL (PlaceR (ImmutablePlace cenv.ce_module id []))`,
                `es`, `G0`, `tn0`, `OK s0`] >>
  simp[gas_explicit_def, gas_path_ptr_rules] >> conj_tac
  >- simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
          return_def, raise_def, get_immutables_def, get_address_immutables_def] >>
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
