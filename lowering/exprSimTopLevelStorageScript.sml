(* Counted top-level name simulation: storage. *)
Theory exprSimTopLevelStorage
Ancestors
  exprSimTopLevelProps exprSimMemorySource accountsRelProps
  exprSimProps exprSimHypsDefs exprSimDefs loweringPosts
  gasOutcome gasSummary gasSummaryCompose gasContext fragGasPath fragGasMode
  list finite_map exprLowering exprLoweringProps compileEnv loweringStateRelDefs context
  vyperAST vyperInterpreter vyperState vyperTypeSystem vyperTypeEnv
  vyperTypeInvariants vyperTypeGlobalLookupSoundness vyperTyping
  vyperValueOperation valueEncoding fragExec venomState
  vyperStorageLayoutSafety vyperLookupStorage

val lookup_global_tac =
  simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
       return_def, raise_def, LET_THM];

Theorem toplevel_storage_marked_exec:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
  lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
  evaluate_type (get_tenv cx) typ = SOME tvt /\ ~s0.vs_halted ==>
  gas_marked_exec F (ctx,func) (eval_expr cx (TopLevelName ann (src,id)))
    (es,s0) [] (INL (PlaceR (StoragePlace tr (n2w slot) tvt)))
    (es with storage_trace := es.storage_trace ++ [StorageRoot tr slot tvt])
    (OK s0)
Proof
  strip_tac >>
  simp[gas_marked_exec_def, gas_marked_path_def, gas_path_rules,
       Once evaluate_def, lookup_global_def, bind_def, ignore_bind_def,
       record_storage_event_def, lift_option_type_def,
       return_def, raise_def, LET_THM]
QED

Theorem toplevel_storage_value_post:
  evaluate_type (get_tenv cx) ann = SOME tvt /\
  read_storage_slot cx tr (n2w slot) tvt es = (INL v,es) /\
  slots_in_range (get_storage cx es tr) (w2n ((n2w slot):bytes32)) tvt /\
  (!st. storage_read_live H tr st (n2w slot) tvt) /\
  w2n ((n2w slot):bytes32) + type_slot_size tvt <= dimword (:256) /\
  stmt_state_rel H ctx func cenv cx es s0 /\
  storage_well_formed_on cx es (FST H) ==>
  vv_post H ctx func cenv cx (TopLevelName ann (src,id)) es sa sa s0
    (es with <|storage_trace := obs; gas_obs := []|>)
    (PlaceR (StoragePlace tr (n2w slot) tvt))
    (LocatedValue ann (mk_ptr (Lit (n2w slot))
       (if tr then LocTransient else LocStorage))) s0
Proof
  strip_tac >>
  `read_result cx (PlaceR (StoragePlace tr (n2w slot) tvt)) es = (INL v,es)` by
    simp[read_result_def, read_place_def] >>
  `read_result cx (PlaceR (StoragePlace tr (n2w slot) tvt))
     (es with <|storage_trace := obs; gas_obs := []|>) =
   (INL v, es with <|storage_trace := obs; gas_obs := []|>)` by
    (drule read_result_gas_obs >> disch_then (qspec_then `[]` assume_tac) >>
     qspecl_then [`cx`, `PlaceR (StoragePlace tr (n2w slot) tvt)`,
                  `es with gas_obs := []`, `obs`] mp_tac
       (Q.GENL [`cx`, `r`, `st`, `p`]
          vyperEvalPureExprTheory.read_result_trace) >>
     simp[]) >>
  `stmt_state_rel H ctx func cenv cx
     (es with <|storage_trace := obs; gas_obs := []|>) s0` by
    (drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`, `s0.vs_inst_idx`, `[]`] mp_tac) >>
     simp[]) >>
  `storage_well_formed_on cx
     (es with <|storage_trace := obs; gas_obs := []|>) (FST H)` by
    (`(es with <|storage_trace := obs; gas_obs := []|>).accounts = es.accounts /\
      (es with <|storage_trace := obs; gas_obs := []|>).tStorage = es.tStorage` by
       simp[] >>
     metis_tac[vyperStorageFootprintTheory.storage_well_formed_on_backends]) >>
  `storage_range_agree (get_storage cx es tr)
    (if tr then contract_transient s0 else contract_storage s0)
    (n2w slot) tvt` by
    (irule storage_range_agree_of_live >> conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`H`, `tr`] >> simp[] >> Cases_on `tr` >>
     gvs[stmt_state_rel_def, state_rel_def, storage_rel_def,
         transient_rel_def, vyperStorageBackendTheory.get_storage_def,
         vfmStateTheory.lookup_account_def]) >>
  Cases_on `tr` >>
  gvs[vv_post_def, vv_holds_def, vv_at_def, storage_holds_def,
      mk_ptr_def, eval_operand_def, vyperASTTheory.expr_type_def,
      locals_kept_mem, read_result_def, read_place_def, vyperStorageBackendTheory.get_storage_def]
QED

Theorem compile_toplevel_storage_vv_sim:
  !ctx func cenv cx env ty ann src id es ts tr typ id_str slot tvt v.
    expr_sim_pre cenv cx env (TopLevelName ann (src, id)) es /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
    evaluate_type (get_tenv cx) typ = SOME tvt /\
    read_storage_slot cx tr (n2w slot) tvt es = (INL v, es) ==>
    expr_vv_sim ctx func cenv cx ty (TopLevelName ann (src, id)) es
Proof
  rw[expr_vv_sim_def] >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`INL (PlaceR (StoragePlace tr (n2w slot) tvt))`,
                `es with storage_trace := es.storage_trace ++ [StorageRoot tr slot tvt]`,
                `OK s0`] >>
  conj_tac >- (irule toplevel_storage_marked_exec >> simp[]) >>
  disj1_tac >> simp[] >> rpt strip_tac >>
  `valid_horizon cx st0 H es.storage_trace /\ MEM (tr,n2w slot,tvt) (FST H)` by
    gvs[vyperStorageFootprintTheory.valid_horizon_def,
        vyperStorageFootprintTheory.storage_observations_ok_def,
        vyperStorageFootprintTheory.storage_trace_regions_def] >>
  first_x_assum drule >> strip_tac >>
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
     metis_tac[vyperTypeGlobalLookupSoundnessTheory.TopLevelName_storage_decl_type_eq]) >>
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
  pop_assum SUBST1_TAC >>
  irule toplevel_storage_value_post >> simp[]
QED
