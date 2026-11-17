(* Counted top-level name simulation: undecodable. *)
Theory exprSimTopLevelUndecodable
Ancestors
  exprSimTopLevelProps exprSimTopLevelStorage exprSimMemorySource
  exprSimProps exprSimHypsDefs exprSimDefs loweringPosts
  gasOutcome gasSummary gasSummaryCompose gasContext fragGasPath fragGasMode
  list finite_map exprLowering exprLoweringProps compileEnv context
  vyperAST vyperInterpreter vyperState vyperTypeSystem vyperTypeEnv
  vyperTypeInvariants vyperTypeGlobalLookupSoundness vyperTyping
  vyperValueOperation valueEncoding fragExec venomState
  vyperStorageLayoutSafety vyperLookupStorage

val lookup_global_tac =
  simp[Once evaluate_def, lookup_global_def, bind_def, lift_option_type_def,
       return_def, raise_def, LET_THM];


Theorem compile_toplevel_storage_undecodable_sim:
  !ctx func cenv cx env ty ann src id es ts tr typ id_str.
    expr_sim_pre cenv cx env (TopLevelName ann (src, id)) es /\
    get_module_code cx src = SOME ts /\
    find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ, id_str) /\
    ~(?slot tvt v. lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
                   evaluate_type (get_tenv cx) typ = SOME tvt /\
                   read_storage_slot cx tr (n2w slot) tvt es = (INL v, es)) ==>
    expr_vv_sim ctx func cenv cx ty (TopLevelName ann (src, id)) es
Proof
  rw[expr_vv_sim_def] >>
  drule_all admissible_toplevel_storage_lookup >> strip_tac >>
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
  qpat_x_assum `!H. valid_horizon _ _ H es.storage_trace ==> _` drule >>
  strip_tac >>
  `slots_in_range (get_storage cx es tr) (w2n ((n2w slot):bytes32)) tvt` by
    gvs[vyperStorageFootprintTheory.storage_well_formed_on_def] >>
  `F` suffices_by simp[] >>
  drule vyperTypeValuesTheory.evaluate_type_well_formed_type_value >> strip_tac >>
  drule_all decode_value_from_slots_in_range >> strip_tac >>
  qpat_x_assum `decode_value _ _ _ = SOME v`
    (assume_tac o REWRITE_RULE [wordsTheory.w2n_n2w]) >>
  qpat_x_assum `!slot tvt v. _` (qspecl_then [`slot`, `tvt`, `v`] mp_tac) >>
  simp[read_storage_slot_def, vyperStorageBackendTheory.get_storage_backend_eq,
       bind_def, lift_option_def, return_def, wordsTheory.w2n_n2w]
QED

