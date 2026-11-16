(* Empty-code TopLevelName storage and transient reads, at full horizons. *)
Theory bodyFullToplevelVVStorage
Ancestors
  bodySimFull bodySim exprSimSource bodyToplevelMemory gasOutcomeFullCompose
  exprSimTopLevelStorage exprSimTopLevelProps exprSimHypsDefs
  exprLoweringProps exprLowering loweringPosts bodyPtrDefs
  vyperStorageFootprint vyperStorageBackend vyperTypeValues
  accountsRelProps fragGasPathPtr context words finite_map pred_set list
  vyperInterpreter vyperState vyperAST exprSimHyps exprSimDefs loweringStateRelDefs
  fragGasOriginPtr exprSimMemDefs

Theorem toplevel_storage_vv_full:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (TopLevelName ann (src,id)) es /\
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ,id_str) ==>
  expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cenv cx ty (TopLevelName ann (src,id)) es
Proof
  strip_tac >>
  `expr_sim_pre cenv cx env (TopLevelName ann (src,id)) es` by
    simp[expr_sim_pre_body, vyperTypeCallGraphTheory.int_calls_expr_def] >>
  rw[expr_vv_sim_full_def] >>
  drule_all admissible_toplevel_storage_lookup >> strip_tac >>
  `!tail. eval_expr cx (TopLevelName ann (src,id)) (es with gas_obs := tail) =
    (INL (PlaceR (StoragePlace tr (n2w slot) tvt)),
     es with <|storage_trace := es.storage_trace ++ [StorageRoot tr slot tvt]; gas_obs := tail|>)` by
    simp[Once evaluate_def, lookup_global_def, bind_def, ignore_bind_def,
         record_storage_event_def, lift_option_type_def, return_def, raise_def] >>
  Cases_on `storage_trace_domain cx st0 (es.storage_trace ++ [StorageRoot tr slot tvt])`
  >- suspend "good" >>
  irule gas_outcome_full_bad_nil >> simp[]
QED

Resume toplevel_storage_vv_full[good]:
  irule gas_outcome_full_pure >>
  reverse conj_tac >- simp[] >>
  qexistsl [`G0`, `es with storage_trace := es.storage_trace ++ [StorageRoot tr slot tvt]`,
            `INL (PlaceR (StoragePlace tr (n2w slot) tvt))`, `s0`, `tn0`] >>
  simp[] >> rpt strip_tac >>
  `valid_horizon cx st0 H es.storage_trace /\ MEM (tr,n2w slot,tvt) (FST H)` by
    gvs[valid_horizon_def, storage_observations_ok_def, storage_trace_regions_def] >>
  qpat_x_assum `!H. valid_horizon _ _ H es.storage_trace ==> _` drule >> strip_tac >>
  `typ = ann` by
    (gvs[expr_sim_pre_def, expr_sim_inv_def] >>
     metis_tac[vyperTypeGlobalLookupSoundnessTheory.TopLevelName_storage_decl_type_eq]) >>
  gvs[] >>
  `storage_vars_rel cenv cx /\ transient_vars_rel cenv cx` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  drule_all toplevel_storage_ce_vars >> strip_tac >>
  `compile_expr cenv ty (TopLevelName ann (src,id)) sa =
    (LocatedValue ann (mk_ptr (Lit (n2w slot))
      (if tr then LocTransient else LocStorage)),sa)` by
    (qpat_assum `FLOOKUP cenv.ce_module_vars (src,id) = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `tr` >>
     simp[compile_expr_def, expr_type_def]) >>
  gvs[] >> suspend "posts"
QED

Resume toplevel_storage_vv_full[posts]:
  markerLib.RESUME_TAC >> Cases_on `tr` >>
  gvs[mk_ptr_def, vv_location_def, vv_operand_def, expr_type_def,
      ghost_kept_at_def, gas_origin_ptr_path_rules, vv_store_bound_nonmem] >>
  all_tac
  >~ [`ghost_inv_at _ _ _ _ _ (es with <|gas_obs := []; storage_trace := obs|>) _ _ _`]
  >- (qpat_x_assum `ghost_inv_at _ _ _ _ _ es _ _ _` mp_tac >>
      simp[ghost_inv_at_def] >> metis_tac[])
  >~ [`ghost_inv_at _ _ _ _ _ (es with <|gas_obs := []; storage_trace := obs|>) _ _ _`]
  >- (qpat_x_assum `ghost_inv_at _ _ _ _ _ es _ _ _` mp_tac >>
      simp[ghost_inv_at_def] >> metis_tac[]) >>
  suspend "nontrivial"
QED

Resume toplevel_storage_vv_full[nontrivial]:
  markerLib.RESUME_TAC >>
  all_tac >~ [`ptr_vv_ok _ _ _ _ _ _ _ _`]
  >- (simp[ptr_vv_ok_def, ptrDisciplineTheory.op_taint_def, venomStateTheory.eval_operand_def] >>
      rpt strip_tac >>
      `!st. storage_read_live H F st (n2w slot) tvt` by
        metis_tac[observed_storage_region_read_live] >>
      qpat_x_assum `!H. dead_lo_ok H (DF H) _ _ _` (qspec_then `H` assume_tac) >>
      fs[ghost_inv_at_def, stor_taint_ok_at_def, dead_lo_ok_def,
         sourceUnitExecutionTheory.cx_dead_def, SUBSET_DEF] >>
      qpat_x_assum `!x. x IN tn0.t_stor ==> _` (qspec_then `(k,b)` mp_tac) >>
      simp[] >> IF_CASES_TAC >> simp[] >> strip_tac >>
      gvs[storage_read_live_def] >> metis_tac[]) >>
  all_tac >~ [`ptr_vv_ok _ _ _ _ _ _ _ _`]
  >- (simp[ptr_vv_ok_def, ptrDisciplineTheory.op_taint_def, venomStateTheory.eval_operand_def] >>
      rpt strip_tac >>
      `!st. storage_read_live H T st (n2w slot) tvt` by
        metis_tac[observed_storage_region_read_live] >>
      qpat_x_assum `!H. dead_lo_ok H (DF H) _ _ _` (qspec_then `H` assume_tac) >>
      fs[ghost_inv_at_def, stor_taint_ok_at_def, dead_lo_ok_def,
         sourceUnitExecutionTheory.cx_dead_def, SUBSET_DEF] >>
      qpat_x_assum `!x. x IN tn0.t_trans ==> _` (qspec_then `(k,b)` mp_tac) >>
      simp[] >> IF_CASES_TAC >> simp[] >> strip_tac >>
      gvs[storage_read_live_def] >> metis_tac[]) >>
  suspend "semantic"
QED

Resume toplevel_storage_vv_full[semantic]:
  markerLib.RESUME_TAC >>
  all_tac >~ [`StoragePlace F _ _`]
  >- (irule (SRULE [mk_ptr_def] (Q.INST [`tr` |-> `F`] toplevel_storage_value_post)) >>
      suspend "producer") >>
  irule (SRULE [mk_ptr_def] (Q.INST [`tr` |-> `T`] toplevel_storage_value_post)) >>
  suspend "producer"
QED

Resume toplevel_storage_vv_full[producer]:
  markerLib.RESUME_TAC >> (
  `well_formed_type_value tvt` by metis_tac[evaluate_type_well_formed_type_value] >>
  fs[storage_well_formed_on_def] >>
  `regions_consistent (FST H)` by fs[valid_horizon_def] >>
  fs[regions_consistent_def] >>
  simp[] >>
  rpt conj_tac
  >- metis_tac[observed_storage_region_read_live]
  >- metis_tac[w2n_n2w]
  >- (simp[read_storage_slot_eq, AllCaseEqs()] >>
      metis_tac[vyperLookupStorageTheory.decode_value_from_slots_in_range, w2n_n2w]) >>
  qpat_x_assum `!b slot tv. MEM _ _ ==> slots_in_range _ _ _` drule >> simp[])
QED

Finalise toplevel_storage_vv_full
