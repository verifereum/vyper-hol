(* A qualified storage/transient read denotes its slot at the entry cursor. *)
Theory bodyQualifiedSlotRawMods
Ancestors
  bodyFullPostsMods exprBodyPreProps exprSimTopLevelStorage exprSimTopLevelProps
  exprSimMemorySource stateRelProj typedMemoryCopy accountsRelProps bodyPtrDefs
  gasOutcomeFull vyperStorageFootprint vyperStorageBackend vyperLookupStorage
  vyperTypeGlobalLookupSoundness vyperTypeValues vyperEvalPureExpr sourceUnitExecution
  ptrDiscipline exprSimMemDefs exprLowering loweringPosts loweringStateRelDefs
  bodyFullShadowBodyInv bodyInvSplit context exprLoweringProps exprSimHypsDefs
  vyperTypeEnv vyperStorage
  vyperInterpreter vyperState vyperAST venomState list pred_set words

Theorem slot_horizon_props[local]:
  valid_horizon cx st0 H (es.storage_trace ++ [StorageRoot tr slot rt]) ==>
  valid_horizon cx st0 H es.storage_trace /\
  MEM (tr,n2w slot,rt) (FST H) /\
  (!st. storage_read_live H tr st (n2w slot) rt) /\
  w2n (n2w slot:bytes32) + type_slot_size rt <= dimword (:256)
Proof
  strip_tac >> conj_tac >- metis_tac[valid_horizon_append] >>
  `MEM (tr,n2w slot,rt) (FST H)` by
    fs[valid_horizon_def, storage_observations_ok_def, storage_trace_regions_def] >>
  simp[observed_storage_region_read_live] >>
  fs[valid_horizon_def, regions_consistent_def] >>
  metis_tac[w2n_n2w]
QED

Theorem slot_ptr_clean_mods[local]:
  evaluate_type (get_tenv cx) ann = SOME rt /\
  (!st. storage_read_live (H:(bool # bytes32 # type_value) list # num list) tr st w rt) /\
  dead_lo_ok_mods H D lo cenv cx /\ stor_taint_ok_at D tn s ==>
  ptr_vv_ok cx ann (PlaceR (StoragePlace tr w rt))
    (LocatedValue ann (mk_ptr (Lit w) (slot_loc tr))) ee G tn s
Proof
  Cases_on `tr` >>
  simp[ptr_vv_ok_def, slot_loc_def, mk_ptr_def, op_taint_def, eval_operand_def] >>
  rpt strip_tac >>
  fs[stor_taint_ok_at_def, dead_lo_ok_mods_def, cx_dead_def, SUBSET_DEF] >>
  first_x_assum drule >>
  simp[] >> IF_CASES_TAC >> simp[] >> strip_tac >>
  fs[storage_read_live_def] >>
  qpat_x_assum `!st j bv. storage_dead _ _ st j bv ==> _` (drule_then strip_assume_tac) >>
  simp[]
QED

Theorem slot_vv_post_mods[local]:
  immutable_frame_mods func cenv cx ee s /\
  vv_post H ctx func cenv cx e es sa sa s ee (PlaceR (StoragePlace tr w rt))
    (LocatedValue ann (mk_ptr (Lit w) (slot_loc tr))) s ==>
  vv_post_mods H ctx func cenv cx e es sa sa s ee (PlaceR (StoragePlace tr w rt))
    (LocatedValue ann (mk_ptr (Lit w) (slot_loc tr))) s
Proof
  Cases_on `tr` >>
  simp[vv_post_def, vv_post_mods_def, vv_holds_mods_def,
       vv_place_ptr_mods_def, slot_loc_def, mk_ptr_def] >>
  metis_tac[]
QED

Theorem slot_raw_frame_mods[local]:
  immutable_frame_mods func cenv cx es s /\
  ghost_inv_at_mods D lo d cenv cx es G tn s ==>
  immutable_frame_mods func cenv cx
    (es with <|storage_trace := obs; gas_obs := []|>) s /\
  ghost_inv_at_mods D lo d cenv cx
    (es with <|storage_trace := obs; gas_obs := []|>) G tn s
Proof
  strip_tac >> conj_tac
  >- (fs[immutable_frame_mods_def, immutables_rel_mods_def,
         immutable_alloca_sep_mods_def, immutable_alloca_sep_def, immutables_rel_def] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      rpt gen_tac >> strip_tac >> first_x_assum (drule_then strip_assume_tac) >>
      first_assum ACCEPT_TAC) >>
  qpat_x_assum `ghost_inv_at_mods _ _ _ _ _ es _ _ _` mp_tac >>
  PURE_ONCE_REWRITE_TAC[ghost_inv_at_mods_def] >> simp[] >>
  disch_then strip_assume_tac >> first_assum ACCEPT_TAC
QED

Theorem slot_read_typed[local]:
  well_formed_type_value rt /\ slots_in_range (get_storage cx es tr) (w2n w) rt ==>
  ?v. read_storage_slot cx tr w rt es = (INL v,es) /\ value_has_type rt v
Proof
  strip_tac >> drule_all_then strip_assume_tac decode_value_from_slots_in_range >>
  qexists_tac `v` >> simp[read_storage_slot_eq]
QED

Theorem slot_read_traced[local]:
  read_storage_slot cx tr w rt es = (INL v,es) ==>
  !tail. read_result cx (PlaceR (StoragePlace tr w rt))
            (es with <|storage_trace := obs; gas_obs := tail|>) =
         (INL v,es with <|storage_trace := obs; gas_obs := tail|>)
Proof
  Cases_on `tr` >>
  simp[read_result_def, read_place_def, read_storage_slot_eq, get_storage_def,
       AllCaseEqs()]
QED

Theorem slot_raw_good[local]:
  evaluate_type (get_tenv cx) ann = SOME rt /\
  read_storage_slot cx tr (n2w slot) rt es = (INL v,es) /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es s /\
       immutable_frame_mods func cenv cx es s /\
       storage_well_formed_on cx es (FST H) /\
       ghost_inv_at_mods (DF H) lo d cenv cx es G tn s) ==>
  let obs = es.storage_trace ++ [StorageRoot tr slot rt];
      e = TopLevelName ann (src,id);
      vv = LocatedValue ann (mk_ptr (Lit (n2w slot)) (slot_loc tr));
      tv = PlaceR (StoragePlace tr (n2w slot) rt);
      ee = es with <|storage_trace := obs; gas_obs := []|>
  in
    !H. valid_horizon cx st0 H obs ==>
        MEM (tr,n2w slot,rt) (FST H) /\
        (!st. storage_read_live H tr st (n2w slot) rt) /\
        w2n (n2w slot:bytes32) + type_slot_size rt <= dimword (:256) /\
        vv_post_mods H ctx func cenv cx e es sa sa s ee tv vv s /\
        vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv s /\
        ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s /\
        ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn s
Proof
  strip_tac >> simp[] >> gen_tac >> strip_tac >>
  drule_then strip_assume_tac slot_horizon_props >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  drule_all_then (qspec_then `es.storage_trace ++ [StorageRoot tr slot rt]` strip_assume_tac)
    slot_raw_frame_mods >>
  fs[expr_type_def] >> conj_tac
  >- (irule slot_vv_post_mods >> simp[slot_loc_def] >>
      irule (SRULE [] toplevel_storage_value_post) >>
      fs[storage_well_formed_on_def, arithmeticTheory.ADD_COMM] >>
      metis_tac[w2n_n2w]) >>
  conj_tac >- (irule vv_store_bound_nonmem >> Cases_on `tr` >> simp[slot_loc_def,mk_ptr_def]) >>
  irule slot_ptr_clean_mods >> simp[] >>
  qexistsl_tac [`DF H`,`H`,`cenv`,`lo`] >> fs[ghost_inv_at_mods_def]
QED

Theorem qualified_slot_raw_mods:
  expr_body_pre_mods mods cenv cx env (TopLevelName ann (src,id)) es /\
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr typ,id_str) /\
  gas_admissible (eval_expr cx (TopLevelName ann (src,id))) expr_vv_res_ok es /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es s /\
       immutable_frame_mods func cenv cx es s /\
       storage_well_formed_on cx es (FST H) /\
       ghost_inv_at_mods (DF H) lo d cenv cx es G tn s) ==>
  ?slot rt.
    let obs = es.storage_trace ++ [StorageRoot tr slot rt];
        e = TopLevelName ann (src,id);
        vv = LocatedValue ann (mk_ptr (Lit (n2w slot)) (slot_loc tr));
        tv = PlaceR (StoragePlace tr (n2w slot) rt);
        ee = es with <|storage_trace := obs; gas_obs := []|>
    in
      lookup_var_slot_from_layout cx tr src id_str = SOME slot /\
      evaluate_type (get_tenv cx) ann = SOME rt /\
      type_memory_bytes cenv ann = type_memory_size rt /\
      (!tail. eval_expr cx e (es with gas_obs := tail) =
              (INL tv,ee with gas_obs := tail)) /\
      (storage_trace_domain cx st0 obs ==>
       ?v. compile_expr cenv ty e sa = (vv,sa) /\ value_has_type rt v /\
           read_storage_slot cx tr (n2w slot) rt es = (INL v,es) /\
           (!tail. read_result cx tv (ee with gas_obs := tail) =
                   (INL v,ee with gas_obs := tail)) /\
           !H. valid_horizon cx st0 H obs ==>
               MEM (tr,n2w slot,rt) (FST H) /\
               (!st. storage_read_live H tr st (n2w slot) rt) /\
               w2n (n2w slot:bytes32) + type_slot_size rt <= dimword (:256) /\
               vv_post_mods H ctx func cenv cx e es sa sa s ee tv vv s /\
               vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv s /\
               ghost_inv_at_mods (DF H) lo d cenv cx ee G tn s /\
               ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn s)
Proof
  strip_tac >> drule_all_then strip_assume_tac admissible_toplevel_storage_lookup >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  `env_consistent env cx es` by fs[expr_sim_inv_mods_def] >>
  drule_all_then SUBST_ALL_TAC TopLevelName_storage_decl_type_eq >>
  `type_memory_bytes cenv ann = type_memory_size tvt` by
    (irule typed_copy_memory_size >> qexists_tac `get_tenv cx` >>
     fs[expr_sim_inv_mods_def] >> rpt strip_tac >>
     qpat_assum `!n fs. FLOOKUP cenv.ce_struct_fields n = SOME fs ==> _`
       (drule_then strip_assume_tac) >> simp[]) >>
  qexistsl_tac [`slot`,`tvt`] >> simp[] >> conj_tac
  >- simp[Once evaluate_def, lookup_global_def, bind_def, ignore_bind_def,
          record_storage_event_def, lift_option_type_def, return_def, raise_def] >>
  simp[storage_trace_domain_def] >> strip_tac >>
  drule_then strip_assume_tac slot_horizon_props >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  drule_then strip_assume_tac stmt_state_rel_vars_rels >>
  drule_all_then assume_tac toplevel_storage_ce_vars >>
  `well_formed_type_value tvt` by metis_tac[evaluate_type_well_formed_type_value] >>
  `?v. read_storage_slot cx tr (n2w slot) tvt es = (INL v,es) /\ value_has_type tvt v` by
    (irule slot_read_typed >> fs[storage_well_formed_on_def]) >>
  qexists_tac `v` >> simp[] >> conj_tac
  >- (Cases_on `tr` >> simp[compile_expr_def, slot_loc_def, expr_type_def]) >>
  conj_tac >- (drule slot_read_traced >> simp[]) >>
  drule_all_then (qspecl_then [`src`,`sa`,`id`] mp_tac) slot_raw_good >>
  simp_tac (srw_ss()) [LET_THM, arithmeticTheory.ADD_COMM] >>
  disch_tac >> gen_tac >> disch_tac >>
  first_x_assum (qspec_then `H` (drule_then strip_assume_tac)) >> simp[]
QED
