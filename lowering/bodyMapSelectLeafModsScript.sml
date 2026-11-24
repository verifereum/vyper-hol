(* A mapping leaf observes the computed storage slot without yet reading it. *)
Theory bodyMapSelectLeafMods
Ancestors
  bodyFullPostsMods bodyFullShadowBodyInv bodyInvSplit gasOutcomeFullPostMods
  exprSimSubscriptMap exprSimMemDefs bodyPtrDefs accountsRelProps sourceUnitExecution
  vyperHashMapStorage vyperStorageFootprint loweringStateRelDefs exprLoweringProps
  fragGasOriginPtr loweringPosts bodyFullHashKeccakFixed ptrDiscipline
  context vyperAST vyperState supportedExprTraverse words pred_set

Theorem mapping_leaf_ptr_mods[local]:
  evaluate_type (get_tenv cx) ann = SOME rt /\
  (!st. storage_read_live (H:(bool # bytes32 # type_value) list # num list) tr st w rt) /\
  dead_lo_ok_mods H D lo cenv cx /\ stor_taint_ok_at D tn s /\
  eval_operand op s = SOME w /\ op_taint tn op = {} ==>
  ptr_vv_ok cx ann (PlaceR (StoragePlace tr w rt))
    (LocatedValue ann (mk_ptr op (slot_loc tr))) ee G tn s
Proof
  Cases_on `tr` >> simp[ptr_vv_ok_def, slot_loc_def, mk_ptr_def] >>
  rpt strip_tac >> gvs[] >>
  fs[stor_taint_ok_at_def, dead_lo_ok_mods_def, cx_dead_def, SUBSET_DEF] >>
  first_x_assum drule >>
  simp[] >> IF_CASES_TAC >> simp[] >> strip_tac >>
  fs[storage_read_live_def] >>
  qpat_x_assum `!st j bv. storage_dead _ _ st j bv ==> _` (drule_then strip_assume_tac) >>
  simp[]
QED

Theorem mapping_leaf_vv_post_mods[local]:
  evaluate_type (get_tenv cx) ann = SOME rt /\
  MEM (tr,w,rt) (FST H) /\ regions_consistent (FST H) /\
  stmt_state_rel H ctx func cenv cx ee u /\
  immutable_frame_mods func cenv cx ee u /\
  storage_well_formed_on cx ee (FST H) /\ eval_operand op u = SOME w /\
  wb_frame cenv es ee sa s0 u /\
  (~expr_has_effect (Subscript ann obj idx) ==> pure_frame cenv func es sa s0 u) ==>
  vv_post_mods H ctx func cenv cx (Subscript ann obj idx) es sa sb s0 ee
    (PlaceR (StoragePlace tr w rt)) (LocatedValue ann (mk_ptr op (slot_loc tr))) u
Proof
  strip_tac >>
  `vv_holds cenv cx ann (PlaceR (StoragePlace tr w rt))
     (LocatedValue ann (mk_ptr op (slot_loc tr))) ee u` by
    (irule mapping_leaf_vv_holds >> simp[mk_ptr_def] >>
     qexistsl [`H`,`ctx`,`func`] >> simp[]) >>
  `storage_read_live H tr (get_storage cx ee tr) w rt` by
    (irule observed_storage_region_read_live >> simp[]) >>
  qpat_x_assum `wb_frame _ _ _ _ _ _` (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
  Cases_on `tr` >>
  gvs[vv_post_mods_def, vv_holds_mods_def, vv_at_def, vv_place_ptr_mods_def,
      vv_place_ptr_def, slot_loc_def, mk_ptr_def, expr_type_def] >>
  first_assum ACCEPT_TAC
QED

Theorem mapping_leaf_extended_horizon[local]:
  valid_horizon cx st0 H (fin.storage_trace ++ [StorageRoot tr (w2n w) rt]) ==>
  valid_horizon cx st0 H fin.storage_trace /\
  MEM (tr,w,rt) (FST H) /\ regions_consistent (FST H)
Proof
  strip_tac >> conj_tac >- metis_tac[gasOutcomeFullTheory.valid_horizon_append] >>
  fs[valid_horizon_def, storage_observations_ok_def, storage_trace_regions_def]
QED

Theorem mapping_leaf_trace_frame[local]:
  immutable_frame_mods func cenv cx fin u /\
  ghost_inv_at_mods D lo d cenv cx fin G tn u /\
  wb_frame cenv es fin sa s0 u /\ storage_well_formed_on cx fin rs ==>
  immutable_frame_mods func cenv cx (fin with storage_trace := obs) u /\
  ghost_inv_at_mods D lo d cenv cx (fin with storage_trace := obs) G tn u /\
  wb_frame cenv es (fin with storage_trace := obs) sa s0 u /\
  storage_well_formed_on cx (fin with storage_trace := obs) rs
Proof
  strip_tac >> rpt conj_tac
  >- (qpat_assum `immutable_frame_mods _ _ _ fin _` mp_tac >>
      simp[NoAsms, immutable_frame_mods_def, immutables_rel_mods_def,
           immutable_alloca_sep_mods_def, immutable_alloca_sep_def, immutables_rel_def] >>
      strip_tac >> conj_tac >- first_assum ACCEPT_TAC >>
      rpt gen_tac >> disch_tac >>
      qpat_assum `!src tops. _ ==> immutable_decl_sep _ _ _ _ _ _ /\ _`
        (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC)
  >- (qpat_assum `ghost_inv_at_mods _ _ _ _ _ fin _ _ _` mp_tac >>
      simp[NoAsms, ghost_inv_at_mods_def] >> strip_tac >> first_assum ACCEPT_TAC)
  >- (qpat_assum `wb_frame _ _ fin _ _ _` mp_tac >>
      simp[NoAsms, wb_frame_def, locals_kept_def, popped_kept_def] >>
      strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  dep_rewrite.DEP_ONCE_REWRITE_TAC [Q.INST [`st` |-> `fin`] storage_well_formed_on_backends] >> simp[]
QED

Theorem mapping_select_leaf_mods:
  evaluate_type (get_tenv cx) ann = SOME rt /\
  fin.gas_obs = [] /\ ~it.vs_halted /\
  vv = LocatedValue ann (mk_ptr outop (slot_loc tr)) /\
  eval_operand outop u = SOME (hashmap_slot slot (encode_hashmap_key kt v)) /\
  op_taint tnu outop = {} /\
  wb_frame cenv es fin sa s0 u /\
  (~expr_has_effect (Subscript ann obj idx) ==> pure_frame cenv func es sa s0 u) /\
  u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gu tnu /\
  (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
      (it,Gi,tni) [] (OK u,Gu,tnu) /\
    stmt_state_rel H ctx func cenv cx fin u /\
    immutable_frame_mods func cenv cx fin u /\
    storage_well_formed_on cx fin (FST H) /\
    ghost_inv_at_mods (DF H) lo d cenv cx fin Gu tnu u) ==>
  gas_outcome_full_mods (DF,lo,explicit,ctx,func,PG) cenv.ce_modules cx st0
    (select_result cx (expr_type obj) (HashMapRef tr slot kt (Type ann))
      (ValueSubscript v)) (fin,it,Gi,tni)
    (\H res ee G tn t. ?tv. res = INL tv /\
      vv_post_mods H ctx func cenv cx (Subscript ann obj idx) es sa sb s0 ee tv vv t /\
      vv_store_bound cx (post_value_type cenv (Subscript ann obj idx))
        (lowered_value_type cenv (Subscript ann obj idx)) ee tv vv t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
      s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
      ptr_vv_ok cx (post_value_type cenv (Subscript ann obj idx)) tv vv ee G tn t /\
      (!v. tv = Value v /\ ~is_word_type (post_value_type cenv (Subscript ann obj idx)) /\
           ~is_bytestring_type (post_value_type cenv (Subscript ann obj idx)) ==>
           vv_own cenv cx (post_value_type cenv (Subscript ann obj idx)) sa sb ee tv vv t /\
           (!t' p. vv = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
      (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
       ?val. read_result cx tv ee = (INL val, ee) /\
             !rt w. evaluate_type (get_tenv cx) (post_value_type cenv (Subscript ann obj idx)) =
                      SOME rt /\ eval_operand (vv_operand vv) t = SOME w ==>
                    w2n w + type_memory_size rt <= lo /\
                    (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
                           val_in_memory rt val (w2n w) mem)) /\
      (!t' op. vv = StackValue t' op /\ ~is_word_type (post_value_type cenv (Subscript ann obj idx)) ==>
               ptr_buf_ok cenv (Subscript ann obj idx) op G t) /\
      (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
              ptr_buf_ok cenv (Subscript ann obj idx) p.ptr_operand G t) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn) R
Proof
  strip_tac >>
  qabbrev_tac `w = hashmap_slot slot (encode_hashmap_key kt v)` >>
  qabbrev_tac `obs = fin.storage_trace ++ [StorageRoot tr (w2n w) rt]` >>
  `fin with gas_obs := [] = fin` by
    (qpat_assum `fin.gas_obs = []` (SUBST1_TAC o SYM) >> simp[]) >>
  irule gas_outcome_full_mods_pure >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`Gu`, `fin with storage_trace := obs`,
    `INL (PlaceR (StoragePlace tr w rt))`, `u`, `tnu`] >>
  conj_tac >-
    (drule_then (fn th => simp[th, Abbr `obs`, Abbr `w`,
       vyperStateTheory.evaluation_state_component_equality]) select_result_hashmap_leaf) >>
  `((fin with storage_trace := obs) with gas_obs := []) = fin with storage_trace := obs` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  simp[] >> qx_gen_tac `H` >> strip_tac >>
  `valid_horizon cx st0 H fin.storage_trace /\
   MEM (tr,w,rt) (FST H) /\ regions_consistent (FST H)` by
    (irule mapping_leaf_extended_horizon >> fs[Abbr `obs`]) >>
  qpat_assum `!H. valid_horizon _ _ H fin.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (drule stmt_state_rel_allocas_below_fmp >> simp[]) >>
  drule_all_then (qspec_then `obs` strip_assume_tac) mapping_leaf_trace_frame >>
  `slot_loc tr <> LocCode /\ slot_loc tr <> LocMemory` by
    (Cases_on `tr` >> simp[slot_loc_def]) >>
  gvs[expr_type_def, vv_location_def, mk_ptr_def] >>
  rpt conj_tac
  >- (irule (REWRITE_RULE [mk_ptr_def] mapping_leaf_vv_post_mods) >> simp[])
  >- (irule vv_store_bound_nonmem >> simp[]) >>
  irule (REWRITE_RULE [mk_ptr_def] mapping_leaf_ptr_mods) >> simp[] >>
  qexistsl_tac [`DF H`, `H`, `cenv`, `lo`] >>
  conj_tac >- (gen_tac >> irule observed_storage_region_read_live >> simp[]) >>
  fs[ghost_inv_at_mods_def]
QED
