(*
 * Augmented assignment to a field or an element of a storage or transient
 * variable (#637), whatever the indices do.  The current word is loaded by
 * SLOAD or TLOAD at the place's slot, combined with the right-hand side,
 * and stored back.  The target's evaluation records the root of the place's
 * region, so every horizon valid after it observes the place, which gives
 * its slots in range and live (aug_place_target_storage_ready), and the load
 * reads the source's current value (aug_place_storage_load_ready).
 *
 * TOP-LEVEL:
 *   compile_augassign_place_storage_case
 *)
Theory stmtSimAugAssignPlaceStorage
Ancestors
  valueEncodingProps
  exprSimSource bodyExprPreFacts exprSimTopLevelProps stmtSimBreak stmtSimContinue stmtSimExpr stmtSimSeqEnv stmtSimPass stmtSimProps exprSimHypsDefs stmtSimZero stmtSimDefs loweringPosts bodyAppendStorageFacts bodyAppendStorageAdapter
  vyperStorageLayoutSafety vyperLookupStorage vyperScopePreservation
  list finite_map bodySim allocLimits allocLimitsProps  exprSimHyps exprLoweringProps
  stmtSimIf stmtLoweringMono stmtLowering compileEnv loweringStateRelDefs fragExec
  supportedExprTraverse supportedStmtTraverse supportedStmts
  vyperAST vyperInterpreter vyperState vyperTypeSystem vyperTypeCallGraph
  vyperTypeCallStackSoundness stmtSimReason stmtSimReasonExpr
  stmtSimReasonStorage stmtSimReasonCode supportedExprs stmtSimAssign stmtSimDeclStore
  stmtSimAugAssign vyperTypeEvalSoundness vyperTypeInvariants
  vyperTypeExprSoundness vyperEvalOutcomeSuffix exprSimMain
  exprReasonOperand
  vyperTypeValues vyperTyping vyperTypeDefaults stmtSimAssignTuple
  vyperTypeEnvPreservation bodySimExprCases bodyStoragePreservation
  vyperCallOutcomeStorage vyperTypeStoragePreservation
  stmtSimAssignStorage supportedDecls vyperTypeContractStaticMaps
  vyperStoragePlaceProvenance vyperPlaceStoragePreservation accountsRelProps
  vyperTypeContract compileVyper supportedTypes stmtSimAssignAttr
  stmtSimAssignStorageCopy
  stmtSimAugAssignAttr stmtSimAssignAttrStorage stmtSimAugAssignStorage
  stmtSimAugAssignAttrStorage stmtSimAssignMem stmtSimAssignTupleMem
  stmtSimAssignTupleTargets
  memoryLocalRhsProps stmtPoppedKeys exprOpenMain bodyStorageMetadata
  vyperPureExpr targetPlaceSim targetPlaceSimCases exprSimDefs
  placeStore supportedTargets exprSimProps exprSimSource loweringPosts
  bodyAugPlaceTarget bodySimAugPlaceStore
  bodySimAugPlaceScopes bodySimAugPlaceMemory
  stmtSimAugAssignPlace targetPlaceLive targetPlaceSimCasesBase
  stmtSimAugAssignPlaceMemory gasOutcome gasSummary gasContext
  targetPlaceSimDefs
Libs
  monadsyntax

Theorem aug_place_storage_query_metadata:
  place_ptr_rel cenv cx s (PlaceR (StoragePlace tr slot tv)) w loc (Type ty) /\
  read_place cx (StoragePlace tr slot tv) st = (INL cur,stc) /\
  place_type_value cx (StoragePlace tr slot tv) stc = (INL ptv,stt) ==>
  w = slot /\ loc = SOME (slot_loc tr) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  stc = st /\ stt = st /\ ptv = tv /\
  read_storage_slot cx tr slot tv st = (INL cur,st)
Proof
  strip_tac >>
  `stc = st /\ stt = st` by
    metis_tac[read_place_state, place_type_value_state] >>
  gvs[place_ptr_rel_def, read_place_def, place_type_value_def,
      return_def]
QED

Theorem aug_place_update_lookup_other:
  !(k:bytes32) u st i.
    i < dimword (:256) /\ i <> w2n k ==>
    lookup_storage (n2w i) (update_storage k u st) = lookup_storage (n2w i) st
Proof
  rpt strip_tac >>
  `(n2w i:bytes32) <> k` by
    (disch_then (mp_tac o AP_TERM ``w2n:bytes32 -> num``) >>
     asm_simp_tac pure_ss [wordsTheory.w2n_n2w,
                          arithmeticTheory.LESS_MOD] >> simp[]) >>
  simp[vfmStateTheory.lookup_storage_def, vfmStateTheory.update_storage_def,
       combinTheory.APPLY_UPDATE_THM]
QED

Theorem aug_place_dead_bytes_field_update:
  !fs fld off ctv bs k u st.
    struct_field_slot fs fld = SOME (off,ctv) /\
    bs + type_slot_size_fields fs <= dimword (:256) /\
    bs + off <= w2n k /\ w2n k < bs + off + type_slot_size ctv /\
    (!j byte. dead_bytes (update_storage k u st) (bs+off) ctv j byte <=>
              dead_bytes st (bs+off) ctv j byte) ==>
    !j byte. dead_bytes_fields (update_storage k u st) bs fs j byte <=>
             dead_bytes_fields st bs fs j byte
Proof
  Induct_on `fs` >- simp[struct_field_slot_def] >>
  Cases >> rpt gen_tac >> rename1 `(fid,fty)::fs` >>
  simp[struct_field_slot_def, vyperValueTheory.type_slot_size_def] >>
  strip_tac >> simp[dead_bytes_def] >>
  Cases_on `fid = fld` >> gvs[] >> rpt gen_tac
  >- (AP_TERM_TAC >> irule (cj 3 accountsRelPropsTheory.dead_bytes_frame) >>
      rpt strip_tac >> irule aug_place_update_lookup_other >> decide_tac) >>
  rename1 `struct_field_slot fs fld = SOME z` >> Cases_on `z` >> gvs[] >>
  rename1 `struct_field_slot fs fld = SOME (off,ctv)` >>
  `off + type_slot_size ctv <= type_slot_size_fields fs` by
    (drule vyperStoragePlaceRegionTheory.struct_field_slot_end_bound >>
     simp[vyperValueTheory.type_slot_size_def]) >>
  `dead_bytes (update_storage k u st) bs fty j byte <=>
   dead_bytes st bs fty j byte` by
    (irule (cj 1 accountsRelPropsTheory.dead_bytes_frame) >> rpt strip_tac >>
     irule aug_place_update_lookup_other >> decide_tac) >>
  simp[] >> AP_TERM_TAC >> first_x_assum irule >> simp[] >>
  qexistsl_tac [`ctv`, `fld`, `off`] >> metis_tac[]
QED

Theorem aug_place_dead_bytes_other_cell:
  i < n /\ h < n /\ h <> i /\ bs+n*type_slot_size tv <= dimword (:256) /\
  bs+i*type_slot_size tv <= w2n k /\
  w2n k < bs+i*type_slot_size tv+type_slot_size tv ==>
  !j byte. dead_bytes (update_storage k u st) (bs+h*type_slot_size tv) tv j byte <=>
           dead_bytes st (bs+h*type_slot_size tv) tv j byte
Proof
  strip_tac >> rpt gen_tac >>
  `(h+1)*type_slot_size tv <= n*type_slot_size tv` by
    simp[arithmeticTheory.LE_MULT_RCANCEL] >>
  `bs+h*type_slot_size tv+type_slot_size tv <= bs+i*type_slot_size tv \/
   bs+i*type_slot_size tv+type_slot_size tv <= bs+h*type_slot_size tv` by
    metis_tac[aug_place_cells_disjoint] >>
  irule (cj 1 accountsRelPropsTheory.dead_bytes_frame) >> rpt strip_tac >>
  irule aug_place_update_lookup_other >>
  rule_assum_tac (PURE_REWRITE_RULE [arithmeticTheory.RIGHT_ADD_DISTRIB,
                                    arithmeticTheory.MULT_CLAUSES]) >>
  decide_tac
QED

Theorem aug_place_dead_bytes_array_fixed_update:
  i < n /\ bs+n*type_slot_size tv <= dimword (:256) /\
  bs+i*type_slot_size tv <= w2n k /\
  w2n k < bs+i*type_slot_size tv+type_slot_size tv /\
  (!j byte. dead_bytes (update_storage k u st) (bs+i*type_slot_size tv) tv j byte <=>
            dead_bytes st (bs+i*type_slot_size tv) tv j byte) ==>
  !j byte. dead_bytes (update_storage k u st) bs (ArrayTV tv (Fixed n)) j byte <=>
           dead_bytes st bs (ArrayTV tv (Fixed n)) j byte
Proof
  strip_tac >>
  `!h j byte. h < n ==>
     (dead_bytes (update_storage k u st) (bs+h*type_slot_size tv) tv j byte <=>
      dead_bytes st (bs+h*type_slot_size tv) tv j byte)` by
    (rpt strip_tac >> Cases_on `h = i` >- gvs[] >>
     irule aug_place_dead_bytes_other_cell >> qexistsl_tac [`i`, `n`] >> simp[]) >>
  simp[dead_bytes_def] >> metis_tac[]
QED

Theorem aug_place_dead_bytes_array_dynamic_update:
  i < n /\ bs+1+n*type_slot_size tv <= dimword (:256) /\
  bs+1+i*type_slot_size tv <= w2n k /\
  w2n k < bs+1+i*type_slot_size tv+type_slot_size tv /\
  (!j byte. dead_bytes (update_storage k u st) (bs+1+i*type_slot_size tv) tv j byte <=>
            dead_bytes st (bs+1+i*type_slot_size tv) tv j byte) ==>
  !j byte. dead_bytes (update_storage k u st) bs (ArrayTV tv (Dynamic n)) j byte <=>
           dead_bytes st bs (ArrayTV tv (Dynamic n)) j byte
Proof
  strip_tac >>
  `lookup_storage (n2w bs) (update_storage k u st) = lookup_storage (n2w bs) st` by
    (irule aug_place_update_lookup_other >> decide_tac) >>
  `!h j byte. h < n ==>
     (dead_bytes (update_storage k u st) (bs+1+h*type_slot_size tv) tv j byte <=>
      dead_bytes st (bs+1+h*type_slot_size tv) tv j byte)` by
    (rpt strip_tac >> Cases_on `h = i` >- gvs[] >>
     irule aug_place_dead_bytes_other_cell >> qexistsl_tac [`i`, `n`] >> simp[]) >>
  simp[dead_bytes_def] >> rpt gen_tac >>
  eq_tac >> strip_tac >> qexists_tac `i'` >>
  Cases_on `i' < w2n (lookup_storage (n2w bs) st)` >> gvs[] >> metis_tac[]
QED

Theorem aug_place_dead_bytes_array_update:
  i < n /\
  c = (if dyn then bs+1 else bs)+i*type_slot_size tv /\
  bs+type_slot_size (ArrayTV tv (if dyn then Dynamic n else Fixed n)) <= dimword (:256) /\
  c <= w2n k /\ w2n k < c+type_slot_size tv /\
  (!j byte. dead_bytes (update_storage k u st) c tv j byte <=>
            dead_bytes st c tv j byte) ==>
  !j byte. dead_bytes (update_storage k u st) bs
             (ArrayTV tv (if dyn then Dynamic n else Fixed n)) j byte <=>
           dead_bytes st bs (ArrayTV tv (if dyn then Dynamic n else Fixed n)) j byte
Proof
  Cases_on `dyn` >> simp[vyperValueTheory.type_slot_size_def] >> strip_tac
  >- (irule aug_place_dead_bytes_array_dynamic_update >>
      reverse conj_tac >- simp[] >>
      qexists_tac `i` >> gvs[]) >>
  irule aug_place_dead_bytes_array_fixed_update >>
  reverse conj_tac >- simp[] >> qexists_tac `i` >> gvs[]
QED

Theorem aug_place_subregion_mask:
  storage_subregion tv [sb] off leaf /\
  ((?fs. tv = StructTV fs) \/ (?et bd. tv = ArrayTV et bd)) /\
  bs + type_slot_size tv <= dimword (:256) /\
  bs+off <= w2n k /\ w2n k < bs+off+type_slot_size leaf /\
  (!j byte. dead_bytes (update_storage k u st) (bs+off) leaf j byte <=>
            dead_bytes st (bs+off) leaf j byte) ==>
  !j byte. dead_bytes (update_storage k u st) bs tv j byte <=>
           dead_bytes st bs tv j byte
Proof
  reverse (strip_tac >> Cases_on `tv` >> gvs[])
  >- (rename1 `ArrayTV et bd` >> Cases_on `sb` >>
      gvs[vyperStoragePlaceRegionTheory.storage_subregion_def] >>
      rename1 `ValueSubscript key` >> Cases_on `key` >>
      Cases_on `bd` >> gvs[vyperStoragePlaceRegionTheory.storage_subregion_def]
      >- (irule aug_place_dead_bytes_array_fixed_update >>
          reverse conj_tac >- gvs[vyperValueTheory.type_slot_size_def] >>
          goal_assum (drule_at Any) >> gvs[]) >>
      irule aug_place_dead_bytes_array_dynamic_update >>
      reverse conj_tac >- gvs[vyperValueTheory.type_slot_size_def] >>
      goal_assum (drule_at Any) >> gvs[]) >>
  Cases_on `sb`
  >- (rename1 `ValueSubscript key` >> Cases_on `key` >>
      gvs[vyperStoragePlaceRegionTheory.storage_subregion_def]) >>
  gvs[vyperStoragePlaceRegionTheory.storage_subregion_def] >>
  simp[dead_bytes_def] >> irule aug_place_dead_bytes_field_update >>
  conj_tac >- gvs[vyperValueTheory.type_slot_size_def] >>
  qexistsl_tac [`leaf`, `s`, `off`] >> gvs[]
QED

Theorem aug_place_storage_extend_mask:
  extend_storage_place cx tr slot tv sb es =
    (INL (StoragePlace tr child leaf),es') /\
  ((?fs. tv = StructTV fs) \/ (?et bd. tv = ArrayTV et bd)) /\
  w2n slot + type_slot_size tv <= dimword (:256) /\
  w2n child <= w2n k /\ w2n k < w2n child+type_slot_size leaf /\
  (!j byte. dead_bytes (update_storage k u st) (w2n child) leaf j byte <=>
            dead_bytes st (w2n child) leaf j byte) ==>
  !j byte. dead_bytes (update_storage k u st) (w2n slot) tv j byte <=>
           dead_bytes st (w2n slot) tv j byte
Proof
  strip_tac >>
  drule vyperStoragePlaceProvenanceTheory.extend_storage_place_subregion >>
  strip_tac >> gvs[] >>
  drule vyperStoragePlaceRegionTheory.storage_subregion_bounds >> strip_tac >>
  `0 < type_slot_size leaf` by decide_tac >>
  `w2n slot + delta < dimword (:256)` by decide_tac >>
  `w2n (slot + n2w delta) = w2n slot + delta` by
    (simp[wordsTheory.word_add_def, wordsTheory.w2n_n2w,
          arithmeticTheory.LESS_MOD]) >>
  irule aug_place_subregion_mask >>
  (conj_tac >- decide_tac) >> (conj_tac >- simp[]) >>
  qexistsl_tac [`leaf`, `delta`, `sb`] >> gvs[]
QED

Theorem aug_place_dead_bytes_tuple_update:
  !types i leaf bs k u st.
    oEL i types = SOME leaf /\
    bs + type_slot_size (TupleTV types) <= dimword (:256) /\
    bs + tuple_prefix_slot_size i types <= w2n k /\
    w2n k < bs + tuple_prefix_slot_size i types + type_slot_size leaf /\
    (!j byte. dead_bytes (update_storage k u st)
                (bs + tuple_prefix_slot_size i types) leaf j byte <=>
              dead_bytes st (bs + tuple_prefix_slot_size i types) leaf j byte) ==>
    !j byte. dead_bytes (update_storage k u st) bs (TupleTV types) j byte <=>
             dead_bytes st bs (TupleTV types) j byte
Proof
  Induct_on `types` >- simp[listTheory.oEL_def] >>
  rpt gen_tac >> Cases_on `i` >>
  simp[listTheory.oEL_def, tuple_prefix_slot_size_def,
       vyperValueTheory.type_slot_size_def] >> strip_tac >> gvs[] >>
  simp[dead_bytes_def] >> rpt gen_tac
  >- (AP_TERM_TAC >> irule (cj 2 accountsRelPropsTheory.dead_bytes_frame) >>
      rpt strip_tac >> irule aug_place_update_lookup_other >> decide_tac) >>
  `dead_bytes (update_storage k u st) bs h j byte <=>
   dead_bytes st bs h j byte` by
    (irule (cj 1 accountsRelPropsTheory.dead_bytes_frame) >> rpt strip_tac >>
     irule aug_place_update_lookup_other >> decide_tac) >>
  simp[] >> AP_TERM_TAC >>
  first_x_assum (irule o SRULE [dead_bytes_def, vyperValueTheory.type_slot_size_def]) >>
  conj_tac >- decide_tac >> qexistsl_tac [`n`, `leaf`] >> gvs[]
QED

Theorem aug_place_subregion_path_mask:
  !tv path off leaf. storage_subregion tv path off leaf ==>
  !bs k u st.
    bs + type_slot_size tv <= dimword (:256) /\
    bs+off <= w2n k /\ w2n k < bs+off+type_slot_size leaf /\
    (!j byte. dead_bytes (update_storage k u st) (bs+off) leaf j byte <=>
              dead_bytes st (bs+off) leaf j byte) ==>
    !j byte. dead_bytes (update_storage k u st) bs tv j byte <=>
             dead_bytes st bs tv j byte
Proof
  ho_match_mp_tac vyperStoragePlaceRegionTheory.storage_subregion_ind >>
  rpt conj_tac >> rpt gen_tac >> rpt strip_tac >>
  qpat_x_assum `storage_subregion _ _ _ _` mp_tac >>
  simp_tac (srw_ss()) [Once vyperStoragePlaceRegionTheory.storage_subregion_def] >>
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >>
  full_simp_tac bool_ss [arithmeticTheory.ADD_CLAUSES] >>
  drule vyperStoragePlaceRegionTheory.storage_subregion_bounds >> strip_tac
  >- (`Num i * type_slot_size tv + type_slot_size tv <= n * type_slot_size tv` by
        (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
      `!j byte. dead_bytes (update_storage k u st)
          (bs + Num i * type_slot_size tv) tv j byte <=>
          dead_bytes st (bs + Num i * type_slot_size tv) tv j byte` by
        (first_x_assum irule >> conj_tac
         >- gvs[vyperValueTheory.type_slot_size_def] >>
         qexists_tac `rest` >> gvs[]) >>
      irule aug_place_dead_bytes_array_fixed_update >>
      reverse conj_tac >- gvs[vyperValueTheory.type_slot_size_def] >>
      qexists_tac `Num i` >> gvs[])
  >- (`Num i * type_slot_size tv + type_slot_size tv <= n * type_slot_size tv` by
        (irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
      `!j byte. dead_bytes (update_storage k u st)
          (bs + 1 + Num i * type_slot_size tv) tv j byte <=>
          dead_bytes st (bs + 1 + Num i * type_slot_size tv) tv j byte` by
        (first_x_assum irule >> conj_tac
         >- gvs[vyperValueTheory.type_slot_size_def] >>
         qexists_tac `rest` >> gvs[]) >>
      irule aug_place_dead_bytes_array_dynamic_update >>
      reverse conj_tac >- gvs[vyperValueTheory.type_slot_size_def] >>
      qexists_tac `Num i` >> gvs[])
  >- (drule vyperStoragePlaceRegionTheory.struct_field_slot_end_bound >> strip_tac >>
      `!j byte. dead_bytes (update_storage k u st) (bs+delta) elem j byte <=>
                dead_bytes st (bs+delta) elem j byte` by
        (first_x_assum irule >> conj_tac >- decide_tac >>
         qexists_tac `rest` >> gvs[]) >>
      simp[dead_bytes_def] >> irule aug_place_dead_bytes_field_update >>
      conj_tac >- gvs[vyperValueTheory.type_slot_size_def] >>
      qexistsl_tac [`elem`, `id`, `delta`] >> gvs[]) >>
  drule vyperStoragePlaceRegionTheory.tuple_component_slot_end_bound >> strip_tac >>
  `!j byte. dead_bytes (update_storage k u st)
       (bs + tuple_prefix_slot_size (Num i) types) elem j byte <=>
       dead_bytes st (bs + tuple_prefix_slot_size (Num i) types) elem j byte` by
    (first_x_assum irule >> conj_tac >- decide_tac >>
     qexists_tac `rest` >> gvs[]) >>
  irule aug_place_dead_bytes_tuple_update >>
  conj_tac >- simp[] >> qexistsl_tac [`Num i`, `elem`] >> gvs[]
QED

Theorem aug_place_region_storage_dead_stable:
  storage_place_observed H (StoragePlace tr slot leaf) /\
  type_slot_size leaf = 1 ==>
  !u st. storage_dead H tr (update_storage slot u st) = storage_dead H tr st
Proof
  simp_tac (srw_ss()) [vyperStoragePlaceObservedTheory.storage_place_observed_def] >>
  strip_tac >> rpt gen_tac >>
  irule accountsRelPropsTheory.storage_dead_update_in_region >>
  qexistsl_tac [`root`, `tv`] >> simp[] >>
  strip_tac >>
  drule vyperStoragePlaceRegionTheory.storage_subregion_bounds >> strip_tac >>
  `w2n root + delta < dimword (:256)` by decide_tac >>
  `w2n slot = w2n root + delta` by
    gvs[wordsTheory.word_add_def, wordsTheory.w2n_n2w,
        arithmeticTheory.LESS_MOD] >>
  qpat_x_assum `slot = _` (SUBST_ALL_TAC o SYM) >>
  conj_tac >- decide_tac >> conj_tac >- decide_tac >>
  irule aug_place_subregion_path_mask >> conj_tac >- simp[] >>
  qexistsl_tac [`leaf`, `delta`, `path`] >> simp[] >>
  rpt strip_tac >> eq_tac >> strip_tac >>
  drule (cj 1 accountsRelPropsTheory.dead_bytes_range) >> simp[]
QED

(* A storage place reached by a traced root is observed by every horizon
   that is valid for the trace. *)
Theorem aug_place_storage_rooted_observed:
  valid_horizon cx st0 H trace /\ MEM (StorageRoot tr offset tv0) trace /\
  storage_subregion tv0 path delta tv /\ slot = n2w offset + n2w delta ==>
  storage_place_observed H (StoragePlace tr slot tv)
Proof
  strip_tac >>
  `storage_observations_ok cx H trace` by
    fs[vyperStorageFootprintTheory.valid_horizon_def] >>
  `MEM (tr,n2w offset,tv0) (FST H)` by
    metis_tac[vyperFiniteStoragePreservationTheory.storage_observations_ok_root] >>
  simp[vyperStoragePlaceObservedTheory.storage_place_observed_def] >>
  qexistsl_tac [`n2w offset`, `tv0`, `path`, `delta`] >> simp[]
QED

(* The place a successful target evaluation returns is observed by every
   horizon valid after it. *)
Theorem aug_place_target_observed:
  eval_target_place cx t es = (INL (StoragePlace tr slot leaf),es') /\
  valid_horizon cx st0 H es'.storage_trace ==>
  storage_place_observed H (StoragePlace tr slot leaf)
Proof
  strip_tac >>
  drule vyperFiniteStoragePreservationTheory.eval_target_place_observed_region >>
  strip_tac >> metis_tac[aug_place_storage_rooted_observed]
QED

Theorem aug_place_target_storage_dead_stable:
  eval_target_place cx t es = (INL (StoragePlace tr slot leaf),es') /\
  valid_horizon cx st0 H es'.storage_trace /\ type_slot_size leaf = 1 ==>
  !u st. storage_dead H tr (update_storage slot u st) = storage_dead H tr st
Proof
  strip_tac >> irule aug_place_region_storage_dead_stable >>
  simp[] >> metis_tac[aug_place_target_observed]
QED

(* An observed place of a well-formed backend has its slots in range. *)
Theorem aug_place_observed_slots_in_range:
  storage_place_observed H (StoragePlace tr slot leaf) /\
  regions_consistent (FST H) /\ storage_well_formed_on cx st (FST H) /\
  0 < type_slot_size leaf ==>
  slots_in_range (get_storage cx st tr) (w2n slot) leaf
Proof
  rw[vyperStoragePlaceObservedTheory.storage_place_observed_def] >>
  `slots_in_range (get_storage cx st tr) (w2n root) tv` by
    metis_tac[vyperStorageFootprintTheory.storage_well_formed_on_def] >>
  `w2n root + type_slot_size tv <= dimword (:256)` by
    metis_tac[vyperStorageFootprintTheory.regions_consistent_def] >>
  drule vyperStoragePlaceRegionTheory.storage_subregion_bounds >> strip_tac >>
  `delta < dimword (:256) /\ w2n root + delta < dimword (:256)` by
    decide_tac >>
  `w2n (root + n2w delta) = w2n root + delta` by
    simp[wordsTheory.word_add_def, wordsTheory.w2n_n2w] >>
  pop_assum SUBST1_TAC >>
  irule vyperStorageRegionWriteTheory.storage_subregion_slots_in_range >>
  metis_tac[]
QED

Theorem aug_place_storage_read_holds:
  evaluate_type (get_tenv cx) ty = SOME tv /\
  read_storage_slot cx tr slot tv st = (INL cur,st) /\
  slots_in_range (get_storage cx st tr) (w2n slot) tv /\
  storage_range_agree (get_storage cx st tr)
    (if tr then contract_transient s0 else contract_storage s0) slot tv ==>
  storage_holds cx tr ty (Value cur) slot st s0
Proof
  strip_tac >> simp[storage_holds_def, read_result_def, return_def] >>
  qexists_tac `tv` >> simp[]
QED

Theorem aug_place_precompile_storage:
  precompile_call_success bt s = (r,s') ==>
  get_storage cx s' tr = get_storage cx s tr
Proof
  simp[precompile_call_success_def] >>
  Cases_on `precompile_builtin bt` >>
  gvs[return_def, check_def, assert_def, raise_def, AllCaseEqs()] >>
  rpt strip_tac >> Cases_on `tr` >> gvs[vyperStorageBackendTheory.get_storage_def]
QED

Theorem aug_place_singleton_storage:
  (!r s'. eval_exprs cx [e] s = (r,s') ==>
     get_storage cx s' tr = get_storage cx s tr) /\
  eval_expr cx e s = (r,s') ==>
  get_storage cx s' tr = get_storage cx s tr
Proof
  strip_tac >>
  `?r'. eval_exprs cx [e] s = (r',s')` by
    (Cases_on `r`
     >- (rename1 `eval_expr cx e s = (INL tv,s')` >>
         simp[evaluate_def, bind_def, return_def] >>
         Cases_on `read_result cx tv s'` >>
         drule read_result_state >> strip_tac >> gvs[] >>
         rename1 `read_result cx tv s' = (rr,s')` >>
         Cases_on `rr` >> simp[])
     >> simp[evaluate_def, bind_def]) >>
  metis_tac[]
QED

Theorem aug_place_pure_storage_mutual:
  (!tops e. supported_pure_expr tops e ==>
    !cx s r s' tr. eval_expr cx e s = (r,s') ==>
      get_storage cx s' tr = get_storage cx s tr) /\
  (!tops es. supported_pure_exprs tops es ==>
    !cx s r s' tr. eval_exprs cx es s = (r,s') ==>
      get_storage cx s' tr = get_storage cx s tr) /\
  (!tops fs. supported_pure_fields tops fs ==>
    !cx s r s' tr. eval_exprs cx (MAP SND fs) s = (r,s') ==>
      get_storage cx s' tr = get_storage cx s tr) /\
  (!tops e. supported_place_expr tops e ==>
    !cx s r s' tr. eval_expr cx e s = (r,s') ==>
      get_storage cx s' tr = get_storage cx s tr)
Proof
  ho_match_mp_tac supported_pure_expr_ind >>
  simp[supported_pure_expr_def] >>
  rpt conj_tac >> rpt gen_tac >> rpt strip_tac
  >~ [`eval_expr cx (Name ty name) s = (r,s')`]
  >- (metis_tac[eval_expr_preserves_state, pure_expr_def])
  >~ [`eval_expr cx (Literal ty lit) s = (r,s')`]
  >- (gvs[evaluate_def, return_def])
  >~ [`eval_expr cx (TopLevelName ty id) s = (r,s')`]
  >- (metis_tac[eval_expr_preserves_state, pure_expr_def])
  >~ [`eval_expr cx (IfExp ty e e' e'') s = (r,s')`]
  >- (gvs[evaluate_def, bind_def, switch_BoolV_def, AllCaseEqs()] >>
     imp_res_tac read_result_state >> imp_res_tac vyperStatePreservationTheory.conditional_result_state >>
     gvs[return_def, raise_def] >>
     rpt (CHANGED_TAC (gvs[AllCaseEqs(), COND_RATOR, raise_def])) >>
     qpat_x_assum `!cx s r s' tr. eval_expr cx e s = (r,s') ==> _`
       (drule_then assume_tac) >>
     first_x_assum (drule_then assume_tac) >> simp[])
  >~ [`eval_expr cx (TopLevelName ty id) s = (r,s')`]
  >- (metis_tac[eval_expr_preserves_state, pure_expr_def])
  >~ [`eval_expr cx (StructLit ty id fs) s = (r,s')`]
  >- (PairCases_on `id` >> gvs[evaluate_def, bind_def, return_def, AllCaseEqs()] >>
      metis_tac[])
  >~ [`eval_expr cx (Subscript ty e e') s = (r,s')`]
  >- (gvs[evaluate_def, bind_def, AllCaseEqs()] >>
      imp_res_tac read_result_state >>
      imp_res_tac vyperPlaceFramesTheory.select_result_state >> gvs[] >>
      qpat_x_assum `!cx s r s' tr. eval_expr cx e s = (r,s') ==> _`
        (drule_then assume_tac) >>
      first_x_assum (drule_then assume_tac) >> simp[])
  >~ [`eval_expr cx (Attribute ty e fld) s = (r,s')`]
  >- (gvs[evaluate_def, bind_def, AllCaseEqs()] >>
      imp_res_tac vyperPlaceFramesTheory.select_result_state >> gvs[] >>
      first_x_assum (drule_then assume_tac) >> simp[])
  >~ [`eval_expr cx (Builtin ty blt es) s = (r,s')`]
  >- (Cases_on `blt = Len`
      >- (gvs[] >> Cases_on `es` >>
          gvs[supportedExprFormsTheory.supported_builtin_form_def] >>
          rename1 `supported_pure_exprs tops (h::t)` >> Cases_on `t` >>
          gvs[supportedExprFormsTheory.supported_builtin_form_def] >>
          `!cx s r s' tr. eval_expr cx h s = (r,s') ==>
             get_storage cx s' tr = get_storage cx s tr` by
            (rpt strip_tac >> irule aug_place_singleton_storage >>
             goal_assum (drule_at Any) >> metis_tac[]) >>
          gvs[evaluate_def, bind_def, ignore_bind_def, type_check_def,
              assert_def, return_def, raise_def, AllCaseEqs()] >>
          imp_res_tac vyperStatePreservationTheory.result_array_length_state >>
          gvs[] >> first_x_assum (drule_then assume_tac) >> simp[])
      >> Cases_on `blt = Env MsgGas`
      >- (Cases_on `es` >> gvs[supportedExprFormsTheory.supported_builtin_form_def] >>
          gvs[evaluate_def, bind_def, ignore_bind_def, type_check_def,
              assert_def, return_def, raise_def, AllCaseEqs()] >>
          imp_res_tac vyperStatePreservationTheory.next_gas_reading_state >>
          Cases_on `tr` >> simp[vyperStorageBackendTheory.get_storage_def])
      >> Cases_on `blt = Bop In \/ blt = Bop NotIn`
      >> gvs[evaluate_def, bind_def, ignore_bind_def, type_check_def,
             assert_def, return_def, raise_def, get_accounts_def, lift_sum_def,
             lift_option_type_def, vyperMiscTheory.option_CASE_rator,
             AllCaseEqs()] >>
      gvs[vyperMiscTheory.sum_CASE_rator, AllCaseEqs(), return_def, raise_def] >>
      imp_res_tac aug_place_precompile_storage >>
      gvs[return_def, raise_def] >>
      metis_tac[])
  >~ [`eval_expr cx (TypeBuiltin ty blt target es) s = (r,s')`]
  >- (gvs[evaluate_def, bind_def, ignore_bind_def, type_check_def,
          assert_def, return_def, raise_def, lift_sum_def, AllCaseEqs()] >>
      gvs[vyperMiscTheory.sum_CASE_rator, AllCaseEqs(), return_def, raise_def, ETA_THM] >>
      first_x_assum (drule_then assume_tac) >> simp[])
  >~ [`eval_exprs cx (e::es) s = (r,s')`]
  >- (gvs[evaluate_def, bind_def, AllCaseEqs(), return_def] >>
      imp_res_tac read_result_state >> gvs[] >>
      qpat_x_assum `!cx s r s' tr. eval_expr cx e s = (r,s') ==> _`
        (drule_then assume_tac) >>
      first_x_assum (drule_then assume_tac) >> simp[])
  >~ [`eval_exprs cx (e::es) s = (r,s')`]
  >- (gvs[evaluate_def, bind_def, AllCaseEqs(), return_def] >>
      imp_res_tac read_result_state >> gvs[] >>
      qpat_x_assum `!cx s r s' tr. eval_expr cx e s = (r,s') ==> _`
        (drule_then assume_tac) >>
      first_x_assum (drule_then assume_tac) >> simp[])
  >~ [`eval_expr cx (Name ty name) s = (r,s')`]
  >- (metis_tac[eval_expr_preserves_state, pure_expr_def])
  >~ [`eval_expr cx (TopLevelName ty id) s = (r,s')`]
  >- (metis_tac[eval_expr_preserves_state, pure_expr_def])
  >~ [`eval_expr cx (Subscript ty e e') s = (r,s')`]
  >- (gvs[evaluate_def, bind_def, AllCaseEqs()] >>
      imp_res_tac read_result_state >>
      imp_res_tac vyperPlaceFramesTheory.select_result_state >> gvs[] >>
      qpat_x_assum `!cx s r s' tr. eval_expr cx e s = (r,s') ==> _`
        (drule_then assume_tac) >>
      first_x_assum (drule_then assume_tac) >> simp[])
  >~ [`eval_expr cx (Attribute ty e fld) s = (r,s')`]
  >- (gvs[evaluate_def, bind_def, AllCaseEqs()] >>
      imp_res_tac vyperPlaceFramesTheory.select_result_state >> gvs[] >>
      first_x_assum (drule_then assume_tac) >> simp[])
  >> gvs[evaluate_def, return_def]
QED

Theorem aug_place_pure_eval_storage:
  supported_pure_expr tops e /\ eval_expr cx e s = (r,s') ==>
  get_storage cx s' tr = get_storage cx s tr
Proof
  metis_tac[aug_place_pure_storage_mutual]
QED

Theorem aug_place_resolve_array_empty:
  resolve_array_element cx tr slot tv [] st = (INL (slot,tv,[]),st)
Proof
  Cases_on `tv` >> simp[resolve_array_element_def, return_def]
QED

Theorem aug_place_pure_base_storage:
  !t tops cx s r s' tr.
    EVERY (supported_pure_expr tops) (target_indices t) /\
    eval_base_place cx t s = (r,s') ==>
    get_storage cx s' tr = get_storage cx s tr
Proof
  measureInduct_on `base_assignment_target_size t` >> Cases_on `t` >>
  rpt gen_tac
  >~ [`TopLevelNameTarget p`]
  >- (PairCases_on `p` >> simp[target_indices_def, Once evaluate_def] >>
      rpt strip_tac >> metis_tac[vyperStatePreservationTheory.lookup_global_state]) >>
  simp[target_indices_def, Once evaluate_def] >>
  rpt strip_tac
  >- (gvs[bind_def, get_scopes_def, type_check_def, assert_def,
          ignore_bind_def, return_def, raise_def, AllCaseEqs()]) >>
  gvs[bind_def, AllCaseEqs()] >>
  qpat_x_assum `!y. _` (qspec_then `b` mp_tac) >>
  simp[expr_size_def] >> strip_tac >>
  metis_tac[aug_place_pure_eval_storage, read_result_state,
            vyperPlaceFramesTheory.extend_place_state, raise_def]
QED

Theorem aug_place_storage_load_ready:
  target_post H ctx func cenv cx es sa sb s0 st
    (PlaceR (StoragePlace tr slot tv)) (Type ty) r vs /\
  read_place cx (StoragePlace tr slot tv) st = (INL cur,stc) /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  slots_in_range (get_storage cx st tr) (w2n slot) tv /\
  storage_read_live H tr (get_storage cx st tr) slot tv ==>
  (if tr then tload slot vs else sload slot vs) = typed_val_to_w256 tv cur
Proof
  strip_tac >> drule read_place_state >> strip_tac >> gvs[] >>
  `read_storage_slot cx tr slot tv st = (INL cur,st)` by
    gvs[read_place_def] >>
  `storage_agree (storage_dead H tr (get_storage cx st tr))
     (get_storage cx st tr)
     (if tr then contract_transient vs else contract_storage vs)` by
    (Cases_on `tr` >>
     gvs[target_post_def, stmt_state_rel_def, state_rel_def,
         storage_rel_def, transient_rel_def, vfmStateTheory.lookup_account_def,
         vyperStorageBackendTheory.get_storage_def]) >>
  `w2n slot + type_slot_size tv <= dimword (:256)` by
    (drule_all exprSimUnwrapTheory.word_type_slot_size >> strip_tac >>
     qspec_then `slot` mp_tac wordsTheory.w2n_lt >> simp[]) >>
  `storage_range_agree (get_storage cx st tr)
     (if tr then contract_transient vs else contract_storage vs) slot tv` by
    (irule accountsRelPropsTheory.storage_range_agree_of_live >>
     simp[] >> qexistsl_tac [`H`, `tr`] >> simp[]) >>
  `storage_holds cx tr ty (Value cur) slot st vs` by
    (irule aug_place_storage_read_holds >> simp[]) >>
  irule exprSimUnwrapTheory.storage_holds_load >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem aug_place_tuple_range_selected:
  !tvs off i tv storage.
    tuple_slots_in_range storage off tvs /\ oEL i tvs = SOME tv ==>
    slots_in_range storage (off + tuple_prefix_slot_size i tvs) tv
Proof
  Induct >> simp[listTheory.oEL_def] >>
  rpt gen_tac >> Cases_on `i` >>
  simp[listTheory.oEL_def, tuple_prefix_slot_size_def,
       Once vyperLookupStorageTheory.slots_in_range_def] >>
  rpt strip_tac >> gvs[] >> first_x_assum drule_all >>
  pure_rewrite_tac[arithmeticTheory.ADD_ASSOC] >> simp[]
QED

Theorem aug_place_range_word_offset:
  slots_in_range storage (w2n (w:bytes32) + off) tv ==>
  slots_in_range storage (w2n (w + n2w off)) tv
Proof
  strip_tac >>
  `slots_in_range storage (w2n w + off) tv =
   slots_in_range storage (w2n (w + n2w off)) tv` by
    (irule (cj 1 vyperLookupStorageTheory.slots_in_range_offset_cong) >>
     `w + n2w off = n2w (w2n w + off)` by
       simp[GSYM wordsTheory.word_add_n2w] >>
     asm_rewrite_tac[wordsTheory.n2w_w2n]) >>
  gvs[]
QED

Theorem aug_place_storage_extend_range:
  slots_in_range (get_storage cx st tr) (w2n slot) tv /\
  extend_storage_place cx tr slot tv sb st =
    (INL (StoragePlace tr' child leaf),st') ==>
  slots_in_range (get_storage cx st' tr') (w2n child) leaf
Proof
  strip_tac >> Cases_on `sb` >> Cases_on `tv` >>
  gvs[extend_storage_place_def, raise_def]
  >~ [`struct_field_slot fs s`]
  >- (gvs[bind_def, ignore_bind_def, check_def, assert_def, lift_option_type_def,
          return_def, raise_def, AllCaseEqs()] >>
      Cases_on `struct_field_slot fs s` >>
      gvs[raise_def, return_def] >> PairCases_on `x` >>
      gvs[return_def] >>
      irule vyperLookupStorageTheory.storage_field_slots_in_range >>
      goal_assum (drule_at Any) >> simp[])
  >~ [`TupleTV tvs`, `ValueSubscript key`]
  >- (Cases_on `key` >> gvs[extend_storage_place_def, raise_def] >>
      gvs[bind_def, ignore_bind_def, check_def, assert_def, lift_option_type_def,
          return_def, raise_def, AllCaseEqs()] >>
      Cases_on `oEL (Num i) tvs` >> gvs[return_def, raise_def] >>
      irule aug_place_range_word_offset >>
      irule aug_place_tuple_range_selected >>
      gvs[Once vyperLookupStorageTheory.slots_in_range_def] >>
      goal_assum (drule_at Any) >> simp[]) >>
  rename1 `ValueSubscript key` >> Cases_on `key` >>
  gvs[extend_storage_place_def, raise_def] >>
  gvs[bind_def, ignore_bind_def, check_def, assert_def, lift_option_type_def,
      return_def, raise_def, AllCaseEqs()] >>
  Cases_on `b` >>
  gvs[resolve_array_element_def, bind_def, ignore_bind_def, check_def,
      assert_def, return_def, raise_def, AllCaseEqs(),
      vyperStorageBackendTheory.get_storage_backend_eq] >>
  gvs[aug_place_resolve_array_empty, return_def]
  >- (irule aug_place_range_word_offset >>
      gvs[Once vyperLookupStorageTheory.slots_in_range_def,
          cj 1 vyperLookupStorageTheory.array_slots_in_range_indexed]) >>
  irule aug_place_range_word_offset >>
  gvs[Once vyperLookupStorageTheory.slots_in_range_def,
      cj 2 vyperLookupStorageTheory.array_slots_in_range_indexed] >>
  first_x_assum irule >> simp[vyperStorageTheory.read_slot_def]
QED

Theorem aug_place_contract_storage_frame:
  contract_storage_well_formed cx s /\
  (!tr. get_storage cx s' tr = get_storage cx s tr) ==>
  contract_storage_well_formed cx s'
Proof
  simp[vyperStorageLayoutSafetyTheory.contract_storage_well_formed_def,
       vyperLookupStorageTheory.well_formed_storage_def,
       vyperLookupStorageTheory.storage_var_in_range_def,
       vyperStorageBackendTheory.get_storage_backend_eq] >>
  metis_tac[]
QED

Theorem aug_place_mapping_extend_range:
  contract_storage_well_formed cx s /\
  vyperStoragePlaceProvenance$storage_mapping_region cx tr slot (HashMapT kt vt) /\
  extend_place cx (HashMapRef tr slot kt vt) sb s =
    (INL (PlaceR (StoragePlace tr' child leaf)),s') ==>
  slots_in_range (get_storage cx s' tr') (w2n child) leaf
Proof
  Cases_on `sb` >> Cases_on `vt` >>
  simp[extend_place_def, raise_def, bind_def, lift_option_type_def,
       vyperMiscTheory.option_CASE_rator, return_def, AllCaseEqs()] >>
  rpt strip_tac >> gvs[] >>
  drule vyperStoragePlaceProvenanceTheory.storage_mapping_region_step >>
  disch_then (qspec_then `v` mp_tac) >>
  simp_tac (srw_ss()) [vyperStoragePlaceProvenanceTheory.storage_mapping_region_def] >>
  strip_tac >>
  qpat_x_assum `!subs leaf_slot leaf_tv. _`
    (qspecl_then [`[]`, `hashmap_slot slot (encode_hashmap_key kt v)`, `leaf`] mp_tac) >>
  simp[vyperStorageLayoutSafetyTheory.resolve_hashmap_leaf_def] >>
  strip_tac >>
  irule vyperStorageLayoutSafetyTheory.contract_storage_well_formed_region >>
      goal_assum (drule_at Any) >>
  simp[vyperStorageBackendTheory.get_storage_backend_eq] >>
  qexists_tac `s` >> simp[]
QED

Theorem aug_place_pure_base_storage_range:
  !t tops cx s tr slot tv s'.
    contract_storage_well_formed cx s /\
    EVERY (supported_pure_expr tops) (target_indices t) /\
    eval_base_place cx t s = (INL (PlaceR (StoragePlace tr slot tv)),s') ==>
    slots_in_range (get_storage cx s' tr) (w2n slot) tv
Proof
  measureInduct_on `base_assignment_target_size t` >> Cases_on `t` >>
  rpt gen_tac
  >~ [`TopLevelNameTarget p`]
  >- (PairCases_on `p` >>
      simp[target_indices_def, Once evaluate_def, bind_def, AllCaseEqs(),
           return_def, raise_def] >> rpt strip_tac >> gvs[] >>
      drule vyperStoragePlaceProvenanceTheory.lookup_global_storage_region >>
      strip_tac >>
      drule vyperStatePreservationTheory.lookup_global_state >> strip_tac >> gvs[] >>
      irule vyperStorageLayoutSafetyTheory.contract_storage_well_formed_region >>
      goal_assum (drule_at Any) >>
      simp[vyperStorageBackendTheory.get_storage_backend_eq] >>
      qexists_tac `s` >> simp[]) >>
  simp[target_indices_def, Once evaluate_def, bind_def, AllCaseEqs(),
       get_scopes_def, type_check_def, assert_def, ignore_bind_def,
       return_def, raise_def] >> rpt strip_tac >> gvs[] >>
  qpat_x_assum `!y. _` (qspec_then `b` mp_tac) >>
  simp[expr_size_def] >> strip_tac
  >- (rename1 `eval_expr cx e s'' = (INL result,s3)` >>
      `!tr. get_storage cx s3 tr = get_storage cx s'' tr` by
        metis_tac[aug_place_pure_eval_storage] >>
      drule read_result_state >> strip_tac >> gvs[] >>
      rename1 `extend_place cx pv sb sx = _` >>
      `contract_storage_well_formed cx sx` by
        (irule aug_place_contract_storage_frame >> qexists_tac `s` >>
         simp[] >> drule_all aug_place_pure_base_storage >> simp[]) >>
      drule vyperStoragePlaceProvenanceTheory.eval_base_place_region >> strip_tac >>
      Cases_on `pv`
      >- (qpat_x_assum `extend_place _ _ _ _ = _` mp_tac >>
          simp[extend_place_def, raise_def])
      >- (Cases_on `p` >>
          gvs[extend_place_def, bind_def, ignore_bind_def, return_def,
              extend_memory_place_def, AllCaseEqs()] >>
          first_x_assum drule_all >> strip_tac >>
          drule_at (Pat `extend_storage_place _ _ _ _ _ _ = _`)
            aug_place_storage_extend_range >> simp[]) >>
      gvs[vyperStoragePlaceProvenanceTheory.storage_result_region_def] >>
      drule_at (Pat `extend_place _ _ _ _ = _`) aug_place_mapping_extend_range >>
      simp[]) >>
  rename1 `extend_place cx pv sb sx = _` >>
  `contract_storage_well_formed cx sx` by
    (irule aug_place_contract_storage_frame >> goal_assum (drule_at Any) >>
     drule_all aug_place_pure_base_storage >> simp[]) >>
  drule vyperStoragePlaceProvenanceTheory.eval_base_place_region >> strip_tac >>
  Cases_on `pv`
  >- (qpat_x_assum `extend_place _ _ _ _ = _` mp_tac >>
      simp[extend_place_def, raise_def])
  >- (Cases_on `p` >>
      gvs[extend_place_def, bind_def, ignore_bind_def, return_def,
          extend_memory_place_def, AllCaseEqs()] >>
      first_x_assum drule_all >> strip_tac >>
      drule_at (Pat `extend_storage_place _ _ _ _ _ _ = _`)
        aug_place_storage_extend_range >> simp[]) >>
  gvs[vyperStoragePlaceProvenanceTheory.storage_result_region_def] >>
  drule_at (Pat `extend_place _ _ _ _ = _`) aug_place_mapping_extend_range >> simp[]
QED

Theorem aug_place_pure_target_storage_range:
  contract_storage_well_formed cx s /\
  EVERY (supported_pure_expr tops) (target_indices t) /\
  eval_target_place cx t s = (INL (StoragePlace tr slot tv),s') ==>
  slots_in_range (get_storage cx s' tr) (w2n slot) tv
Proof
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def] >>
  drule_all aug_place_pure_base_storage_range >> simp[]
QED

Theorem aug_place_base_memory_origin[local]:
  !t cx s id path st.
    eval_base_place cx t s = (INL (PlaceR (MemoryPlace id path)),st) ==>
    target_root t = NameTarget id
Proof
  `(!e:expr. T) /\ (!t. !cx s id path st.
    eval_base_place cx t s = (INL (PlaceR (MemoryPlace id path)),st) ==>
    target_root t = NameTarget id)` suffices_by simp[] >>
  ho_match_mp_tac (TypeBase.induction_of ``:base_assignment_target``) >>
  simp[] >> rpt conj_tac >> rpt gen_tac
  >- simp[Once evaluate_def, bind_def, get_scopes_def, ignore_bind_def,
          type_check_def, assert_def, return_def, raise_def, AllCaseEqs(),
          target_root_def]
  >- (PairCases_on `p` >> simp[Once evaluate_def] >>
      metis_tac[aug_place_lookup_global_not_memory]) >>
  rpt strip_tac >>
  qpat_x_assum `eval_base_place _ _ _ = _` mp_tac >>
  simp[Once evaluate_def, bind_def, return_def, raise_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  drule aug_place_extend_memory_inversion >> strip_tac >> gvs[] >>
  simp[target_root_def] >> metis_tac[]
QED

Theorem aug_place_target_memory_origin[local]:
  eval_target_place cx t s = (INL (MemoryPlace id path),st) ==>
  target_root t = NameTarget id
Proof
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def] >>
  metis_tac[aug_place_base_memory_origin]
QED

Theorem aug_place_supported_storage_kind:
  body_inv tops ctx cenv cx /\
  supported_target_info tops bindings t = SOME pt /\
  (!id. target_root t <> NameTarget id) /\
  eval_target_place cx t es = (INL p,st) ==>
  ?tr slot tv. p = StoragePlace tr slot tv
Proof
  strip_tac >> drule_all aug_place_supported_success_kind >>
  metis_tac[aug_place_target_memory_origin]
QED

Theorem aug_place_storage_read_ready:
  evaluate_type (get_tenv cx) ty = SOME tv /\
  slots_in_range (get_storage cx st tr) (w2n slot) tv ==>
  ?cur. read_place cx (StoragePlace tr slot tv) st = (INL cur,st) /\
        place_type_value cx (StoragePlace tr slot tv) st = (INL tv,st) /\
        value_has_type tv cur
Proof
  strip_tac >>
  `well_formed_type_value tv` by
    metis_tac[cj 1 vyperTypingTheory.evaluate_type_well_formed] >>
  drule_all vyperLookupStorageTheory.decode_value_from_slots_in_range >>
  strip_tac >> qexists_tac `v` >>
  simp[read_place_def, vyperStorageBackendTheory.read_storage_slot_eq,
       place_type_value_def, return_def]
QED

(* The target's place, in range and live in the storage after the target's
   evaluation, whatever its indices did: the evaluation records the root of
   the place's region, so every horizon valid after it observes the place
   (aug_place_target_observed); the backend is well formed on an observed
   region, and an observed word place is live. *)
Theorem aug_place_target_storage_ready:
  !cx st0 H st ty tv bt s tr slot.
    valid_horizon cx st0 H st.storage_trace /\
    storage_well_formed_on cx st (FST H) /\
    is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
    eval_target_place cx bt s = (INL (StoragePlace tr slot tv),st) ==>
    slots_in_range (get_storage cx st tr) (w2n slot) tv /\
    storage_read_live H tr (get_storage cx st tr) slot tv
Proof
  rpt gen_tac >> strip_tac >>
  `0 < type_slot_size tv` by
    (drule_all exprSimUnwrapTheory.word_type_slot_size >> simp[]) >>
  drule_all aug_place_target_observed >> strip_tac >>
  `regions_consistent (FST H)` by
    fs[vyperStorageFootprintTheory.valid_horizon_def] >>
  conj_tac
  >- metis_tac[aug_place_observed_slots_in_range] >>
  irule accountsRelPropsTheory.storage_place_observed_read_live >> simp[]
QED

Theorem aug_place_storage_load_path[local]:
  emit_op (if tr then TLOAD else SLOAD) [arg] sa = (op,sb) /\
  fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand arg s = SOME slot ==>
  gas_path ctx func s 0
    (OK ((update_var (STRING #"%" (toString sa.cs_next_var))
      (if tr then tload slot s else sload slot s) s)
      with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> irule emitHelperPropsTheory.emit_op_zero_path >> simp[] >>
  qexistsl_tac [`[arg]`, `op`, `if tr then TLOAD else SLOAD`, `sb`] >>
  Cases_on `tr` >> full_simp_tac bool_ss [] >>
  (conj_tac
   >- (gen_tac >>
       rw[venomExecSemanticsTheory.step_inst_base_def,
          venomExecSemanticsTheory.exec_read1_def, venomInstTheory.mk_inst_def]) >>
   asm_simp_tac (srw_ss()) [venomInstTheory.is_terminator_def])
QED

Theorem aug_place_storage_load_endpoint[local]:
  emit_op (if tr then TLOAD else SLOAD) [arg] sa = (op,sb) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  let u = (update_var (STRING #"%" (toString sa.cs_next_var)) w s)
            with vs_inst_idx := SUC s.vs_inst_idx in
    eval_operand op u = SOME w /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    (!x w'. not_fresh_at sa x /\ lookup_var x s = SOME w' ==>
             lookup_var x u = SOME w') /\
    u.vs_allocas = s.vs_allocas
Proof
  simp[emitHelperTheory.emit_op_def, comp_bind_def, fresh_var_def, fresh_id_def,
       comp_ignore_bind_def, comp_return_def, emit_def] >>
  rpt strip_tac >> gvs[venomStateTheory.eval_operand_def, venomStateTheory.update_var_def,
                        venomStateTheory.lookup_var_def,
                        not_fresh_at_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac[arithmeticTheory.LESS_EQ_REFL]
QED

Theorem aug_place_storage_load_state[local]:
  stmt_state_rel H ctx func cenv cx st s /\ local_ptrs_reserved cenv sa ==>
  stmt_state_rel H ctx func cenv cx st
    ((update_var (STRING #"%" (toString sa.cs_next_var)) w s)
       with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >> simp[stmt_state_rel_inst_idx] >>
  irule stmt_state_rel_update_var >> simp[] >>
  irule local_ptrs_reserved_fresh >> qexists_tac `sa` >> simp[]
QED

Theorem aug_place_storage_load_value[local]:
  emit_op (if tr then TLOAD else SLOAD) [arg] sa = (op,sb) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv ==>
  expr_val_rel cx ty cur op
    ((update_var (STRING #"%" (toString sa.cs_next_var))
       (typed_val_to_w256 tv cur) s) with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >> drule_all aug_place_storage_load_endpoint >>
  disch_then (qspec_then `typed_val_to_w256 tv cur` mp_tac) >>
  simp[expr_val_rel_def]
QED

(* The load's endpoint is the same whatever the horizon, so the relation
   carries over for every one. *)
Theorem aug_place_storage_load_counted_nofresh[local]:
  emit_op (if tr then TLOAD else SLOAD) [arg] sa = (op,sb) /\
  fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand arg s = SOME slot /\
  (!x. arg = Var x ==> not_fresh_at sa x) /\
  local_ptrs_reserved cenv sa /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  (if tr then tload slot s else sload slot s) = typed_val_to_w256 tv cur ==>
  ?u. gas_path ctx func s 0 (OK u) /\
      expr_val_rel cx ty cur op u /\
      (!(H:(bool # bytes32 # type_value) list # num list) st.
         stmt_state_rel H ctx func cenv cx st s ==>
         stmt_state_rel H ctx func cenv cx st u) /\
      eval_operand arg u = SOME slot /\
      ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
             lookup_var x u = SOME w) /\
      u.vs_allocas = s.vs_allocas /\ u.vs_memory = s.vs_memory
Proof
  strip_tac >>
  qexists_tac `(update_var (STRING #"%" (toString sa.cs_next_var))
    (typed_val_to_w256 tv cur) s) with vs_inst_idx := SUC s.vs_inst_idx` >>
  conj_tac >- metis_tac[aug_place_storage_load_path] >>
  conj_tac >- metis_tac[aug_place_storage_load_value] >>
  conj_tac
  >- (rpt strip_tac >> irule aug_place_storage_load_state >> simp[]) >>
  drule_all aug_place_storage_load_endpoint >>
  disch_then (qspec_then `typed_val_to_w256 tv cur` mp_tac) >>
  simp[venomStateTheory.update_var_def] >> strip_tac >>
  conj_tac >- (Cases_on `arg` >>
    fs[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def] >>
    qpat_x_assum `!x w'. _` (drule_then drule) >>
    rw[finite_mapTheory.FLOOKUP_UPDATE] >> gvs[]) >>
  simp[] >> metis_tac[]
QED

Theorem aug_place_storage_write_static[local]:
  cx.txn.is_static ==>
  write_place cx (StoragePlace tr slot tv) v ee =
    (INR (Error (RuntimeError "write in static context")),ee)
Proof
  simp[write_place_def, write_storage_slot_def, ignore_bind_def, bind_def]
QED

Theorem aug_place_storage_write_outcome[local]:
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\
  write_place cx (StoragePlace tr slot tv) v ee = (res,ff) ==>
  (cx.txn.is_static /\
   res = INR (Error (RuntimeError "write in static context")) /\ ff = ee) \/
  (~cx.txn.is_static /\ res = INL ())
Proof
  strip_tac >> Cases_on `cx.txn.is_static`
  >- metis_tac[aug_place_storage_write_static, pairTheory.PAIR_EQ] >>
  drule_all tupleTargetStorePropsTheory.tuple_target_storage_write_safe >>
  metis_tac[pairTheory.PAIR_EQ]
QED

Theorem aug_place_storage_suffix_assoc[local]:
  bind (eval_expr cx e) (\raw. bind (read_result cx raw)
    (\v. bind (lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      tv bop cur v)) (write_place cx (StoragePlace tr slot tv)))) =
  bind (bind (eval_expr cx e) (read_result cx))
    (\v. bind (lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      tv bop cur v)) (write_place cx (StoragePlace tr slot tv)))
Proof
  simp[bind_assoc]
QED

Theorem aug_place_storage_write_gas_obs:
  write_place cx (StoragePlace tr slot tv) v ee = (res,fin) ==>
  !gs. write_place cx (StoragePlace tr slot tv) v (ee with gas_obs := gs) =
    (res,fin with gas_obs := gs)
Proof
  simp[write_place_def, ignore_bind_def, bind_def, return_def,
       stmtSimAssignStorageTheory.write_storage_slot_gas_obs,
       AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem aug_place_storage_binop_admissible:
  gas_admissible
    (bind (eval_expr cx e) (\raw. bind (read_result cx raw)
      (\v. bind (lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        tv bop cur v)) (write_place cx (StoragePlace tr slot tv)))))
    (stmt_res_ok lctx) st /\
  bind (eval_expr cx e) (read_result cx) (st with gas_obs := gs) = (INL v,ee) /\
  bop <> In /\ bop <> NotIn ==>
  expr_res_ok (bop_result cx ty bop [ty;expr_type e] cur v ee)
Proof
  rewrite_tac[aug_place_storage_suffix_assoc] >> strip_tac >>
  `expr_res_ok (bop_result cx ty bop [ty;expr_type e] cur v ee) <=>
   expr_res_ok (case evaluate_binop
       (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
       tv bop cur v of INL w => INL w | INR err => INR (Error err))` by
    (irule bop_result_augassign_res_ok >> simp[]) >>
  Cases_on `evaluate_binop
    (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
    tv bop cur v` >- simp[expr_res_ok_def] >>
  qpat_x_assum `gas_admissible _ _ _` mp_tac >>
  simp[gasContextTheory.gas_admissible_def] >>
  disch_then (qspec_then `gs` mp_tac) >>
  simp[bind_def, lift_sum_def, raise_def, stmt_res_ok_def, expr_res_ok_def]
QED

Theorem aug_place_storage_suffix_gas_obs[local]:
  bind (lift_sum bv) (write_place cx (StoragePlace tr slot tv)) ee = (res,ff) ==>
  !tail. bind (lift_sum bv) (write_place cx (StoragePlace tr slot tv))
    (ee with gas_obs := tail) = (res,ff with gas_obs := tail)
Proof
  Cases_on `bv` >> simp[lift_sum_def, bind_def, return_def, raise_def] >>
  metis_tac[aug_place_storage_write_gas_obs]
QED

(* One SSTORE or TSTORE of the new word at the place's slot.  Its endpoint
   is the same whatever the horizon; the relation carries over for every
   horizon that observes the place. *)
Theorem aug_place_storage_store_run[local]:
  emit_void (if tr then TSTORE else SSTORE) [dst;op] sa = ((),sb) /\
  eval_operand dst s = SOME slot /\
  eval_operand op s = SOME (typed_val_to_w256 tv v) /\
  ~s.vs_call_ctx.cc_static /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\
  write_place cx (StoragePlace tr slot tv) v ee = (INL (),ff) /\
  fn_has_code sa sb func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
      (!(H:(bool # bytes32 # type_value) list # num list).
         stmt_state_rel H ctx func cenv cx ee s /\
         storage_place_observed H (StoragePlace tr slot tv) ==>
         stmt_state_rel H ctx func cenv cx ff t) /\
      (!x. lookup_var x t = lookup_var x s) /\
      t.vs_allocas = s.vs_allocas /\ t.vs_memory = s.vs_memory /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  qabbrev_tac `u = if tr then tstore slot (typed_val_to_w256 tv v) s
                   else sstore slot (typed_val_to_w256 tv v) s` >>
  qspecl_then [`ctx`, `func`, `slot_loc tr`, `dst`, `op`, `sa`, `sb`, `s`,
               `slot`, `typed_val_to_w256 tv v`, `u`] mp_tac
    placeStoreTheory.place_store_emit_run >>
  impl_tac >- (Cases_on `tr` >> gvs[Abbr `u`, slot_loc_def]) >>
  strip_tac >>
  qexists_tac `u with vs_inst_idx := SUC s.vs_inst_idx` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (rpt strip_tac >> simp[stmt_state_rel_inst_idx, Abbr `u`] >>
      qspecl_then [`H`, `ctx`, `func`, `cenv`, `cx`, `ee`, `ff`, `s`, `tr`,
                   `slot`, `tv`, `ty`, `v`] mp_tac
        (Q.GEN `H` placeStoreTheory.place_store_word_backend_state) >>
      simp[]) >>
  Cases_on `tr` >>
  gvs[Abbr `u`, venomStateTheory.lookup_var_def,
      venomStateTheory.sstore_def, venomStateTheory.tstore_def]
QED

(* A storage place reads the same at any gas observations. *)
Theorem aug_place_storage_read_gas_obs[local]:
  read_place cx (StoragePlace tr slot tv) st = (INL cur,st) ==>
  !gs. read_place cx (StoragePlace tr slot tv) (st with gas_obs := gs) =
       (INL cur,st with gas_obs := gs)
Proof
  rpt strip_tac >> simp[exprSimLenTheory.len_rp_obs]
QED

(* A value source that changes nothing but the gas observations runs no
   instruction. *)
Theorem aug_place_value_prefix_outcome[local]:
  (!gs. source (es with gas_obs := gs) =
    (INL (v:value),es with gas_obs := gs)) /\
  ~s.vs_halted /\
  gas_outcome F tops (ctx,func) cx st0 (next v)
    (es with gas_obs := [],s) Q R ==>
  gas_outcome F tops (ctx,func) cx st0 (bind source next)
    (es with gas_obs := [],s) Q R
Proof
  strip_tac >>
  `gas_marked_exec F (ctx,func) source (es with gas_obs := [],s) []
     (INL v) es (OK s)` by
    (simp[gasSummaryTheory.gas_marked_exec_def,
          gasSummaryTheory.gas_explicit_def,
          fragGasModeTheory.gas_marked_path_def] >>
     irule (cj 1 fragGasPathTheory.gas_path_rules) >> simp[]) >>
  drule_all aug_place_completed_value_prefix >> simp[]
QED

(* A whole-leaf storage write at a traced root keeps the backends well
   formed on a horizon valid after it. *)
Theorem aug_place_storage_store_wf:
  MEM (StorageRoot tr offset tv0) ee.storage_trace /\
  storage_subregion tv0 path delta tv /\ slot = n2w offset + n2w delta /\
  well_formed_type_value tv /\ value_has_type tv v /\
  write_place cx (StoragePlace tr slot tv) v ee = (INL (),ff) /\
  valid_horizon cx st0 H ff.storage_trace /\
  storage_well_formed_on cx ee (FST H) ==>
  storage_well_formed_on cx ff (FST H)
Proof
  strip_tac >>
  `?xs. ff.storage_trace = ee.storage_trace ++ xs` by
    metis_tac[vyperStorageTraceTheory.storage_trace_frame_prefix,
              vyperStorageTraceTheory.storage_trace_frame_write_place] >>
  `regions_consistent (FST H) /\ storage_observations_ok cx H ee.storage_trace` by
    (qpat_x_assum `valid_horizon _ _ _ _` mp_tac >>
     simp[vyperStorageFootprintTheory.valid_horizon_def]) >>
  mp_tac (Q.INST [`st` |-> `ee`, `observations` |-> `ee.storage_trace`,
                  `p` |-> `StoragePlace tr slot tv`, `leaf_tv` |-> `tv`,
                  `res` |-> `INL ()`, `st'` |-> `ff`]
    vyperFiniteStoragePreservationTheory.write_place_preserves_storage_well_formed_on) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
      >- (rpt strip_tac >> gvs[] >> qexistsl_tac [`offset`, `tv0`, `path`, `delta`] >> simp[]) >>
      simp[vyperPlaceTypingTheory.runtime_place_typed_storage]) >>
  simp[]
QED

Theorem aug_place_storage_suffix_admissible[local]:
  gas_admissible
    (bind (lift_sum bv) (write_place cx (StoragePlace tr slot tv))) A ee /\
  bind (lift_sum bv) (write_place cx (StoragePlace tr slot tv)) ee =
    (res,ff) ==>
  A res
Proof
  strip_tac >> drule aug_place_storage_suffix_gas_obs >>
  disch_then (qspec_then `[]` assume_tac) >>
  fs[gas_admissible_def] >> metis_tac[]
QED

(* The operator and the store at a storage place.  The relation excludes
   a static call, so the write succeeds, and the store keeps the
   relation at every horizon valid after it: such a horizon observes the
   place, whose root the trace holds. *)
Theorem aug_place_storage_binop_store_outcome[local]:
  bop <> In /\ bop <> NotIn /\ word_value cur /\
  compile_binop bop x y ty NONE el s2 = (op,s3) /\
  emit_void (if tr then TSTORE else SSTORE) [dst;op] s3 = ((),sf) /\
  binop_frag ctx func cenv cx bop ty ty NONE el [ty;expr_type e] cur rhs ee /\
  gas_admissible
    (bind (lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
      tv bop cur rhs)) (write_place cx (StoragePlace tr slot tv)))
    (stmt_res_ok lctx) ee /\
  (!z. x = Var z ==> not_fresh_at s2 z) /\
  (!z. y = Var z ==> not_fresh_at s2 z) /\
  (!z. dst = Var z ==> not_fresh_at s2 z) /\
  (!z. not_fresh_at s2 z ==> not_fresh_at s3 z) /\
  (!z. not_fresh_at sa z ==> not_fresh_at s2 z) /\
  fn_has_code s2 s3 func /\ fn_has_code s3 sf func /\
  fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv s2 /\ local_ptrs_reserved cenv s3 /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ee s /\
       storage_well_formed_on cx ee (FST H)) /\
  alloca_frame cenv es0 sa s_entry cenv ee s /\
  sa.cs_next_id <= s2.cs_next_id /\
  eval_operand x s = SOME (val_to_w256 cur) /\
  eval_operand y s = SOME (val_to_w256 rhs) /\
  eval_operand dst s = SOME slot /\
  (?offset tv0 path delta.
     MEM (StorageRoot tr offset tv0) ee.storage_trace /\
     storage_subregion tv0 path delta tv /\ slot = n2w offset + n2w delta) /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  (!v. bop_result cx ty bop [ty;expr_type e] cur rhs ee = INL v ==>
       value_has_type tv v) /\
  ~block_is_terminated sf /\
  ~s.vs_halted /\ s.vs_current_bb = s2.cs_current_bb /\
  s.vs_inst_idx = LENGTH s2.cs_current_insts /\
  (!z u. not_fresh_at sa z /\ lookup_var z s_entry = SOME u ==>
         lookup_var z s = SOME u) /\
  (!aid b. FLOOKUP s_entry.vs_allocas aid = SOME b ==>
           FLOOKUP s.vs_allocas aid = SOME b) ==>
  gas_outcome F (cx_tops cx) (ctx,func) cx st0
    (bind (lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
      tv bop cur rhs)) (write_place cx (StoragePlace tr slot tv))) (ee,s)
    (\H. stmt_post H ctx func cx lctx cenv cenv sa sf es0 s_entry)
    (\H res ff r. !tail. stmt_exit (RetQ H) (ff with gas_obs := tail) res r)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qmatch_goalsub_abbrev_tac `gas_outcome _ _ _ _ _ k _ _ _` >>
  Cases_on `k ee` >> rename1 `k ee = (res,ff)` >>
  `stmt_res_ok lctx res` by
    (unabbrev_all_tac >> drule_all aug_place_storage_suffix_admissible >>
     simp[]) >>
  `case bop_result cx ty bop [ty;expr_type e] cur rhs ee of
     INR ex => res = INR ex /\ ff = ee
   | INL v => write_place cx (StoragePlace tr slot tv) v ee = (res,ff)` by
    (`bop_result cx ty bop [ty;expr_type e] cur rhs ee =
      case evaluate_binop
        (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
        tv bop cur rhs of INL v => INL v | INR err => INR (Error err)` by
       (irule bop_result_augassign >> metis_tac[word_value_not_bytes]) >>
     simp[] >>
     qpat_x_assum `k ee = _` mp_tac >>
     simp[Abbr `k`, bind_def, lift_sum_def, return_def, raise_def] >>
     Cases_on `evaluate_binop
       (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
       tv bop cur rhs` >> simp[return_def, raise_def] >> metis_tac[]) >>
  `expr_res_ok (bop_result cx ty bop [ty;expr_type e] cur rhs ee)` by
    (irule aug_place_bop_write_result_ok >> metis_tac[]) >>
  qpat_x_assum `binop_frag _ _ _ _ _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [exprBopSimDefsTheory.binop_frag_def,
                          exprBopSimDefsTheory.binop_frag_words_def]) >>
  disch_then (qspecl_then [`st0`, `s2`, `s3`, `x`, `y`, `op`, `s`] mp_tac) >>
  impl_tac >- simp[] >>
  strip_tac >- suspend "normal" >> suspend "exit"
QED

Resume aug_place_storage_binop_store_outcome[normal]:
  rename1 `eval_operand op t = SOME (val_to_w256 v)` >>
  TRY (qpat_x_assum `r = OK _` SUBST_ALL_TAC) >>
  `write_place cx (StoragePlace tr slot tv) v ee = (res,ff)` by
    (qpat_x_assum `bop_result _ _ _ _ _ _ _ = INL _` (fn th =>
       qpat_x_assum `sum_CASE _ _ _` (mp_tac o REWRITE_RULE [th])) >>
     simp[]) >>
  `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx
     ee s /\
   stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx
     ee t` by
    metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  `~t.vs_call_ctx.cc_static /\ ~cx.txn.is_static` by
    (qpat_x_assum `stmt_state_rel (storage_trace_horizon _) _ _ _ _ ee t`
       mp_tac >>
     rewrite_tac[stmt_state_rel_def, state_rel_def] >> strip_tac >> simp[]) >>
  `value_has_type tv v` by metis_tac[] >>
  `res = INL ()` by
    (drule_all aug_place_storage_write_outcome >> metis_tac[]) >>
  qpat_x_assum `res = INL ()` SUBST_ALL_TAC >>
  `eval_operand dst t = SOME slot` by metis_tac[aug_place_saved_operand] >>
  `eval_operand op t = SOME (typed_val_to_w256 tv v)` by
    simp[typed_val_to_w256_word_value] >>
  mp_tac (Q.INST [`sa` |-> `s3`, `sb` |-> `sf`, `s` |-> `t`]
            aug_place_storage_store_run) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `t2` strip_assume_tac) >>
  `gas_marked_path F ctx func s 0 (OK t2)` by
    (drule_all fragGasModeTheory.gas_marked_path_then >> simp[]) >>
  `MAP FDOM ff.scopes = MAP FDOM ee.scopes` by
    metis_tac[vyperScopePreservationTheory.write_place_scopes_dom] >>
  `!z a. not_fresh_at s2 z /\ lookup_var z s = SOME a ==>
         lookup_var z t2 = SOME a` by metis_tac[] >>
  `alloca_frame cenv ee s2 s cenv ff t2` by
    (qspecl_then [`storage_trace_horizon ee.storage_trace`] mp_tac
       (Q.GEN `H` (Q.INST [`es` |-> `ee`, `es'` |-> `ff`, `sa` |-> `s2`,
                           `s0` |-> `s`, `s` |-> `t2`]
                     alloca_frame_of_mem_frame)) >>
     impl_tac >- simp[] >> simp[]) >>
  `alloca_frame cenv es0 sa s_entry cenv ff t2` by
    (irule alloca_frame_trans >>
     goal_assum (drule_at (Pat `alloca_frame _ _ _ _ _ _ s`)) >>
     goal_assum (drule_at (Pat `alloca_frame _ _ _ _ _ _ t2`)) >> simp[]) >>
  `!z u. not_fresh_at sa z /\ lookup_var z s_entry = SOME u ==>
         lookup_var z t2 = SOME u` by metis_tac[] >>
  `!aid b. FLOOKUP s_entry.vs_allocas aid = SOME b ==>
           FLOOKUP t2.vs_allocas aid = SOME b` by metis_tac[] >>
  `!H. valid_horizon cx st0 H ff.storage_trace ==>
       stmt_post H ctx func cx lctx cenv cenv sa sf es0 s_entry
         (INL ()) (ff with gas_obs := []) t2` by
    (gen_tac >> strip_tac >>
     `valid_horizon cx st0 H ee.storage_trace` by
       metis_tac[vyperStorageFootprintTheory.valid_horizon_frame,
                 vyperStorageTraceTheory.storage_trace_frame_write_place] >>
     `stmt_state_rel H ctx func cenv cx ee t /\
      storage_well_formed_on cx ee (FST H)` by metis_tac[] >>
     qpat_x_assum `?offset tv0 path delta. _` strip_assume_tac >>
     `storage_place_observed H (StoragePlace tr slot tv)` by
       (mp_tac (Q.INST [`trace` |-> `ee.storage_trace`]
                  aug_place_storage_rooted_observed) >> simp[]) >>
     `stmt_state_rel H ctx func cenv cx ff t2` by metis_tac[] >>
     `storage_well_formed_on cx ff (FST H)` by
       (mp_tac aug_place_storage_store_wf >>
        impl_tac
        >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
            metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value]) >>
        simp[]) >>
     `storage_well_formed_on cx (ff with gas_obs := []) (FST H)` by
       (`(ff with gas_obs := []).accounts = ff.accounts /\
         (ff with gas_obs := []).tStorage = ff.tStorage` by simp[] >>
        metis_tac[vyperStorageFootprintTheory.storage_well_formed_on_backends]) >>
     `alloca_frame cenv es0 sa s_entry cenv (ff with gas_obs := []) t2` by
       (qpat_x_assum `alloca_frame cenv es0 sa s_entry cenv ff t2` mp_tac >>
        simp[alloca_frame_def]) >>
     irule aug_place_normal_post >>
     simp[exprSimWordArgsTheory.stmt_state_rel_gas_obs]) >>
  `!tail. k (ee with gas_obs := tail) = (INL (),ff with gas_obs := tail)` by
    (unabbrev_all_tac >> drule aug_place_storage_suffix_gas_obs >> simp[]) >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  simp[gas_summary_at_def, gas_marked_exec_def] >>
  qexistsl_tac [`INL ()`, `ff`, `OK t2`] >> simp[] >> metis_tac[]
QED

Resume aug_place_storage_binop_store_outcome[exit]:
  `?ex. bop_result cx ty bop [ty;expr_type e] cur rhs ee = INR ex` by
    (Cases_on `bop_result cx ty bop [ty;expr_type e] cur rhs ee` >>
     fs[expr_exit_def]) >>
  `res = INR ex /\ ff = ee` by
    (qpat_x_assum `bop_result _ _ _ _ _ _ _ = INR _` (fn th =>
       qpat_x_assum `sum_CASE _ _ _` (mp_tac o REWRITE_RULE [th])) >>
     simp[]) >>
  qpat_x_assum `res = _` SUBST_ALL_TAC >>
  qpat_x_assum `ff = _` SUBST_ALL_TAC >>
  `!tail. k (ee with gas_obs := tail) = (INR ex,ee with gas_obs := tail)` by
    (unabbrev_all_tac >> drule aug_place_storage_suffix_gas_obs >> simp[]) >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  rewrite_tac[gas_summary_at_def, gas_marked_exec_def] >>
  qexistsl_tac [`INR ex`, `ee`, `r`] >>
  conj_tac >- simp[]
  >- (disj2_tac >> conj_tac >- first_assum ACCEPT_TAC >>
      gen_tac >> strip_tac >> simp[stmt_exit_def] >> gen_tac >> disj1_tac >>
      Cases_on `ex` >> Cases_on `r` >> gvs[expr_exit_def] >>
      rename1 `expr_exit (INR (Error err)) _` >> Cases_on `err` >>
      gvs[expr_exit_def])
QED

Finalise aug_place_storage_binop_store_outcome

(* The whole statement, replayed from a reached rhs: the target, the
   load and the rhs leave the operator and the store. *)
Theorem aug_place_storage_source_replay[local]:
  (!gs. eval_target_place cx bt (es with gas_obs := prefix ++ gs) =
    (INL (StoragePlace tr slot tv),mid with gas_obs := gs)) /\
  (!gs. read_place cx (StoragePlace tr slot tv) (mid with gas_obs := gs) =
    (INL cur,mid with gas_obs := gs)) /\
  (!gs. bind (eval_expr cx e) (read_result cx)
    (mid with gas_obs := readings ++ gs) = (INL rhs,last with gas_obs := gs)) ==>
  !gs. eval_stmt cx (AugAssign ty bt bop e)
    (es with gas_obs := (prefix ++ readings) ++ gs) =
    bind (lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
      tv bop cur rhs)) (write_place cx (StoragePlace tr slot tv))
      (last with gas_obs := gs)
Proof
  strip_tac >> gen_tac >> pure_once_rewrite_tac[GSYM APPEND_ASSOC] >>
  simp[Once evaluate_def, bind_def, place_type_value_def, return_def,
       Excl "APPEND_ASSOC"] >>
  qpat_x_assum `!gs. bind (eval_expr _ _) _ _ = _`
    (qspec_then `gs` mp_tac) >>
  Cases_on `eval_expr cx e (mid with gas_obs := readings ++ gs)` >>
  Cases_on `q` >> simp[bind_def] >> strip_tac >> simp[]
QED

Theorem compile_augassign_place_storage_case:
  !ctx func cx lctx RetQ cenv ret_ty env env' tops bindings ty bt bop e es.
    (!id. target_root bt <> NameTarget id) /\
    ((?b fld. bt = AttributeTarget b fld) \/ (?b k. bt = SubscriptTarget b k)) /\
    body_inv tops ctx cenv cx /\
    supported_stmt tops bindings (AugAssign ty bt bop e) /\
    type_stmt env ret_ty (AugAssign ty bt bop e) = SOME env' /\
    target_case F ctx func cenv cx bt /\
    ~immutable_root cx bt /\ target_indices_pre cenv cx env bt /\
    ((?s p s1 s2 cur s3 s4 ptv s5.
        eval_target_place cx bt s = (INL p,s1) /\
        read_place cx p s2 = (INL cur,s3) /\
        place_type_value cx p s4 = (INL ptv,s5)) ==>
     expr_sim_case F ctx func cenv cx e) /\
    expr_body_pre cenv cx env e es ==>
    stmt_frag ctx func cx lctx RetQ cenv
      (stmt_env cenv lctx ret_ty (AugAssign ty bt bop e))
      (eval_stmt cx (AugAssign ty bt bop e)) es
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  simp[stmt_frag_def, stmt_framed_frag_def] >> rpt gen_tac >> strip_tac >>
  `?info. supported_target_info tops bindings bt = SOME info` by
    (drule_all aug_place_supported_stmt_target_info >> simp[]) >>
  qpat_x_assum `(?b fld. bt = AttributeTarget b fld) \/ _` kall_tac >>
  drule aug_place_typing >> strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  drule_all aug_place_code_parts >>
  disch_then (CONJUNCTS_THEN2 SUBST_ALL_TAC
    (qx_choosel_then [`r`, `s0'`] (CONJUNCTS_THEN2 assume_tac assume_tac))) >>
  `cs_extends sa s0'` by
    (qpat_x_assum `compile_get_target_ptr _ _ _ _ = _` mp_tac >>
     qmatch_goalsub_abbrev_tac `compile_get_target_ptr _ _ target _` >>
     qspecl_then [`compile_expr`, `target`, `cenv`, `sa`]
       mp_tac ci_mono_compile_get_target_ptr_cfn >>
     simp[cj 1 compile_expr_ci_mono, ci_mono_def] >>
     rpt strip_tac >> gvs[]) >>
  `cs_extends s0' sb` by
    (qpat_x_assum `FST (SND r) = NONE /\ _ \/ _` strip_assume_tac >>
     imp_res_tac (REWRITE_RULE [cs_appends_def] cs_appends_emit_helpers) >>
     imp_res_tac (cj 2 compile_expr_grows) >>
     imp_res_tac compile_binop_grows >>
     fs[cs_appends_def] >> metis_tac[cs_extends_trans]) >>
  `fn_has_code sa s0' func` by metis_tac[fn_has_code_mid, cs_extends_refl] >>
  `target_sim ctx func cenv cx env bt es` by
    (fs[target_case_def, target_pre_def]) >>
  `gas_admissible (eval_base_place cx bt) target_res_ok es` by
    metis_tac[aug_place_base_admissible] >>
  qpat_x_assum `target_sim _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[target_sim_def] >>
  disch_then (qspecl_then [`st0`, `Type ty`, `sa`, `s0'`, `r`, `s0`] mp_tac) >>
  (impl_tac >- simp[]) >>
  strip_tac >>
  rewrite_tac[aug_place_stmt_source] >>
  drule exprSimSubscriptMapTheory.gas_outcome_bind_result_exec >>
  disch_then irule >> rpt conj_tac
  >- (rpt strip_tac >> fs[])
  >- (rpt strip_tac >> BETA_TAC >> Cases_on `res` >> fs[expr_exit_def] >>
      rename1 `expr_exit (INR ex) _` >> qexists_tac `ex` >>
      simp[stmt_exit_def] >> metis_tac[expr_exit_INR_type])
  >- (rpt gen_tac >> strip_tac >> suspend "base_normal")
  >- simp[aug_place_rest_trace_frame]
QED

(* The target reached a place: it is a storage place, loaded at the
   slot the lowering computed. *)
Resume compile_augassign_place_storage_case[base_normal]:
  rename1 `gas_marked_exec _ _ _ _ marks' (INL pv) raw (OK t)` >>
  qpat_x_assum `gas_outcome _ _ _ _ _ (eval_base_place _ _) _ _ _` kall_tac >>
  reverse (Cases_on `storage_trace_domain cx st0 raw.storage_trace`)
  >- (rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
      irule gasStorageTheory.gas_bad_storage_at_initial >>
      simp[aug_place_rest_trace_frame]) >>
  qpat_assum `!H. valid_horizon cx st0 H raw.storage_trace ==> _`
    (qspec_then `storage_trace_horizon raw.storage_trace` mp_tac) >>
  impl_tac
  >- (qpat_x_assum `storage_trace_domain _ _ raw.storage_trace` mp_tac >>
      simp[vyperStorageFootprintTheory.storage_trace_domain_def]) >>
  disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [target_post_def]) >>
  `?p. pv = PlaceR p` by
    (qpat_x_assum `place_ptr_rel _ _ _ _ _ _ _` mp_tac >>
     Cases_on `pv` >> simp[place_ptr_rel_def]) >>
  qpat_x_assum `pv = _` SUBST_ALL_TAC >>
  `!tail. eval_target_place cx bt
      (es with gas_obs := gas_explicit marks' s0.vs_gas_readings ++ tail) =
      (INL p, raw with gas_obs := tail)` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     simp[Once evaluate_def, bind_def, get_place_def, return_def]) >>
  qpat_assum `!tail. eval_target_place _ _ _ = _`
    (assume_tac o SIMP_RULE std_ss [listTheory.APPEND_NIL] o Q.SPEC `[]`) >>
  `?tr slot tv. p = StoragePlace tr slot tv` by
    metis_tac[aug_place_supported_storage_kind] >>
  qpat_x_assum `p = _` SUBST_ALL_TAC >>
  qpat_x_assum `place_ptr_rel _ _ _ (PlaceR (StoragePlace _ _ _)) _ _ _`
    (strip_assume_tac o REWRITE_RULE [place_ptr_rel_def]) >>
  qpat_x_assum `w = slot` SUBST_ALL_TAC >>
  qpat_x_assum `Type _ = Type _` (assume_tac o SIMP_RULE (srw_ss()) []) >>
  `evaluate_type (get_tenv cx) ty = SOME tv` by metis_tac[] >>
  `?ld rhsop result s1 s2 s3.
     emit_op (if tr then TLOAD else SLOAD) [FST r] s0' = (ld,s1) /\
     lower_value compile_expr cenv ty e s1 = (rhsop,s2) /\
     compile_binop bop ld rhsop ty NONE
       (if bop = Exp then expr_int_literal e else NONE) s2 = (result,s3) /\
     emit_void (if tr then TSTORE else SSTORE) [FST r; result] s3 = ((),sb)` by
    (qpat_x_assum `FST (SND r) = NONE /\ _ \/ _` mp_tac >>
     Cases_on `tr` >> asm_simp_tac (srw_ss()) [slot_loc_def] >> metis_tac[]) >>
  qpat_x_assum `FST (SND r) = NONE /\ _ \/ _` kall_tac >>
  `is_word_type ty` by metis_tac[exprSimSourceTheory.word_value_type_word] >>
  qspecl_then [`cx`, `st0`, `storage_trace_horizon raw.storage_trace`,
               `raw with gas_obs := []`, `ty`, `tv`, `bt`,
               `es with gas_obs := gas_explicit marks' s0.vs_gas_readings`,
               `tr`, `slot`] mp_tac aug_place_target_storage_ready >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      qpat_x_assum `storage_trace_domain _ _ raw.storage_trace` mp_tac >>
      simp[vyperStorageFootprintTheory.storage_trace_domain_def]) >>
  strip_tac >>
  mp_tac (Q.INST [`st` |-> `raw with gas_obs := []`]
            aug_place_storage_read_ready) >>
  impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `old` strip_assume_tac) >>
  drule_all aug_place_storage_load_ready >> strip_tac >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  drule compile_binop_grows >> strip_tac >>
  drule emit_void_extends >> strip_tac >>
  drule emit_op_extends >> strip_tac >>
  `cs_extends s3 sb /\ cs_extends s0' s1` by
    (simp[cs_extends_def] >> conj_tac >> qexists_tac `[]` >>
     fs[same_blocks_def]) >>
  `cs_extends s1 sb` by
    (irule cs_extends_trans >> qexists_tac `s2` >> simp[] >>
     irule cs_extends_trans >> qexists_tac `s3` >> simp[]) >>
  `fn_has_code s0' s1 func` by metis_tac[fn_has_code_split] >>
  `~t.vs_halted` by
    (qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     drule aug_place_marked_path_not_halted >> simp[]) >>
  `sa.cs_next_var <= s0'.cs_next_var` by
    (qspecl_then [`bt`, `cenv`, `sa`] mp_tac
       stmtLoweringMonoTheory.ci_mono_compile_get_target_ptr >>
     simp[ci_mono_def]) >>
  `local_ptrs_reserved cenv s0'` by metis_tac[local_ptrs_reserved_next_var] >>
  `s0'.cs_next_var <= s1.cs_next_var` by
    (qspec_then `if tr then TLOAD else SLOAD` mp_tac
       (CONJUNCT1 exprOperandVarTheory.compiler_counter_emit) >>
     disch_then (qspecl_then [`[FST r]`, `s0'`] mp_tac) >> simp[]) >>
  `local_ptrs_reserved cenv s1` by metis_tac[local_ptrs_reserved_next_var] >>
  mp_tac (Q.INST [`arg` |-> `FST r`, `sa` |-> `s0'`, `sb` |-> `s1`,
                  `s` |-> `t`, `op` |-> `ld`, `cur` |-> `old`]
            aug_place_storage_load_counted_nofresh) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  `gas_marked_path F ctx func t 0 (OK u)` by
    simp[fragGasModeTheory.gas_marked_path_def] >>
  `word_value old` by
    (drule_all exprSimSourceTheory.word_value_type_typed >> simp[]) >>
  `eval_operand ld u = SOME (val_to_w256 old)` by
    (irule exprBopSimPropsTheory.expr_val_rel_word >>
     qexistsl_tac [`cx`, `ty`] >> simp[]) >>
  `!z. ld = Var z ==> not_fresh_at s1 z` by
    (drule exprSafeOperandTheory.emit_op_safe_operand >>
     simp[exprSafeOperandTheory.safe_operand_def]) >>
  `expr_body_pre cenv cx env e (raw with gas_obs := [])` by
    metis_tac[aug_place_rhs_pre_target_gas_obs] >>
  `expr_sim_case F ctx func cenv cx e` by
    (qpat_x_assum `(?s p s1 s2 cur s3 s4 ptv s5. _) ==> _` irule >>
     metis_tac[]) >>
  qpat_x_assum `(?s p s1 s2 cur s3 s4 ptv s5. _) ==> _` kall_tac >>
  qpat_x_assum `target_case _ _ _ _ _ _` kall_tac >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx))
     expr_res_ok (raw with gas_obs := [])` by
    (irule expr_body_pre_gas_admissible >> metis_tac[]) >>
  `fn_has_code s1 s2 func` by
    metis_tac[fn_has_code_mid, cs_extends_trans] >>
  `expr_sim ctx func cenv cx ty e (raw with gas_obs := [])` by
    (qpat_x_assum `expr_sim_case F _ _ _ _ _` mp_tac >>
     rewrite_tac[expr_sim_case_def] >>
     disch_then (qspecl_then [`env`, `ty`, `raw with gas_obs := []`] mp_tac) >>
     simp[]) >>
  `!H. valid_horizon cx st0 H (raw with gas_obs := []).storage_trace ==>
       stmt_state_rel H ctx func cenv cx (raw with gas_obs := []) u /\
       storage_well_formed_on cx (raw with gas_obs := []) (FST H)` by
    (gen_tac >> strip_tac >>
     `valid_horizon cx st0 H raw.storage_trace` by
       (qpat_x_assum `valid_horizon _ _ H _` mp_tac >> simp[]) >>
     qpat_x_assum `!H. valid_horizon cx st0 H raw.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) [target_post_def]) >>
     metis_tac[]) >>
  qpat_x_assum `expr_sim ctx func cenv cx ty e _` mp_tac >>
  pure_rewrite_tac[expr_sim_def] >>
  disch_then (qspecl_then [`st0`, `s1`, `s2`, `rhsop`, `u`] mp_tac) >>
  (impl_tac >- fs[]) >> strip_tac >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  drule stmtSimDeclComposeTheory.gas_outcome_zero_prefix >>
  disch_then irule >>
  rewrite_tac[get_place_def, bind_return] >> BETA_TAC >>
  drule aug_place_storage_read_gas_obs >>
  disch_then (assume_tac o SIMP_RULE (srw_ss()) []) >>
  irule (Q.INST [`v` |-> `old`] aug_place_value_prefix_outcome) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  BETA_TAC >> rewrite_tac[place_type_value_def, bind_return] >> BETA_TAC >>
  drule aug_place_bind_value_exec >>
  disch_then irule >> rpt conj_tac
  >- (rpt strip_tac >> fs[])
  >- (rpt strip_tac >> BETA_TAC >> Cases_on `res` >> fs[expr_exit_def] >>
      rename1 `expr_exit (INR ex) _` >> qexists_tac `ex` >>
      simp[stmt_exit_def] >> metis_tac[expr_exit_INR_type])
  >- (rpt gen_tac >> strip_tac >> suspend "rhs_normal")
  >- simp[aug_place_store_trace_frame]
QED

(* The rhs reached a value: the operator and the store close the
   statement. *)
Resume compile_augassign_place_storage_case[rhs_normal]:
  rename1 `gas_marked_exec _ _ _ _ marks'' (INL v'') raw' (OK t')` >>
  qpat_x_assum `!H. valid_horizon cx st0 H raw'.storage_trace ==> _`
    (assume_tac o SIMP_RULE (srw_ss()) []) >>
  reverse (Cases_on `storage_trace_domain cx st0 raw'.storage_trace`)
  >- (rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
      irule gasStorageTheory.gas_bad_storage_at_initial >>
      simp[aug_place_store_trace_frame]) >>
  `valid_horizon cx st0 (storage_trace_horizon raw'.storage_trace)
     raw'.storage_trace` by
    (qpat_x_assum `storage_trace_domain _ _ raw'.storage_trace` mp_tac >>
     simp[vyperStorageFootprintTheory.storage_trace_domain_def]) >>
  qpat_assum `!H. valid_horizon cx st0 H raw'.storage_trace ==> _`
    (qspec_then `storage_trace_horizon raw'.storage_trace` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  `!gs. bind (eval_expr cx e) (read_result cx)
     (raw with gas_obs := gas_explicit marks'' u.vs_gas_readings ++ gs) =
     (INL v'',raw' with gas_obs := gs)` by
    (gen_tac >>
     qpat_assum `gas_marked_exec _ _ _ _ marks'' _ _ _` mp_tac >>
     rewrite_tac[gas_marked_exec_def] >> strip_tac >>
     qpat_x_assum `!tail. _` (qspec_then `gs` mp_tac) >> simp[]) >>
  `bind (eval_expr cx e) (read_result cx)
     (raw with gas_obs := gas_explicit marks'' u.vs_gas_readings) =
     (INL v'',raw' with gas_obs := [])` by
    (qpat_x_assum `!gs. bind (eval_expr _ _) _ _ = _`
       (qspec_then `[]` mp_tac) >> simp[]) >>
  `!H. valid_horizon cx st0 H raw'.storage_trace ==>
       valid_horizon cx st0 H raw.storage_trace /\
       valid_horizon cx st0 H es.storage_trace` by
    (gen_tac >> strip_tac >>
     `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
       simp[stmtSimAugAssignTheory.augassign_rhs_trace_frame] >>
     `storage_trace_frame (eval_target_place cx bt)` by
       simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
     `valid_horizon cx st0 H raw.storage_trace` by
       metis_tac[aug_place_valid_back] >>
     metis_tac[aug_place_valid_back]) >>
  qpat_assum `!H. valid_horizon cx st0 H raw'.storage_trace ==>
                  valid_horizon _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon raw'.storage_trace` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  qpat_assum `!H. valid_horizon cx st0 H raw.storage_trace ==> _`
    (qspec_then `storage_trace_horizon raw'.storage_trace` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (strip_assume_tac o SIMP_RULE (srw_ss()) []) >>
  `stmt_state_rel (storage_trace_horizon raw'.storage_trace) ctx func cenv cx
     es s0` by metis_tac[] >>
  `stmt_state_rel (storage_trace_horizon raw'.storage_trace) ctx func cenv cx
     (raw with gas_obs := []) t` by
    (qpat_x_assum `target_post (storage_trace_horizon raw'.storage_trace)
                     _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [target_post_def]) >>
     first_assum ACCEPT_TAC) >>
  `stmt_state_rel (storage_trace_horizon raw'.storage_trace) ctx func cenv cx
     (raw with gas_obs := []) u` by metis_tac[] >>
  Q.SUBGOAL_THEN
    `?offset tv0 path delta.
       MEM (StorageRoot tr offset tv0) (raw' with gas_obs := []).storage_trace /\
       storage_subregion tv0 path delta tv /\ slot = n2w offset + n2w delta`
    assume_tac
  >- (qpat_assum `eval_target_place cx bt
                    (es with gas_obs := gas_explicit _ _) = _`
        (strip_assume_tac o SIMP_RULE (srw_ss()) [] o MATCH_MP
           vyperFiniteStoragePreservationTheory.eval_target_place_observed_region) >>
      `storage_trace_frame (bind (eval_expr cx e) (read_result cx))` by
        simp[stmtSimAugAssignTheory.augassign_rhs_trace_frame] >>
      first_assum (fn frame =>
        qpat_assum `bind (eval_expr cx e) (read_result cx)
                      (raw with gas_obs := gas_explicit _ _) = _`
          (fn eq => mp_tac (MATCH_MP
             vyperStorageTraceTheory.storage_trace_frame_prefix
             (CONJ frame eq)))) >>
      simp[] >> strip_tac >> simp[listTheory.MEM_APPEND] >> metis_tac[]) >>
  `expr_body_pre cenv cx env e
     (raw with gas_obs := gas_explicit marks'' u.vs_gas_readings)` by
    metis_tac[expr_body_pre_gas_obs] >>
  `type_bits ty MOD 8 = 0` by
    (irule well_formed_type_bits >> qexists_tac `get_tenv cx` >>
     simp[well_formed_type_def] >> metis_tac[]) >>
  drule_all aug_place_rhs_suffix_ready >>
  disch_then (qspecl_then [`func`, `ctx`] strip_assume_tac) >>
  qpat_assum `expr_post (storage_trace_horizon raw'.storage_trace)
                _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
  `gas_marked_path F ctx func u (LENGTH marks'') (OK t')` by
    (qpat_assum `gas_marked_exec _ _ _ _ marks'' _ _ _` mp_tac >>
     rewrite_tac[gas_marked_exec_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
  `eval_operand ld t' = SOME (val_to_w256 old)` by
    metis_tac[aug_place_saved_operand] >>
  `!z. FST r = Var z ==> not_fresh_at s1 z` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `eval_operand (FST r) t' = SOME slot` by
    metis_tac[aug_place_saved_operand] >>
  `gas_admissible
    (bind (lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME u => u | NONE => Unsigned 0)
      tv bop old v'')) (write_place cx (StoragePlace tr slot tv)))
    (stmt_res_ok lctx) (raw' with gas_obs := [])` by
    (irule aug_place_replay_admissible >>
     goal_assum (drule_at Any) >>
     qexists_tac `gas_explicit marks' s0.vs_gas_readings ++
       gas_explicit marks'' u.vs_gas_readings` >>
     irule aug_place_storage_source_replay >>
     goal_assum (drule_at Any) >> simp[]) >>
  `!z. not_fresh_at sa z ==> not_fresh_at s1 z` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!z a. not_fresh_at sa z /\ lookup_var z s0 = SOME a ==>
         lookup_var z t' = SOME a` by
    (rpt strip_tac >>
     `not_fresh_at s0' z` by
       (irule freshWritesTheory.not_fresh_at_mono >>
        goal_assum (drule_at Any) >> simp[]) >>
     metis_tac[]) >>
  `!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
           FLOOKUP t'.vs_allocas aid = SOME b` by metis_tac[] >>
  `!z. rhsop = Var z ==> not_fresh_at s2 z` by
    (drule_at (Pos hd) exprOperandVarTheory.compile_lower_value_var >>
     simp[]) >>
  `!z. ld = Var z ==> not_fresh_at s2 z` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!z. FST r = Var z ==> not_fresh_at s2 z` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!z. not_fresh_at sa z ==> not_fresh_at s2 z` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `!z. not_fresh_at s2 z ==> not_fresh_at s3 z` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `local_ptrs_reserved cenv s2` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `s1` >> simp[]) >>
  `local_ptrs_reserved cenv s3` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `s2` >> simp[]) >>
  `fn_has_code s2 s3 func /\ fn_has_code s3 sb func` by
    metis_tac[fn_has_code_mid, fn_has_code_split, cs_extends_trans] >>
  `~t'.vs_halted` by metis_tac[aug_place_marked_path_not_halted] >>
  `word_value v'' /\ ?tyv.
     evaluate_type (get_tenv cx) (expr_type e) = SOME tyv /\
     value_has_type tyv v''` by
    (qpat_assum `expr_body_pre _ _ _ _ (_ with gas_obs := gas_explicit _ _)` mp_tac >>
     qpat_assum `word_value_type (expr_type e)` mp_tac >>
     qpat_assum `_ = (INL v'',raw' with gas_obs := [])` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     metis_tac[expr_body_pre_word_result, ETA_THM]) >>
  `is_word_type (expr_type e)` by metis_tac[word_value_type_word] >>
  `post_value_type cenv e = expr_type e` by simp[] >>
  `expr_val_rel cx (expr_type e) v'' rhsop t'` by metis_tac[] >>
  `eval_operand rhsop t' = SOME (val_to_w256 v'')` by
    (irule exprBopSimPropsTheory.expr_val_rel_word >>
     qexistsl_tac [`cx`, `expr_type e`] >> simp[]) >>
  `~block_is_terminated sb` by
    (irule stmtSimDeclMemTheory.emit_void_nonterminator_open >>
     goal_assum (drule_at Any) >>
     Cases_on `tr` >> simp[venomInstTheory.is_terminator_def]) >>
  `sa.cs_next_id <= s0'.cs_next_id` by
    (qspecl_then [`bt`, `cenv`, `sa`] mp_tac
       stmtLoweringMonoTheory.ci_mono_compile_get_target_ptr >>
     simp[ci_mono_def]) >>
  `s0'.cs_next_id <= s1.cs_next_id` by
    (drule emitHelperPropsTheory.emitted_insts_emit_op >> simp[]) >>
  `sa.cs_next_id <= s2.cs_next_id` by decide_tac >>
  `MAP FDOM raw.scopes = MAP FDOM es.scopes` by
    (qpat_assum `eval_target_place cx bt
                   (es with gas_obs := gas_explicit _ _) = _`
       (mp_tac o MATCH_MP
          vyperEvalExprPreservesScopesDomTheory.eval_target_place_preserves_scopes_dom) >>
     simp[]) >>
  `MAP FDOM raw'.scopes = MAP FDOM raw.scopes` by
    (qpat_assum `bind (eval_expr cx e) (read_result cx)
                   (raw with gas_obs := gas_explicit _ _) = _`
       (mp_tac o MATCH_MP eval_read_preserves_scopes_dom) >> simp[]) >>
  `alloca_frame cenv es sa s0 cenv (raw' with gas_obs := []) t'` by
    (irule aug_place_prefix_frame >>
     qpat_assum `target_post (storage_trace_horizon raw'.storage_trace)
                   _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `expr_post (storage_trace_horizon raw'.storage_trace)
                   _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     simp[exprSimWordArgsTheory.stmt_state_rel_gas_obs] >>
     metis_tac[]) >>
  `!H. valid_horizon cx st0 H (raw' with gas_obs := []).storage_trace ==>
       stmt_state_rel H ctx func cenv cx (raw' with gas_obs := []) t' /\
       storage_well_formed_on cx (raw' with gas_obs := []) (FST H)` by
    (gen_tac >> strip_tac >>
     qpat_x_assum `!H. valid_horizon cx st0 H raw'.storage_trace ==>
                       expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >>
     impl_tac >- (qpat_x_assum `valid_horizon _ _ H _` mp_tac >> simp[]) >>
     rewrite_tac[expr_post_def] >> strip_tac >> simp[]) >>
  `storage_trace_domain cx st0 (raw' with gas_obs := []).storage_trace` by
    simp[] >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  irule aug_place_storage_binop_store_outcome >>
  goal_assum (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `emit_void _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `binop_frag _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  asm_simp_tac std_ss [exprBopSimPropsTheory.bop_result_gas_obs] >>
  metis_tac[]
QED

Finalise compile_augassign_place_storage_case

