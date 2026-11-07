(*
 * Augmented assignment to a field or an element of a storage or transient
 * variable with pure indices (#637).  The current word is loaded by SLOAD
 * or TLOAD at the place's slot, combined with the right-hand side, and
 * stored back.  With pure indices the target's evaluation leaves storage
 * unchanged, so the place's slots are in range and live
 * (aug_place_pure_target_storage_range, _live) and the load reads the
 * source's current value (aug_place_storage_load_ready).
 *
 * TOP-LEVEL:
 *   compile_augassign_place_storage_case
 *)
Theory stmtSimAugAssignPlaceStorage
Ancestors
  valueEncodingProps
  exprSimSource bodyExprPreFacts exprSimTopLevelProps stmtSimBreak stmtSimContinue stmtSimExpr stmtSimSeqEnv stmtSimPass stmtSimProps exprSimHypsDefs stmtSimZero stmtSimDefs loweringPosts bodyAppendStorageFacts bodyAppendStorageAdapter
  vyperStorageLayoutSafety vyperLookupStorage
  list finite_map bodySim allocLimits allocLimitsProps  exprSimHyps exprLoweringProps
  stmtSimIf stmtLoweringMono stmtLowering compileEnv fragExec
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
  strip_tac >> rpt BasicProvers.VAR_EQ_TAC >> gvs[] >>
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
  storage_place_region cx (StoragePlace tr slot leaf) /\ type_slot_size leaf = 1 ==>
  !u st. storage_dead cx tr (update_storage slot u st) = storage_dead cx tr st
Proof
  simp_tac (srw_ss()) [vyperStoragePlaceProvenanceTheory.storage_place_region_def] >>
  strip_tac >> rpt gen_tac >>
  irule accountsRelPropsTheory.storage_dead_update_in_region >>
  qexistsl_tac [`root`, `mid`, `var_name`, `keys`, `tv`] >> simp[] >>
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

Theorem aug_place_target_storage_dead_stable:
  eval_target_place cx t es = (INL (StoragePlace tr slot leaf),es') /\
  type_slot_size leaf = 1 ==>
  !u st. storage_dead cx tr (update_storage slot u st) = storage_dead cx tr st
Proof
  strip_tac >> drule vyperStoragePlaceProvenanceTheory.eval_target_place_region >>
  strip_tac >> irule aug_place_region_storage_dead_stable >>
  qexists_tac `leaf` >> simp[]
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
      >> gvs[evaluate_def, bind_def, ignore_bind_def, type_check_def,
             assert_def, return_def, raise_def, get_accounts_def, lift_sum_def,
             AllCaseEqs()] >>
      gvs[vyperMiscTheory.sum_CASE_rator, AllCaseEqs(), return_def, raise_def] >>
      imp_res_tac aug_place_precompile_storage >>
      gvs[return_def, raise_def] >>
      first_x_assum (drule_then assume_tac) >> simp[])
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

Theorem aug_place_pure_index_storage:
  supported_pure_expr tops e /\
  (do result <- eval_expr cx e; read_result cx result od) s = (r,s') ==>
  get_storage cx s' tr = get_storage cx s tr
Proof
  strip_tac >>
  gvs[bind_def, AllCaseEqs()] >>
  metis_tac[aug_place_pure_eval_storage, read_result_state, raise_def]
QED

Theorem aug_place_dead_array_selected:
  i < n /\ (dyn ==> i < w2n (lookup_storage (n2w bs) st)) /\
  c = (if dyn then bs+1 else bs) + i * type_slot_size tv /\
  c <= j /\ j < c + type_slot_size tv /\
  dead_bytes st bs (ArrayTV tv (if dyn then Dynamic n else Fixed n)) j b ==>
  dead_bytes st c tv j b
Proof
  Cases_on `dyn` >> simp[dead_bytes_def] >> rpt strip_tac >> gvs[] >>
  rename1 `h < n` >>
  `h = i` suffices_by (strip_tac >> gvs[]) >>
  spose_not_then assume_tac >>
  `bs + h * type_slot_size tv + type_slot_size tv <= bs + i * type_slot_size tv \/
   bs + i * type_slot_size tv + type_slot_size tv <= bs + h * type_slot_size tv` by
    metis_tac[aug_place_cells_disjoint] >>
  gvs[AllCaseEqs()] >>
  imp_res_tac accountsRelPropsTheory.dead_bytes_range >>
  gvs[arithmeticTheory.RIGHT_ADD_DISTRIB] >> decide_tac
QED

Theorem aug_place_storage_read_live_array:
  storage_read_live cx tr st w (ArrayTV tv (if dyn then Dynamic n else Fixed n)) /\
  i < n /\ (dyn ==> i < w2n (lookup_storage w st)) ==>
  storage_read_live cx tr st
    (w + n2w ((if dyn then 1 else 0) + i * type_slot_size tv)) tv
Proof
  strip_tac >> Cases_on `type_slot_size tv = 0`
  >- (simp[storage_read_live_def] >> rpt strip_tac >>
      qspec_then `w + n2w (if dyn then 1 else 0)` mp_tac wordsTheory.w2n_lt >>
      decide_tac) >>
  `i * type_slot_size tv + type_slot_size tv <= n * type_slot_size tv` by
    (`(i+1) * type_slot_size tv <= n * type_slot_size tv` by
       simp[arithmeticTheory.LE_MULT_RCANCEL] >>
     pop_assum mp_tac >>
     pure_rewrite_tac[arithmeticTheory.RIGHT_ADD_DISTRIB,
                      arithmeticTheory.MULT_CLAUSES] >> decide_tac) >>
  qpat_x_assum `storage_read_live _ _ _ _ _` mp_tac >>
  rewrite_tac[storage_read_live_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >>
  `w2n w + ((if dyn then 1 else 0) + i * type_slot_size tv) < dimword (:256)` by
    (Cases_on `dyn` >> gvs[vyperValueTheory.type_slot_size_def]) >>
  `w2n (w + n2w ((if dyn then 1 else 0) + i * type_slot_size tv)) =
   w2n w + ((if dyn then 1 else 0) + i * type_slot_size tv)` by
    (Cases_on `dyn` >> gvs[] >>
     simp[wordsTheory.word_add_def, wordsTheory.w2n_n2w,
          arithmeticTheory.LESS_MOD] >> decide_tac) >>
  conj_tac >- (Cases_on `dyn` >> gvs[vyperValueTheory.type_slot_size_def]) >>
  strip_tac >> irule aug_place_dead_array_selected >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  qexistsl_tac [`w2n w`, `dyn`, `i`, `n`] >>
  Cases_on `dyn` >> gvs[vyperValueTheory.type_slot_size_def]
QED

Theorem aug_place_resolve_array_empty:
  resolve_array_element cx tr slot tv [] st = (INL (slot,tv,[]),st)
Proof
  Cases_on `tv` >> simp[resolve_array_element_def, return_def]
QED

Theorem aug_place_storage_extend_live:
  storage_read_live cx tr (get_storage cx st tr) slot tv /\
  ((?fs. tv = StructTV fs) \/ (?et bd. tv = ArrayTV et bd)) /\
  extend_storage_place cx tr slot tv sb st =
    (INL (StoragePlace tr child leaf),st') ==>
  storage_read_live cx tr (get_storage cx st' tr) child leaf
Proof
  reverse (strip_tac >> Cases_on `tv` >> gvs[])
  >- (rename1 `ArrayTV et bd` >> Cases_on `sb` >>
      gvs[extend_storage_place_def, raise_def] >>
      rename1 `ValueSubscript key` >> Cases_on `key` >>
      gvs[extend_storage_place_def, raise_def] >>
      Cases_on `bd` >>
      gvs[extend_storage_place_def, resolve_array_element_def, bind_def,
          ignore_bind_def, check_def, assert_def, return_def, raise_def,
          vyperStorageBackendTheory.get_storage_backend_eq,
          aug_place_resolve_array_empty, AllCaseEqs()]
      >- (irule (aug_place_storage_read_live_array |> Q.INST [`dyn` |-> `F`] |> SRULE []) >>
          simp[] >> goal_assum (drule_at Any) >> simp[])
      >> (drule_all (aug_place_storage_read_live_array |> Q.INST [`dyn` |-> `T`] |> SRULE []) >>
          simp_tac pure_ss [arithmeticTheory.ADD_COMM] >> disch_then ACCEPT_TAC)) >>
  Cases_on `sb` >>
  gvs[extend_storage_place_def, bind_def, lift_option_type_def,
      return_def, raise_def, AllCaseEqs()]
  >- (Cases_on `v` >> gvs[extend_storage_place_def, raise_def]) >>
  Cases_on `struct_field_slot fs s` >>
  gvs[return_def, raise_def] >>
  PairCases_on `x` >> gvs[return_def] >>
  irule accountsRelPropsTheory.storage_read_live_field >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem aug_place_dead_tuple_selected:
  !tvs i tv st bs j b.
    oEL i tvs = SOME tv /\
    bs + tuple_prefix_slot_size i tvs <= j /\
    j < bs + tuple_prefix_slot_size i tvs + type_slot_size tv /\
    dead_bytes_list st bs tvs j b ==>
    dead_bytes st (bs + tuple_prefix_slot_size i tvs) tv j b
Proof
  Induct_on `tvs` >- simp[listTheory.oEL_def] >>
  rpt gen_tac >> Cases_on `i` >>
  simp[listTheory.oEL_def, tuple_prefix_slot_size_def] >>
  rpt strip_tac >> gvs[] >>
  qpat_x_assum `dead_bytes_list _ _ _ _ _` mp_tac >>
  simp[Once dead_bytes_def] >> strip_tac
  >- (drule (cj 2 accountsRelPropsTheory.dead_bytes_range) >> simp[])
  >- (drule (cj 1 accountsRelPropsTheory.dead_bytes_range) >> simp[]) >>
  first_x_assum drule >>
  disch_then (qspecl_then [`st`, `bs + type_slot_size h`, `j`, `b`] mp_tac) >>
  simp_tac bool_ss [GSYM arithmeticTheory.ADD_ASSOC] >>
  disch_then irule >> asm_rewrite_tac []
QED

Theorem aug_place_storage_read_live_tuple:
  storage_read_live cx tr st w (TupleTV tvs) /\ oEL i tvs = SOME tv ==>
  storage_read_live cx tr st (w + n2w (tuple_prefix_slot_size i tvs)) tv
Proof
  strip_tac >>
  drule vyperStoragePlaceRegionTheory.tuple_component_slot_end_bound >> strip_tac >>
  Cases_on `type_slot_size tv = 0`
  >- (simp[storage_read_live_def] >> rpt strip_tac >>
      qspec_then `w + n2w (tuple_prefix_slot_size i tvs)` mp_tac wordsTheory.w2n_lt >>
      decide_tac) >>
  qpat_x_assum `storage_read_live _ _ _ _ _` mp_tac >>
  rewrite_tac[storage_read_live_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >> first_x_assum drule >> strip_tac >>
  `w2n w + tuple_prefix_slot_size i tvs < dimword (:256)` by decide_tac >>
  `w2n (w + n2w (tuple_prefix_slot_size i tvs)) =
   w2n w + tuple_prefix_slot_size i tvs` by
    (Cases_on `w` >> gvs[wordsTheory.word_add_n2w]) >>
  simp[] >> strip_tac >>
  `dead_bytes_list st (w2n w) tvs j b` by
    (qpat_x_assum `_ ==> dead_bytes _ _ _ _ _` mp_tac >>
     simp[Once dead_bytes_def]) >>
  irule aug_place_dead_tuple_selected >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem aug_place_storage_extend_live_all:
  storage_read_live cx tr (get_storage cx st tr) slot tv /\
  extend_storage_place cx tr slot tv sb st = (INL p,st') ==>
  ?child leaf. p = StoragePlace tr child leaf /\
    storage_read_live cx tr (get_storage cx st' tr) child leaf
Proof
  strip_tac >>
  drule vyperStoragePlaceProvenanceTheory.extend_storage_place_subregion >>
  strip_tac >> gvs[] >>
  Cases_on `sb` >> Cases_on `tv` >>
  gvs[extend_storage_place_def, raise_def]
  >~ [`TupleTV tvs`, `ValueSubscript key`]
  >- (Cases_on `key` >> gvs[extend_storage_place_def, raise_def] >>
      gvs[extend_storage_place_def, bind_def, ignore_bind_def,
          check_def, assert_def, lift_option_type_def, return_def,
          vyperMiscTheory.option_CASE_rator, raise_def, AllCaseEqs(),
          Once vyperStoragePlaceRegionTheory.storage_subregion_def] >>
      gvs[Once vyperStoragePlaceRegionTheory.storage_subregion_def] >>
      irule aug_place_storage_read_live_tuple >>
      goal_assum (drule_at Any) >> simp[])
  >>~- ([`ValueSubscript key`], Cases_on `key` >>
    gvs[extend_storage_place_def, raise_def] >>
    irule aug_place_storage_extend_live >>
    goal_assum (drule_at Any) >> simp[] >>
    qexists_tac `ValueSubscript (IntV i)` >>
    asm_rewrite_tac [extend_storage_place_def]) >>
  irule aug_place_storage_extend_live >>
  goal_assum (drule_at Any) >> simp[] >>
  qexists_tac `AttrSubscript s` >> asm_rewrite_tac [extend_storage_place_def]
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

Theorem aug_place_pure_target_storage:
  EVERY (supported_pure_expr tops) (target_indices t) /\
  eval_target_place cx t s = (r,s') ==>
  get_storage cx s' tr = get_storage cx s tr
Proof
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >>
  metis_tac[aug_place_pure_base_storage, vyperPlaceFramesTheory.get_place_state,
            raise_def]
QED

Theorem aug_place_mapping_extend_live:
  vyperStoragePlaceProvenance$storage_mapping_region cx tr slot (HashMapT kt vt) /\
  extend_place cx (HashMapRef tr slot kt vt) sb s =
    (INL (PlaceR (StoragePlace tr' child leaf)),s') ==>
  storage_read_live cx tr' (get_storage cx s' tr') child leaf
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
  irule accountsRelPropsTheory.declared_storage_region_read_live >>
  goal_assum (drule_at Any)
QED

Theorem aug_place_pure_base_storage_live:
  !t tops cx s tr slot tv s'.
    EVERY (supported_pure_expr tops) (target_indices t) /\
    eval_base_place cx t s = (INL (PlaceR (StoragePlace tr slot tv)),s') ==>
    storage_read_live cx tr (get_storage cx s' tr) slot tv
Proof
  measureInduct_on `base_assignment_target_size t` >> Cases_on `t` >>
  rpt gen_tac
  >~ [`TopLevelNameTarget p`]
  >- (PairCases_on `p` >>
      simp[target_indices_def, Once evaluate_def, bind_def, AllCaseEqs(),
           return_def, raise_def] >> rpt strip_tac >> gvs[] >>
      drule vyperStoragePlaceProvenanceTheory.lookup_global_storage_region >>
      strip_tac >>
      irule accountsRelPropsTheory.declared_storage_region_read_live >>
      goal_assum (drule_at Any)) >>
  simp[target_indices_def, Once evaluate_def, bind_def, AllCaseEqs(),
       get_scopes_def, type_check_def, assert_def, ignore_bind_def,
       return_def, raise_def] >> rpt strip_tac >> gvs[] >>
  qpat_x_assum `!y. _` (qspec_then `b` mp_tac) >>
  simp[expr_size_def] >> strip_tac
  >- (rename1 `eval_expr cx e s'' = (INL result,s3)` >>
      `!tr. get_storage cx s3 tr = get_storage cx s'' tr` by
        metis_tac[aug_place_pure_eval_storage] >>
      drule read_result_state >> strip_tac >> gvs[] >>
      drule vyperStoragePlaceProvenanceTheory.eval_base_place_region >> strip_tac >>
      Cases_on `pv`
      >- (qpat_x_assum `extend_place _ _ _ _ = _` mp_tac >>
          simp[extend_place_def, raise_def])
      >- (Cases_on `p` >>
          gvs[extend_place_def, bind_def, ignore_bind_def, return_def,
              extend_memory_place_def, AllCaseEqs()] >>
          first_x_assum drule_all >> strip_tac >>
          drule_at (Pat `extend_storage_place _ _ _ _ _ _ = _`)
            aug_place_storage_extend_live_all >>
          (impl_tac >- metis_tac[]) >> simp[]) >>
      gvs[vyperStoragePlaceProvenanceTheory.storage_result_region_def] >>
      irule aug_place_mapping_extend_live >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
  drule vyperStoragePlaceProvenanceTheory.eval_base_place_region >> strip_tac >>
  (Cases_on `pv`
  >- (qpat_x_assum `extend_place _ _ _ _ = _` mp_tac >>
      simp[extend_place_def, raise_def])
  >- (Cases_on `p` >>
      gvs[extend_place_def, bind_def, ignore_bind_def, return_def,
          extend_memory_place_def, AllCaseEqs()]
      >> first_x_assum drule_all >> strip_tac >>
      drule_all aug_place_storage_extend_live_all >> simp[]) >>
  gvs[vyperStoragePlaceProvenanceTheory.storage_result_region_def] >>
  irule aug_place_mapping_extend_live >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any))
QED

Theorem aug_place_pure_target_storage_live:
  EVERY (supported_pure_expr tops) (target_indices t) /\
  eval_target_place cx t s = (INL (StoragePlace tr slot tv),s') ==>
  storage_read_live cx tr (get_storage cx s' tr) slot tv
Proof
  simp[Once evaluate_def, bind_def, AllCaseEqs()] >> rpt strip_tac >>
  Cases_on `pv` >> gvs[get_place_def, return_def, raise_def] >>
  drule_all aug_place_pure_base_storage_live >> simp[]
QED

Theorem aug_place_storage_load_ready:
  target_post ctx func cenv cx es sa sb s0 st
    (PlaceR (StoragePlace tr slot tv)) (Type ty) r vs /\
  read_place cx (StoragePlace tr slot tv) st = (INL cur,stc) /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  slots_in_range (get_storage cx st tr) (w2n slot) tv /\
  storage_read_live cx tr (get_storage cx st tr) slot tv ==>
  (if tr then tload slot vs else sload slot vs) = typed_val_to_w256 tv cur
Proof
  strip_tac >> drule read_place_state >> strip_tac >> gvs[] >>
  `read_storage_slot cx tr slot tv st = (INL cur,st)` by
    gvs[read_place_def] >>
  `storage_agree (storage_dead cx tr (get_storage cx st tr))
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
     simp[] >> qexistsl_tac [`cx`, `tr`] >> simp[]) >>
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
  storage_read_live cx tr (get_storage cx st tr) slot tv /\
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
          drule_all aug_place_pure_base_storage_live >> strip_tac >>
          drule_at (Pat `extend_storage_place _ _ _ _ _ _ = _`)
            aug_place_storage_extend_range >>
          (impl_tac >- simp[]) >> simp[]) >>
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
      drule_all aug_place_pure_base_storage_live >> strip_tac >>
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


Theorem aug_place_storage_entry_pre[local]:
  expr_body_pre cenv cx env e es ==>
  expr_body_pre cenv cx env e (es with gas_obs := gs)
Proof
  simp[expr_body_pre_gas_obs]
QED

(* x op= e at a field or element of a storage or transient variable,
   with pure indices. *)
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

Theorem aug_place_supported_storage_kind[local]:
  body_inv tops ctx cenv cx /\
  supported_target_info tops bindings t = SOME pt /\
  (!id. target_root t <> NameTarget id) /\
  eval_target_place cx t es = (INL p,st) ==>
  ?tr slot tv. p = StoragePlace tr slot tv
Proof
  strip_tac >> drule_all aug_place_supported_success_kind >>
  metis_tac[aug_place_target_memory_origin]
QED

Theorem aug_place_storage_rhs_pre[local]:
  target_pre cenv cx env bt es /\
  expr_body_pre cenv cx env e es /\
  eval_base_place cx bt es = (res,st) ==>
  expr_body_pre cenv cx env e st
Proof
  strip_tac >> drule_all eval_base_place_sim_inv >>
  gvs[expr_body_pre_def]
QED

Theorem aug_place_storage_read_ready[local]:
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

Theorem aug_place_storage_target_ready[local]:
  body_inv tops ctx cenv cx /\
  supported_target_info tops bindings bt = SOME pt /\
  (!id. target_root bt <> NameTarget id) /\
  eval_base_place cx bt es = (INL pv,st) /\
  target_post ctx func cenv cx es sa sb s0 st pv (Type ty) r s ==>
  ?tr slot tv.
    pv = PlaceR (StoragePlace tr slot tv) /\
    eval_target_place cx bt es = (INL (StoragePlace tr slot tv),st) /\
    eval_operand (FST r) s = SOME slot /\
    FST (SND r) = SOME (slot_loc tr) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    stmt_state_rel ctx func cenv cx st s /\
    SND (SND r) = SOME (value_type_place (Type ty)) /\
    (!x. FST r = Var x ==> not_fresh_at sb x)
Proof
  strip_tac >>
  `?p. pv = PlaceR p` by
    (gvs[target_post_def] >> Cases_on `pv` >>
     gvs[place_ptr_rel_def] >> Cases_on `p` >>
     gvs[place_ptr_rel_def]) >>
  gvs[] >>
  `eval_target_place cx bt es = (INL p,st)` by
    simp[Once evaluate_def, bind_def, get_place_def, return_def] >>
  drule_all aug_place_supported_storage_kind >> strip_tac >>
  gvs[target_post_def, place_ptr_rel_def] >> metis_tac[]
QED

Theorem aug_place_storage_source_ready[local]:
  target_pre cenv cx env bt es /\
  expr_body_pre cenv cx env e es /\
  EVERY (supported_pure_expr tops) (target_indices bt) /\
  eval_base_place cx bt es = (INL (PlaceR (StoragePlace tr slot tv)),st) /\
  evaluate_type (get_tenv cx) ty = SOME tv ==>
  ?cur.
    eval_target_place cx bt es = (INL (StoragePlace tr slot tv),st) /\
    read_place cx (StoragePlace tr slot tv) st = (INL cur,st) /\
    place_type_value cx (StoragePlace tr slot tv) st = (INL tv,st) /\
    value_has_type tv cur /\
    expr_body_pre cenv cx env e st
Proof
  strip_tac >>
  `eval_target_place cx bt es = (INL (StoragePlace tr slot tv),st)` by
    simp[Once evaluate_def, bind_def, get_place_def, return_def] >>
  `contract_storage_well_formed cx es` by
    gvs[target_pre_def, expr_sim_inv_def] >>
  drule_all aug_place_pure_target_storage_range >> strip_tac >>
  drule_all aug_place_storage_read_ready >> strip_tac >>
  drule_all aug_place_storage_rhs_pre >> strip_tac >>
  metis_tac[]
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
  Cases_on `tr` >>
  simp[venomInstTheory.is_terminator_def,
       venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_read1_def, venomInstTheory.mk_inst_def]
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
  stmt_state_rel ctx func cenv cx st s /\ local_ptrs_reserved cenv sa ==>
  stmt_state_rel ctx func cenv cx st
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

Theorem aug_place_storage_load_pointer[local]:
  eval_operand arg s = SOME slot /\ fresh_vars_wrt sa s ==>
  eval_operand arg
    ((update_var (STRING #"%" (toString sa.cs_next_var)) w s)
       with vs_inst_idx := SUC s.vs_inst_idx) = SOME slot
Proof
  strip_tac >>
  `eval_operand arg (update_var (STRING #"%" (toString sa.cs_next_var)) w s) = SOME slot` by
    (irule emitHelperPropsTheory.eval_operand_update_fresh >>
     goal_assum (drule_at Any) >> qexistsl_tac [`sa.cs_next_var`, `sa`] >> simp[]) >>
  Cases_on `arg` >>
  gvs[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def]
QED

Theorem aug_place_storage_load_counted[local]:
  emit_op (if tr then TLOAD else SLOAD) [arg] sa = (op,sb) /\
  fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand arg s = SOME slot /\ fresh_vars_wrt sa s /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx st s /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  (if tr then tload slot s else sload slot s) = typed_val_to_w256 tv cur ==>
  ?u. gas_path ctx func s 0 (OK u) /\
      expr_val_rel cx ty cur op u /\
      stmt_state_rel ctx func cenv cx st u /\
      eval_operand arg u = SOME slot /\ fresh_vars_wrt sb u /\
      ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
             lookup_var x u = SOME w) /\
      u.vs_allocas = s.vs_allocas
Proof
  strip_tac >>
  qexists_tac `(update_var (STRING #"%" (toString sa.cs_next_var))
    (typed_val_to_w256 tv cur) s) with vs_inst_idx := SUC s.vs_inst_idx` >>
  conj_tac >- metis_tac[aug_place_storage_load_path] >>
  conj_tac >- metis_tac[aug_place_storage_load_value] >>
  conj_tac >- metis_tac[aug_place_storage_load_state] >>
  conj_tac >- metis_tac[aug_place_storage_load_pointer] >>
  conj_tac
  >- (gvs[emitHelperTheory.emit_op_def, comp_bind_def, fresh_var_def,
          fresh_id_def, comp_ignore_bind_def, comp_return_def, emit_def] >>
      gvs[fresh_vars_wrt_def, venomStateTheory.update_var_def]) >>
  drule_all aug_place_storage_load_endpoint >>
  disch_then (qspec_then `typed_val_to_w256 tv cur` mp_tac) >>
  simp[venomStateTheory.update_var_def] >> metis_tac[]
QED

Theorem aug_place_storage_load_counted_nofresh[local]:
  emit_op (if tr then TLOAD else SLOAD) [arg] sa = (op,sb) /\
  fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand arg s = SOME slot /\
  (!x. arg = Var x ==> not_fresh_at sa x) /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx st s /\
  is_word_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  (if tr then tload slot s else sload slot s) = typed_val_to_w256 tv cur ==>
  ?u. gas_path ctx func s 0 (OK u) /\
      expr_val_rel cx ty cur op u /\
      stmt_state_rel ctx func cenv cx st u /\
      eval_operand arg u = SOME slot /\
      ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (!x w. not_fresh_at sa x /\ lookup_var x s = SOME w ==>
             lookup_var x u = SOME w) /\
      u.vs_allocas = s.vs_allocas
Proof
  strip_tac >>
  qexists_tac `(update_var (STRING #"%" (toString sa.cs_next_var))
    (typed_val_to_w256 tv cur) s) with vs_inst_idx := SUC s.vs_inst_idx` >>
  conj_tac >- metis_tac[aug_place_storage_load_path] >>
  conj_tac >- metis_tac[aug_place_storage_load_value] >>
  conj_tac >- metis_tac[aug_place_storage_load_state] >>
  drule_all aug_place_storage_load_endpoint >>
  disch_then (qspec_then `typed_val_to_w256 tv cur` mp_tac) >>
  simp[venomStateTheory.update_var_def] >> strip_tac >>
  conj_tac >- (Cases_on `arg` >>
    fs[venomStateTheory.eval_operand_def, venomStateTheory.lookup_var_def] >>
    metis_tac[]) >> simp[] >> metis_tac[]
QED

Theorem aug_place_static_store_exit[local]:
  emit_void (if tr then TSTORE else SSTORE) [dst;op] sa = ((),sb) /\
  fn_has_code sa sb func /\
  eval_operand dst s = SOME slot /\ eval_operand op s = SOME w /\
  s.vs_call_ctx.cc_static /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?r. gas_marked_path F ctx func s 0 r /\ exit_result r /\
      stmt_exit RetQ ee (INR (Error (RuntimeError "write in static context"))) r
Proof
  strip_tac >>
  drule emitHelperPropsTheory.emitted_insts_emit_void >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb` by
    gvs[emitHelperTheory.emit_void_def, comp_bind_def, fresh_id_def, emit_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sa.cs_current_insts) =
     SOME (mk_inst sa.cs_next_id (if tr then TSTORE else SSTORE) [dst;op] [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  qexists_tac `Abort ExHalt_abort (halt_state (set_returndata [] s))` >>
  simp[stmt_exit_def, expr_exit_def, exit_result_def] >>
  `gas_marked_path F ctx func s
     (if (mk_inst sa.cs_next_id (if tr then TSTORE else SSTORE) [dst;op] []).inst_opcode = GAS then 1 else 0)
     (Abort ExHalt_abort (halt_state (set_returndata [] s)))` by
    (irule fragGasSeqAbortTheory.gas_marked_path_abort >>
     Cases_on `tr` >>
     simp[venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def,
          venomExecSemanticsTheory.step_inst_base_def,
          venomStateTheory.eval_operands_def]) >>
  Cases_on `tr` >> gvs[venomInstTheory.mk_inst_def]
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

Theorem aug_place_storage_store_outcome[local]:
  emit_void (case slot_loc tr of LocStorage => SSTORE | LocTransient => TSTORE
                       | _ => MSTORE) [dst;op] sa = ((),sb) /\
  eval_operand dst s = SOME w /\
  place_ptr_rel cenv cx s (PlaceR (StoragePlace tr slot tv)) w
    (SOME (slot_loc tr)) (Type ty) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  is_word_type ty /\ expr_val_rel cx ty v op s /\
  expr_sim_inv cenv cx env ee /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  local_ptrs_reserved cenv sa /\
  storage_place_region cx (StoragePlace tr slot tv) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
  stmt_state_rel ctx func cenv cx ee s /\
  write_place cx (StoragePlace tr slot tv) v ee = (res,ff) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?r. gas_marked_path F ctx func s 0 r /\
      ((?t. r = OK t /\ res = INL () /\
          stmt_state_rel ctx func cenv cx ff t /\
          (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
          (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                   FLOOKUP t.vs_allocas aid = SOME b) /\
          ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts) \/
       (exit_result r /\ stmt_exit RetQ ff res r))
Proof
  strip_tac >>
  `~cx.txn.is_static` by fs[stmt_state_rel_def, state_rel_def] >>
  drule_all aug_place_storage_write_outcome >> strip_tac >> gvs[] >>
  drule_at (Pat `write_place _ _ _ _ = _`) place_store_word_run >>
  simp[] >> disch_then drule_all >> strip_tac >>
  qexists_tac `OK t` >> simp[]
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

Theorem aug_place_storage_write_gas_obs[local]:
  write_place cx (StoragePlace tr slot tv) v ee = (res,fin) ==>
  !gs. write_place cx (StoragePlace tr slot tv) v (ee with gas_obs := gs) =
    (res,fin with gas_obs := gs)
Proof
  simp[write_place_def, ignore_bind_def, bind_def, return_def,
       stmtSimAssignStorageTheory.write_storage_slot_gas_obs,
       AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem aug_place_storage_error_exec[local]:
  evaluate_binop bound tv bop cur v = INR err /\
  gas_marked_path F ctx func z 0 r ==>
  gas_marked_exec F (ctx,func)
    (bind (lift_sum (evaluate_binop bound tv bop cur v))
      (write_place cx (StoragePlace tr slot tv)))
    (ee,z) [] (INR (Error err)) ee r
Proof
  simp[gasSummaryTheory.gas_marked_exec_def, bind_def, lift_sum_def, raise_def]
QED

Theorem aug_place_storage_write_exec[local]:
  evaluate_binop bound tv bop cur v = INL w /\
  write_place cx (StoragePlace tr slot tv) w ee = (res,fin) /\
  gas_marked_path F ctx func z 0 r ==>
  gas_marked_exec F (ctx,func)
    (bind (lift_sum (evaluate_binop bound tv bop cur v))
      (write_place cx (StoragePlace tr slot tv)))
    (ee,z) [] res fin r
Proof
  strip_tac >> simp[gasSummaryTheory.gas_marked_exec_def, bind_def, lift_sum_def, return_def] >>
  metis_tac[aug_place_storage_write_gas_obs]
QED

Theorem aug_place_storage_rhs_exception_exec[local]:
  gas_marked_exec F (ctx,func) (bind (eval_expr cx e) (read_result cx))
    (st,u) marks (INR ex) ee r ==>
  gas_marked_exec F (ctx,func)
    (bind (eval_expr cx e) (\raw. bind (read_result cx raw)
      (\v. bind (lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        tv bop cur v)) (write_place cx (StoragePlace tr slot tv)))))
    (st,u) marks (INR ex) ee r
Proof
  rewrite_tac[aug_place_storage_suffix_assoc] >>
  metis_tac[gasSummaryComposeTheory.gas_marked_exec_bind_exception]
QED

Theorem aug_place_storage_rhs_normal_exec[local]:
  gas_marked_exec F (ctx,func) (bind (eval_expr cx e) (read_result cx))
    (st,u) marks (INL v) ee (OK z) /\
  gas_marked_exec F (ctx,func)
    (bind (lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      tv bop cur v)) (write_place cx (StoragePlace tr slot tv)))
    (ee with gas_obs := [],z) [] res fin r ==>
  gas_marked_exec F (ctx,func)
    (bind (eval_expr cx e) (\raw. bind (read_result cx raw)
      (\v. bind (lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        tv bop cur v)) (write_place cx (StoragePlace tr slot tv)))))
    (st,u) marks res fin r
Proof
  rewrite_tac[aug_place_storage_suffix_assoc] >> strip_tac >>
  irule (SRULE [] (Q.INST [`right` |-> `[]`]
    gasSummaryComposeTheory.gas_marked_exec_bind_normal)) >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem aug_place_storage_rhs_admissible[local]:
  gas_admissible
    (bind (eval_expr cx e) (\raw. bind (read_result cx raw)
      (\v. bind (lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        tv bop cur v)) (write_place cx (StoragePlace tr slot tv)))))
    (stmt_res_ok lctx) st ==>
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok st
Proof
  rewrite_tac[aug_place_storage_suffix_assoc] >> strip_tac >>
  rw[gasContextTheory.gas_admissible_def] >>
  Cases_on `res` >- simp[expr_res_ok_def] >>
  `no_control_exc y` by
    (qpat_x_assum `bind _ _ _ = (INR y,_)` mp_tac >>
     simp[NoAsms, bind_def, AllCaseEqs()] >> strip_tac >>
     metis_tac[cj 1 vyperExprNoControlTheory.eval_expr_no_control,
               vyperExprNoControlTheory.read_result_no_control]) >>
  qpat_x_assum `gas_admissible _ _ _` mp_tac >>
  simp[gasContextTheory.gas_admissible_def] >>
  disch_then (qspec_then `gs` mp_tac) >> simp[bind_def] >>
  Cases_on `y` >> gvs[vyperExprNoControlTheory.no_control_exc_def, stmt_res_ok_def, expr_res_ok_def]
QED

Theorem aug_place_storage_binop_admissible[local]:
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
  `bop_result cx ty bop [ty;expr_type e] cur v ee =
     case evaluate_binop
       (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
       tv bop cur v of INL w => INL w | INR err => INR (Error err)` by
    (irule bop_result_augassign >> simp[]) >>
  Cases_on `evaluate_binop
    (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
    tv bop cur v` >- simp[expr_res_ok_def] >>
  qpat_x_assum `gas_admissible _ _ _` mp_tac >>
  simp[gasContextTheory.gas_admissible_def] >>
  disch_then (qspec_then `gs` mp_tac) >>
  simp[bind_def, lift_sum_def, raise_def, stmt_res_ok_def, expr_res_ok_def]
QED

Theorem aug_place_storage_rhs_exempt[local]:
  gas_exempt_cert F tops (ctx,func)
    (ignore_bind (bind (eval_expr cx e) (read_result cx)) (return ()))
    (st,u) marks (err,ee) (leaf,finstate) ==>
  gas_exempt_cert F tops (ctx,func)
    (ignore_bind
      (bind (eval_expr cx e) (\raw. bind (read_result cx raw)
        (\v. bind (lift_sum (evaluate_binop
          (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
          tv bop cur v)) (write_place cx (StoragePlace tr slot tv)))))
      (return ())) (st,u) marks (err,ee) (leaf,finstate)
Proof
  rewrite_tac[aug_place_storage_suffix_assoc] >> strip_tac >>
  rewrite_tac[ignore_bind_def] >>
  once_rewrite_tac[bind_assoc] >>
  irule gasExemptCertTheory.gas_exempt_cert_error_value >> simp[]
QED

Theorem aug_place_storage_binop_store_nofresh[local]:
  compile_binop bop cur_op rhs_op ty NONE
    (if bop = Exp then expr_int_literal e else NONE) s2 = (out,s3) /\
  emit_void (if tr then TSTORE else SSTORE) [dst;out] s3 = ((),sf) /\
  fn_has_code s2 s3 func /\ fn_has_code s3 sf func /\
  fn_inst_ids_distinct func /\
  binop_frag ctx func cenv cx bop ty ty NONE
    (if bop = Exp then expr_int_literal e else NONE) [ty;expr_type e] cur v ee /\
  expr_res_ok (bop_result cx ty bop [ty;expr_type e] cur v ee) /\
  bop <> In /\ bop <> NotIn /\ word_value_type ty /\
  word_value cur /\ word_value v /\
  eval_operand cur_op z = SOME (val_to_w256 cur) /\
  eval_operand rhs_op z = SOME (val_to_w256 v) /\
  (!x. cur_op = Var x ==> not_fresh_at s2 x) /\
  (!x. rhs_op = Var x ==> not_fresh_at s2 x) /\
  eval_operand dst z = SOME slot /\ (!l. dst <> Label l) /\
  (!x. dst = Var x ==> not_fresh_at s2 x) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  (!w. evaluate_binop
    (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
    tv bop cur v = INL w ==> value_has_type tv w) /\
  expr_sim_inv cenv cx env ee /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  local_ptrs_reserved cenv s2 /\
  storage_place_region cx (StoragePlace tr slot tv) /\
  stmt_state_rel ctx func cenv cx ee z /\
  ~z.vs_halted /\ z.vs_current_bb = s2.cs_current_bb /\
  z.vs_inst_idx = LENGTH s2.cs_current_insts ==>
  ?res fin r. gas_marked_exec F (ctx,func)
    (bind (lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      tv bop cur v)) (write_place cx (StoragePlace tr slot tv)))
    (ee,z) [] res fin r /\
    ((?last. r = OK last /\
        stmt_post ctx func cx lctx cenv cenv s2 sf z res
          (fin with gas_obs := []) last) \/
     (exit_result r /\ stmt_exit RetQ (fin with gas_obs := []) res r))
Proof
  strip_tac >>
  `bop_result cx ty bop [ty;expr_type e] cur v ee =
   case evaluate_binop
     (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
     tv bop cur v of INL w => INL w | INR err => INR (Error err)` by
    (irule bop_result_augassign >> simp[]) >>
  qpat_x_assum `binop_frag _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[exprBopSimDefsTheory.binop_frag_def,
              exprBopSimDefsTheory.binop_frag_words_def] >>
  disch_then drule >> simp[] >>
  disch_then (qspec_then `z` mp_tac) >> simp[] >> strip_tac
  >- suspend "normal"
  >> suspend "exit"
QED

Resume aug_place_storage_binop_store_nofresh[normal]:
  gvs[AllCaseEqs()] >>
  qpat_x_assum `_ = bop_result _ _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `expr_res_ok _` kall_tac >>
  drule compile_binop_grows >> strip_tac >>
  `eval_operand dst s = SOME slot` by
    (irule exprBopSimPropsTheory.eval_operand_frame >> simp[] >>
     qexistsl_tac [`s2`, `z`] >> simp[]) >>
  `local_ptrs_reserved cenv s3` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `!x. dst = Var x ==> not_fresh_at s3 x` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `is_word_type ty` by metis_tac[word_value_type_word] >>
  `expr_val_rel cx ty v' out s` by
    simp[expr_val_rel_def, typed_val_to_w256_word_value] >>
  `place_ptr_rel cenv cx s (PlaceR (StoragePlace tr slot tv)) slot
     (SOME (slot_loc tr)) (Type ty)` by simp[place_ptr_rel_def] >>
  Cases_on `write_place cx (StoragePlace tr slot tv) v' ee` >>
  `emit_void (case slot_loc tr of LocStorage => SSTORE |
     LocTransient => TSTORE | _ => MSTORE) [dst;out] s3 = ((),sf)` by
    (Cases_on `tr` >> gvs[slot_loc_def]) >>
  drule_all aug_place_storage_store_outcome >>
  disch_then (qspec_then `RetQ` strip_assume_tac)
  >- (gvs[] >>
      `gas_marked_path F ctx func z 0 (OK t)` by
        metis_tac[fragGasModeTheory.gas_marked_path_then, arithmeticTheory.ADD] >>
      qexistsl_tac [`INL ()`, `r`, `OK t`] >>
      conj_tac >-
        (simp[gasSummaryTheory.gas_marked_exec_def, bind_def,
              lift_sum_def, return_def] >>
         metis_tac[aug_place_storage_write_gas_obs]) >>
      simp[] >>
      `~block_is_terminated sf` by
        (drule stmtSimDeclMemTheory.emit_void_nonterminator_open >>
         Cases_on `tr` >> simp[slot_loc_def, venomInstTheory.is_terminator_def]) >>
      simp[stmt_post_def, stmt_lands_def] >>
      disj1_tac >> simp[cenv_top_ext_refl] >>
      metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  drule_all aug_place_storage_write_outcome >> strip_tac >>
  gvs[stmt_exit_def, expr_exit_def] >>
  fs[stmt_state_rel_def, state_rel_def]
QED

Resume aug_place_storage_binop_store_nofresh[exit]:
  Cases_on `evaluate_binop
    (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
    tv bop cur v` >> gvs[expr_exit_def] >>
  rename1 `expr_exit (INR (Error err)) r` >>
  qexistsl_tac [`INR (Error err)`, `ee`, `r`] >>
  simp[gasSummaryTheory.gas_marked_exec_def, bind_def, lift_sum_def,
       raise_def, stmt_exit_def] >>
  disj2_tac >> Cases_on `err` >> Cases_on `r` >> gvs[expr_exit_def]
QED

Finalise aug_place_storage_binop_store_nofresh

Theorem aug_place_storage_binop_store[local]:
  compile_binop bop cur_op rhs_op ty NONE
    (if bop = Exp then expr_int_literal e else NONE) s2 = (out,s3) /\
  emit_void (if tr then TSTORE else SSTORE) [dst;out] s3 = ((),sf) /\
  fn_has_code s2 s3 func /\ fn_has_code s3 sf func /\
  fn_inst_ids_distinct func /\
  binop_frag ctx func cenv cx bop ty ty NONE
    (if bop = Exp then expr_int_literal e else NONE) [ty;expr_type e] cur v ee /\
  expr_res_ok (bop_result cx ty bop [ty;expr_type e] cur v ee) /\
  bop <> In /\ bop <> NotIn /\ word_value_type ty /\
  word_value cur /\ word_value v /\
  eval_operand cur_op z = SOME (val_to_w256 cur) /\
  eval_operand rhs_op z = SOME (val_to_w256 v) /\
  (!x. cur_op = Var x ==> not_fresh_at s2 x) /\
  (!x. rhs_op = Var x ==> not_fresh_at s2 x) /\
  eval_operand dst z = SOME slot /\ (!l. dst <> Label l) /\
  (!x. dst = Var x ==> not_fresh_at s2 x) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  (!w. evaluate_binop
    (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
    tv bop cur v = INL w ==> value_has_type tv w) /\
  expr_sim_inv cenv cx env ee /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  local_ptrs_reserved cenv s2 /\
  storage_place_region cx (StoragePlace tr slot tv) /\
  stmt_state_rel ctx func cenv cx ee z /\ fresh_vars_wrt s2 z /\
  ~z.vs_halted /\ z.vs_current_bb = s2.cs_current_bb /\
  z.vs_inst_idx = LENGTH s2.cs_current_insts ==>
  ?res fin r. gas_marked_exec F (ctx,func)
    (bind (lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      tv bop cur v)) (write_place cx (StoragePlace tr slot tv)))
    (ee,z) [] res fin r /\
    ((?last. r = OK last /\
        stmt_post ctx func cx lctx cenv cenv s2 sf z res
          (fin with gas_obs := []) last) \/
     (exit_result r /\ stmt_exit RetQ (fin with gas_obs := []) res r))
Proof
  strip_tac >> drule_all aug_place_storage_binop_store_nofresh >> simp[]
QED

Theorem aug_place_storage_rhs_success[local]:
  expr_body_pre cenv cx env e st /\
  bind (eval_expr cx e) (read_result cx) st = (INL v,fin) ==>
  expr_sim_inv cenv cx env fin /\ expr_result_typed env e (Value v)
Proof
  metis_tac[exprSimSourceTheory.expr_body_pre_eval]
QED

Theorem aug_place_storage_rhs_success_gas[local]:
  expr_body_pre cenv cx env e st /\
  bind (eval_expr cx e) (read_result cx) (st with gas_obs := gs) = (INL v,fin) ==>
  expr_sim_inv cenv cx env fin /\ expr_result_typed env e (Value v)
Proof
  metis_tac[aug_place_storage_rhs_success, expr_body_pre_gas_obs]
QED

Theorem aug_place_storage_suffix_outcome_nofresh[local]:
  lower_value compile_expr cenv ty e s1 = (rhs_op,s2) /\
  compile_binop bop cur_op rhs_op ty NONE
    (if bop = Exp then expr_int_literal e else NONE) s2 = (out,s3) /\
  emit_void (if tr then TSTORE else SSTORE) [dst;out] s3 = ((),sf) /\
  fn_has_code s1 s2 func /\ fn_has_code s2 s3 func /\
  fn_has_code s3 sf func /\ fn_inst_ids_distinct func /\
  type_stmt env ret_ty (AugAssign ty bt bop e) = SOME env' /\
  type_bits ty MOD 8 = 0 /\
  word_value_type ty /\ word_value_type (expr_type e) /\
  bop <> In /\ bop <> NotIn /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv cur /\
  word_value cur /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tvrhs /\
  (!v w. value_has_type tvrhs v /\
    evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      tv bop cur v = INL w ==> value_has_type tv w) /\
  expr_body_pre cenv cx env e st /\
  expr_sim ctx func cenv cx ty e st /\
  gas_admissible
    (bind (eval_expr cx e) (\raw. bind (read_result cx raw)
      (\v. bind (lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        tv bop cur v)) (write_place cx (StoragePlace tr slot tv)))))
    (stmt_res_ok lctx) st /\
  eval_operand cur_op u = SOME (val_to_w256 cur) /\
  (!x. cur_op = Var x ==> not_fresh_at s1 x) /\
  (!l. cur_op <> Label l) /\
  eval_operand dst u = SOME slot /\
  (!x. dst = Var x ==> not_fresh_at s1 x) /\
  (!l. dst <> Label l) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  local_ptrs_reserved cenv s1 /\
  storage_place_region cx (StoragePlace tr slot tv) /\
  stmt_state_rel ctx func cenv cx st u /\
  ~u.vs_halted /\ u.vs_current_bb = s1.cs_current_bb /\
  u.vs_inst_idx = LENGTH s1.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (eval_expr cx e) (\raw. bind (read_result cx raw)
      (\v. bind (lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        tv bop cur v)) (write_place cx (StoragePlace tr slot tv))))) (st,u)
    (stmt_post ctx func cx lctx cenv cenv s1 sf u)
    (\res fin r. !tail. stmt_exit RetQ (fin with gas_obs := tail) res r)
Proof
  strip_tac >>
  drule aug_place_storage_rhs_admissible >> strip_tac >>
  qpat_x_assum `expr_sim _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[expr_sim_def] >> disch_then drule >> simp[] >>
  disch_then (qspec_then `u` mp_tac) >> simp[] >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >>
  disch_then (qx_choose_then `marks` strip_assume_tac)
  >- suspend "summary"
  >> qexists_tac `marks` >> disj2_tac >>
  metis_tac[aug_place_storage_rhs_exempt]
QED

Resume aug_place_storage_suffix_outcome_nofresh[summary]:
  qexists_tac `marks` >> disj1_tac >>
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[gasSummaryTheory.gas_summary_at_def] >> strip_tac
  >- suspend "normal"
  >> suspend "exception"
QED

Resume aug_place_storage_suffix_outcome_nofresh[exception]:
  Cases_on `res` >> gvs[expr_exit_def] >>
  qexistsl_tac [`INR y`, `es_end`, `r`] >>
  conj_tac >- (irule aug_place_storage_rhs_exception_exec >> simp[]) >>
  simp[stmt_exit_def] >> disj2_tac >>
  Cases_on `y` >> Cases_on `r` >> gvs[expr_exit_def] >>
  rename1 `Error err` >> Cases_on `err` >> gvs[expr_exit_def]
QED

Resume aug_place_storage_suffix_outcome_nofresh[normal]:
  gvs[] >>
  `bind (eval_expr cx e) (read_result cx)
     (st with gas_obs := gas_explicit marks u.vs_gas_readings) =
     (INL v,es_end with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gasSummaryTheory.gas_marked_exec_def] >>
     disch_then (qspec_then `[]` mp_tac o CONJUNCT1) >> simp[]) >>
  drule_all aug_place_storage_rhs_success_gas >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `value_has_type tvrhs v` by
    (gvs[vyperTypeExprResultTheory.expr_result_typed_def, expr_runtime_typed_def, value_result_typed_def] >> metis_tac[]) >>
  `word_value v` by metis_tac[word_value_type_typed] >>
  drule_all aug_place_storage_binop_admissible >> strip_tac >>
  `binop_frag ctx func cenv cx bop ty ty NONE
     (if bop = Exp then expr_int_literal e else NONE)
     [ty;expr_type e] cur v (es_end with gas_obs := [])` by
    (irule aug_place_binop_ready >> simp[] >> metis_tac[]) >>
  `eval_operand dst t = SOME slot /\
   eval_operand cur_op t = SOME (val_to_w256 cur)` by
    (fs[expr_post_def] >> conj_tac >>
     irule exprBopSimPropsTheory.eval_operand_frame >> simp[] >>
     qexistsl_tac [`s1`, `u`] >> simp[]) >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  `(!x. dst = Var x ==> not_fresh_at s2 x) /\
   (!x. cur_op = Var x ==> not_fresh_at s2 x)` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  `local_ptrs_reserved cenv s2` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `stmt_state_rel ctx func cenv cx (es_end with gas_obs := []) t` by
    fs[expr_post_def] >>
  `is_word_type (expr_type e)` by metis_tac[word_value_type_word] >>
  `post_value_type cenv e = expr_type e` by simp[] >>
  `eval_operand rhs_op t = SOME (val_to_w256 v)` by
    (fs[expr_post_def, expr_val_rel_def, typed_val_to_w256_word_value] >>
     metis_tac[]) >>
  `is_word_type (expr_type e)` by metis_tac[word_value_type_word] >>
  drule_all exprSimSourceTheory.expr_body_pre_lower_value_word_shape >> strip_tac >>
  `expr_sim_inv cenv cx env (es_end with gas_obs := [])` by
    simp[expr_sim_inv_gas_obs] >>
  `expr_res_ok (bop_result cx ty bop [ty;expr_type e] cur v
     (es_end with gas_obs := []))` by
    simp[exprBopSimPropsTheory.bop_result_gas_obs] >>
  `~t.vs_halted` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gasSummaryTheory.gas_marked_exec_def] >> strip_tac >>
     drule fragGasModeTheory.gas_marked_path_exec >>
     metis_tac[fragGasPathTheory.gas_path_normal]) >>
  `!w. evaluate_binop
     (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
     tv bop cur v = INL w ==> value_has_type tv w` by metis_tac[] >>
  drule_all aug_place_storage_binop_store_nofresh >>
  disch_then (qspecl_then [`lctx`, `\v es r. F`] strip_assume_tac)
  >- suspend "store_normal"
  >> suspend "store_exit"
QED

Resume aug_place_storage_suffix_outcome_nofresh[store_normal]:
  gvs[] >>
  drule_all aug_place_storage_rhs_normal_exec >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >>
  disj1_tac >>
  fs[stmt_post_def, expr_post_def] >>
  metis_tac[freshWritesTheory.not_fresh_at_mono]
QED

Resume aug_place_storage_suffix_outcome_nofresh[store_exit]:
  drule_all aug_place_storage_rhs_normal_exec >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >>
  disj2_tac >>
  fs[stmt_exit_def]
QED

Finalise aug_place_storage_suffix_outcome_nofresh

Theorem aug_place_storage_suffix_outcome[local]:
  lower_value compile_expr cenv ty e s1 = (rhs_op,s2) /\
  compile_binop bop cur_op rhs_op ty NONE
    (if bop = Exp then expr_int_literal e else NONE) s2 = (out,s3) /\
  emit_void (if tr then TSTORE else SSTORE) [dst;out] s3 = ((),sf) /\
  fn_has_code s1 s2 func /\ fn_has_code s2 s3 func /\
  fn_has_code s3 sf func /\ fn_inst_ids_distinct func /\
  type_stmt env ret_ty (AugAssign ty bt bop e) = SOME env' /\
  type_bits ty MOD 8 = 0 /\
  word_value_type ty /\ word_value_type (expr_type e) /\
  bop <> In /\ bop <> NotIn /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv cur /\
  word_value cur /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tvrhs /\
  (!v w. value_has_type tvrhs v /\
    evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      tv bop cur v = INL w ==> value_has_type tv w) /\
  expr_body_pre cenv cx env e st /\
  expr_sim ctx func cenv cx ty e st /\
  gas_admissible
    (bind (eval_expr cx e) (\raw. bind (read_result cx raw)
      (\v. bind (lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        tv bop cur v)) (write_place cx (StoragePlace tr slot tv)))))
    (stmt_res_ok lctx) st /\
  eval_operand cur_op u = SOME (val_to_w256 cur) /\
  (!x. cur_op = Var x ==> not_fresh_at s1 x) /\
  (!l. cur_op <> Label l) /\
  eval_operand dst u = SOME slot /\
  (!x. dst = Var x ==> not_fresh_at s1 x) /\
  (!l. dst <> Label l) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  local_ptrs_reserved cenv s1 /\
  storage_place_region cx (StoragePlace tr slot tv) /\
  stmt_state_rel ctx func cenv cx st u /\ fresh_vars_wrt s1 u /\
  ~u.vs_halted /\ u.vs_current_bb = s1.cs_current_bb /\
  u.vs_inst_idx = LENGTH s1.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (eval_expr cx e) (\raw. bind (read_result cx raw)
      (\v. bind (lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        tv bop cur v)) (write_place cx (StoragePlace tr slot tv))))) (st,u)
    (stmt_post ctx func cx lctx cenv cenv s1 sf u)
    (\res fin r. !tail. stmt_exit RetQ (fin with gas_obs := tail) res r)
Proof
  strip_tac >> drule_all aug_place_storage_suffix_outcome_nofresh >> simp[]
QED

Theorem aug_place_storage_target_bind[local]:
  eval_stmt cx (AugAssign ty bt bop e) =
  bind (eval_base_place cx bt) (\pv.
    bind (get_place pv) (\p.
    bind (read_place cx p) (\cur.
    bind (place_type_value cx p) (\tv.
    bind (eval_expr cx e) (\raw.
    bind (read_result cx raw) (\v.
    vyperState$bind (lift_sum (evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      tv bop cur v)) (\res. write_place cx p res)))))))
Proof
  simp[Once evaluate_def] >>
  simp[Once evaluate_def] >>
  simp[bind_assoc, ETA_AX]
QED

Theorem aug_place_storage_target_error[local]:
  eval_base_place cx bt es = (INR ex,st) ==>
  eval_stmt cx (AugAssign ty bt bop e) es = (INR ex,st)
Proof
  simp[aug_place_storage_target_bind, bind_def]
QED

Theorem aug_place_storage_target_exit[local]:
  expr_exit (INR ex) r ==>
  !tail. stmt_exit RetQ (fin with gas_obs := tail) (INR ex) r
Proof
  Cases_on `ex` >> Cases_on `r` >> simp[stmt_exit_def, expr_exit_def] >>
  rename1 `Error err` >> Cases_on `err` >> simp[stmt_exit_def, expr_exit_def]
QED

Theorem aug_place_storage_target_admissible[local]:
  gas_admissible (eval_stmt cx (AugAssign ty bt bop e)) (stmt_res_ok lctx) es ==>
  gas_admissible (eval_base_place cx bt) target_res_ok es
Proof
  rewrite_tac[gasContextTheory.gas_admissible_def] >>
  rpt strip_tac >> Cases_on `res`
  >- simp[targetPlaceSimDefsTheory.target_res_ok_def] >>
  drule aug_place_storage_target_error >>
  disch_then (qspecl_then [`ty`, `e`, `bop`] mp_tac) >>
  strip_tac >> first_x_assum drule >>
  simp[stmt_res_ok_def, targetPlaceSimDefsTheory.target_res_ok_def] >>
  drule vyperExprNoControlTheory.eval_base_place_no_control >>
  Cases_on `y` >> simp[vyperExprNoControlTheory.no_control_exc_def]
QED

Theorem aug_place_result_bind_outcome[local]:
  gas_outcome memory tops (ctx,func)
    (a : evaluation_state -> eval_result evaluation_result) (es,s0) P E /\
  (!v mid t. P (INL v) mid t ==>
    gas_outcome memory tops (ctx,func) (k v) (mid,t) Q R) /\
  (!ex mid t. P (INR ex) mid t ==> Q (INR ex) mid t) /\
  (!res mid r. E res mid r ==> ?ex. res = INR ex /\ R (INR ex) mid r) ==>
  gas_outcome memory tops (ctx,func) (bind a k) (es,s0) Q R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >>
  disch_then (qx_choose_then `left` strip_assume_tac)
  >- (gvs[gasSummaryTheory.gas_summary_at_def]
      >- (Cases_on `res` >- suspend "normal" >> suspend "error") >>
      suspend "exit") >> suspend "exempt"
QED

Resume aug_place_result_bind_outcome[normal]:
  first_x_assum drule >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >>
  disch_then (qx_choose_then `right` strip_assume_tac)
  >- (gvs[gasSummaryTheory.gas_summary_at_def] >>
      qexists_tac `left ++ right` >> disj1_tac >>
      simp[gasSummaryTheory.gas_summary_at_def] >>
      drule_all gasSummaryComposeTheory.gas_marked_exec_bind_normal >>
      metis_tac[]) >>
  qexists_tac `left ++ right` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  simp[ignore_bind_def, bind_assoc] >>
  irule (cj 6 gasExemptCertTheory.gas_exempt_cert_rules) >>
  simp[GSYM ignore_bind_def] >> metis_tac[]
QED
Resume aug_place_result_bind_outcome[error]:
  qexists_tac `left` >> disj1_tac >>
  simp[gasSummaryTheory.gas_summary_at_def] >>
  irule_at Any gasSummaryComposeTheory.gas_marked_exec_bind_exception >>
  goal_assum (drule_at Any) >> simp[]
QED
Resume aug_place_result_bind_outcome[exit]:
  first_x_assum drule >> strip_tac >> gvs[] >>
  qexists_tac `left` >> disj1_tac >>
  simp[gasSummaryTheory.gas_summary_at_def] >>
  irule_at Any gasSummaryComposeTheory.gas_marked_exec_bind_exception >>
  goal_assum (drule_at Any) >> simp[]
QED
Resume aug_place_result_bind_outcome[exempt]:
  qexists_tac `left` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  simp[ignore_bind_def, bind_assoc] >>
  irule (cj 7 gasExemptCertTheory.gas_exempt_cert_rules) >>
  simp[ignore_bind_def]
QED
Finalise aug_place_result_bind_outcome

Theorem aug_place_result_bind_outcome_exec[local]:
  gas_outcome memory tops (ctx,func)
    (a : evaluation_state -> eval_result evaluation_result) (es,s0) P E /\
  (!v mid t marks. P (INL v) mid t /\
    (!tail. a (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
      (INL v, mid with gas_obs := tail)) ==>
    gas_outcome memory tops (ctx,func) (k v) (mid,t) Q R) /\
  (!ex mid t. P (INR ex) mid t ==> Q (INR ex) mid t) /\
  (!res mid r. E res mid r ==> ?ex. res = INR ex /\ R (INR ex) mid r) ==>
  gas_outcome memory tops (ctx,func) (bind a k) (es,s0) Q R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >>
  disch_then (qx_choose_then `left` strip_assume_tac)
  >- (gvs[gasSummaryTheory.gas_summary_at_def]
      >- (Cases_on `res` >- suspend "normal" >> suspend "error") >>
      suspend "exit") >> suspend "exempt"
QED

Resume aug_place_result_bind_outcome_exec[normal]:
  `gas_outcome memory tops (ctx,func) (k x)
     (es_end with gas_obs := [],t) Q R` by
    (qpat_x_assum `!v mid t marks. _` (qspecl_then
       [`x`, `es_end with gas_obs := []`, `t`, `left`] mp_tac) >>
     fs[gasSummaryTheory.gas_marked_exec_def]) >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >>
  disch_then (qx_choose_then `right` strip_assume_tac)
  >- (gvs[gasSummaryTheory.gas_summary_at_def] >>
      qexists_tac `left ++ right` >> disj1_tac >>
      simp[gasSummaryTheory.gas_summary_at_def] >>
      drule_all gasSummaryComposeTheory.gas_marked_exec_bind_normal >>
      metis_tac[]) >>
  qexists_tac `left ++ right` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  simp[ignore_bind_def, bind_assoc] >>
  irule (cj 6 gasExemptCertTheory.gas_exempt_cert_rules) >>
  simp[GSYM ignore_bind_def] >> metis_tac[]
QED
Resume aug_place_result_bind_outcome_exec[error]:
  qexists_tac `left` >> disj1_tac >>
  simp[gasSummaryTheory.gas_summary_at_def] >>
  irule_at Any gasSummaryComposeTheory.gas_marked_exec_bind_exception >>
  goal_assum (drule_at Any) >> simp[]
QED
Resume aug_place_result_bind_outcome_exec[exit]:
  first_x_assum drule >> strip_tac >> gvs[] >>
  qexists_tac `left` >> disj1_tac >>
  simp[gasSummaryTheory.gas_summary_at_def] >>
  irule_at Any gasSummaryComposeTheory.gas_marked_exec_bind_exception >>
  goal_assum (drule_at Any) >> simp[]
QED
Resume aug_place_result_bind_outcome_exec[exempt]:
  qexists_tac `left` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  simp[ignore_bind_def, bind_assoc] >>
  irule (cj 7 gasExemptCertTheory.gas_exempt_cert_rules) >>
  simp[ignore_bind_def]
QED
Finalise aug_place_result_bind_outcome_exec

Theorem aug_place_result_bind_outcome_path[local]:
  gas_outcome memory tops (ctx,func)
    (a : evaluation_state -> eval_result evaluation_result) (es,s0) P E /\
  (!v mid t marks. P (INL v) mid t /\
    (!tail. a (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
      (INL v, mid with gas_obs := tail)) /\
    gas_marked_path memory ctx func s0 (LENGTH marks) (OK t) ==>
    gas_outcome memory tops (ctx,func) (k v) (mid,t) Q R) /\
  (!ex mid t. P (INR ex) mid t ==> Q (INR ex) mid t) /\
  (!res mid r. E res mid r ==> ?ex. res = INR ex /\ R (INR ex) mid r) ==>
  gas_outcome memory tops (ctx,func) (bind a k) (es,s0) Q R
Proof
  strip_tac >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >>
  disch_then (qx_choose_then `left` strip_assume_tac)
  >- (gvs[gasSummaryTheory.gas_summary_at_def]
      >- (Cases_on `res` >- suspend "normal" >> suspend "error") >>
      suspend "exit") >> suspend "exempt"
QED

Resume aug_place_result_bind_outcome_path[normal]:
  `gas_outcome memory tops (ctx,func) (k x)
     (es_end with gas_obs := [],t) Q R` by
    (qpat_x_assum `!v mid t marks. _` (qspecl_then
       [`x`, `es_end with gas_obs := []`, `t`, `left`] mp_tac) >>
     fs[gasSummaryTheory.gas_marked_exec_def]) >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >>
  disch_then (qx_choose_then `right` strip_assume_tac)
  >- (gvs[gasSummaryTheory.gas_summary_at_def] >>
      qexists_tac `left ++ right` >> disj1_tac >>
      simp[gasSummaryTheory.gas_summary_at_def] >>
      drule_all gasSummaryComposeTheory.gas_marked_exec_bind_normal >>
      metis_tac[]) >>
  qexists_tac `left ++ right` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  simp[ignore_bind_def, bind_assoc] >>
  irule (cj 6 gasExemptCertTheory.gas_exempt_cert_rules) >>
  simp[GSYM ignore_bind_def] >> metis_tac[]
QED
Resume aug_place_result_bind_outcome_path[error]:
  qexists_tac `left` >> disj1_tac >>
  simp[gasSummaryTheory.gas_summary_at_def] >>
  irule_at Any gasSummaryComposeTheory.gas_marked_exec_bind_exception >>
  goal_assum (drule_at Any) >> simp[]
QED
Resume aug_place_result_bind_outcome_path[exit]:
  first_x_assum drule >> strip_tac >> gvs[] >>
  qexists_tac `left` >> disj1_tac >>
  simp[gasSummaryTheory.gas_summary_at_def] >>
  irule_at Any gasSummaryComposeTheory.gas_marked_exec_bind_exception >>
  goal_assum (drule_at Any) >> simp[]
QED
Resume aug_place_result_bind_outcome_path[exempt]:
  qexists_tac `left` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  simp[ignore_bind_def, bind_assoc] >>
  irule (cj 7 gasExemptCertTheory.gas_exempt_cert_rules) >>
  simp[ignore_bind_def]
QED
Finalise aug_place_result_bind_outcome_path

Theorem aug_place_target_exempt_lift[local]:
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (eval_base_place cx bt) (return ()))
    start marks err endpoint ==>
  gas_exempt_cert memory tops (ctx,func)
    (ignore_bind (eval_stmt cx (AugAssign ty bt bop e)) (return ()))
    start marks err endpoint
Proof
  PairCases_on `start` >> PairCases_on `err` >> PairCases_on `endpoint` >>
  strip_tac >>
  simp[aug_place_storage_target_bind, ignore_bind_def, bind_assoc] >>
  irule (cj 7 gasExemptCertTheory.gas_exempt_cert_rules) >>
  simp[ignore_bind_def]
QED

Theorem aug_place_zero_prefix_outcome[local]:
  gas_marked_path F ctx func s0 0 (OK s1) /\
  gas_outcome F tops (ctx,func) source (es,s1) P E /\
  (!res mid t. P res mid t ==> Q res mid t) /\
  (!res mid r. E res mid r ==> R res mid r) ==>
  gas_outcome F tops (ctx,func) source (es,s0) Q R
Proof
  simp[gasOutcomeTheory.gas_outcome_def] >> strip_tac >>
  qexists_tac `marks`
  >- (disj1_tac >> fs[gasSummaryTheory.gas_summary_at_def] >>
      drule_all stmtSimDeclGasTheory.gas_marked_exec_zero_prefix >>
      metis_tac[]) >>
  disj2_tac >> qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  irule stmtSimDeclGasTheory.gas_exempt_cert_zero_prefix >>
  qexists_tac `s1` >> simp[]
QED

Theorem aug_place_stmt_post_prefix[local]:
  sa.cs_next_var <= sp.cs_next_var /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
    lookup_var x u = SOME w) /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
    FLOOKUP u.vs_allocas aid = SOME b) /\
  stmt_post ctx func cx lctx cenv cenv' sp sf u res ee t ==>
  stmt_post ctx func cx lctx cenv cenv' sa sf s0 res ee t
Proof
  rw[stmt_post_def] >> qexists_tac `cenv''` >> simp[] >>
  metis_tac[freshWritesTheory.not_fresh_at_mono]
QED

Theorem aug_place_bind_admissible_success[local]:
  gas_admissible (bind a k) admissible es /\
  (!tail. a (es with gas_obs := prefix ++ tail) =
    (INL v, mid with gas_obs := tail)) ==>
  gas_admissible (k v) admissible mid
Proof
  simp[gasContextTheory.gas_admissible_def] >> rpt strip_tac >>
  qpat_x_assum `!gs res ee. _`
    (qspec_then `prefix ++ gs` mp_tac) >>
  simp[bind_def] >> metis_tac[]
QED

Theorem aug_place_value_prefix_outcome[local]:
  (!gs. source (es with gas_obs := gs) =
    (INL (v:value), es with gas_obs := gs)) /\
  ~s.vs_halted /\
  gas_outcome F tops (ctx,func) (next v)
    (es with gas_obs := [],s) Q R ==>
  gas_outcome F tops (ctx,func) (bind source next) (es,s) Q R
Proof
  strip_tac >>
  `gas_marked_exec F (ctx,func) source (es,s) [] (INL v) es (OK s)` by
    (simp[gasSummaryTheory.gas_marked_exec_def,
          gasSummaryTheory.gas_explicit_def, fragGasModeTheory.gas_marked_path_def] >>
     irule (cj 1 fragGasPathTheory.gas_path_rules) >> simp[]) >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gasOutcomeTheory.gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      qpat_x_assum `gas_summary_at _ _ _ _ _ _ _` mp_tac >>
      rewrite_tac[gasSummaryTheory.gas_summary_at_def] >> strip_tac >>
      qexistsl_tac [`res`, `es_end`, `r`] >>
      (conj_tac
       >- (drule_all gasSummaryComposeTheory.gas_marked_exec_bind_normal >> simp[]) >>
       simp[])) >>
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`, `ee`, `leaf`, `finish'`] >>
  rewrite_tac[ignore_bind_def, bind_assoc] >>
  drule (cj 8 gasExemptCertTheory.gas_exempt_cert_rules) >>
  disch_then (qspecl_then [`tops`, `\v. bind (next v) (\x. return ())`] mp_tac) >>
  fs[ignore_bind_def] >> disch_then drule >> simp[]
QED

Theorem aug_place_storage_success_ready[local]:
  ((?b fld. bt = AttributeTarget b fld) \/ (?b k. bt = SubscriptTarget b k)) /\
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (AugAssign ty bt bop e) /\
  supported_target_pure tops bt /\
  (!id. target_root bt <> NameTarget id) /\
  target_pre cenv cx env bt es /\
  expr_body_pre cenv cx env e es /\
  (!tail. eval_base_place cx bt
    (es with gas_obs := prefix ++ tail) =
    (INL pv, mid with gas_obs := tail)) /\
  target_post ctx func cenv cx es sa sp s0 mid pv (Type ty) ptrout t ==>
  ?tr slot tv cur.
    pv = PlaceR (StoragePlace tr slot tv) /\
    eval_operand (FST ptrout) t = SOME slot /\
    FST (SND ptrout) = SOME (slot_loc tr) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    stmt_state_rel ctx func cenv cx mid t /\
    (!x. FST ptrout = Var x ==> not_fresh_at sp x) /\
    read_place cx (StoragePlace tr slot tv) mid = (INL cur,mid) /\
    place_type_value cx (StoragePlace tr slot tv) mid = (INL tv,mid) /\
    value_has_type tv cur /\
    expr_body_pre cenv cx env e mid /\
    eval_target_place cx bt (es with gas_obs := prefix ++ mid.gas_obs) =
      (INL (StoragePlace tr slot tv),mid)
Proof
  strip_tac >>
  qpat_assum `!tail. eval_base_place _ _ _ = _`
    (qspec_then `mid.gas_obs` assume_tac) >>
  pop_assum (assume_tac o SRULE []) >>
  qmatch_asmsub_abbrev_tac `eval_base_place cx bt start` >>
  `?pt. supported_target_info tops bindings bt = SOME pt` by
    metis_tac[aug_place_supported_stmt_target_info] >>
  `target_post ctx func cenv cx start sa sp s0 mid pv (Type ty) ptrout t` by
    (qpat_x_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[Abbr `start`, target_post_def, locals_kept_def] >>
     strip_tac >> metis_tac[]) >>
  drule_all aug_place_storage_target_ready >> strip_tac >>
  qpat_x_assum `pv = _` SUBST_ALL_TAC >>
  `target_pre cenv cx env bt start` by
    (simp[Abbr `start`, target_pre_def] >>
     metis_tac[target_pre_def, expr_sim_inv_gas_obs]) >>
  `expr_body_pre cenv cx env e start` by
    simp[Abbr `start`, expr_body_pre_gas_obs] >>
  `EVERY (supported_pure_expr tops) (target_indices bt)` by
    (qpat_x_assum `supported_target_pure tops bt` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt` >>
     fs[supported_target_pure_def, target_indices_def] >>
     first_x_assum irule >> simp[]) >>
  drule_all aug_place_storage_source_ready >> strip_tac >>
  qexistsl_tac [`tr`, `slot`, `tv`, `cur`] >> fs[Abbr `start`]
QED

Theorem aug_place_storage_success_continue[local]:
  ((?b fld. bt = AttributeTarget b fld) \/ (?b k. bt = SubscriptTarget b k)) /\
  body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (AugAssign ty bt bop e) /\
  supported_target_pure tops bt /\
  type_stmt env ret_ty (AugAssign ty bt bop e) = SOME env' /\
  expr_body_pre cenv cx env e es /\
  expr_body_pre cenv cx env e mid /\
  ((?s p s1 s2 cur s3 s4 ptv s5.
      eval_target_place cx bt s = (INL p,s1) /\
      read_place cx p s2 = (INL cur,s3) /\
      place_type_value cx p s4 = (INL ptv,s5)) ==>
    expr_sim_case F ctx func cenv cx e) /\
  gas_admissible (eval_stmt cx (AugAssign ty bt bop e)) (stmt_res_ok lctx) es /\
  stmt_env cenv lctx ret_ty (AugAssign ty bt bop e) sa = (cenv,sb) /\
  compile_get_target_ptr compile_expr cenv bt sa = (ptrout,sp) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  (!tail. eval_base_place cx bt (es with gas_obs := prefix ++ tail) =
    (INL (PlaceR (StoragePlace tr slot tv)),mid with gas_obs := tail)) /\
  eval_target_place cx bt (es with gas_obs := prefix ++ mid.gas_obs) =
    (INL (StoragePlace tr slot tv),mid) /\
  target_post ctx func cenv cx es sa sp s0 mid
    (PlaceR (StoragePlace tr slot tv)) (Type ty) ptrout t /\
  eval_operand (FST ptrout) t = SOME slot /\
  FST (SND ptrout) = SOME (slot_loc tr) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  stmt_state_rel ctx func cenv cx mid t /\
  (!x. FST ptrout = Var x ==> not_fresh_at sp x) /\
  (!gs. read_place cx (StoragePlace tr slot tv) (mid with gas_obs := gs) =
    (INL cur,mid with gas_obs := gs)) /\
  value_has_type tv cur /\
  ~t.vs_halted /\ t.vs_current_bb = sp.cs_current_bb /\
  t.vs_inst_idx = LENGTH sp.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (bind (eval_expr cx e) (\raw. bind (read_result cx raw)
      (\v. bind (lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        tv bop cur v)) (write_place cx (StoragePlace tr slot tv)))))
    (mid with gas_obs := [],t)
    (stmt_post ctx func cx lctx cenv cenv sa sb s0)
    (\res fin r. !tail. stmt_exit RetQ (fin with gas_obs := tail) res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!l. FST ptrout <> Label l` by
    (irule aug_place_target_ptr_not_label >> goal_assum (drule_at Any) >> simp[]) >>
  qpat_x_assum `_ \/ _` kall_tac >>
  `EVERY (supported_pure_expr tops) (target_indices bt)` by
    (qpat_x_assum `supported_target_pure tops bt` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt` >>
     fs[supported_target_pure_def, target_indices_def] >>
     first_x_assum irule >> simp[]) >>
  `contract_storage_well_formed cx
    (es with gas_obs := prefix ++ mid.gas_obs)` by
    (`expr_body_pre cenv cx env e
       (es with gas_obs := prefix ++ mid.gas_obs)` by
       simp[expr_body_pre_gas_obs] >>
     pop_assum mp_tac >>
     pure_rewrite_tac[expr_body_pre_def, expr_sim_inv_def] >>
     rpt strip_tac >> simp[]) >>
  drule_all aug_place_pure_target_storage_range >> strip_tac >>
  drule_all aug_place_pure_target_storage_live >> strip_tac >>
  drule vyperStoragePlaceProvenanceTheory.eval_target_place_region >> strip_tac >>
  drule aug_place_typing >> strip_tac >>
  `well_formed_type env.type_defs ty /\
   well_formed_type env.type_defs (expr_type e)` by
    metis_tac[assignable_type_well_formed] >>
  `type_bits ty MOD 8 = 0` by
    metis_tac[stmtSimAugAssignTheory.well_formed_type_bits] >>
  `env.type_defs = get_tenv cx` by
    (qpat_assum `expr_body_pre _ _ _ _ es` mp_tac >>
     pure_rewrite_tac[expr_body_pre_def, expr_sim_inv_def,
                     vyperTypeInvariantsTheory.env_consistent_def,
                     vyperTypeInvariantsTheory.env_context_consistent_def] >>
     rpt strip_tac >> simp[]) >>
  `?tvrhs. evaluate_type (get_tenv cx) (expr_type e) = SOME tvrhs` by
    metis_tac[well_formed_type_def, optionTheory.IS_SOME_EXISTS] >>
  `word_value cur` by metis_tac[word_value_type_typed] >>
  `is_word_type ty` by metis_tac[word_value_type_word] >>
  `read_place cx (StoragePlace tr slot tv) mid = (INL cur,mid)` by
    (qpat_x_assum `!gs. read_place _ _ _ = _`
      (qspec_then `mid.gas_obs` mp_tac) >> simp[]) >>
  drule_all aug_place_storage_load_ready >> strip_tac >>
  `!v w. value_has_type tvrhs v /\
    evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      tv bop cur v = INL w ==> value_has_type tv w` by
    (rpt strip_tac >>
     irule vyperTypeBuiltinsTheory.well_typed_binop_success_type >>
     goal_assum (drule_at Any) >> simp[] >>
     metis_tac[]) >>
  `expr_sim_case F ctx func cenv cx e` by
    (qpat_x_assum `(?s p s1 s2 cur s3 s4 ptv s5. _) ==> _` irule >>
     goal_assum (drule_at Any) >>
     goal_assum (drule_at Any) >>
     simp[place_type_value_def, return_def]) >>
  `expr_body_pre cenv cx env e (mid with gas_obs := [])` by
    simp[expr_body_pre_gas_obs] >>
  `expr_sim ctx func cenv cx ty e (mid with gas_obs := [])` by
    metis_tac[expr_sim_case_def] >>
  qpat_assum `gas_admissible (eval_stmt _ _) _ _`
    (mp_tac o REWRITE_RULE [aug_place_storage_target_bind]) >>
  disch_then assume_tac >>
  drule_all aug_place_bind_admissible_success >>
  simp[get_place_def, bind_return] >> strip_tac >>
  qpat_x_assum `gas_admissible (bind (read_place _ _) _) _ _` mp_tac >>
  simp[gasContextTheory.gas_admissible_def, bind_def,
       place_type_value_def, return_def] >> strip_tac >>
  qpat_x_assum `gas_admissible (bind (eval_base_place _ _) _) _ _` kall_tac >>
  qpat_x_assum `gas_admissible (eval_stmt _ _) _ _` kall_tac >>
  qpat_x_assum `!tail. eval_base_place _ _ _ = _` kall_tac >>
  qpat_x_assum `eval_target_place _ _ _ = _` kall_tac >>
  qpat_x_assum `contract_storage_well_formed _ _` kall_tac >>
  qpat_x_assum `EVERY (supported_pure_expr _) _` kall_tac >>
  qpat_x_assum `(?s p s1 s2 cur s3 s4 ptv s5. _) ==> _` kall_tac >>
  `gas_admissible
    (bind (eval_expr cx e) (\raw. bind (read_result cx raw)
      (\v. bind (lift_sum (evaluate_binop
        (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
        tv bop cur v)) (write_place cx (StoragePlace tr slot tv)))))
    (stmt_res_ok lctx) (mid with gas_obs := [])` by
    (simp[gasContextTheory.gas_admissible_def, bind_def] >>
     first_assum ACCEPT_TAC) >>
  qpat_x_assum `!gs res ee. _` kall_tac >>
  drule aug_place_code_parts >> strip_tac >> gvs[] >>
  qmatch_asmsub_abbrev_tac `emit_op loadop [FST ptrout] sp` >>
  `loadop = (if tr then TLOAD else SLOAD)` by
    (simp[Abbr `loadop`] >> Cases_on `tr` >> simp[slot_loc_def]) >>
  gvs[] >>
  rename1 `compile_get_target_ptr compile_expr cenv bt sa = (ptrout,sp)` >>
  drule aug_place_emit_op_grows >> strip_tac >>
  drule compile_binop_grows >> strip_tac >>
  drule aug_place_emit_void_grows >> strip_tac >>
  `cs_extends sa sp` by
    metis_tac[ci_mono_compile_get_target_ptr_cfn, compile_expr_ci_mono,
              ci_mono_def, pairTheory.SND] >>
  `cs_extends s1 s2` by
    metis_tac[ci_mono_lower_value_cfn, compile_expr_ci_mono,
              ci_mono_def, pairTheory.SND] >>
  `cs_extends s1 sb` by metis_tac[cs_extends_trans] >>
  `cs_extends sp sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sp sb func` by metis_tac[fn_has_code_split] >>
  `fn_has_code sp s1 func /\ fn_has_code s1 sb func` by
    metis_tac[fn_has_code_split] >>
  `sa.cs_next_var <= sp.cs_next_var` by
    metis_tac[ci_mono_compile_get_target_ptr_cfn, compile_expr_ci_mono,
              ci_mono_def, pairTheory.SND] >>
  `local_ptrs_reserved cenv sp` by metis_tac[local_ptrs_reserved_next_var] >>
  qpat_x_assum `supported_stmt _ _ _` kall_tac >>
  qpat_x_assum `supported_target_pure _ _` kall_tac >>
  qpat_x_assum `stmt_env _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `!gs. read_place _ _ _ = _` kall_tac >>
  qpat_x_assum `expr_sim_case _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `well_typed_binop _ _ _ _` kall_tac >>
  qpat_x_assum `type_place_target _ _ = _` kall_tac >>
  drule_all aug_place_storage_load_counted_nofresh >> strip_tac >>
  `sp.cs_next_var <= s1.cs_next_var` by
    metis_tac[ci_mono_emit_op, ci_mono_def, pairTheory.SND] >>
  `local_ptrs_reserved cenv s1` by metis_tac[local_ptrs_reserved_next_var] >>
  drule exprSafeOperandTheory.emit_op_safe_operand >>
  rewrite_tac[exprSafeOperandTheory.safe_operand_def] >> strip_tac >>
  `!x. FST ptrout = Var x ==> not_fresh_at s1 x` by
    metis_tac[loweringShapeDefsTheory.not_fresh_at_mono] >>
  `acyclic_struct_metadata cenv.ce_struct_fields` by fs[body_inv_def] >>
  qpat_x_assum `body_inv _ _ _ _` kall_tac >>
  qpat_x_assum `slots_in_range _ _ _` kall_tac >>
  qpat_x_assum `storage_read_live _ _ _ _ _` kall_tac >>
  qpat_x_assum `read_place _ _ _ = _` kall_tac >>
  qpat_x_assum `(if tr then tload _ _ else sload _ _) = _` kall_tac >>
  `fn_has_code s1 s2 func /\ fn_has_code s2 s3 func /\ fn_has_code s3 sb func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `eval_operand cur' u = SOME (val_to_w256 cur)` by
    (fs[expr_val_rel_def] >>
     qpat_x_assum `!tv. evaluate_type _ _ = SOME tv ==> _` drule >>
     simp[typed_val_to_w256_word_value]) >>
  `emit_void (if tr then TSTORE else SSTORE) [FST ptrout;result] s3 = ((),sb)` by
    (Cases_on `tr` >> fs[slot_loc_def]) >>
  `expr_body_pre cenv cx env e (mid with gas_obs := [])` by
    metis_tac[expr_body_pre_gas_obs] >>
  `stmt_state_rel ctx func cenv cx (mid with gas_obs := []) u` by
    simp[exprSimWordArgsTheory.stmt_state_rel_gas_obs] >>
  qmatch_asmsub_abbrev_tac `gas_admissible suffix (stmt_res_ok lctx) mid` >>
  `gas_admissible suffix (stmt_res_ok lctx) (mid with gas_obs := [])` by
    simp[gasContextTheory.gas_admissible_gas_obs] >>
  unabbrev_all_tac >>
  drule_all aug_place_storage_suffix_outcome_nofresh >>
  disch_then (qspec_then `RetQ` assume_tac) >>
  `gas_marked_path F ctx func t 0 (OK u)` by
    simp[fragGasModeTheory.gas_marked_path_def] >>
  irule aug_place_zero_prefix_outcome >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  simp[] >> rpt strip_tac >>
  irule aug_place_stmt_post_prefix >>
  qexists_tac `sp` >> qexists_tac `t` >>
  simp[] >>
  conj_tac >- fs[target_post_def] >>
  conj_tac >- fs[target_post_def] >>
  irule aug_place_stmt_post_prefix >>
  qexists_tac `s1` >> qexists_tac `u` >> simp[]
QED

Theorem compile_augassign_place_storage_case:
  !ctx func cx lctx RetQ cenv ret_ty env env' tops bindings ty bt bop e es.
    (!id. target_root bt <> NameTarget id) /\ supported_target_pure tops bt /\
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
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule aug_place_typing >> strip_tac >>
  `target_pre cenv cx env bt es` by
    fs[target_pre_def, expr_body_pre_def] >>
  `target_sim ctx func cenv cx env bt es` by
    metis_tac[target_case_def] >>
  simp[stmt_frag_def, stmt_framed_frag_def] >> rpt gen_tac >> strip_tac >>
  drule aug_place_code_parts >>
  disch_then (fn th => map_every assume_tac (CONJUNCTS th)) >>
  pop_assum (qx_choose_then `ptrout` (qx_choose_then `sp`
    (map_every assume_tac o CONJUNCTS))) >>
  `cs_extends sa sp` by
    metis_tac[ci_mono_compile_get_target_ptr_cfn, compile_expr_ci_mono,
              ci_mono_def, pairTheory.SND] >>
  `cs_extends sp sb` by
    (qpat_x_assum `_ \/ _` strip_assume_tac
     >- metis_tac[ci_mono_emit_void, ci_mono_def, pairTheory.SND] >>
     drule compile_binop_grows >> strip_tac >>
     `cs_extends sp s1` by metis_tac[ci_mono_emit_op, ci_mono_def, pairTheory.SND] >>
     `cs_extends s1 s2` by
       metis_tac[ci_mono_lower_value_cfn, compile_expr_ci_mono,
                 ci_mono_def, pairTheory.SND] >>
     `cs_extends s3 sb` by metis_tac[ci_mono_emit_void, ci_mono_def, pairTheory.SND] >>
     metis_tac[cs_extends_trans]) >>
  `fn_has_code sa sp func` by metis_tac[fn_has_code_split] >>
  drule aug_place_storage_target_admissible >> strip_tac >>
  qpat_x_assum `target_sim _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[targetPlaceSimDefsTheory.target_sim_def] >> disch_then drule_all >> strip_tac >>
  rewrite_tac[aug_place_storage_target_bind] >>
  irule aug_place_result_bind_outcome_path >>
  goal_assum (drule_at Any) >>
  conj_tac >- suspend "target_success" >>
  conj_tac >- simp[] >>
  rpt strip_tac >> Cases_on `res` >> fs[expr_exit_def] >>
  metis_tac[aug_place_storage_target_exit]
QED

Resume compile_augassign_place_storage_case[target_success]:
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `(\res ee t. _) (INL v) mid t`
    (strip_assume_tac o SRULE []) >>
  drule_all aug_place_storage_success_ready >> strip_tac >>
  qpat_x_assum `v = _` SUBST_ALL_TAC >>
  simp[get_place_def, bind_return] >>
  `!gs. read_place cx (StoragePlace tr slot tv) (mid with gas_obs := gs) =
    (INL cur, mid with gas_obs := gs)` by
    (fs[read_place_def] >> metis_tac[read_storage_slot_gas_obs]) >>
  `~t.vs_halted` by
    (fs[fragGasModeTheory.gas_marked_path_def] >>
     metis_tac[fragGasPathTheory.gas_path_normal]) >>
  irule aug_place_value_prefix_outcome >>
  goal_assum (drule_at Any) >> simp[] >>
  simp[place_type_value_def, bind_return] >>
  qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC >>
  drule_all aug_place_storage_success_continue >>
  disch_then (qspec_then `RetQ` mp_tac) >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >>
  simp[vyperStateTheory.bind_def]
QED

Finalise compile_augassign_place_storage_case
