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
  stmtSimAugAssignPlace
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


(* x op= e at a field or element of a storage or transient variable,
   with pure indices. *)
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
  cheat
QED
