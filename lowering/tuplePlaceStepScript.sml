(* Consume store frames at the single correctness endpoint. *)
Theory tuplePlaceStep
Ancestors
  vyperEvalExprPreservesScopesDom
  tuplePlaceHeadAdvance vyperScopePreservation vyperPlaceFrames vyperPlaceTyping
  vyperStorageBackend
Libs horizonTypeLib

Theorem tuple_place_endpoint_local_regions_some:
  stmt_state_rel H ctx func cenv cx es s /\ local_ptrs_reserved cenv cs /\
  (!x v. not_fresh_at cs x /\ lookup_var x s = SOME v ==>
    lookup_var x t = SOME v) /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes ==>
  (!n b sz. local_region cenv es'.scopes t n b sz <=>
            local_region cenv es.scopes s n b sz)
Proof
  strip_tac >> rpt gen_tac >> eq_tac
  >- (strip_tac >> irule exprSimPropsTheory.local_region_frame >>
      fs[exprLoweringPropsTheory.stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def] >>
      metis_tac[]) >>
  strip_tac >> irule exprSimPropsTheory.local_region_frame_fwd >> metis_tac[]
QED

(* Convert the store runners' protected-allocation byte frame into the
   statement frame, without choosing another execution endpoint. *)
Theorem tuple_place_store_alloca_frame:
  stmt_state_rel H ctx func cenv cx ee s /\ local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  MAP FDOM ee.scopes = MAP FDOM ff.scopes /\
  place_ptr_rel cenv cx s (PlaceR p) w (SOME loc) (Type dty) /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  write_place cx p v ee = (INL (),ff) /\
  (!id path entry t0. p = MemoryPlace id path /\
    lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
  (!aid off sz. aid < sa.cs_next_id /\
    FLOOKUP s.vs_allocas aid = SOME (off,sz) /\
    (loc = LocMemory ==> off+sz <= w2n w \/ w2n w+type_memory_size dtv <= off) ==>
    mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz s.vs_memory) ==>
  alloca_frame cenv ee sa s cenv ff t
Proof
  strip_tac >>
  `!n b sz. local_region cenv ff.scopes t n b sz <=>
             local_region cenv ee.scopes s n b sz` by
    (irule tuple_place_endpoint_local_regions_some >> metis_tac[]) >>
  rewrite_tac[stmtSimDefsTheory.alloca_frame_def] >> rpt strip_tac
  >- (qpat_x_assum `!aid off sz. _ ==> mem_bytes_at _ _ _ = _` irule >>
      simp[] >> conj_tac >- (qexists `aid` >> simp[]) >> strip_tac >> gvs[] >>
      drule_all placeMemoryLiveRegionTheory.memory_place_live_region >> strip_tac >>
      `off + sz <= b \/ b + len <= off` by metis_tac[] >> decide_tac) >>
  metis_tac[]
QED

Theorem tuple_place_pointer_store_alloca_frame:
  tuple_place_head ctx func cenv cx st0 es lo sp tys ltys ltvs vs elems w i s0 /\
  valid_horizon cx st0 H ee.storage_trace /\
  EVERY (supported_expr tops) (target_indices bt) /\ eval_base_place cx bt es = (res,ee) /\
  target_post H ctx func cenv cx es sp sa s0 ee pv vt r s /\
  compile_get_target_ptr compile_expr cenv bt sp = (r,sa) /\
  alloca_frame cenv ee sa s cenv ff t ==>
  alloca_frame cenv es sp s0 cenv ff t
Proof
  strip_tac >>
  `MAP FDOM ee.scopes = MAP FDOM es.scopes` by
    metis_tac[eval_base_place_preserves_scopes_dom] >>
  `valid_horizon cx st0 H es.storage_trace` by
    (irule (INST_TYPE [alpha |-> ``:eval_result``]
              vyperStorageFootprintTheory.valid_horizon_frame) >>
     qpat_assum `eval_base_place _ _ _ = _` (irule_at Any) >>
     simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>
  `stmt_state_rel H ctx func cenv cx es s0` by
    (qpat_x_assum `tuple_place_head _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [tuplePlaceHeadTheory.tuple_place_head_def]) >>
     res_tac) >>
  `alloca_frame cenv es sp s0 cenv ee s` by
    (fs[tuplePlaceHeadTheory.tuple_place_head_def] >>
     drule_all stmtSimDefsTheory.target_post_alloca_frame >> simp[]) >>
  `ci_mono sp sa` by
    (qspec_then `bt` mp_tac stmtLoweringMonoTheory.ci_mono_compile_get_target_ptr >>
     disch_then (qspecl_then [`cenv`, `sp`] mp_tac) >> simp[]) >>
  irule stmtSimDefsTheory.alloca_frame_trans >>
  qpat_assum `alloca_frame _ _ _ _ _ ff t` (irule_at Any) >>
  qpat_assum `alloca_frame _ _ _ _ _ ee s` (irule_at Any) >>
  fs[exprLoweringPropsTheory.ci_mono_def, loweringPostsTheory.target_post_def]
QED

Theorem tuple_place_head_advance_some:
  tuple_place_head ctx func cenv cx st0 es lo sp tys ltys ltvs vs elems w i s /\
  i < LENGTH ltys /\ sp.cs_next_var <= sb.cs_next_var /\
  sp.cs_next_id <= sb.cs_next_id /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP t.vs_allocas aid = SOME entry) /\
  (!n b sz. local_region cenv ff.scopes t n b sz <=>
            local_region cenv es.scopes s n b sz) /\
  (!x v. not_fresh_at sp x /\ lookup_var x s = SOME v ==>
    lookup_var x t = SOME v) /\
  (?H. valid_horizon cx st0 H ff.storage_trace) /\
  (!H. valid_horizon cx st0 H ff.storage_trace ==>
     stmt_state_rel H ctx func cenv cx ff t /\ storage_well_formed_on cx ff (FST H)) /\
  ~t.vs_halted /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  (!j. SUC i <= j /\ j < LENGTH ltys /\ ~is_word_type (EL j ltys) ==>
    val_in_memory (EL j ltvs) (EL j vs)
      (w2n w + SUM (MAP type_memory_size (TAKE j ltvs))) t.vs_memory) ==>
  tuple_place_head ctx func cenv cx st0 ff lo sb tys ltys ltvs vs elems w (SUC i) t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `tuple_place_snapshot cenv cx ff lo sb.cs_next_id tys ltys ltvs w t` by
    (irule tuple_place_snapshot_endpoint >>
     fs[tuplePlaceHeadTheory.tuple_place_head_def] >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  fs[tuplePlaceHeadTheory.tuple_place_head_def] >>
  `local_ptrs_reserved cenv sb` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     goal_assum (drule_at Any) >> simp[]) >>
  simp[] >>
  conj_tac >- (qexists_tac `H'` >> first_assum ACCEPT_TAC) >>
  conj_tac >- metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  rpt strip_tac >>
  `MEM (EL j elems) elems` by (irule listTheory.EL_MEM >> simp[]) >>
  `?x. EL j elems = Var x` by gvs[listTheory.EVERY_MEM] >>
  `not_fresh_at sp x` by metis_tac[] >>
  `i <= j` by simp[] >>
  qpat_x_assum `!j. _ ==> ?v. _` (qspec_then `j` mp_tac) >>
  simp[venomStateTheory.eval_operand_def] >> strip_tac >>
  qexists `v` >> simp[]
QED

(* A place write leaves the storage observations alone. *)
Theorem write_place_storage_trace:
  write_place cx p v st = (res,st') ==> st'.storage_trace = st.storage_trace
Proof
  Cases_on `p`
  >- (simp[vyperPlaceFramesTheory.write_storage_place_eq] >>
      Cases_on `cx.txn.is_static` >> Cases_on `encode_value t v` >> simp[] >>
      rpt strip_tac >> Cases_on `b` >>
      gvs[vyperStorageBackendTheory.set_storage_def])
  >- (strip_tac >> drule vyperPlaceFramesTheory.write_memory_place_frame >>
      strip_tac >> gvs[]) >>
  strip_tac >> drule vyperPlaceFramesTheory.write_immutable_place_frame >>
  strip_tac >> gvs[]
QED

(* A typed write through an observed place keeps storage well formed on every
   horizon valid after it; a memory or immutable write leaves storage alone. *)
Theorem tuple_place_write_storage_wf:
  eval_base_place cx bt es = (INL (PlaceR p),ee) /\
  valid_horizon cx st0 H ee.storage_trace /\
  storage_well_formed_on cx ee (FST H) /\
  (!tr slot leaf. p = StoragePlace tr slot leaf ==>
     well_formed_type_value leaf /\ value_has_type leaf v) /\
  write_place cx p v ee = (INL (),ff) ==>
  storage_well_formed_on cx ff (FST H)
Proof
  strip_tac >>
  qpat_x_assum `valid_horizon _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [vyperStorageFootprintTheory.valid_horizon_def]) >>
  Cases_on `p`
  >- (drule vyperFiniteStoragePreservationTheory.eval_base_place_observed_region >>
      strip_tac >>
      qpat_x_assum `!tr slot leaf. _ ==> _` (qspecl_then [`b`, `c`, `t`] mp_tac) >>
      simp[] >> strip_tac >>
      irule (Q.INST [`observations` |-> `ee.storage_trace`]
        vyperFiniteStoragePreservationTheory.write_place_preserves_storage_well_formed_on) >>
      qpat_assum `write_place _ _ _ _ = _` (irule_at Any) >>
      qexists_tac `t` >> simp[vyperPlaceTypingTheory.runtime_place_typed_storage] >>
      metis_tac[])
  >- (drule vyperPlaceFramesTheory.write_memory_place_frame >> strip_tac >>
      `ff.accounts = ee.accounts /\ ff.tStorage = ee.tStorage` by simp[] >>
      metis_tac[vyperStorageFootprintTheory.storage_well_formed_on_backends]) >>
  drule vyperPlaceFramesTheory.write_immutable_place_frame >> strip_tac >>
  `ff.accounts = ee.accounts /\ ff.tStorage = ee.tStorage` by simp[] >>
  metis_tac[vyperStorageFootprintTheory.storage_well_formed_on_backends]
QED

(* The guarded head at the write's endpoint: every horizon valid there was
   valid at the place, where the target post and the runner's frame hold. *)
Theorem tuple_place_store_guard:
  eval_base_place cx bt es = (INL (PlaceR p),ee) /\
  write_place cx p v ee = (INL (),ff) /\
  valid_horizon cx st0 H0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     target_post H ctx func cenv cx es sp sa s0 ee (PlaceR p) vt r s) /\
  (!tr slot leaf. p = StoragePlace tr slot leaf ==>
     well_formed_type_value leaf /\ value_has_type leaf v) /\
  (!H. stmt_state_rel H ctx func cenv cx ee s /\ storage_place_observed H p /\
       regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H) ==>
       stmt_state_rel H ctx func cenv cx ff t) ==>
  (?H. valid_horizon cx st0 H ff.storage_trace) /\
  (!H. valid_horizon cx st0 H ff.storage_trace ==>
     stmt_state_rel H ctx func cenv cx ff t /\ storage_well_formed_on cx ff (FST H))
Proof
  strip_tac >>
  drule write_place_storage_trace >> strip_tac >>
  conj_tac >- (qexists_tac `H0` >> simp[]) >>
  qx_gen_tac `Hx` >> disch_tac >>
  `valid_horizon cx st0 Hx ee.storage_trace` by
    (qpat_assum `ff.storage_trace = ee.storage_trace`
       (fn th => REWRITE_TAC [GSYM th]) >> first_assum ACCEPT_TAC) >>
  `target_post Hx ctx func cenv cx es sp sa s0 ee (PlaceR p) vt r s` by
    (qpat_x_assum `!H. valid_horizon _ _ H _ ==> _` irule >> first_assum ACCEPT_TAC) >>
  drule_all tuplePlacePointerReadyTheory.tuple_place_pointer_storage_facts >> strip_tac >>
  qpat_x_assum `target_post Hx _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [loweringPostsTheory.target_post_def]) >>
  conj_tac
  >- (qpat_x_assum `!H. stmt_state_rel H _ _ _ _ ee s /\ _ ==> _` irule >> simp[]) >>
  irule tuple_place_write_storage_wf >>
  qpat_assum `write_place _ _ _ _ = _` (irule_at Any) >>
  qpat_assum `eval_base_place _ _ _ = _` (irule_at Any) >>
  simp[] >> metis_tac[]
QED

Theorem tuple_place_pointer_head_advance:
  tuple_place_head ctx func cenv cx st0 es lo sp tys ltys ltvs vs elems w i s0 /\
  EVERY (supported_expr tops) (target_indices bt) /\ eval_base_place cx bt es = (res,ee) /\
  target_post H ctx func cenv cx es sp sa s0 ee pv vt r s /\
  compile_get_target_ptr compile_expr cenv bt sp = (r,sa) /\
  ci_mono sa sb /\ i < LENGTH ltys /\
  write_place cx p v ee = (INL (),ff) /\
  (?H. valid_horizon cx st0 H ff.storage_trace) /\
  (!H. valid_horizon cx st0 H ff.storage_trace ==>
     stmt_state_rel H ctx func cenv cx ff t /\ storage_well_formed_on cx ff (FST H)) /\
  ~t.vs_halted /\
  t.vs_current_bb = sb.cs_current_bb /\
  t.vs_inst_idx = LENGTH sb.cs_current_insts /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP t.vs_allocas aid = SOME entry) /\
  (!j. SUC i <= j /\ j < LENGTH ltys /\ ~is_word_type (EL j ltys) ==>
    val_in_memory (EL j ltvs) (EL j vs)
      (w2n w + SUM (MAP type_memory_size (TAKE j ltvs))) t.vs_memory) ==>
  tuple_place_head ctx func cenv cx st0 ff lo sb tys ltys ltvs vs elems w (SUC i) t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ci_mono sp sa` by
    (qspec_then `bt` mp_tac stmtLoweringMonoTheory.ci_mono_compile_get_target_ptr >>
     disch_then (qspecl_then [`cenv`, `sp`] mp_tac) >> simp[]) >>
  `sp.cs_next_var <= sa.cs_next_var /\ sp.cs_next_id <= sa.cs_next_id /\
   sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id` by
    gvs[exprLoweringPropsTheory.ci_mono_def] >>
  `MAP FDOM es.scopes = MAP FDOM ff.scopes` by
    (metis_tac[eval_base_place_preserves_scopes_dom, write_place_scopes_dom]) >>
  `!x v. not_fresh_at sp x /\ lookup_var x s0 = SOME v ==>
    lookup_var x t = SOME v` by
    (rpt strip_tac >>
     `not_fresh_at sa x` by metis_tac[freshWritesTheory.not_fresh_at_mono] >>
     fs[loweringPostsTheory.target_post_def]) >>
  `!aid entry. FLOOKUP s0.vs_allocas aid = SOME entry ==>
    FLOOKUP t.vs_allocas aid = SOME entry` by
    (fs[loweringPostsTheory.target_post_def] >> metis_tac[]) >>
  `!n b sz. local_region cenv ff.scopes t n b sz <=>
    local_region cenv es.scopes s0 n b sz` by
    (drule tuplePlaceHeadTheory.tuple_place_head_witness >> strip_tac >>
     fs[tuplePlaceHeadTheory.tuple_place_head_def] >>
     drule_all tuple_place_endpoint_local_regions_some >> simp[]) >>
  irule tuple_place_head_advance_some >>
  qpat_assum `tuple_place_head _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
  simp[]
QED

(* Whole snapshot separation is derived from ownership or a typed borrow,
   not imposed on callers of the eventual successful-head step. *)
Theorem tuple_place_pointer_snapshot_apart:
  tuple_place_head ctx func cenv cx st0 es lo sp tys ltys ltvs vs elems w i s0 /\
  target_pre cenv cx env bt es /\ EVERY (supported_expr tops) (target_indices bt) /\
  well_typed_target env bt (EL i tys) /\
  call_evaluation_safe cx (int_calls_target bt) /\
  eval_base_place cx bt es = (INL (PlaceR p),ee) /\
  target_post H ctx func cenv cx es sp sa s0 ee (PlaceR p) (Type (EL i tys)) r s /\
  compile_get_target_ptr compile_expr cenv bt sp = (r,sa) /\
  assignable_type (get_tenv cx) (TupleT tys) /\ arg_types_fit ltys tys /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  evaluate_type (get_tenv cx) (TupleT ltys) = SOME (TupleTV ltvs) /\
  i < LENGTH tys /\
  place_ptr_rel cenv cx s (PlaceR p) dw (SOME LocMemory) (Type (EL i tys)) /\
  write_place cx p (EL i vs) ee = (INL (),ff) ==>
  EVERY is_word_type ltys \/
  w2n w + type_memory_size_list ltvs <= w2n dw \/
  w2n dw + type_memory_size (EL i tvs) <= w2n w
Proof
  strip_tac >>
  drule_all tuplePlaceSourceTheory.tuple_place_type_facts >> strip_tac >>
  `evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs)` by metis_tac[] >>
  qpat_x_assum `!j. j < LENGTH tys ==> _` kall_tac >>
  drule_all tuplePlacePointerReadyTheory.tuple_place_pointer_source_facts >> strip_tac >>
  `stmt_state_rel H ctx func cenv cx ee s` by fs[loweringPostsTheory.target_post_def] >>
  `tuple_place_snapshot cenv cx ee lo sa.cs_next_id tys ltys ltvs w s` by
    (drule_all tuplePlacePointerReadyTheory.tuple_place_pointer_snapshot >> simp[]) >>
  `0 < type_memory_size_list ltvs` by
    (drule_all tuplePlaceZeroTheory.tuple_place_element_source_positive >> strip_tac >>
     `SUM (MAP type_memory_size (TAKE i ltvs)) + type_memory_size (EL i ltvs)
       <= type_memory_size_list ltvs` by
       (simp[valueEncodingProofsTheory.type_memory_size_list_sum] >>
        irule tupleMemoryLayoutTheory.tuple_element_interval >> simp[]) >> decide_tac) >>
  fs[tuplePlacePrefixCertTheory.tuple_place_snapshot_def]
  >- (disj2_tac >>
      drule_all placeMemoryLiveRegionTheory.memory_place_live_region >> strip_tac >>
      `b+sz <= b' \/ b'+len <= b` by metis_tac[] >> decide_tac) >>
  `ltvs = tvs` by gvs[] >>
  qpat_x_assum `ltys = tys` SUBST_ALL_TAC >>
  qpat_x_assum `ltvs = tvs` SUBST_ALL_TAC >>
  `writable_place_result cx ee (PlaceR p)` by
    (irule tuplePlacePointerReadyTheory.tuple_place_target_endpoint_writable >>
     fs[targetPlaceSimTheory.target_pre_def] >> metis_tac[]) >>
  `w2n w = b + (w2n w-b)` by simp[] >>
  `w2n w + type_memory_size_list tvs <= w2n dw \/
   w2n dw + type_memory_size (EL i tvs) <= w2n w` suffices_by simp[] >>
  drule_all tuplePlaceReachableTheory.tuple_place_local_path_extent >> strip_tac >>
  drule_all tuplePlacePointerReadyTheory.tuple_place_writable_borrow_destination_apart >>
  simp[valueEncodingTheory.type_memory_size_def]
QED
