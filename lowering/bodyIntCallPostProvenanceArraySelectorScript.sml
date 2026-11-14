(* Actual-index reconstruction boundaries for noncapturing array selection. *)
Theory bodyIntCallPostProvenanceArraySelector
Ancestors
  bodyIntCallPostProvenanceArrayMemoryFrame
  bodyIntCallPostProvenanceArrayImmutableFrame
  bodyIntCallPostProvenanceArrayLiveSource bodyIntCallPostProvenanceArrayCode
  bodyIntCallPostProvenanceArrayElement bodyIntCallPostProvenanceSelectors
  exprSimSubscriptArrayFrame exprSimSubscriptArraySource vyperState pair
  loweringPosts exprSimProps valueEncodingProofs valueEncodingDefs bodyIntCallArgType

Theorem immutable_holds_source_frame[local]:
  immutable_holds ce cx ty r w es s /\
  ee.scopes = es.scopes /\ ee.immutables = es.immutables /\
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) ==>
  immutable_holds ce cx ty r w ee t
Proof
  strip_tac >>
  `FST (read_result cx r ee) = FST (read_result cx r es)` by
    (irule read_result_nonstorage_frame >> simp[]) >>
  `SND (read_result cx r ee) = ee` by
    (Cases_on `read_result cx r ee` >> drule read_result_state >> simp[]) >>
  gvs[immutable_holds_def] >>
  qexistsl [`name`, `off`, `itv`, `iv`, `k`, `v`] >> simp[] >>
  metis_tac[PAIR, FST, SND]
QED

Theorem vv_holds_located_code_source_frame[local]:
  vv_holds ce cx ty r (LocatedValue ann p) es s /\
  p.ptr_location = LocCode /\
  (!w. eval_operand p.ptr_operand s = SOME w ==>
       eval_operand p.ptr_operand t = SOME w) /\
  ee.scopes = es.scopes /\ ee.immutables = es.immutables /\
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) ==>
  vv_holds ce cx ty r (LocatedValue ann p) ee t
Proof
  strip_tac >> gvs[vv_holds_def] >>
  drule_all immutable_holds_source_frame >> simp[]
QED

Theorem provenance_memory_value_frame[local]:
  intcall_vv_provenance ce cx ty sa sb es raw (LocatedValue ann p) s /\
  p.ptr_location = LocMemory /\ eval_operand p.ptr_operand s = SOME w /\
  read_result cx raw es = (INL v,es) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\ val_wf tv v /\
  val_in_memory tv v (w2n w) s.vs_memory /\
  expr_sim_inv ce cx env es /\ wb_frame ce es ee sb s t /\
  ee.scopes = es.scopes /\ local_ptrs_reserved ce sb /\
  local_ptrs_rel func ce ee.scopes t ==>
  val_in_memory tv v (w2n w) t.vs_memory
Proof
  strip_tac >>
  qpat_x_assum `intcall_vv_provenance _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [bodyIntCallProducerInterfaceTheory.intcall_vv_provenance_def]) >>
  strip_tac >> qpat_x_assum `!op. _` (qspec_then `p.ptr_operand` mp_tac) >>
  simp[] >> strip_tac >> gvs[]
  >~ [`FLOOKUP s.vs_allocas aid = SOME (b,sz)`]
  >- (`mem_bytes_at b sz t.vs_memory = mem_bytes_at b sz s.vs_memory` by
        (gvs[wb_frame_def] >> first_x_assum irule >> simp[] >> metis_tac[]) >>
      irule val_in_memory_footprint_agree >>
      simp[] >> qexists `s.vs_memory` >> simp[] >>
      drule mem_bytes_at_agree_window >> strip_tac >>
      first_x_assum irule >> simp[]) 
  >~ [`val_footprint tv v = 0`]
  >- (irule val_in_memory_footprint_agree >>
      simp[mem_bytes_at_def] >> qexists `s.vs_memory` >> simp[])
  >~ [`local_val_at ce cx n (w2n w - b) tv v`]
  >- (`mem_bytes_at (w2n w) (val_footprint tv v) t.vs_memory =
       mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory` by
        (irule locals_kept_dynarray_free_value >>
         goal_assum (drule_at Any) >> gvs[wb_frame_def] >> metis_tac[]) >>
      irule val_in_memory_footprint_agree >>
      simp[] >> qexists `s.vs_memory` >> simp[]) >>
  rename1 `lookup_var root s = SOME rootword` >>
  `lookup_var root t = SOME rootword` by
    (gvs[wb_frame_def, loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
  drule_all bodyIntCallLocalFrameTheory.local_ptrs_rel_sub_layout >>
  simp[arithmeticTheory.ADD_COMM]
QED

Theorem vv_holds_memory_provenance_frame[local]:
  vv_holds ce cx ty raw (LocatedValue ann p) es s /\
  vv_at ce cx ty sa sb es raw (LocatedValue ann p) s /\
  intcall_vv_provenance ce cx ty sa sb es raw (LocatedValue ann p) s /\
  p.ptr_location = LocMemory /\ ~is_word_type ty /\
  (!w. eval_operand p.ptr_operand s = SOME w ==>
       eval_operand p.ptr_operand t = SOME w) /\
  (!tr slot vt. raw <> PlaceR (StoragePlace tr slot vt)) /\
  ee.scopes = es.scopes /\ ee.immutables = es.immutables /\
  expr_sim_inv ce cx env es /\ wb_frame ce es ee sb s t /\
  local_ptrs_reserved ce sb /\ local_ptrs_rel func ce ee.scopes t ==>
  vv_holds ce cx ty raw (LocatedValue ann p) ee t
Proof
  strip_tac >>
  `FST (read_result cx raw ee) = FST (read_result cx raw es)` by
    (irule read_result_nonstorage_frame >> simp[]) >>
  gvs[vv_holds_def] >>
  `read_result cx raw ee = (INL v,ee)` by
    (Cases_on `read_result cx raw ee` >> gvs[] >>
     drule read_result_state >> simp[]) >>
  qexists `v` >> simp[] >> rpt strip_tac >>
  `val_wf tvt v` by (gvs[vv_at_def] >> metis_tac[]) >>
  irule provenance_memory_value_frame >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem enriched_array_base_representation[local]:
  vv_post ctx func ce cx obj es sa sb s0 st raw (LocatedValue ann p) s /\
  intcall_vv_provenance ce cx (expr_type obj) sa sb st raw (LocatedValue ann p) s /\
  expr_post ctx func ce cx idx st sb sc s ee iv iop t /\
  expr_type obj = ArrayT et bd /\ ~expr_has_effect obj /\
  (p.ptr_location = LocCode \/ p.ptr_location = LocMemory) /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sb x) /\
  (!l. p.ptr_operand <> Label l) /\
  (!tr slot vt. raw <> PlaceR (StoragePlace tr slot vt)) /\
  ee.scopes = st.scopes /\ ee.immutables = st.immutables /\
  expr_sim_inv ce cx env st /\ local_ptrs_reserved ce sb /\
  sb.cs_next_id <= sc.cs_next_id ==>
  vv_holds ce cx (ArrayT et bd) raw (LocatedValue ann p) ee t /\
  vv_at ce cx (ArrayT et bd) sa sc ee raw (LocatedValue ann p) t
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `wb_frame ce st ee sb s t` by
    (gvs[expr_post_def, wb_frame_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!w. eval_operand p.ptr_operand s = SOME w ==>
       eval_operand p.ptr_operand t = SOME w` by
    (rpt strip_tac >> irule exprBopSimPropsTheory.eval_operand_frame >>
     goal_assum (drule_at Any) >> gvs[wb_frame_def] >> metis_tac[]) >>
  `local_ptrs_rel func ce st.scopes s` by
    gvs[vv_post_def, exprLoweringPropsTheory.stmt_state_rel_def,
        loweringStateRelDefsTheory.state_rel_def] >>
  `local_ptrs_rel func ce ee.scopes t` by
    gvs[expr_post_def, exprLoweringPropsTheory.stmt_state_rel_def,
        loweringStateRelDefsTheory.state_rel_def] >>
  qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[vv_post_def] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `post_value_type ce obj = ArrayT et bd` by metis_tac[effect_free_post_value_type] >>
  `ann = ArrayT et bd` by
    (qpat_x_assum `vv_holds _ _ _ _ _ _ _` mp_tac >>
     simp[Once vv_holds_def] >> strip_tac >> gvs[compileEnvTheory.is_bytestring_type_def]) >>
  gnvs[] >> conj_tac
  >- (Cases_on `p.ptr_location = LocCode`
      >- (irule vv_holds_located_code_source_frame >>
          goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
      irule vv_holds_memory_provenance_frame >>
      goal_assum (drule_at Any) >> simp[compileEnvTheory.is_word_type_def] >> metis_tac[]) >>
  drule_all vv_at_located_frame >> simp[]
QED

Theorem intcall_located_provenance_index_frame[local]:
  intcall_vv_provenance ce cx ty sa sb es raw (LocatedValue ann p) s /\
  eval_operand p.ptr_operand t = eval_operand p.ptr_operand s /\
  (!tr slot vt. raw <> PlaceR (StoragePlace tr slot vt)) /\
  ee.scopes = es.scopes /\ ee.immutables = es.immutables /\
  wb_frame ce es ee sb s t /\ local_ptrs_reserved ce sb /\
  local_ptrs_rel func ce es.scopes s /\ sb.cs_next_id <= sc.cs_next_id ==>
  intcall_vv_provenance ce cx ty sa sc ee raw (LocatedValue ann p) t
Proof
  strip_tac >>
  `!n b sz. local_region ce ee.scopes t n b sz <=>
             local_region ce es.scopes s n b sz` by
    (rpt gen_tac >> simp[] >> irule local_region_wb_frame >> metis_tac[]) >>
  `FST (read_result cx raw ee) = FST (read_result cx raw es)` by
    (irule read_result_nonstorage_frame >> simp[]) >>
  `!v. read_result cx raw ee = (INL v,ee) <=>
        read_result cx raw es = (INL v,es)` by
    (gen_tac >> Cases_on `read_result cx raw es` >>
     Cases_on `read_result cx raw ee` >> gvs[] >>
     metis_tac[read_result_state]) >>
  `!root sz w n. FLOOKUP ce.ce_vars n = SOME (PtrVar (Var root) sz) /\
     lookup_var root s = SOME w ==> lookup_var root t = SOME w` by
    (rpt strip_tac >> gvs[wb_frame_def, loweringStateRelDefsTheory.local_ptrs_reserved_def] >>
     first_x_assum irule >> metis_tac[]) >>
  gvs[bodyIntCallProducerInterfaceTheory.intcall_vv_provenance_def] >>
  rpt strip_tac >>
  qpat_x_assum `p.ptr_location = LocMemory ==> _` drule >>
  disch_then drule_all >> strip_tac >> qexists `w` >> simp[] >>
  gvs[wb_frame_def]
  >~ [`FLOOKUP s.vs_allocas aid = SOME (b,sz)`]
  >- (disj1_tac >> qexistsl [`aid`, `b`, `sz`] >> simp[] >>
      first_assum ACCEPT_TAC)
  >~ [`local_val_at ce cx n (w2n w - b) tvt v`]
  >- (disj2_tac >> disj2_tac >> disj1_tac >>
      qexistsl [`n`, `b`, `sz`] >> simp[]) >>
  disj2_tac >> disj2_tac >> disj2_tac >>
  rename1 `lookup_var rootvar s = SOME rootword` >>
  qexistsl [`n`, `sz`, `entry`, `rootvar`, `rootword`, `k`] >> simp[] >>
  metis_tac[]
QED

Theorem pure_array_select_read[local]:
  expr_body_pre ce cx env obj es /\ ~expr_has_effect obj /\
  eval_expr cx obj es = (INL raw,st) /\
  expr_type obj = ArrayT et bd /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  ee.scopes = st.scopes /\ ee.immutables = st.immutables /\
  (!tr slot vt. raw <> PlaceR (StoragePlace tr slot vt)) /\
  read_result cx raw ee = (INL (ArrayV av),ee) /\
  array_index (ArrayTV etv bd) av i = SOME v ==>
  ?child. select_result cx (ArrayT et bd) raw (ValueSubscript (IntV i)) ee =
            (INL child,ee) /\ read_result cx child ee = (INL v,ee)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `evaluate_subscripts (ArrayTV etv bd) (ArrayV av)
      [ValueSubscript (IntV i)] = INL v` by
    simp[exprSimSubscriptArraySourceTheory.evaluate_array_subscript_result] >>
  Cases_on `raw`
  >~ [`read_result cx (HashMapRef tr slot tv key) _ = _`] >-
    gvs[read_result_def, raise_def]
  >~ [`Value value`] >-
    (gvs[read_result_def, return_def] >>
     drule_all exprSimSubscriptArraySourceTheory.select_value_read >> metis_tac[]) >>
  drule_all exprSimSubscriptArraySourceTheory.expr_body_pre_place_metadata >> strip_tac >>
  gnvs[] >> Cases_on `p`
  >~ [`StoragePlace tr slot vt`] >- metis_tac[]
  >~ [`MemoryPlace id path`] >-
    (`read_result cx (PlaceR (MemoryPlace id path)) st = (INL (ArrayV av),st)` by
       (`FST (read_result cx (PlaceR (MemoryPlace id path)) st) = INL (ArrayV av)` by
          (mp_tac (Q.INST [`r` |-> `PlaceR (MemoryPlace id path)`,
                            `s'` |-> `ee`, `s` |-> `st`]
             exprSimSubscriptArraySourceTheory.read_result_nonstorage_frame) >> simp[]) >>
        Cases_on `read_result cx (PlaceR (MemoryPlace id path)) st` >> gvs[] >>
        metis_tac[read_result_state]) >>
     drule_all bodyIntCallPostProvenanceLiveSourceTheory.effect_free_memory_result_selection >>
     strip_tac >>
     `subscripts_type entry.type path = SOME (ArrayTV etv bd)` by
       gvs[vyperPlaceTypingTheory.runtime_place_typed_memory] >>
     `lookup_scopes id ee.scopes = SOME entry` by simp[] >>
     qpat_x_assum `lookup_scopes id st.scopes = _` kall_tac >>
     drule_all live_memory_child_read >> metis_tac[]) >>
  rename1 `ImmutablePlace src id path` >>
  `runtime_place_typed cx ee (ImmutablePlace src id path) (ArrayTV etv bd)` by
    (qpat_x_assum `runtime_place_typed _ _ _ _` mp_tac >>
     Cases_on `ALOOKUP st.immutables cx.txn.target` >>
     simp[vyperPlaceTypingTheory.runtime_place_typed_immutable,
          get_immutables_def, get_address_immutables_def, bind_def, return_def, raise_def]) >>
  drule_all exprSimSubscriptArraySourceTheory.select_typed_immutable_read >> metis_tac[]
QED
