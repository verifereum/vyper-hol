(* Actual-index reconstruction boundaries for noncapturing array selection. *)
Theory bodyIntCallPostProvenanceArraySelector
Ancestors
  bodyIntCallPostProvenanceArrayMemoryFrame
  bodyIntCallPostProvenanceArrayImmutableFrame
  bodyIntCallPostProvenanceArrayLiveSource bodyIntCallPostProvenanceArrayCode
  bodyIntCallPostProvenanceArrayElement bodyIntCallPostProvenanceSelectors
  exprSimSubscriptArrayFrame exprSimSubscriptArraySource vyperState pair
  loweringPosts exprSimProps valueEncodingProofs valueEncodingDefs bodyIntCallArgType
  bodyIntCallPostProvenanceArrayOrigin bodySim placeTypingProps exprSimHypsDefs
  supportedExprTraverse gasOutcome gasSummary bodyIntCallFamAggSubscriptArraySetup
  bodyPtrMakeArrayConsSource

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

Theorem array_child_sub_layout[local]:
  val_wf (ArrayTV et bd) (ArrayV av) /\
  array_index (ArrayTV et bd) av i = SOME v ==>
  sub_layout (ArrayTV et bd) (ArrayV av)
    ((case bd of Fixed _ => 0 | Dynamic _ => 32) + Num i * type_memory_size et) et v
Proof
  strip_tac >>
  `sub_layout (ArrayTV et bd) (ArrayV av) 0 (ArrayTV et bd) (ArrayV av)` by
    simp[sub_layout_def] >>
  drule_all exprSimSubscriptArrayFramedTheory.sub_layout_array_element >> simp[]
QED

Theorem intcall_array_dynamic_memory_provenance[local]:
  intcall_vv_provenance ce cx (ArrayT et bd) sa sb ee raw
    (LocatedValue ann p) s /\ p.ptr_location = LocMemory /\
  read_result cx raw ee = (INL (ArrayV av),ee) /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  evaluate_type (get_tenv cx) et = SOME etv /\ ~dynarray_free (ArrayTV etv bd) /\
  read_result cx child ee = (INL v,ee) /\
  val_wf (ArrayTV etv bd) (ArrayV av) /\ value_has_type (ArrayTV etv bd) (ArrayV av) /\
  array_index (ArrayTV etv bd) av i = SOME v /\ val_wf etv v /\
  eval_operand p.ptr_operand s = SOME w /\
  j = (case bd of Fixed _ => 0 | Dynamic _ => 32) + Num i * type_memory_size etv /\
  eval_operand dst s = SOME (w + n2w j) /\ w2n (w + n2w j) = w2n w + j ==>
  intcall_vv_provenance ce cx et sa sb ee child
    (LocatedValue et (mk_ptr dst LocMemory)) s
Proof
  strip_tac >> drule_all array_child_sub_layout >> strip_tac >>
  drule_all array_element_footprint_contained >> strip_tac >>
  irule intcall_dynamic_memory_selection >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`ArrayT et bd`,`LocatedValue ann p`,`p.ptr_operand`,`raw`] >>
  gvs[arithmeticTheory.ADD_COMM]
QED

Theorem intcall_array_selection_provenance[local]:
  intcall_vv_provenance ce cx (ArrayT et bd) sa sb ee raw
    (LocatedValue ann p) s /\
  vv_post ctx func ce cx (Subscript et obj idx) es sa sb s0 ee child
    (LocatedValue et (mk_ptr dst p.ptr_location)) s /\
  (p.ptr_location = LocMemory \/ p.ptr_location = LocCode) /\
  read_result cx raw ee = (INL (ArrayV av),ee) /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  read_result cx child ee = (INL v,ee) /\
  val_wf (ArrayTV etv bd) (ArrayV av) /\ value_has_type (ArrayTV etv bd) (ArrayV av) /\
  array_index (ArrayTV etv bd) av i = SOME v /\ val_wf etv v /\
  eval_operand p.ptr_operand s = SOME w /\
  j = (case bd of Fixed _ => 0 | Dynamic _ => 32) + Num i * type_memory_size etv /\
  eval_operand dst s = SOME (w + n2w j) /\
  (p.ptr_location = LocMemory ==> w2n (w + n2w j) = w2n w + j) ==>
  intcall_vv_provenance ce cx et sa sb ee child
    (LocatedValue et (mk_ptr dst p.ptr_location)) s
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `p.ptr_location = LocMemory`
  >- (Cases_on `dynarray_free etv`
      >- (qpat_x_assum `intcall_vv_provenance _ _ _ _ _ _ _ _ _` kall_tac >>
          gvs[vv_post_def, bodyIntCallProducerInterfaceTheory.intcall_vv_provenance_def, vv_at_def,
              contextTheory.mk_ptr_def, vyperASTTheory.expr_type_def] >>
          rpt strip_tac >> gvs[] >> metis_tac[]) >>
      `~dynarray_free (ArrayTV etv bd)` by
        (strip_tac >>
         `mem_step_offset (ArrayTV etv bd) (ValueSubscript (IntV i)) = SOME (j,etv)` by
           (Cases_on `bd` >> Cases_on `av` >>
            gvs[mem_step_offset_def, vyperValueOperationTheory.array_index_def, val_wf_def,
                listTheory.oEL_THM, AllCaseEqs()]) >>
         fs[dynarray_free_def] >>
         first_x_assum (qspecl_then [`ValueSubscript (IntV i)::path`,`j+k`,`etv'`,`m`] mp_tac) >>
         simp[mem_path_offset_def]) >>
      metis_tac[intcall_array_dynamic_memory_provenance]) >>
  qpat_x_assum `intcall_vv_provenance _ _ _ _ _ _ _ _ _` kall_tac >>
  gvs[vv_post_def, vv_holds_def, bodyIntCallProducerInterfaceTheory.intcall_vv_provenance_def,
      contextTheory.mk_ptr_def, immutable_holds_def, vyperASTTheory.expr_type_def] >>
  metis_tac[]
QED

Theorem pure_array_element_summary[local]:
  expr_body_pre ce cx env obj es /\ ~expr_has_effect obj /\
  eval_expr cx obj es = (INL raw,st) /\ expr_type obj = ArrayT et bd /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  ee.scopes = st.scopes /\ ee.immutables = st.immutables /\ ee.gas_obs = [] /\
  (!tr slot vt. raw <> PlaceR (StoragePlace tr slot vt)) /\
  read_result cx raw ee = (INL (ArrayV av),ee) /\
  array_index (ArrayTV etv bd) av i = SOME v /\
  val_wf (ArrayTV etv bd) (ArrayV av) /\
  value_has_type (ArrayTV etv bd) (ArrayV av) /\ val_wf etv v /\ value_has_type etv v /\
  vv_post ctx func ce cx (Subscript (ArrayT et bd) obj idx) es sa sd s0 ee raw
    (LocatedValue ann p) q /\
  (p.ptr_location = LocMemory \/ p.ptr_location = LocCode) /\
  eval_operand p.ptr_operand q = SOME w /\
  j = (case bd of Fixed _ => 0 | Dynamic _ => 32) + Num i * type_memory_size etv /\
  eval_operand dst q = SOME (w + n2w j) /\
  (p.ptr_location = LocMemory ==> w2n (w + n2w j) = w2n w + j) /\
  intcall_vv_provenance ce cx (ArrayT et bd) sa sd ee raw (LocatedValue ann p) q /\
  gas_marked_path F ctx func s 0 (OK q) /\
  q.vs_current_bb = sd.cs_current_bb /\ q.vs_inst_idx = LENGTH sd.cs_current_insts ==>
  gas_summary_at F (ctx,func) []
    (select_result cx (ArrayT et bd) raw (ValueSubscript (IntV i))) (ee,s)
    (\res ee' q. ?child. res = INL child /\
      vv_post ctx func ce cx (Subscript et obj idx) es sa sd s0 ee' child
        (LocatedValue et (mk_ptr dst p.ptr_location)) q /\
      intcall_vv_provenance ce cx et sa sd ee' child
        (LocatedValue et (mk_ptr dst p.ptr_location)) q /\
      q.vs_current_bb = sd.cs_current_bb /\ q.vs_inst_idx = LENGTH sd.cs_current_insts)
    (\res ee' outcome. expr_exit res outcome)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all pure_array_select_read >> strip_tac >>
  qpat_assum `select_result _ _ _ _ _ = (INL _, _)`
    (assume_tac o MATCH_MP exprSimPropsTheory.select_result_memory_place) >>
  drule_all vv_post_array_element_general >> strip_tac >>
  drule_all intcall_array_selection_provenance >> strip_tac >>
  irule exprSimSubscriptArraySuffixTheory.select_result_counted_summary >> simp[] >>
  qexists_tac `OK q` >> simp[] >>
  `ee with gas_obs := [] = ee` by
    (Cases_on `ee` >> gvs[vyperStateTheory.evaluation_state_component_equality]) >>
  simp[] >> metis_tac[]
QED

Theorem located_array_subscript_path[local]:
  (loc = LocMemory \/ loc = LocCode) /\
  compile_array_subscript bop iop dyn cnt ws esz sgn
    (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca loc) sa = (dst,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved ce sa /\
  stmt_state_rel ctx func ce cx es s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. bop = Var x ==> not_fresh_at sa x) /\
  (!x. iop = Var x ==> not_fresh_at sa x) /\
  (!l. bop <> Label l) /\ (!l. iop <> Label l) /\
  eval_operand bop s = SOME b /\ eval_operand iop s = SOME i /\
  idx_in_range sgn i (if dyn then
    (if loc = LocMemory then mload (w2n b) s else immutable_copy_read ce.ce_is_ctor b s)
    else n2w cnt) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    eval_operand dst t = SOME ((if dyn then b + n2w ws else b) + i * n2w esz) /\
    stmt_state_rel ctx func ce cx es t /\
    (!x v. not_fresh_at sa x /\ lookup_var x s = SOME v ==> lookup_var x t = SOME v) /\
    (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==> FLOOKUP t.vs_allocas aid = SOME a) /\
    t.vs_memory = s.vs_memory /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >> Cases_on `loc = LocMemory`
  >- (gvs[] >> drule_all targetSubscriptMemoryTheory.target_memory_array_path >> simp[]) >>
  gvs[] >>
  `compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca LocCode =
     compile_imm_load_word ce.ce_is_ctor ce.ce_imm_alloca` by
    simp[FUN_EQ_THM, contextTheory.compile_ptr_load_def] >>
  gvs[] >> drule_all code_array_subscript_path >> simp[]
QED

Theorem located_array_length_read[local]:
  stmt_state_rel ctx func ce cx es s /\
  vv_holds ce cx (ArrayT et bd) raw (LocatedValue ann p) es s /\
  (p.ptr_location = LocMemory \/ p.ptr_location = LocCode) /\
  eval_operand p.ptr_operand s = SOME w /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  read_result cx raw es = (INL (ArrayV av),es) /\
  value_has_type (ArrayTV etv bd) (ArrayV av) ==>
  (case bd of Fixed n => n2w n | Dynamic _ =>
    if p.ptr_location = LocMemory then mload (w2n w) s
    else immutable_copy_read ce.ce_is_ctor w s) =
  n2w (array_length (ArrayTV etv bd) av)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> Cases_on `bd`
  >- (Cases_on `av` >>
      gvs[vyperTypingTheory.value_has_type_def, vyperValueOperationTheory.array_length_def]) >>
  simp[] >> Cases_on `p.ptr_location = LocMemory`
  >- (gvs[vv_holds_def, vyperValueTheory.evaluate_type_def] >>
      drule_all targetSubscriptMemoryTheory.target_memory_array_header >> simp[]) >>
  `immutable_holds ce cx (ArrayT et (Dynamic n)) raw w es s` by
    gvs[vv_holds_def] >>
  drule_all immutable_array_length_read >> simp[]
QED

Theorem located_array_subscript_abort_path[local]:
  (loc = LocMemory \/ loc = LocCode) /\
  compile_array_subscript bop iop dyn cnt ws esz sgn
    (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca loc) sa = (dst,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved ce sa /\
  stmt_state_rel ctx func ce cx es s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. bop = Var x ==> not_fresh_at sa x) /\
  (!x. iop = Var x ==> not_fresh_at sa x) /\ (!l. iop <> Label l) /\
  eval_operand bop s = SOME b /\ eval_operand iop s = SOME i /\
  ~idx_in_range sgn i (if dyn then
    (if loc = LocMemory then mload (w2n b) s else immutable_copy_read ce.ce_is_ctor b s)
    else n2w cnt) ==>
  ?t. gas_marked_path F ctx func s 0 (Abort Revert_abort t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> Cases_on `loc = LocMemory`
  >- (gvs[] >> drule_all targetSubscriptMemoryTheory.target_memory_array_abort_path >> simp[]) >>
  gvs[] >>
  `compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca LocCode =
     compile_imm_load_word ce.ce_is_ctor ce.ce_imm_alloca` by
    simp[FUN_EQ_THM, contextTheory.compile_ptr_load_def] >>
  gvs[] >> drule_all code_array_subscript_abort_path >> simp[]
QED

Theorem pure_array_valid_suffix[local]:
  expr_body_pre ce cx env obj es /\ ~expr_has_effect obj /\
  eval_expr cx obj es = (INL raw,st) /\ expr_type obj = ArrayT et bd /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  ee.scopes = st.scopes /\ ee.immutables = st.immutables /\ ee.gas_obs = [] /\
  (!tr slot vt. raw <> PlaceR (StoragePlace tr slot vt)) /\
  read_result cx raw ee = (INL (ArrayV av),ee) /\
  val_wf (ArrayTV etv bd) (ArrayV av) /\ value_has_type (ArrayTV etv bd) (ArrayV av) /\
  array_index (ArrayTV etv bd) av i = SOME v /\ val_wf etv v /\ value_has_type etv v /\
  valid_index (ArrayTV etv bd) av i /\ array_length (ArrayTV etv bd) av < dimword (:256) /\
  i = (if is_signed_type (expr_type idx) then w2i iw else &(w2n iw)) /\ iw = n2w (Num i) /\
  vv_post ctx func ce cx (Subscript (ArrayT et bd) obj idx) es sa sc s0 ee raw
    (LocatedValue (ArrayT et bd) p) s /\
  (p.ptr_location = LocMemory \/ p.ptr_location = LocCode) /\
  eval_operand p.ptr_operand s = SOME w /\ eval_operand iop s = SOME iw /\
  type_memory_bytes ce et = type_memory_size etv /\
  compile_array_subscript p.ptr_operand iop
    (case bd of Fixed _ => F | Dynamic _ => T) (case bd of Fixed n => n | Dynamic _ => 0)
    (word_scale p.ptr_location) (elem_size_in_location ce p.ptr_location et)
    (is_signed_type (expr_type idx))
    (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca p.ptr_location) sc = (dst,sd) /\
  fn_has_code sc sd func /\ local_ptrs_reserved ce sc /\ stmt_state_rel ctx func ce cx ee s /\
  ~s.vs_halted /\ s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sc x) /\ (!l. p.ptr_operand <> Label l) /\
  (!x. iop = Var x ==> not_fresh_at sc x) /\ (!l. iop <> Label l) /\
  (!q. (!x z. not_fresh_at sc x /\ lookup_var x s = SOME z ==> lookup_var x q = SOME z) /\
    (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
    q.vs_memory = s.vs_memory /\ stmt_state_rel ctx func ce cx ee q ==>
    vv_post ctx func ce cx (Subscript (ArrayT et bd) obj idx) es sa sd s0 ee raw
      (LocatedValue (ArrayT et bd) p) q /\
    intcall_vv_provenance ce cx (ArrayT et bd) sa sd ee raw
      (LocatedValue (ArrayT et bd) p) q) ==>
  gas_summary_at F (ctx,func) []
    (select_result cx (ArrayT et bd) raw (ValueSubscript (IntV i))) (ee,s)
    (\res ee' q. ?child. res = INL child /\
      vv_post ctx func ce cx (Subscript et obj idx) es sa sd s0 ee' child
        (LocatedValue et (mk_ptr dst p.ptr_location)) q /\
      intcall_vv_provenance ce cx et sa sd ee' child
        (LocatedValue et (mk_ptr dst p.ptr_location)) q /\
      q.vs_current_bb = sd.cs_current_bb /\ q.vs_inst_idx = LENGTH sd.cs_current_insts)
    (\res ee' outcome. expr_exit res outcome)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `vv_holds ce cx (ArrayT et bd) raw (LocatedValue (ArrayT et bd) p) ee s` by
    (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ s` mp_tac >>
     simp[vv_post_def, vyperASTTheory.expr_type_def]) >>
  drule_all located_array_length_read >> strip_tac >>
  drule_all exprSimSubscriptArraySuffixTheory.array_index_word_bounds >> strip_tac >>
  qpat_x_assum `i = if _ then _ else _` kall_tac >>
  `idx_in_range (is_signed_type (expr_type idx)) iw
    (if (case bd of Fixed _ => F | Dynamic _ => T) then
      (if p.ptr_location = LocMemory then mload (w2n w) s
       else immutable_copy_read ce.ce_is_ctor w s)
     else n2w (case bd of Fixed n => n | Dynamic _ => 0))` by
    (Cases_on `bd` >>
     qpat_x_assum `(case _ of Fixed _ => _ | Dynamic _ => _) = _` mp_tac >>
     simp_tac bool_ss (TypeBase.case_def_of ``:bound`` :: []) >>
     disch_then SUBST1_TAC >> metis_tac[]) >>
  drule_all located_array_subscript_path >> strip_tac >>
  `vv_post ctx func ce cx (Subscript (ArrayT et bd) obj idx) es sa sd s0 ee raw
      (LocatedValue (ArrayT et bd) p) t /\
    intcall_vv_provenance ce cx (ArrayT et bd) sa sd ee raw
      (LocatedValue (ArrayT et bd) p) t` by (first_x_assum irule >> simp[]) >>
  `eval_operand p.ptr_operand t = SOME w` by
    (irule exprBopSimPropsTheory.eval_operand_frame >>
     conj_tac >- simp[] >> qexistsl [`sc`,`s`] >> simp[]) >>
  `eval_operand dst t = SOME (w + n2w ((case bd of Fixed _ => 0 | Dynamic _ => 32) +
      Num i * type_memory_size etv))` by
    (Cases_on `bd` >> Cases_on `p.ptr_location = LocMemory` >>
     gvs[compileEnvTheory.word_scale_def, compileEnvTheory.elem_size_in_location_def,
         compileEnvTheory.is_slot_addressed_def, wordsTheory.word_mul_n2w,
         wordsTheory.word_add_n2w, AC wordsTheory.WORD_ADD_ASSOC wordsTheory.WORD_ADD_COMM]) >>
  irule pure_array_element_summary >> simp[] >>
  conj_tac >- metis_tac[] >>
  qexistsl [`ArrayT et bd`,`t`,`w`] >> simp[arithmeticTheory.ADD_COMM] >>
  strip_tac >> irule array_element_address_no_wrap >>
  goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`av`,`bd`,`i`] >> simp[] >>
  drule_at (Pos hd) exprSimSubscriptArraySuffixTheory.vv_post_memory_footprint_bound >>
  simp[vyperASTTheory.expr_type_def] >>
  disch_then irule >> simp[]
QED

Theorem pure_array_abort_suffix[local]:
  expr_body_pre ce cx env obj es /\
  eval_expr cx obj es = (INL raw,st) /\ expr_type obj = ArrayT et bd /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  ee.scopes = st.scopes /\ ee.immutables = st.immutables /\ ee.gas_obs = [] /\
  (!tr slot vt. raw <> PlaceR (StoragePlace tr slot vt)) /\
  read_result cx raw ee = (INL (ArrayV av),ee) /\
  value_has_type (ArrayTV etv bd) (ArrayV av) /\
  ~valid_index (ArrayTV etv bd) av i /\ array_length (ArrayTV etv bd) av < dimword (:256) /\
  i = (if is_signed_type (expr_type idx) then w2i iw else &(w2n iw)) /\
  vv_holds ce cx (ArrayT et bd) raw (LocatedValue (ArrayT et bd) p) ee s /\
  (p.ptr_location = LocMemory \/ p.ptr_location = LocCode) /\
  eval_operand p.ptr_operand s = SOME w /\ eval_operand iop s = SOME iw /\
  compile_array_subscript p.ptr_operand iop
    (case bd of Fixed _ => F | Dynamic _ => T) (case bd of Fixed n => n | Dynamic _ => 0)
    (word_scale p.ptr_location) (elem_size_in_location ce p.ptr_location et)
    (is_signed_type (expr_type idx))
    (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca p.ptr_location) sc = (dst,sd) /\
  fn_has_code sc sd func /\ local_ptrs_reserved ce sc /\ stmt_state_rel ctx func ce cx ee s /\
  ~s.vs_halted /\ s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sc x) /\
  (!x. iop = Var x ==> not_fresh_at sc x) /\ (!l. iop <> Label l) ==>
  gas_summary_at F (ctx,func) []
    (select_result cx (ArrayT et bd) raw (ValueSubscript (IntV i))) (ee,s)
    P (\res ee' outcome. expr_exit res outcome)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all located_array_length_read >> strip_tac >>
  drule_all exprSimSubscriptArraySuffixTheory.array_index_word_bounds >> strip_tac >>
  qpat_x_assum `i = if _ then _ else _` kall_tac >>
  `~idx_in_range (is_signed_type (expr_type idx)) iw
    (if (case bd of Fixed _ => F | Dynamic _ => T) then
      (if p.ptr_location = LocMemory then mload (w2n w) s
       else immutable_copy_read ce.ce_is_ctor w s)
     else n2w (case bd of Fixed n => n | Dynamic _ => 0))` by
    (Cases_on `bd` >>
     qpat_x_assum `(case _ of Fixed _ => _ | Dynamic _ => _) = _` mp_tac >>
     simp_tac bool_ss [TypeBase.case_def_of ``:bound``] >>
     disch_then SUBST1_TAC >> metis_tac[]) >>
  drule_all located_array_subscript_abort_path >> strip_tac >>
  `!al. av = SArrayV al ==> ?n. bd = Fixed n` by
    (rpt strip_tac >> gvs[vyperTypingTheory.value_has_type_def] >>
     Cases_on `bd` >> gvs[vyperTypingTheory.value_has_type_def]) >>
  drule_all exprSimSubscriptArraySuffixTheory.framed_array_select_error >> strip_tac >>
  irule exprSimSubscriptArraySuffixTheory.select_result_counted_summary >> simp[] >>
  qexists_tac `Abort Revert_abort t` >> simp[exprSimDefsTheory.expr_exit_def] >>
  `ee with gas_obs := [] = ee` by
    (Cases_on `ee` >> gvs[vyperStateTheory.evaluation_state_component_equality]) >>
  simp[fragExecTheory.exit_result_def]
QED


Theorem pure_array_suffix_summary[local]:
  expr_body_pre ce cx env obj es /\ ~expr_has_effect obj /\
  eval_expr cx obj es = (INL raw,st) /\ expr_type obj = ArrayT et bd /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  ee.scopes = st.scopes /\ ee.immutables = st.immutables /\ ee.gas_obs = [] /\
  (!tr slot vt. raw <> PlaceR (StoragePlace tr slot vt)) /\
  read_result cx raw ee = (INL (ArrayV av),ee) /\
  val_wf (ArrayTV etv bd) (ArrayV av) /\ value_has_type (ArrayTV etv bd) (ArrayV av) /\
  array_length (ArrayTV etv bd) av < dimword (:256) /\
  i = (if is_signed_type (expr_type idx) then w2i iw else &(w2n iw)) /\
  vv_post ctx func ce cx (Subscript (ArrayT et bd) obj idx) es sa sc s0 ee raw
    (LocatedValue (ArrayT et bd) p) s /\
  (p.ptr_location = LocMemory \/ p.ptr_location = LocCode) /\
  eval_operand p.ptr_operand s = SOME w /\ eval_operand iop s = SOME iw /\
  type_memory_bytes ce et = type_memory_size etv /\
  compile_array_subscript p.ptr_operand iop
    (case bd of Fixed _ => F | Dynamic _ => T) (case bd of Fixed n => n | Dynamic _ => 0)
    (word_scale p.ptr_location) (elem_size_in_location ce p.ptr_location et)
    (is_signed_type (expr_type idx))
    (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca p.ptr_location) sc = (dst,sd) /\
  fn_has_code sc sd func /\ local_ptrs_reserved ce sc /\ stmt_state_rel ctx func ce cx ee s /\
  ~s.vs_halted /\ s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sc x) /\ (!l. p.ptr_operand <> Label l) /\
  (!x. iop = Var x ==> not_fresh_at sc x) /\ (!l. iop <> Label l) /\
  (!q. (!x z. not_fresh_at sc x /\ lookup_var x s = SOME z ==> lookup_var x q = SOME z) /\
    (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
    q.vs_memory = s.vs_memory /\ stmt_state_rel ctx func ce cx ee q ==>
    vv_post ctx func ce cx (Subscript (ArrayT et bd) obj idx) es sa sd s0 ee raw
      (LocatedValue (ArrayT et bd) p) q /\
    intcall_vv_provenance ce cx (ArrayT et bd) sa sd ee raw
      (LocatedValue (ArrayT et bd) p) q) ==>
  gas_summary_at F (ctx,func) []
    (select_result cx (ArrayT et bd) raw (ValueSubscript (IntV i))) (ee,s)
    (\res ee' q. ?child. res = INL child /\
      vv_post ctx func ce cx (Subscript et obj idx) es sa sd s0 ee' child
        (LocatedValue et (mk_ptr dst p.ptr_location)) q /\
      intcall_vv_provenance ce cx et sa sd ee' child
        (LocatedValue et (mk_ptr dst p.ptr_location)) q /\
      q.vs_current_bb = sd.cs_current_bb /\ q.vs_inst_idx = LENGTH sd.cs_current_insts)
    (\res ee' outcome. expr_exit res outcome)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `valid_index (ArrayTV etv bd) av i`
  >- (drule vyperArrayTheory.array_index_valid >>
      pure_rewrite_tac[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
      rename1 `array_index (ArrayTV etv bd) av i = SOME v` >>
      `well_formed_type_value etv` by
        (drule (CONJUNCT1 vyperTypingTheory.evaluate_type_well_formed) >> simp[]) >>
      `value_has_type etv v` by
        (drule_at (Pos hd) vyperAssignPreservesTypeTheory.array_index_has_type >> simp[]) >>
      `val_wf etv v` by
        (irule valueTypingMemoryPropsTheory.value_has_type_memory_wf >> simp[]) >>
      `iw = n2w (Num i)` by
        (qpat_x_assum `valid_index _ _ _` mp_tac >>
         qpat_x_assum `i = _` mp_tac >> rpt (pop_assum kall_tac) >>
         Cases_on `is_signed_type (expr_type idx)` >> simp[integer_wordTheory.w2i_def] >>
         Cases_on `word_msb iw` >> simp[] >> rw[] >> gvs[]) >>
      drule_all pure_array_valid_suffix >> simp[]) >>
  `vv_holds ce cx (ArrayT et bd) raw (LocatedValue (ArrayT et bd) p) ee s` by
    gvs[vv_post_def, vyperASTTheory.expr_type_def] >>
  drule_all pure_array_abort_suffix >> simp[]
QED

Theorem enriched_array_base_endpoint[local]:
  vv_post ctx func ce cx obj es sa sb s0 st raw (LocatedValue (ArrayT et bd) p) u /\
  intcall_vv_provenance ce cx (ArrayT et bd) sa sb st raw (LocatedValue (ArrayT et bd) p) u /\
  expr_post ctx func ce cx idx st sb sc u ee iv iop s /\
  expr_type obj = ArrayT et bd /\ ~expr_has_effect obj /\
  is_word_type (expr_type idx) /\
  (p.ptr_location = LocCode \/ p.ptr_location = LocMemory) /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sb x) /\ (!l. p.ptr_operand <> Label l) /\
  (!x. iop = Var x ==> not_fresh_at sc x) /\ (!l. iop <> Label l) /\
  (!tr slot vt. raw <> PlaceR (StoragePlace tr slot vt)) /\
  ee.scopes = st.scopes /\ ee.immutables = st.immutables /\
  expr_sim_inv ce cx env st /\ stmt_state_rel ctx func ce cx es s0 /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sb /\
  MAP FDOM es.scopes = MAP FDOM st.scopes /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  sb.cs_next_var <= sc.cs_next_var /\ sb.cs_next_id <= sd.cs_next_id /\
  (!x w. not_fresh_at sc x /\ lookup_var x s = SOME w ==> lookup_var x q = SOME w) /\
  (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
  q.vs_memory = s.vs_memory /\ stmt_state_rel ctx func ce cx ee q ==>
  vv_post ctx func ce cx (Subscript (ArrayT et bd) obj idx) es sa sd s0 ee raw
    (LocatedValue (ArrayT et bd) p) q /\
  intcall_vv_provenance ce cx (ArrayT et bd) sa sd ee raw
    (LocatedValue (ArrayT et bd) p) q
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_post ctx func ce cx idx st sb sd u ee iv iop q` by
    (irule exprSimSubscriptArrayEndpointTheory.word_expr_post_readonly_tail >> simp[] >>
     qexistsl [`s`,`sc`] >> simp[]) >>
  qpat_x_assum `expr_post _ _ _ _ _ _ _ sc _ _ _ _ s` kall_tac >>
  `intcall_vv_provenance ce cx (expr_type obj) sa sb st raw
     (LocatedValue (ArrayT et bd) p) u` by simp[] >>
  drule_all enriched_array_base_representation >> strip_tac >>
  `wb_frame ce es st sa s0 u` by
    (gvs[vv_post_def, wb_frame_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `wb_frame ce st ee sb u q` by metis_tac[exprSimWordArgsTheory.expr_post_frame] >>
  `wb_frame ce es ee sa s0 q` by (drule_all exprSimWordArgsTheory.wb_frame_trans >> simp[]) >>
  `~expr_has_effect obj /\ ~expr_has_effect idx ==> pure_frame ce func es sa s0 q` by
    (strip_tac >>
     `pure_frame ce func es sa s0 u` by gvs[vv_post_def] >>
     `pure_frame ce func st sb u q` by
       (irule exprSimWordArgsTheory.expr_post_pure_frame >>
        qexistsl [`ctx`,`cx`,`idx`,`ee`,`iop`,`sd`,`iv`] >> simp[]) >>
     irule exprSimPropsTheory.pure_frame_trans >>
     conj_tac >- simp[] >>
     qexistsl [`st`,`sb`,`u`] >> fs[wb_frame_def]) >>
  conj_tac
  >- (irule exprSimHashTheory.vv_post_frame_intro >>
      simp[vyperASTTheory.expr_type_def, expr_has_effect_thm] >>
      qpat_x_assum `_ \/ _` strip_assume_tac >> simp[]) >>
  irule intcall_located_provenance_index_frame >>
  conj_tac >- simp[] >>
  qexistsl [`st`,`func`,`u`,`sb`] >> simp[] >>
  conj_tac
  >- (`?w. eval_operand p.ptr_operand u = SOME w` by
        (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
         simp[vv_post_def, vv_holds_def] >> metis_tac[]) >>
      Cases_on `p.ptr_operand` >>
      gvs[venomStateTheory.eval_operand_def, wb_frame_def]) >>
  gvs[vv_post_def, exprLoweringPropsTheory.stmt_state_rel_def,
      loweringStateRelDefsTheory.state_rel_def]
QED

Theorem pure_array_holds_view[local]:
  expr_body_pre ce cx env obj es /\
  eval_expr cx obj es = (INL r,st) /\ expr_type obj = ArrayT et bd /\
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) /\
  ee.scopes = st.scopes /\ ee.immutables = st.immutables /\
  vv_holds ce cx (ArrayT et bd) r (LocatedValue ann p) ee q /\
  (p.ptr_location = LocMemory \/ p.ptr_location = LocCode) ==>
  ?etv av w.
    evaluate_type (get_tenv cx) et = SOME etv /\
    evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
    read_result cx r ee = (INL (ArrayV av),ee) /\
    val_wf (ArrayTV etv bd) (ArrayV av) /\
    value_has_type (ArrayTV etv bd) (ArrayV av) /\
    eval_operand p.ptr_operand q = SOME w /\
    array_length (ArrayTV etv bd) av < dimword (:256)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all exprSimSourceTheory.expr_body_pre_runtime_typed >> strip_tac >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
  `?v w. read_result cx r ee = (INL v,ee) /\
           eval_operand p.ptr_operand q = SOME w` by
    (fs[vv_holds_def, immutable_holds_def] >> metis_tac[]) >>
  `FST (read_result cx r ee) = FST (read_result cx r st)` by
    (irule read_result_nonstorage_frame >> simp[]) >>
  `read_result cx r st = (INL v,st)` by
    (Cases_on `read_result cx r st` >> imp_res_tac read_result_state >> gvs[]) >>
  `value_has_type (ArrayTV tv bd) v` by metis_tac[] >>
  `val_wf (ArrayTV tv bd) v` by
    metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def] >>
  rename1 `read_result cx r ee = (INL (ArrayV av),ee)` >>
  Cases_on `bd` >> Cases_on `av` >>
  gvs[vyperTypingTheory.value_has_type_def,
      vyperValueTheory.type_slot_size_def, vyperValueOperationTheory.array_length_def] >>
  `n * 1 <= n * type_slot_size tv` by simp[arithmeticTheory.LE_MULT_LCANCEL] >>
  decide_tac
QED

Theorem enriched_array_index_suffix[local]:
  expr_body_pre ce cx env (Subscript et obj idx) es /\
  expr_type obj = ArrayT et bd /\ ~expr_has_effect obj /\
  eval_expr cx obj es = (INL raw,st) /\
  eval_expr cx idx st = (INL ir,ee) /\ read_result cx ir ee = (INL iv,ee) /\
  ee.scopes = st.scopes /\ ee.immutables = st.immutables /\ ee.gas_obs = [] /\
  (!tr slot vt. raw <> PlaceR (StoragePlace tr slot vt)) /\
  vv_post ctx func ce cx obj es sa sb s0 st raw (LocatedValue (ArrayT et bd) p) u /\
  intcall_vv_provenance ce cx (ArrayT et bd) sa sb st raw (LocatedValue (ArrayT et bd) p) u /\
  expr_post ctx func ce cx idx st sb sc u ee iv iop s /\
  (p.ptr_location = LocMemory \/ p.ptr_location = LocCode) /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sb x) /\ (!l. p.ptr_operand <> Label l) /\
  (!x. iop = Var x ==> not_fresh_at sc x) /\ (!l. iop <> Label l) /\
  expr_sim_inv ce cx env st /\ stmt_state_rel ctx func ce cx es s0 /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sb /\ local_ptrs_reserved ce sc /\
  MAP FDOM es.scopes = MAP FDOM st.scopes /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  sb.cs_next_var <= sc.cs_next_var /\ sb.cs_next_id <= sc.cs_next_id /\
  compile_array_subscript p.ptr_operand iop
    (case bd of Fixed _ => F | Dynamic _ => T) (case bd of Fixed n => n | Dynamic _ => 0)
    (word_scale p.ptr_location) (elem_size_in_location ce p.ptr_location et)
    (is_signed_type (expr_type idx))
    (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca p.ptr_location) sc = (dst,sd) /\
  fn_has_code sc sd func /\ ~s.vs_halted /\
  s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts ==>
  gas_summary_at F (ctx,func) []
    (select_result cx (ArrayT et bd) raw (ValueSubscript iv)) (ee,s)
    (\res ee' q. ?child. res = INL child /\
      vv_post ctx func ce cx (Subscript et obj idx) es sa sd s0 ee' child
        (LocatedValue et (mk_ptr dst p.ptr_location)) q /\
      intcall_vv_provenance ce cx et sa sd ee' child
        (LocatedValue et (mk_ptr dst p.ptr_location)) q /\
      q.vs_current_bb = sd.cs_current_bb /\ q.vs_inst_idx = LENGTH sd.cs_current_insts)
    (\res ee' outcome. expr_exit res outcome)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all exprSimSubscriptArraySourceTheory.expr_body_pre_array_subscript_base >> strip_tac >>
  drule_all exprSimSubscriptArraySourceTheory.expr_body_pre_array_subscript_index_after_base >> strip_tac >>
  drule_all exprSimSourceTheory.expr_body_pre_runtime_typed >> strip_tac >>
  `value_has_type tvt iv` by metis_tac[] >>
  drule_all exprSimSubscriptArraySuffixTheory.framed_array_index_post_view >> strip_tac >>
  `is_word_type (expr_type idx)` by
    (qpat_x_assum `value_has_type tvt iv` mp_tac >>
     qpat_x_assum `evaluate_type _ (expr_type idx) = _` mp_tac >>
     qpat_x_assum `iv = IntV i` SUBST1_TAC >> rpt (pop_assum kall_tac) >>
     Cases_on `expr_type idx` >>
     simp[vyperValueTheory.evaluate_type_def, AllCaseEqs(),
          vyperTypingTheory.value_has_type_def, compileEnvTheory.is_word_type_def] >>
     rpt strip_tac >> gvs[vyperTypingTheory.value_has_type_def, compileEnvTheory.is_word_type_def]) >>
  `stmt_state_rel ctx func ce cx ee s` by fs[expr_post_def] >>
  `cs_extends sc sd /\ sc.cs_next_var <= sd.cs_next_var /\ sc.cs_next_id <= sd.cs_next_id` by
    (qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ sc = _`
       (mp_tac o Q.AP_TERM `SND`) >> simp[] >> disch_then (SUBST1_TAC o SYM) >>
     rewrite_tac[GSYM exprLoweringPropsTheory.ci_mono_def] >>
     irule exprLoweringPropsTheory.ci_mono_compile_array_subscript >>
     simp[exprLoweringPropsTheory.ci_mono_compile_ptr_load]) >>
  suspend "finish"
QED

Resume enriched_array_index_suffix[finish]:
  `vv_post ctx func ce cx (Subscript (ArrayT et bd) obj idx) es sa sc s0 ee raw
    (LocatedValue (ArrayT et bd) p) s /\
   intcall_vv_provenance ce cx (ArrayT et bd) sa sc ee raw
    (LocatedValue (ArrayT et bd) p) s` by
    (irule enriched_array_base_endpoint >> simp[] >>
     conj_tac >- metis_tac[] >>
     qexistsl [`env`,`iop`,`iv`,`s`,`sb`,`sc`,`st`,`u`] >> simp[]) >>
  `vv_holds ce cx (ArrayT et bd) raw (LocatedValue (ArrayT et bd) p) ee s` by
    fs[vv_post_def, vyperASTTheory.expr_type_def] >>
  drule_all pure_array_holds_view >> strip_tac >>
  `type_memory_bytes ce et = type_memory_size etv` by
    (irule exprSimHypsTheory.expr_sim_inv_memory_size >> simp[] >>
     qexistsl [`cx`,`env`,`st`] >> simp[]) >>
  qpat_x_assum `iv = IntV i` SUBST_ALL_TAC >>
  irule pure_array_suffix_summary >> simp[] >>
  conj_tac >- (qexists_tac `env` >> simp[]) >>
  qexistsl [`iop`,`iw`,`sc`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> fs[loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[arithmeticTheory.LE_TRANS]) >>
  gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  irule enriched_array_base_endpoint >> simp[] >>
  conj_tac >- metis_tac[] >>
  qexistsl [`env`,`iop`,`IntV i`,`s`,`sb`,`sc`,`st`,`u`] >> simp[]
QED
Finalise enriched_array_index_suffix

Theorem enriched_array_index_suffix_gas_entries[local]:
  expr_body_pre ce cx env (Subscript et obj idx) es /\
  expr_type obj = ArrayT et bd /\ ~expr_has_effect obj /\
  eval_expr cx obj (es with gas_obs := g0) = (INL raw,st with gas_obs := g1) /\
  eval_expr cx idx (st with gas_obs := g1) = (INL ir,ee) /\ read_result cx ir ee = (INL iv,ee) /\
  ee.scopes = st.scopes /\ ee.immutables = st.immutables /\ ee.gas_obs = [] /\
  (!tr slot vt. raw <> PlaceR (StoragePlace tr slot vt)) /\
  vv_post ctx func ce cx obj es sa sb s0 st raw (LocatedValue (ArrayT et bd) p) u /\
  intcall_vv_provenance ce cx (ArrayT et bd) sa sb st raw (LocatedValue (ArrayT et bd) p) u /\
  expr_post ctx func ce cx idx st sb sc u ee iv iop s /\
  (p.ptr_location = LocMemory \/ p.ptr_location = LocCode) /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sb x) /\ (!l. p.ptr_operand <> Label l) /\
  (!x. iop = Var x ==> not_fresh_at sc x) /\ (!l. iop <> Label l) /\
  expr_sim_inv ce cx env st /\ stmt_state_rel ctx func ce cx es s0 /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sb /\ local_ptrs_reserved ce sc /\
  MAP FDOM es.scopes = MAP FDOM st.scopes /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  sb.cs_next_var <= sc.cs_next_var /\ sb.cs_next_id <= sc.cs_next_id /\
  compile_array_subscript p.ptr_operand iop
    (case bd of Fixed _ => F | Dynamic _ => T) (case bd of Fixed n => n | Dynamic _ => 0)
    (word_scale p.ptr_location) (elem_size_in_location ce p.ptr_location et)
    (is_signed_type (expr_type idx))
    (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca p.ptr_location) sc = (dst,sd) /\
  fn_has_code sc sd func /\ ~s.vs_halted /\
  s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts ==>
  gas_summary_at F (ctx,func) []
    (select_result cx (ArrayT et bd) raw (ValueSubscript iv)) (ee,s)
    (\res ee' q. ?child. res = INL child /\
      vv_post ctx func ce cx (Subscript et obj idx) es sa sd s0 ee' child
        (LocatedValue et (mk_ptr dst p.ptr_location)) q /\
      intcall_vv_provenance ce cx et sa sd ee' child
        (LocatedValue et (mk_ptr dst p.ptr_location)) q /\
      q.vs_current_bb = sd.cs_current_bb /\ q.vs_inst_idx = LENGTH sd.cs_current_insts)
    (\res ee' outcome. expr_exit res outcome)
Proof
  strip_tac >>
  qspecl_then [`es with gas_obs := g0`, `st with gas_obs := g1`]
    mp_tac (Q.GENL [`es`,`st`] enriched_array_index_suffix) >>
  simp[bodyPtrMakeArrayConsSourceTheory.literal_vv_post_marked_input,
       exprSimSubscriptArrayComposeTheory.vv_post_final_gas,
       exprSimSubscriptArrayComposeTheory.expr_post_initial_gas]
QED

Theorem body_array_base_nonstorage[local]:
  body_inv tops ctx ce cx /\ stmt_state_rel ctx func ce cx es s0 /\
  ~expr_has_effect obj /\ eval_expr cx obj es = (INL raw,st) /\
  compile_expr ce ty obj sa = (bvv,sb) /\
  (vv_location bvv = NONE \/ vv_location bvv = SOME LocMemory \/
   vv_location bvv = SOME LocCode) ==>
  !tr slot vt. raw <> PlaceR (StoragePlace tr slot vt)
Proof
  strip_tac >> irule intcall_array_base_nonstorage_lookup >>
  goal_assum (drule_at Any) >> simp[] >>
  drule body_inv_modules_aligned >> strip_tac >>
  gvs[exprLoweringPropsTheory.stmt_state_rel_def,
      loweringStateRelDefsTheory.state_rel_def] >> metis_tac[]
QED

(* Pending C1.9.11.8.3: preserved unfinished consumer; not a proved export.
Theorem intcall_noncapturing_array_subscript_outcome:
  (!env ty es sa sb vv s0.
    expr_body_pre ce cx env obj es /\ ~expr_has_effect obj /\
    compile_expr ce ty obj sa = (vv,sb) /\ fn_has_code sa sb func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
    gas_admissible (eval_expr cx obj) expr_vv_res_ok es /\
    stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome F (cx_tops cx) (ctx,func) (eval_expr cx obj) (es,s0)
      (\res ee t. ?tv. res = INL tv /\
        vv_post ctx func ce cx obj es sa sb s0 ee tv vv t /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        intcall_vv_provenance ce cx (expr_type obj) sa sb ee tv vv t)
      (\res ee r. expr_exit res r)) /\
  expr_sim_case F ctx func ce cx idx /\ expr_vv_case F ctx func ce cx idx /\
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env (Subscript ann obj idx) es /\
  ~expr_has_effect (Subscript ann obj idx) /\ expr_type obj = ArrayT et bd /\
  ~subscript_reads_base cx obj idx /\ ~copies_subscript_base ce obj idx /\
  compile_expr ce ty (Subscript ann obj idx) sa = (vv,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  gas_admissible (eval_expr cx (Subscript ann obj idx)) expr_vv_res_ok es /\
  stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func) (eval_expr cx (Subscript ann obj idx)) (es,s0)
    (\res ee t. ?tv. res = INL tv /\
      vv_post ctx func ce cx (Subscript ann obj idx) es sa sb s0 ee tv vv t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      intcall_vv_provenance ce cx ann sa sb ee tv vv t)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `place_type ce obj = ValPT (ArrayT et bd)` by
    (qpat_assum `expr_type obj = _` (fn th => once_rewrite_tac[GSYM th]) >>
     irule place_type_well_typed_on_defined >>
     drule_all exprSimSubscriptArraySourceTheory.expr_body_pre_array_subscript_base >>
     gvs[expr_body_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
  drule_all exprSimSubscriptArrayFramedTheory.compile_expr_array_subscript >> strip_tac >>
  rename1 `compile_expr ce ty obj sa = (bvv,sm)` >>
  drule exprSimUnwrapTheory.compile_expr_extends >> strip_tac >>
  drule (cj 2 exprLoweringPropsTheory.compile_expr_grows) >> strip_tac >>
  `cs_extends st2 sb /\ st2.cs_next_var <= sb.cs_next_var /\
   st2.cs_next_id <= sb.cs_next_id` by
    (qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ st2 = _`
       (mp_tac o Q.AP_TERM `SND`) >> simp[] >> disch_then (SUBST1_TAC o SYM) >>
     rewrite_tac[GSYM exprLoweringPropsTheory.ci_mono_def] >>
     irule exprLoweringPropsTheory.ci_mono_compile_array_subscript >>
     simp[exprLoweringPropsTheory.ci_mono_compile_ptr_load]) >>
  `cs_extends sm sb` by metis_tac[compileEnvTheory.cs_extends_trans] >>
  drule_all fragExecTheory.fn_has_code_split >> strip_tac >>
  `expr_body_pre ce cx env obj es` by
    metis_tac[exprSimSubscriptArraySourceTheory.expr_body_pre_array_subscript_base] >>
  `~expr_has_effect obj /\ ~expr_has_effect idx` by
    gvs[expr_has_effect_def, supported_expr_exists_def, expr_effect_root_def] >>
  `gas_admissible (eval_expr cx obj) expr_vv_res_ok es` by
    metis_tac[exprSimHypsTheory.expr_body_pre_vv_gas_admissible] >>
  qpat_x_assum `!env ty es sa sb vv s0. _` drule_all >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
        (strip_assume_tac o PURE_ONCE_REWRITE_RULE [gas_summary_at_def])
      >- suspend "normal"
      >> suspend "exit") >>
  suspend "exempt"
QED

Resume intcall_noncapturing_array_subscript_outcome[exit]:
  Cases_on `res` >- fs[] >> rename1 `INR exc` >>
  qexists_tac `marks` >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INR exc`,`es_end`,`r`] >> simp[] >>
  qpat_assum `~subscript_reads_base _ _ _` (fn th =>
    pure_once_rewrite_tac[MATCH_MP exprSimSubscriptArraySourceTheory.eval_expr_subscript_bind th]) >>
  conj_tac >- (irule gasSummaryComposeTheory.gas_marked_exec_bind_exception >>
               first_assum ACCEPT_TAC) >> fs[]
QED

Resume intcall_noncapturing_array_subscript_outcome[exempt]:
  qexists_tac `marks` >> disj2_tac >>
  qexistsl_tac [`err`,`ee`,`leaf`,`finish'`] >>
  qpat_assum `~subscript_reads_base _ _ _` (fn th =>
    pure_once_rewrite_tac[MATCH_MP exprSimSubscriptArraySourceTheory.eval_expr_subscript_bind th]) >>
  pure_rewrite_tac[vyperStateTheory.ignore_bind_def, vyperStateTheory.bind_assoc] >>
  irule gasExemptCertTheory.gas_exempt_cert_error_result >>
  first_assum ACCEPT_TAC
QED

Resume intcall_noncapturing_array_subscript_outcome[normal]:
  qpat_x_assum `(\res ee t. _) _ _ _` (strip_assume_tac o BETA_RULE) >>
  gnvs[] >>
  pure_rewrite_tac[GSYM gas_outcome_def] >>
  qpat_assum `~subscript_reads_base _ _ _`
    (irule o MATCH_MP exprSimSubscriptArrayComposeTheory.framed_array_after_base) >>
  simp[] >>
  goal_assum (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)) >> simp[] >>
  goal_assum (drule_at (Pat `lower_value _ _ _ _ _ = _`)) >> simp[] >>
  conj_tac >- suspend "suffix" >>
  `eval_expr cx obj
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
      (INL tv, es_end with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >>
     disch_then (qspec_then `[]` mp_tac o CONJUNCT1) >> simp[]) >>
  `expr_body_pre ce cx env idx (es_end with gas_obs := [])` by
    (irule exprSimSubscriptArraySourceTheory.expr_body_pre_array_subscript_index_after_base >>
     goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >> simp[] >>
     qexists_tac `ann` >> simp[]) >>
  conj_tac
  >- metis_tac[gas_marked_exec_def, fragGasModeTheory.gas_marked_path_exec,
               fragGasPathTheory.gas_path_normal] >>
  conj_tac >- metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  conj_tac >- metis_tac[fragExecTheory.fn_has_code_split] >>
  conj_tac
  >- (simp[gasContextTheory.gas_admissible_def] >> rpt strip_tac >>
      `expr_body_pre ce cx env idx (es_end with gas_obs := gs)` by fs[] >>
      drule_all (REWRITE_RULE [ETA_THM] exprSimSourceTheory.expr_body_pre_res_ok) >> simp[]) >>
  conj_tac
  >- (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`
        (mp_tac o CONJUNCT1 o REWRITE_RULE [vv_post_def]) >>
      simp[exprLoweringPropsTheory.stmt_state_rel_def,
           loweringStateRelDefsTheory.state_rel_gas_obs,
           exprLoweringPropsTheory.immutable_alloca_sep_def] >> metis_tac[]) >>
  qpat_x_assum `expr_sim_case _ _ _ _ _ idx` mp_tac >>
  simp[exprSimHypsDefsTheory.expr_sim_case_def] >> disch_then irule >>
  qexists_tac `env` >> simp[]
QED

Resume intcall_noncapturing_array_subscript_outcome[suffix]:
  rpt gen_tac >> strip_tac >>
  `vyperState$bind (eval_expr cx idx) (read_result cx)
     (es_end with gas_obs := gas_explicit imarks t.vs_gas_readings) =
     (INL v, raw with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ imarks _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >>
     disch_then (qspec_then `[]` mp_tac o CONJUNCT1) >> simp[]) >>
  `?ir. eval_expr cx idx
      (es_end with gas_obs := gas_explicit imarks t.vs_gas_readings) =
      (INL ir,raw with gas_obs := []) /\
      read_result cx ir (raw with gas_obs := []) = (INL v,raw with gas_obs := [])` by
    (qpat_x_assum `vyperState$bind _ _ _ = _` mp_tac >>
     simp[vyperStateTheory.bind_def, AllCaseEqs()] >> rpt strip_tac >>
     imp_res_tac vyperStateTheory.read_result_state >> gvs[] >> metis_tac[]) >>
  `eval_expr cx obj
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++
                          gas_explicit imarks t.vs_gas_readings) =
      (INL tv,es_end with gas_obs := gas_explicit imarks t.vs_gas_readings)` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ marks _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >>
     disch_then (qspec_then `gas_explicit imarks t.vs_gas_readings` mp_tac o CONJUNCT1) >>
     simp[]) >>
  `raw.scopes = es_end.scopes /\ raw.immutables = es_end.immutables` by
    (drule_all bodyIntCallJointPureSourceTheory.effect_free_eval_expr_frame >>
     disch_then (fn th => mp_tac (Q.AP_TERM `\s:evaluation_state. s.scopes` th) >>
       mp_tac (Q.AP_TERM `\s:evaluation_state. s.immutables` th)) >> simp[]) >>
  suspend "located"
QED
Resume intcall_noncapturing_array_subscript_outcome[located]:
  `~u.vs_halted` by
    metis_tac[gas_marked_exec_def, fragGasModeTheory.gas_marked_path_exec,
              fragGasPathTheory.gas_path_normal] >>
  `local_ptrs_reserved ce sm /\ local_ptrs_reserved ce st2` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `expr_body_pre ce cx env idx
     (es_end with gas_obs := gas_explicit imarks t.vs_gas_readings)` by
    (irule exprSimSubscriptArraySourceTheory.expr_body_pre_array_subscript_index_after_base >>
     goal_assum (drule_at (Pat `eval_expr cx obj _ = _`)) >> simp[] >>
     qexists_tac `ann` >> simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM es_end.scopes` by
    (qpat_x_assum `eval_expr cx obj _ = _`
      (mp_then Any mp_tac
       vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom) >> simp[]) >>
  Cases_on `bvv` >- suspend "stack" >>
  rename1 `LocatedValue bty p` >>
  `bty = ArrayT et bd` by
    (qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[vv_post_def, vv_holds_def, effect_free_post_value_type,
          compileEnvTheory.is_bytestring_type_def]) >>
  gvs[contextTheory.vv_location_def, contextTheory.vv_operand_def] >>
  Cases_on `p.ptr_location = LocMemory \/ p.ptr_location = LocCode`
  >- suspend "memory_code" >>
  suspend "other_location"
QED
Resume intcall_noncapturing_array_subscript_outcome[memory_code]:
  drule_all intcall_array_subscript_annotation >> strip_tac >> gnvs[] >>
  `!tr slot vt. tv <> PlaceR (StoragePlace tr slot vt)` by
    (irule body_array_base_nonstorage >> simp[contextTheory.vv_location_def] >>
     goal_assum (drule_at (Pat `eval_expr cx obj _ = _`)) >> simp[] >>
     goal_assum (drule_at (Pat `compile_expr _ _ _ _ = _`)) >>
     simp[contextTheory.vv_location_def] >>
     goal_assum (drule_at (Pat `body_inv _ _ _ _`)) >> simp[] >> metis_tac[]) >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sm x` by
    (qpat_x_assum `compile_expr ce ty obj sa = _`
       (mp_then Any mp_tac (CONJUNCT1 exprOperandVarTheory.compiler_compile_var)) >>
     simp[contextTheory.vv_operand_def]) >>
  `!x. iop = Var x ==> not_fresh_at st2 x` by
    (qpat_x_assum `lower_value _ _ _ _ _ = _`
       (mp_then Any mp_tac exprOperandVarTheory.compile_lower_value_var) >> simp[]) >>
  `!l. p.ptr_operand <> Label l` by
    (drule exprSimSubscriptArrayOriginTheory.compile_array_pointer_not_label >>
     disch_then irule >> simp[] >> qexists_tac `env` >>
     fs[expr_body_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
  `!l. iop <> Label l` by
    (drule exprWordOperandTheory.lower_value_word_shape >>
     disch_then (qspec_then `env` mp_tac) >> simp[] >>
     impl_tac >- (conj_tac >- fs[expr_body_pre_def] >>
         metis_tac[exprSimSourceTheory.expr_body_pre_var_types_well_formed]) >> simp[]) >>
  simp[AC CONJ_ASSOC CONJ_COMM] >>
  irule (SRULE [AC CONJ_ASSOC CONJ_COMM] enriched_array_index_suffix) >> simp[] >>
  FAIL_TAC "suffix interface"
QED
Finalise intcall_noncapturing_array_subscript_outcome

*)
