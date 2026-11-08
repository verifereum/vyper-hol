(* Transport metadata of a captured argument, without selecting another run. *)
Theory bodyIntCallHeldFrame
Ancestors
  bodyIntCallProducerInterface bodyIntCallSourceFrame
  bodyIntCallArgOwnedFrame bodyIntCallArgLocalFrame bodyIntCallStorageFrame
  exprSimSubscriptArrayFrame exprSimProps loweringPosts exprLoweringProps
  compileEnv context bodyMemAssignTopCopySem

Theorem intcall_vv_provenance_outcomes[simp]:
  intcall_vv_provenance ce cx ty sa sb
    (es with <|outcomes := os; gas_obs := gs|>) raw vv s <=>
  intcall_vv_provenance ce cx ty sa sb es raw vv s
Proof
  simp[intcall_vv_provenance_def, read_result_outcomes_iff]
QED

(* Restatement of the [local] exprSimIfExp$ifexp_vv_at_alloc_frame
   (lowering/exprSimIfExpScript.sml:270), which this branch can't export;
   to be deduplicated at the trunk merge (moved next to vv_at_def). *)
Theorem held_vv_at_alloc_frame[local]:
  vv_at cenv cx ty sa sb es raw vv s /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
               FLOOKUP q.vs_allocas aid = SOME entry) /\
  eval_operand (vv_operand vv) q = eval_operand (vv_operand vv) s /\
  (!n b sz. local_region cenv es.scopes q n b sz <=>
            local_region cenv es.scopes s n b sz) /\
  sb.cs_next_id <= sm.cs_next_id ==>
  vv_at cenv cx ty sa sm es raw vv q
Proof
  Cases_on `vv` >>
  simp[vv_at_def, vv_operand_def, expr_val_at_def] >>
  rpt strip_tac >> gvs[]
  >>~- ([`FLOOKUP s.vs_allocas aid = SOME (b,sz)`],
        disj1_tac >> qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >>
        metis_tac[])
  >>~- ([`local_region cenv es.scopes s n b sz`],
        disj2_tac >> disj1_tac >> qexistsl_tac [`n`, `b`, `sz`] >> simp[])
QED

Theorem intcall_vv_provenance_frame:
  intcall_vv_provenance ce cx ty sa sm es raw vv s /\
  eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s /\
  wb_frame ce es sm s t /\ local_ptrs_reserved ce sm /\
  local_ptrs_rel func ce es.scopes s /\
  sm.cs_next_id <= sn.cs_next_id ==>
  intcall_vv_provenance ce cx ty sa sn es raw vv t
Proof
  strip_tac >>
  `!n b sz. local_region ce es.scopes t n b sz <=>
             local_region ce es.scopes s n b sz` by
    (rpt gen_tac >> irule local_region_wb_frame >> metis_tac[]) >>
  `!n p sz w. local_region ce es.scopes s n (w2n w) sz /\
    FLOOKUP ce.ce_vars n = SOME (PtrVar (Var p) sz) /\
    lookup_var p s = SOME w ==> lookup_var p t = SOME w` by
    (rpt strip_tac >> gvs[wb_frame_def, local_ptrs_reserved_def] >>
     first_x_assum irule >> simp[] >> metis_tac[]) >>
  Cases_on `vv` >>
  gvs[intcall_vv_provenance_def, vv_operand_def, wb_frame_def] >>
  rpt strip_tac >> first_x_assum drule_all >> strip_tac >>
  qexists_tac `w` >> simp[]
  >>~- ([`FLOOKUP s.vs_allocas aid = SOME (b,sz)`],
    disj1_tac >> qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >>
    metis_tac[arithmeticTheory.LESS_LESS_EQ_TRANS])
  >- (disj2_tac >> disj2_tac >> disj1_tac >>
      qexistsl_tac [`n`, `b`, `sz`] >> simp[])
  >- (disj2_tac >> disj2_tac >> disj2_tac >>
      rename1 `lookup_var rootp s = SOME rootw` >>
      qexistsl_tac [`n`, `sz`, `entry`, `rootp`, `rootw`, `k`] >> simp[] >>
      first_x_assum irule >> simp[] >> qexistsl_tac [`n`, `sz`] >> simp[])
  >- (disj2_tac >> disj2_tac >> disj1_tac >>
      qexistsl_tac [`n`, `b`, `sz`] >> simp[])
  >> disj2_tac >> disj2_tac >> disj2_tac >>
  rename1 `lookup_var rootp s = SOME rootw` >>
  qexistsl_tac [`n`, `sz`, `entry`, `rootp`, `rootw`, `k`] >> simp[] >>
  first_x_assum irule >> simp[] >> qexistsl_tac [`n`, `sz`] >> simp[]
QED

Theorem intcall_provenance_memory_value:
  intcall_vv_provenance ce cx ty sa sm es raw vv s /\
  ((?t'. vv = StackValue t' op /\ ~is_word_type ty) \/
   (?t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory /\
           op = p.ptr_operand)) /\
  read_result cx raw es = (INL v,es) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_operand op s = SOME w /\ val_wf tv v /\
  val_in_memory tv v (w2n w) s.vs_memory /\
  vv_post ctx func ce cx e es sm sn s ee r ev t /\
  ee.scopes = es.scopes /\ expr_sim_inv ce cx env es /\
  local_ptrs_reserved ce sm ==>
  val_in_memory tv v (w2n w) t.vs_memory
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `intcall_vv_provenance _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[intcall_vv_provenance_def] >> strip_tac >>
  first_x_assum drule_all >> strip_tac >> gvs[]
  >- (irule vv_post_old_buffer_value >> goal_assum (drule_at Any) >>
      metis_tac[])
  >- (irule vv_post_old_buffer_value >> metis_tac[])
  >- (irule val_in_memory_footprint_agree >> simp[] >> qexists_tac `s.vs_memory` >>
      simp[valueEncodingTheory.mem_bytes_at_def])
  >- (irule val_in_memory_footprint_agree >> simp[] >> qexists_tac `s.vs_memory` >>
      simp[valueEncodingTheory.mem_bytes_at_def])
  >- (`locals_kept ce es s t` by gvs[vv_post_def] >>
      drule_all locals_kept_dynarray_free_value >> strip_tac >>
      irule val_in_memory_footprint_agree >> simp[] >>
      qexists_tac `s.vs_memory` >> simp[])
  >- (`locals_kept ce es s t` by gvs[vv_post_def] >>
      drule_all locals_kept_dynarray_free_value >> strip_tac >>
      irule val_in_memory_footprint_agree >> simp[] >>
      qexists_tac `s.vs_memory` >> simp[]) >>
  rename1 `lookup_var p s = SOME rootw` >>
  `not_fresh_at sm p` by
    (gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `val_in_memory tv v (w2n rootw + k) t.vs_memory` by
    (irule vv_post_local_sub_layout_value >> goal_assum (drule_at Any) >>
     metis_tac[]) >>
  gvs[arithmeticTheory.ADD_COMM]
QED

Theorem intcall_memory_holds_frame:
  vv_holds ce cx ty raw vv es s /\
  intcall_vv_provenance ce cx ty sa sm es raw vv s /\
  ((?sty op. vv = StackValue sty op) \/
   (?sty p. vv = LocatedValue sty p /\ p.ptr_location = LocMemory)) /\
  (!v tv. read_result cx raw es = (INL v,es) /\
          evaluate_type (get_tenv cx) ty = SOME tv ==>
          val_wf tv v /\ value_has_type tv v) /\
  eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s /\
  vv_post ctx func ce cx e es sm sn s ee r ev t /\
  ee.scopes = es.scopes /\ expr_sim_inv ce cx env es /\
  local_ptrs_reserved ce sm ==>
  vv_holds ce cx ty raw vv es t
Proof
  strip_tac >> Cases_on `vv` >>
  gvs[vv_holds_def, vv_operand_def, expr_val_rel_def]
  >- (rpt strip_tac >> Cases_on `is_word_type ty`
      >- gvs[] >> gvs[] >>
      irule intcall_provenance_memory_value >> metis_tac[])
  >> (rpt strip_tac
      >- (irule intcall_provenance_memory_value >> metis_tac[])
      >> irule exprSimPropsTheory.val_in_memory_word_type >>
      simp[] >> conj_tac >- metis_tac[] >>
      irule intcall_provenance_memory_value >> metis_tac[])
QED

Theorem intcall_held_holds_storage_frame:
  vv_holds ce cx ty raw vv es s /\
  intcall_vv_provenance ce cx ty sa sm es raw vv s /\
  vv_storage_live cx vv es s /\
  (!v tv. read_result cx raw es = (INL v,es) /\
          evaluate_type (get_tenv cx) ty = SOME tv ==>
          val_wf tv v /\ value_has_type tv v) /\
  eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s /\
  vv_post ctx func ce cx e es sm sn s ee r ev t /\
  ee.scopes = es.scopes /\ expr_sim_inv ce cx env es /\
  local_ptrs_reserved ce sm /\
  (!tr. storage_agree (storage_dead cx tr (get_storage cx es tr))
      (get_storage cx es tr)
      (if tr then contract_transient t else contract_storage t)) ==>
  vv_holds ce cx ty raw vv es t
Proof
  strip_tac >> Cases_on `vv`
  >- (irule intcall_memory_holds_frame >> metis_tac[]) >>
  rename1 `LocatedValue sty p` >> Cases_on `p.ptr_location = LocMemory`
  >- (irule intcall_memory_holds_frame >> metis_tac[]) >>
  gvs[vv_holds_def, vv_operand_def] >>
  Cases_on `p.ptr_location` >> gvs[]
  >- (irule storage_holds_live_endpoint >> goal_assum (drule_at Any) >>
      metis_tac[])
  >- (irule storage_holds_live_endpoint >> goal_assum (drule_at Any) >>
      metis_tac[]) >>
  gvs[intcall_vv_provenance_def, immutable_holds_def] >>
  metis_tac[]
QED

Theorem intcall_held_holds_frame:
  vv_holds ce cx ty raw vv es s /\
  intcall_vv_provenance ce cx ty sa sm es raw vv s /\
  vv_storage_live cx vv es s /\
  (!v tv. read_result cx raw es = (INL v,es) /\
          evaluate_type (get_tenv cx) ty = SOME tv ==>
          val_wf tv v /\ value_has_type tv v) /\
  eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s /\
  vv_post ctx func ce cx e es sm sn s ee r ev t /\
  ee.scopes = es.scopes /\ expr_sim_inv ce cx env es /\
  local_ptrs_reserved ce sm /\ stmt_state_rel ctx func ce cx es t ==>
  vv_holds ce cx ty raw vv es t
Proof
  strip_tac >> irule intcall_held_holds_storage_frame >>
  goal_assum (drule_at Any) >>
  metis_tac[topcopy_initial_agree]
QED

Theorem intcall_held_source_outcomes:
  (vv_holds ce cx ty raw vv (es with <|outcomes := os; gas_obs := gs|>) s <=>
   vv_holds ce cx ty raw vv es s) /\
  (vv_at ce cx ty sa sb (es with <|outcomes := os; gas_obs := gs|>) raw vv s <=>
   vv_at ce cx ty sa sb es raw vv s) /\
  (vv_storage_live cx vv (es with <|outcomes := os; gas_obs := gs|>) s <=>
   vv_storage_live cx vv es s)
Proof
  Cases_on `vv` >>
  simp[vv_holds_def, vv_at_def, expr_val_at_def,
       read_result_outcomes_iff, immutable_holds_def, storage_holds_outcomes,
       vyperStorageBackendTheory.get_storage_def]
QED

Theorem intcall_held_storage_endpoint:
  vv_holds ce cx ty raw vv es s /\ vv_at ce cx ty sa sm es raw vv s /\
  intcall_vv_provenance ce cx ty sa sm es raw vv s /\
  vv_storage_live cx vv es s /\
  (!v tv. read_result cx raw es = (INL v,es) /\
          evaluate_type (get_tenv cx) ty = SOME tv ==>
          val_wf tv v /\ value_has_type tv v) /\
  eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s /\
  vv_post ctx func ce cx e es sm sn s ee r ev t /\
  ee.scopes = es.scopes /\ expr_sim_inv ce cx env es /\
  local_ptrs_reserved ce sm /\ local_ptrs_rel func ce es.scopes s /\
  (!tr. storage_agree (storage_dead cx tr (get_storage cx es tr))
      (get_storage cx es tr)
      (if tr then contract_transient t else contract_storage t)) /\
  wb_frame ce es sm s t /\ sm.cs_next_id <= sn.cs_next_id ==>
  vv_holds ce cx ty raw vv es t /\ vv_at ce cx ty sa sn es raw vv t /\
  intcall_vv_provenance ce cx ty sa sn es raw vv t /\
  vv_storage_live cx vv es t
Proof
  strip_tac >>
  `!n b sz. local_region ce es.scopes t n b sz <=>
             local_region ce es.scopes s n b sz` by
    (rpt gen_tac >> irule local_region_wb_frame >> metis_tac[]) >>
  conj_tac >- (irule intcall_held_holds_storage_frame >> metis_tac[]) >>
  conj_tac >- (irule held_vv_at_alloc_frame >> gvs[wb_frame_def] >> metis_tac[]) >>
  conj_tac >- (irule intcall_vv_provenance_frame >> metis_tac[]) >>
  Cases_on `vv` >> gvs[vv_operand_def]
QED

Theorem intcall_held_endpoint:
  vv_holds ce cx ty raw vv es s /\ vv_at ce cx ty sa sm es raw vv s /\
  intcall_vv_provenance ce cx ty sa sm es raw vv s /\
  vv_storage_live cx vv es s /\
  (!v tv. read_result cx raw es = (INL v,es) /\
          evaluate_type (get_tenv cx) ty = SOME tv ==>
          val_wf tv v /\ value_has_type tv v) /\
  eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s /\
  vv_post ctx func ce cx e es sm sn s ee r ev t /\
  ee.scopes = es.scopes /\ expr_sim_inv ce cx env es /\
  local_ptrs_reserved ce sm /\ local_ptrs_rel func ce es.scopes s /\
  stmt_state_rel ctx func ce cx es t /\ wb_frame ce es sm s t /\
  sm.cs_next_id <= sn.cs_next_id ==>
  vv_holds ce cx ty raw vv es t /\ vv_at ce cx ty sa sn es raw vv t /\
  intcall_vv_provenance ce cx ty sa sn es raw vv t /\
  vv_storage_live cx vv es t
Proof
  strip_tac >> irule intcall_held_storage_endpoint >>
  goal_assum (drule_at Any) >> metis_tac[topcopy_initial_agree]
QED

Theorem intcall_held_endpoint_outcomes:
  vv_holds ce cx ty raw vv es s /\ vv_at ce cx ty sa sm es raw vv s /\
  intcall_vv_provenance ce cx ty sa sm es raw vv s /\
  vv_storage_live cx vv es s /\
  (!v tv. read_result cx raw es = (INL v,es) /\
          evaluate_type (get_tenv cx) ty = SOME tv ==>
          val_wf tv v /\ value_has_type tv v) /\
  eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s /\
  vv_post ctx func ce cx e es sm sn s ee r ev t /\
  ee.scopes = es.scopes /\ expr_sim_inv ce cx env es /\
  local_ptrs_reserved ce sm /\ local_ptrs_rel func ce es.scopes s /\
  stmt_state_rel ctx func ce cx es t /\ wb_frame ce es sm s t /\
  sm.cs_next_id <= sn.cs_next_id ==>
  vv_holds ce cx ty raw vv (es with <|outcomes := os; gas_obs := gs|>) t /\
  vv_at ce cx ty sa sn (es with <|outcomes := os; gas_obs := gs|>) raw vv t /\
  intcall_vv_provenance ce cx ty sa sn
    (es with <|outcomes := os; gas_obs := gs|>) raw vv t /\
  vv_storage_live cx vv (es with <|outcomes := os; gas_obs := gs|>) t
Proof
  simp[intcall_held_source_outcomes] >> metis_tac[intcall_held_endpoint]
QED

(* The endpoint relation belongs to the source after argument evaluation;
   only its storage observations are used to retain earlier arguments. *)
Theorem intcall_held_updated_endpoint_outcomes:
  vv_holds ce cx ty raw vv es s /\ vv_at ce cx ty sa sm es raw vv s /\
  intcall_vv_provenance ce cx ty sa sm es raw vv s /\
  vv_storage_live cx vv es s /\
  (!v tv. read_result cx raw es = (INL v,es) /\
          evaluate_type (get_tenv cx) ty = SOME tv ==>
          val_wf tv v /\ value_has_type tv v) /\
  eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s /\
  vv_post ctx func ce cx e es sm sn s ee r ev t /\
  ee = es with <|outcomes := ee.outcomes; gas_obs := ee.gas_obs|> /\
  ee.scopes = es.scopes /\ expr_sim_inv ce cx env es /\
  local_ptrs_reserved ce sm /\ local_ptrs_rel func ce es.scopes s /\
  stmt_state_rel ctx func ce cx ee t /\ wb_frame ce es sm s t /\
  sm.cs_next_id <= sn.cs_next_id ==>
  vv_holds ce cx ty raw vv (es with <|outcomes := os; gas_obs := gs|>) t /\
  vv_at ce cx ty sa sn (es with <|outcomes := os; gas_obs := gs|>) raw vv t /\
  intcall_vv_provenance ce cx ty sa sn
    (es with <|outcomes := os; gas_obs := gs|>) raw vv t /\
  vv_storage_live cx vv (es with <|outcomes := os; gas_obs := gs|>) t
Proof
  strip_tac >>
  `!tr. storage_agree (storage_dead cx tr (get_storage cx es tr))
      (get_storage cx es tr)
      (if tr then contract_transient t else contract_storage t)` by
    (gen_tac >> drule topcopy_initial_agree >>
     disch_then (qspec_then `tr` mp_tac) >>
     qpat_x_assum `ee = _` SUBST1_TAC >>
     Cases_on `tr` >> simp[vyperStorageBackendTheory.get_storage_def]) >>
  simp[intcall_held_source_outcomes] >>
  metis_tac[intcall_held_storage_endpoint]
QED
