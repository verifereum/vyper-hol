(* Transport metadata of a captured argument, without selecting another run. *)
Theory bodyIntCallHeldFrame
Ancestors
  bodyIntCallProducerInterface bodyIntCallSourceFrame
  bodyIntCallArgOwnedFrame bodyIntCallArgLocalFrame bodyIntCallStorageFrame
  exprSimSubscriptArrayFrame exprSimProps loweringPosts exprLoweringProps
  compileEnv context

Theorem intcall_vv_provenance_outcomes[simp]:
  intcall_vv_provenance ce cx ty sa sb
    (es with <|outcomes := os; gas_obs := gs|>) raw vv s <=>
  intcall_vv_provenance ce cx ty sa sb es raw vv s
Proof
  simp[intcall_vv_provenance_def, read_result_outcomes_iff]
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
