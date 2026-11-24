(* Physical resources of the original VV, across a fixed target endpoint. *)
Theory bodySavedTargetPtrMods
Ancestors
  bodyFullPostsMods bodyFullShadowBodyInv bodyPtrDefs exprSimMemDefs
  logValueFramePtr exprBopSimProps valueEncodingProofs loweringPosts
  stateRelProj stateRelProjStorage accountsRelProps vyperStorageFootprint
  exprLoweringProps loweringStateRelDefs venomState context words arithmetic
  ptrDiscipline vyperStorageBackend pred_set valueEncodingDefs
  exprPtrUnwrapStorageFacts sourceUnitExecution

Theorem saved_footprint_window[local]:
  wb_frame cenv es es sm s u /\
  ghost_kept_at lo cenv es sm (G : string |-> num # num) tn s Gu tnu /\
  ((?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ aid < sm.cs_next_id /\
      b <= p /\ p + len <= b + sz /\
      (!n lb lsz. local_region cenv es.scopes s n lb lsz ==>
        b + sz <= lb \/ lb + lsz <= b)) \/
   (?n b sz. local_region cenv es.scopes s n b sz /\ b <= p /\ p + len <= b + sz) \/
   len = 0) ==>
  mem_bytes_at p len u.vs_memory = mem_bytes_at p len s.vs_memory /\
  (!i. p <= i /\ i < p + len /\ i IN tnu.t_mem ==> i IN tn.t_mem)
Proof
  strip_tac
  >- (fs[wb_frame_def, ghost_kept_at_def] >>
      `mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz s.vs_memory` by
        (qpat_assum `!aid off sz. _ ==> mem_bytes_at _ _ _ = _`
           (qspecl_then [`aid`,`b`,`sz`] mp_tac) >> metis_tac[]) >>
      conj_tac >- (drule mem_bytes_at_agree_window >> metis_tac[ADD_COMM]) >>
      rpt strip_tac >>
      `b <= i /\ i < b + sz` by decide_tac >>
      qpat_assum `!aid off sz i. _ ==> i IN tn.t_mem`
        (qspecl_then [`aid`,`b`,`sz`,`i`] mp_tac) >> metis_tac[])
  >- (fs[wb_frame_def, locals_kept_def, ghost_kept_at_def] >>
      `mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz s.vs_memory` by
        (qpat_assum `!n b sz. _ ==> mem_bytes_at _ _ _ = _`
           (qspecl_then [`n`,`b`,`sz`] mp_tac) >> simp[]) >>
      conj_tac >- (drule mem_bytes_at_agree_window >> metis_tac[ADD_COMM]) >>
      rpt strip_tac >>
      `b <= i /\ i < b + sz` by decide_tac >>
      qpat_assum `!n b sz i. _ ==> i IN tn.t_mem`
        (qspecl_then [`n`,`b`,`sz`,`i`] mp_tac) >> simp[]) >>
  fs[mem_bytes_at_def] >> decide_tac
QED

Theorem saved_ptr_operand_frame[local]:
  vv_holds_mods cenv cx ty raw vv mid s /\
  wb_frame cenv mid mid sm s u /\ ghost_kept_at lo cenv mid sm G tn s Gu tnu /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!l. vv_operand vv <> Label l) ==>
  eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) s /\
  (!x. vv_operand vv = Var x ==> FLOOKUP Gu x = FLOOKUP G x) /\
  op_taint tnu (vv_operand vv) = op_taint tn (vv_operand vv) /\
  op_prov Gu (vv_operand vv) = op_prov G (vv_operand vv)
Proof
  strip_tac >>
  `?w. eval_operand (vv_operand vv) s = SOME w` by
    (Cases_on `vv` >> fs[vv_holds_mods_def,vv_holds_def,vv_operand_def,expr_val_rel_def] >>
     gvs[AllCaseEqs()] >> metis_tac[]) >>
  conj_tac
  >- (simp[] >> irule eval_operand_frame >> simp[] >>
      qexistsl [`sm`,`s`] >> fs[wb_frame_def]) >>
  Cases_on `vv_operand vv` >> gvs[op_taint_def,op_prov_def,ghost_kept_at_def]
QED

Theorem saved_memory_ptr_frame[local]:
  vv_at cenv cx ty sa sm mid raw vv s /\
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) /\
  read_result cx raw mid = (INL v,mid) /\ read_result cx raw ee = (INL v,ee) /\
  wb_frame cenv mid mid sm s u /\ ghost_kept_at lo cenv mid sm G tn s Gu tnu /\
  eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) s /\
  (!x. vv_operand vv = Var x ==> FLOOKUP Gu x = FLOOKUP G x) /\
  op_taint tnu (vv_operand vv) = op_taint tn (vv_operand vv) /\
  ptr_vv_ok cx ty raw vv mid G tn s ==>
  ptr_vv_ok cx ty raw vv ee Gu tnu u
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!vt w. (vv_location vv = SOME LocMemory \/ ~is_word_type ty) /\
      evaluate_type (get_tenv cx) ty = SOME vt /\ eval_operand (vv_operand vv) s = SOME w ==>
      val_wf vt v /\
      mem_bytes_at (w2n w) (val_footprint vt v) u.vs_memory =
        mem_bytes_at (w2n w) (val_footprint vt v) s.vs_memory /\
      (!i. w2n w <= i /\ i < w2n w + val_footprint vt v /\ i IN tnu.t_mem ==> i IN tn.t_mem)` by
    (rpt gen_tac >> disch_tac >> Cases_on `vv` >>
     (gvs[vv_operand_def, vv_location_def, vv_at_def, expr_val_at_def]
      >>~- ([`mem_bytes_at _ 0 _ = _ /\ _`], simp[mem_bytes_at_def] >> decide_tac)) >>
     MATCH_MP_TAC (Q.INST [`es` |-> `mid`] saved_footprint_window) >>
     simp[SF SFY_ss] >> disj1_tac >> HINT_EXISTS_TAC >> simp[] >>
     qpat_assum `!n lb lsz. local_region _ _ _ n lb lsz ==> _` ACCEPT_TAC) >>
  Cases_on `vv` >> gvs[vv_operand_def, vv_location_def, ptr_vv_ok_def]
  >- (irule ptr_val_ok_footprint_frame >> metis_tac[]) >>
  simp[ptr_mem_ok_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `ptr_mem_ok _ _ _ _ _ _ _` mp_tac >>
  simp[ptr_mem_ok_def] >> strip_tac >>
  reverse conj_tac >- metis_tac[] >>
  rpt strip_tac >> irule robust_val_in_memory_footprint_frame >> metis_tac[]
QED

Theorem saved_slot_dead[local]:
  storage_agree (storage_dead H tr src) src dst /\
  storage_range_agree src dst w rt /\ storage_read_live H tr src w rt /\
  storage_dead H tr dst j b /\ w2n w <= j /\ j < w2n w + type_slot_size rt ==>
  dead_bytes dst (w2n w) rt j b
Proof
  strip_tac >> drule storage_agree_storage_dead >> strip_tac >>
  `dead_bytes src (w2n w) rt j b` by fs[storage_read_live_def] >>
  drule storage_range_agree_dead_bytes >> simp[]
QED

Theorem saved_nonmemory_ptr_frame:
  stmt_state_rel H ctx func cenv cx ee u /\
  vv_holds_mods cenv cx ty raw (LocatedValue ann p) ee u /\
  vv_storage_live H cx (LocatedValue ann p) ee u /\
  tnu.t_stor SUBSET (cx_dead H cx).d_stor u.vs_call_ctx.cc_address
                      (u.vs_accounts u.vs_call_ctx.cc_address).storage /\
  tnu.t_trans SUBSET (cx_dead H cx).d_trans u.vs_call_ctx.cc_address
                      (u.vs_transient u.vs_call_ctx.cc_address) /\
  p.ptr_location <> LocMemory /\ op_taint tnu p.ptr_operand = {} /\
  (p.ptr_location = LocCode ==> op_prov Gu p.ptr_operand = NONE) ==>
  ptr_vv_ok cx ty raw (LocatedValue ann p) ee Gu tnu u
Proof
  strip_tac >>
  `ann = ty` by
    (Cases_on `p.ptr_location = LocCode` >> fs[vv_holds_mods_def,vv_holds_def]) >>
  drule stmt_state_rel_state_rel >> strip_tac >>
  `u.vs_call_ctx.cc_address = cx.txn.target` by
    (drule state_rel_call_ctx_rel >> simp[call_ctx_rel_def]) >>
  simp[ptr_vv_ok_def] >> rpt gen_tac >> strip_tac >>
  conj_tac
  >- suspend "storage" >>
  suspend "transient"
QED

Resume saved_nonmemory_ptr_frame[storage]:
  strip_tac >>
  drule state_rel_storage_rel >>
  simp[storage_rel_def, GSYM (cj 2 get_storage_def),
       vfmStateTheory.lookup_account_def] >> strip_tac >>
  `storage_range_agree (get_storage cx ee F) (contract_storage u) w ty'` by
    gvs[vv_holds_mods_def,vv_holds_def,storage_holds_def] >>
  `storage_read_live H F (get_storage cx ee F) w ty'` by fs[vv_storage_live_def] >>
  `storage_dead H F (contract_storage u) (w2n k) b` by
    (qpat_x_assum `tnu.t_stor SUBSET _` mp_tac >>
     simp[cx_dead_def, contract_storage_def,vfmStateTheory.lookup_account_def,SUBSET_DEF] >>
     disch_then (qspec_then `(k,b)` mp_tac) >> simp[]) >>
  `dead_bytes (contract_storage u) (w2n w) ty' (w2n k) b` by
    metis_tac[saved_slot_dead,ADD_COMM] >>
  gvs[contract_storage_def,vfmStateTheory.lookup_account_def]
QED

Resume saved_nonmemory_ptr_frame[transient]:
  strip_tac >>
  drule state_rel_transient_rel >>
  simp[transient_rel_def, GSYM (cj 1 get_storage_def)] >> strip_tac >>
  `storage_range_agree (get_storage cx ee T) (contract_transient u) w ty'` by
    gvs[vv_holds_mods_def,vv_holds_def,storage_holds_def] >>
  `storage_read_live H T (get_storage cx ee T) w ty'` by fs[vv_storage_live_def] >>
  `storage_dead H T (contract_transient u) (w2n k) b` by
    (qpat_x_assum `tnu.t_trans SUBSET _` mp_tac >>
     simp[cx_dead_def, contract_transient_def,SUBSET_DEF] >>
     disch_then (qspec_then `(k,b)` mp_tac) >> simp[]) >>
  `dead_bytes (contract_transient u) (w2n w) ty' (w2n k) b` by
    metis_tac[saved_slot_dead,ADD_COMM] >>
  gvs[contract_transient_def]
QED
Finalise saved_nonmemory_ptr_frame[local]

(* The same read is a source premise; the reached machine pointer and its
   extent are derived here, not required of the target runner. *)
Theorem saved_target_ptr_resources_mods:
  vv_post_mods H ctx func cenv cx e es sa sm s0 mid raw vv s /\
  vv_post_mods H ctx func cenv cx e ee sa sm u ee raw vv u /\
  vv_storage_live H cx vv ee u /\
  dead_lo_ok_mods H D lo cenv cx /\ ghost_inv_at_mods D lo d cenv cx ee Gu tnu u /\
  read_result cx raw mid = (INL v,mid) /\ read_result cx raw ee = (INL v,ee) /\
  wb_frame cenv mid mid sm s u /\ ghost_kept_at lo cenv mid sm G tn s Gu tnu /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  (!l. vv_operand vv <> Label l) /\ s.vs_alloca_next <= u.vs_alloca_next /\
  ptr_vv_ok cx (post_value_type cenv e) raw vv mid G tn s /\
  ((vv_location vv = NONE /\ ~is_word_type (post_value_type cenv e) \/
    vv_location vv = SOME LocMemory) ==> ptr_buf_ok cenv e (vv_operand vv) G s) /\
  vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) mid raw vv s ==>
  ptr_vv_ok cx (post_value_type cenv e) raw vv ee Gu tnu u /\
  ((vv_location vv = NONE /\ ~is_word_type (post_value_type cenv e) \/
    vv_location vv = SOME LocMemory) ==> ptr_buf_ok cenv e (vv_operand vv) Gu u) /\
  vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee raw vv u
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt (qhdtm_x_assum `vv_post_mods` (strip_assume_tac o REWRITE_RULE [vv_post_mods_def])) >>
  drule_all saved_ptr_operand_frame >> strip_tac >>
  reverse conj_tac
  >- (conj_tac
      >- (disch_tac >> irule ptr_buf_ok_frame >> qexistsl [`G`,`s`] >> simp[] >> metis_tac[]) >>
      irule vv_store_bound_frame_mem_src >> qexists `s` >> simp[] >>
      fs[vv_store_bound_def] >> metis_tac[]) >>
  Cases_on `vv_location vv = NONE \/ vv_location vv = SOME LocMemory`
  >- (irule saved_memory_ptr_frame >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `tnu.t_stor SUBSET (cx_dead H cx).d_stor u.vs_call_ctx.cc_address
                       (u.vs_accounts u.vs_call_ctx.cc_address).storage /\
   tnu.t_trans SUBSET (cx_dead H cx).d_trans u.vs_call_ctx.cc_address
                       (u.vs_transient u.vs_call_ctx.cc_address)` by
    (fs[dead_lo_ok_mods_def,ghost_inv_at_mods_def,stor_taint_ok_at_def] >>
     metis_tac[]) >>
  Cases_on `vv` >> gvs[vv_location_def,vv_operand_def] >>
  irule saved_nonmemory_ptr_frame >>
  fs[ptr_vv_ok_def] >> qexistsl [`H`,`cenv`,`ctx`,`func`] >> simp[]
QED
