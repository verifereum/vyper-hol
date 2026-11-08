Theory bodyPtrPopStoragePureSummary
Ancestors
  bodyPtrPopStoragePureEndpoint bodyPtrPopStoragePureCounted bodyPtrPopStoragePureOutcome
  bodyPtrPopStoragePureEntry bodyPtrDefs exprSimPopNestedBase targetPlaceSimDefs
  exprSimDefs loweringPosts compileEnv exprLoweringProps venomState context
  vyperStorageBackend vyperStorage vyperValue ptrDiscipline fragGasPathPtr
  gasSummaryComposePtr appendStorageSourcePtr exprSimPopStorage words list

Theorem pop_storage_live_summary:
  storage_layout_safe cx /\
  storage_place_region cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) /\
  slots_in_range (get_storage cx es tr) (w2n slot) (ArrayTV tv (Dynamic cap)) /\
  storage_read_live cx tr (get_storage cx es tr) slot (ArrayTV tv (Dynamic cap)) /\
  target_post ctx func cenv cx es0 sa sm s0 es
    (PlaceR (StoragePlace tr slot (ArrayTV tv (Dynamic cap))))
    (Type (ArrayT ann (Dynamic cap))) (hdr,loc,pt) s /\
  compile_dynarray_pop hdr 1 (type_slot_size tv) cenv.ce_is_ctor cenv.ce_imm_alloca
    (if tr then LocTransient else LocStorage) sm = (q,sb) /\
  ci_mono sa sm /\ local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  ghost_inv d cenv cx es G tn s /\ op_prov G hdr = NONE /\ op_taint tn hdr = {} /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  fn_has_code sm sb func /\ ~ctx_has_dalloca ctx /\ es.gas_obs = [] /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  gas_summary_ptr_at (cx_dead cx) (ctx,func) PG []
    (pop_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap)))) (es,s,G,tn)
    (\res ee Gf tnf u. ?v. res = INL v /\
      vv_post ctx func cenv cx (Pop ann bt) es0 sa sb s0 ee v
        (LocatedValue ann (mk_ptr q (if tr then LocTransient else LocStorage))) u /\
      u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      ghost_inv d cenv cx ee Gf tnf u /\
      ptr_vv_ok cx ann v (LocatedValue ann (mk_ptr q (if tr then LocTransient else LocStorage)))
        ee Gf tnf u /\ ghost_kept cenv es sm G tn s Gf tnf)
    (\res ee gt r. expr_exit res r)
Proof
  strip_tac >> drule nested_pop_storage_target_metadata >> strip_tac >> gvs[] >>
  `~cx.txn.is_static /\ ~s.vs_call_ctx.cc_static /\
   s.vs_call_ctx.cc_address = cx.txn.target /\ stor_taint_ok cx tn s` by
    fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def, ghost_inv_def] >>
  drule_all nested_pop_storage_natural_region >> strip_tac >>
  drule_all nested_pop_live_array_agree >> strip_tac >>
  drule_all pop_storage_machine_live >> strip_tac >>
  drule nested_pop_array_header_load >> strip_tac >>
  `key_taint (if tr then tn.t_trans else tn.t_stor) slot = {}` by
    (irule pop_storage_live_header_clean >> goal_assum (drule_at Any) >>
     simp[type_slot_size_def] >> metis_tac[]) >>
  Cases_on `lookup_storage slot (get_storage cx es tr) = 0w`
  >- (irule pop_storage_empty_summary >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `0 < w2n (lookup_storage slot (get_storage cx es tr))` by
    (Cases_on `lookup_storage slot (get_storage cx es tr)` >> gvs[]) >>
  suspend "positive"
QED

Resume pop_storage_live_summary[positive]:
  `w2n (lookup_storage slot (get_storage cx es tr)) =
     w2n (if tr then tload slot s else sload slot s)` by metis_tac[] >>
  `0 < w2n (if tr then tload slot s else sload slot s)` by metis_tac[] >>
  drule_all pop_storage_positive_counted >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  suspend "package"
QED

Resume pop_storage_live_summary[package]:
  qabbrev_tac `len = w2n (lookup_storage slot (get_storage cx es tr))` >>
  qabbrev_tac `ee = set_storage cx es tr
    (apply_writes slot [(0,n2w (len-1))] (get_storage cx es tr))` >>
  `len <= cap` by
    (simp[Abbr `len`] >> metis_tac[pop_array_length_bound]) >>
  `vv_post ctx func cenv cx (Pop ann bt) es0 sa sb s0 ee
    (PlaceR (StoragePlace tr (slot + n2w (1+(len-1)*type_slot_size tv)) tv))
    (LocatedValue ann (mk_ptr q (if tr then LocTransient else LocStorage))) u /\
   ghost_inv d cenv cx ee Gf tnf u /\
   ptr_vv_ok cx ann
    (PlaceR (StoragePlace tr (slot + n2w (1+(len-1)*type_slot_size tv)) tv))
    (LocatedValue ann (mk_ptr q (if tr then LocTransient else LocStorage))) ee Gf tnf u /\
   ghost_kept cenv es sm G tn s Gf tnf` by
    (irule pop_storage_positive_endpoint >>
     qpat_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `declared_storage_region _ _ _ _ = _` (irule_at Any) >>
     qpat_assum `storage_subregion _ _ _ _` (irule_at Any) >>
     qexistsl [`xs`, `LENGTH sb.cs_current_insts`] >>
     rpt conj_tac >> metis_tac[markerTheory.Abbrev_def]) >>
  suspend "summary"
QED

Resume pop_storage_live_summary[summary]:
  `!tail. pop_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap)))
    (es with gas_obs := tail) =
    (INL (PlaceR (StoragePlace tr (slot + n2w (1+(len-1)*type_slot_size tv)) tv)),
      ee with gas_obs := tail)` by
    (gen_tac >>
     mp_tac (Q.INST [`es` |-> `es with gas_obs := tail`] pop_storage_positive_source) >>
     simp_tac (srw_ss()) [get_storage_gas_obs, set_storage_gas_obs] >>
     impl_tac >- simp[Abbr `len`] >>
     simp[Abbr `ee`]) >>
  `ee with gas_obs := [] = ee` by
    (simp[Abbr `ee`] >> Cases_on `tr` >>
     simp[set_storage_def, vyperStateTheory.evaluation_state_component_equality]) >>
  pure_rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl [`INL (PlaceR (StoragePlace tr
      (slot + n2w (1+(len-1)*type_slot_size tv)) tv))`, `ee`, `Gf`, `tnf`, `OK u`] >>
  qpat_x_assum `slot = _` kall_tac >>
  qpat_x_assum `len = w2n _` kall_tac >>
  qpat_x_assum `(if tr then tload _ _ else sload _ _) = _` kall_tac >>
  qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  qpat_x_assum `ptr_vv_ok _ _ _ _ _ _ _ _` mp_tac >>
  simp[] >> metis_tac[]
QED

Finalise pop_storage_live_summary
