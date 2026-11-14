(* Outcome composition for raw-RHS, target, and widened place stores. *)
Theory placeRelayoutFrag
Ancestors
  placeRelayoutOutcome placeRelayoutGasCompose placeRelayoutCode
  stmtSimProps exprLoweringProps loweringPosts stmtSimDefs gasOutcome gasSummary
  stmtSimDeclCompose placeRelayoutPhysicalSource exprSimIfExpWidenedCounted
  annassignRelayoutPost exprLowering context
  stmtSimAssignStorage stmtSimAugAssignPlaceMemory compileEnv freshWrites
  vyperStorageFootprint vyperStorageTrace vyperStoragePlaceObserved
  vyperFiniteStoragePreservation vyperPlaceTyping vyperPlaceFrames

Theorem relayout_store_stmt_post:
  vv_post H ctx func cenv cx e es sa sv s0 mid (Value v) vv s1 /\
  target_post H ctx func cenv cx mid sv st s1 ee (PlaceR p) (Type dty) tr s2 /\
  sa.cs_next_var <= sv.cs_next_var /\ sv.cs_next_var <= st.cs_next_var /\
  sa.cs_next_id <= sv.cs_next_id /\ sv.cs_next_id <= st.cs_next_id /\
  stmt_state_rel H ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sv /\
  stmt_state_rel H ctx func cenv cx ff u /\
  storage_well_formed_on cx ff (FST H) /\
  alloca_frame cenv ee st s2 cenv ff u /\
  (!x. not_fresh_at st x ==> lookup_var x u = lookup_var x s2) /\
  (!aid b. FLOOKUP s2.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
  ~u.vs_halted /\ u.vs_current_bb = sf.cs_current_bb /\
  u.vs_inst_idx = LENGTH sf.cs_current_insts /\ ~block_is_terminated sf ==>
  stmt_post H ctx func cx lctx cenv cenv sa sf es s0 (INL ()) ff u
Proof
  strip_tac >>
  `MAP FDOM mid.scopes = MAP FDOM es.scopes /\
   MAP FDOM ee.scopes = MAP FDOM mid.scopes` by
    fs[vv_post_def, target_post_def, locals_kept_def] >>
  `alloca_frame cenv es sa s0 cenv mid s1` by
    (irule vv_post_alloca_frame >> metis_tac[]) >>
  `alloca_frame cenv mid sv s1 cenv ee s2` by
    (irule target_post_alloca_frame >> fs[vv_post_def] >> metis_tac[]) >>
  `alloca_frame cenv es sa s0 cenv ee s2` by
    (irule alloca_frame_trans >>
     goal_assum (drule_at (Pat `alloca_frame _ _ _ _ _ ee s2`)) >>
     fs[vv_post_def]) >>
  `alloca_frame cenv es sa s0 cenv ff u` by
    (irule alloca_frame_trans >>
     goal_assum (drule_at (Pat `alloca_frame _ ee st s2 _ _ _`)) >>
     fs[vv_post_def, target_post_def] >> qexists_tac `st` >> simp[]) >>
  simp[stmt_post_def, stmt_lands_def, cenv_top_ext_refl] >>
  fs[vv_post_def, target_post_def] >> rpt strip_tac >>
  `not_fresh_at sv x /\ not_fresh_at st x` by
    metis_tac[not_fresh_at_mono] >>
  metis_tac[]
QED

Theorem place_pointer_write_gas_obs:
  place_ptr_rel cenv cx s (PlaceR p) w loc vt /\
  write_place cx p v ee = (res,ff) ==>
  !tail. write_place cx p v (ee with gas_obs := tail) =
    (res,ff with gas_obs := tail)
Proof
  Cases_on `p`
  >- (pure_rewrite_tac[vyperStateTheory.write_place_def] >>
      rpt strip_tac >>
      simp[stmtSimAssignStorageTheory.write_storage_slot_gas_obs])
  >- metis_tac[aug_place_memory_write_gas_obs] >>
  simp[place_ptr_rel_def]
QED

(* Lift a physical store outcome without changing its normal-or-exit split. *)
Theorem relayout_store_gas_outcome:
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func cenv cx e es sa sv s0 mid (Value v) vv s1 /\
    target_post H ctx func cenv cx mid sv st s1 ee (PlaceR p) (Type dty) tr s2 /\
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx ff (FST H)) /\
  sa.cs_next_var <= sv.cs_next_var /\ sv.cs_next_var <= st.cs_next_var /\
  sa.cs_next_id <= sv.cs_next_id /\ sv.cs_next_id <= st.cs_next_id /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sv /\
  ~block_is_terminated sf /\ write_place cx p v ee = (res,ff) /\
  gas_marked_path F ctx func s2 0 r /\
  ((?u. r = OK u /\ res = INL () /\
     (!H. valid_horizon cx st0 H ee.storage_trace ==>
       stmt_state_rel H ctx func cenv cx ff u) /\
  alloca_frame cenv ee st s2 cenv ff u /\
     (!x. not_fresh_at st x ==> lookup_var x u = lookup_var x s2) /\
     (!aid b. FLOOKUP s2.vs_allocas aid = SOME b ==> FLOOKUP u.vs_allocas aid = SOME b) /\
     ~u.vs_halted /\ u.vs_current_bb = sf.cs_current_bb /\
     u.vs_inst_idx = LENGTH sf.cs_current_insts) \/
   (exit_result r /\ !H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_exit (RetQ H) ff res r)) ==>
  gas_outcome F (cx_tops cx) (ctx,func) cx st0 (write_place cx p v) (ee,s2)
    (\H. stmt_post H ctx func cx lctx cenv cenv sa sf es s0)
    (\H res ff r. !tail. stmt_exit (RetQ H) (ff with gas_obs := tail) res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `?H. valid_horizon _ _ H _`
    (qx_choose_then `H0` assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `H0` (drule_then strip_assume_tac)) >>
  `!tail. write_place cx p v (ee with gas_obs := tail) =
      (res,ff with gas_obs := tail)` by
    (irule place_pointer_write_gas_obs >>
     fs[target_post_def] >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H ff.storage_trace ==>
    valid_horizon cx st0 H ee.storage_trace` by
    (rpt strip_tac >> irule (INST_TYPE [alpha |-> ``:unit``] valid_horizon_frame) >>
     qexistsl_tac [`write_place cx p v`, `res`, `ff`] >>
     simp[storage_trace_frame_write_place]) >>
  rewrite_tac[gas_outcome_def] >> qexists_tac `[]` >> disj2_tac >> disj1_tac >>
  rewrite_tac[gas_summary_at_def] >> qexistsl_tac [`res`, `ff`, `r`] >>
  (conj_tac >- simp[gas_marked_exec_def]) >>
  qpat_x_assum `(?u. _) \/ _` strip_assume_tac
  >- (disj1_tac >> qexists_tac `u` >> simp[stmt_post_end_gas_obs] >>
      rpt strip_tac >>
      `valid_horizon cx st0 H ee.storage_trace` by metis_tac[] >>
      qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
        (qspec_then `H` (drule_then strip_assume_tac)) >>
      irule relayout_store_stmt_post >> simp[] >>
      goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      goal_assum (drule_at (Pat `target_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[]) >>
  disj2_tac >> simp[] >> rpt strip_tac >>
  `valid_horizon cx st0 H ee.storage_trace` by metis_tac[] >>
  `stmt_exit (RetQ H) ff res r` by metis_tac[] >>
  `expr_exit res r` suffices_by simp[stmt_exit_def] >>
  Cases_on `res` >- fs[stmt_exit_def] >>
  drule vyperExprNoControlTheory.write_place_no_control >>
  fs[stmt_exit_def, vyperExprNoControlTheory.no_control_exc_def]
QED

Theorem widened_target_store_gas_outcome:
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    vv_post H ctx func cenv cx e es sa sv s0 mid (Value v) vv s1 /\
    target_post H ctx func cenv cx mid sv st s1 ee (PlaceR p) (Type dty)
      (dst,SOME loc,SOME (ValPT dty)) s2 /\
    stmt_state_rel H ctx func cenv cx es s0 /\ storage_place_observed H p) /\
  compile_expr cenv (expr_type e) e sa = (vv,sv) /\
  post_value_type cenv e = sty /\ lowered_value_type cenv e = sty /\
  sty <> expr_type e /\ ~is_word_type sty /\ ~is_bytestring_type sty /\
  compile_get_target_ptr compile_expr cenv bt sv =
    ((dst,SOME loc,SOME (ValPT dty)),st) /\
  compile_assign_value cenv dst loc (vv_operand vv) (is_word_type dty)
    (vv_location vv) dty sty
    (type_memory_bytes cenv dty) st = ((),sf) /\
  ci_mono sa sv /\ ci_mono sv st /\
  local_ptrs_reserved cenv sa /\
  local_ptrs_reserved cenv sv /\ local_ptrs_reserved cenv st /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\ dty <> sty /\
  type_widens_to (get_tenv cx) sty dty /\ assignable_type (get_tenv cx) sty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sv x /\ not_fresh_at st x) /\
  (!l. vv_operand vv <> Label l) /\
  type_memory_bytes cenv sty = type_memory_size stv /\
  type_memory_bytes cenv sty < dimword (:256) /\
  expr_sim_inv cenv cx env ee /\ acyclic_struct_metadata cenv.ce_struct_fields /\
  assign_alloc_ok cenv bt e /\
  ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
  cenv.ce_target CapMcopy /\
  write_place cx p v ee = (res,ff) /\ stmt_res_ok lctx res /\
  fn_has_code st sf func /\ fn_inst_ids_distinct func /\ ~block_is_terminated sf /\
  ~s2.vs_halted /\ s2.vs_current_bb = st.cs_current_bb /\
  s2.vs_inst_idx = LENGTH st.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func) cx st0 (write_place cx p v) (ee,s2)
    (\H. stmt_post H ctx func cx lctx cenv cenv sa sf es s0)
    (\H res ff r. !tail. stmt_exit (RetQ H) (ff with gas_obs := tail) res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `?H. valid_horizon _ _ H _`
    (qx_choose_then `H` assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `H` (drule_then strip_assume_tac)) >>
  `post_value_type cenv e <> expr_type e /\
   ~is_word_type (post_value_type cenv e) /\
   evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME stv` by fs[] >>
  `(vv_location vv = NONE \/ vv_location vv = SOME LocMemory)` by
    (drule_all compile_changed_physical_unwrap_shape >> strip_tac >>
     gvs[vv_location_def]) >>
  drule_all strict_widened_vv_physical_source >> strip_tac >>
  `stmt_state_rel H ctx func cenv cx mid s1` by fs[vv_post_def] >>
  `MAP FDOM mid.scopes = MAP FDOM ee.scopes` by
    fs[target_post_def, locals_kept_def] >>
  `0 < type_memory_size stv` by metis_tac[strict_widening_source_positive] >>
  `sa.cs_next_id <= sv.cs_next_id /\ sv.cs_next_id <= st.cs_next_id /\ sa.cs_next_var <= sv.cs_next_var /\
   sv.cs_next_var <= st.cs_next_var` by fs[ci_mono_def, cs_extends_def] >>
  `expr_val_own cenv cx sty sa sv mid v (vv_operand vv) s1` by metis_tac[] >>
  `sv.cs_next_id <= sv.cs_next_id` by simp[] >>
  `(vv_location vv = NONE \/ vv_location vv = SOME LocMemory)` by simp[] >>
  `?r. gas_marked_path F ctx func s2 0 r /\
    ((?u. r = OK u /\ res = INL () /\
       (!H. valid_horizon cx st0 H ee.storage_trace ==>
         stmt_state_rel H ctx func cenv cx ff u) /\
       (!x. not_fresh_at st x ==> lookup_var x u = lookup_var x s2) /\
       (!aid b. FLOOKUP s2.vs_allocas aid = SOME b ==>
          FLOOKUP u.vs_allocas aid = SOME b) /\
       ~u.vs_halted /\ u.vs_current_bb = sf.cs_current_bb /\
       u.vs_inst_idx = LENGTH sf.cs_current_insts /\
       alloca_frame cenv ee st s2 cenv ff u) \/
      (exit_result r /\ !H. valid_horizon cx st0 H ee.storage_trace ==>
        stmt_exit (RetQ H) ff res r))` by
    (mp_tac (Q.INST [`cfn` |-> `compile_expr`, `es` |-> `mid`,
       `op` |-> `vv_operand vv`, `s0` |-> `s1`, `s` |-> `s2`,
       `sa` |-> `sv`, `sb` |-> `st`, `si` |-> `sa`, `sj` |-> `sv`,
       `src_loc` |-> `vv_location vv`, `sw` |-> `w`]
       owned_target_relayout_store_outcome) >>
     impl_tac
     >- (simp[] >> conj_tac
         >- (qx_gen_tac `HH` >> strip_tac >>
             qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
               (qspec_then `HH` (drule_then strip_assume_tac)) >>
             fs[vv_post_def]) >>
         metis_tac[]) >>
     strip_tac >> qexists_tac `r` >> simp[]) >>
  `!HH. valid_horizon cx st0 HH ee.storage_trace ==>
    storage_well_formed_on cx ff (FST HH)` by
    (rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> _ /\ _`
       (qspec_then `HH` (drule_then strip_assume_tac)) >>
     `storage_well_formed_on cx ee (FST HH)` by fs[target_post_def] >>
     Cases_on `p`
     >- (rename1 `write_place cx (StoragePlace tr slot leaf) v ee = _` >>
         `leaf = dtv` by fs[target_post_def, place_ptr_rel_def] >>
         qpat_x_assum `leaf = dtv` SUBST_ALL_TAC >>
         qpat_x_assum `storage_place_observed HH _`
           (mp_tac o REWRITE_RULE [storage_place_observed_def]) >>
         disch_then (qx_choosel_then [`rootHH`, `tvHH`, `pathHH`, `deltaHH`]
           strip_assume_tac) >>
         `regions_consistent (FST HH)` by fs[valid_horizon_def] >>
         `storage_observations_ok cx HH [StorageRoot tr (w2n rootHH) tvHH]` by
           (simp[storage_observations_ok_def, storage_trace_regions_def,
              storage_trace_locks_def, storage_roots_fit_def,
              storage_trace_backends_well_formed_def] >>
            qpat_assum `regions_consistent (FST HH)`
              (mp_tac o Q.SPECL [`tr`, `rootHH`, `tvHH`] o CONJUNCT1 o
               REWRITE_RULE [regions_consistent_def]) >> simp[]) >>
         `well_formed_type_value dtv` by
           (qpat_assum `evaluate_type (get_tenv cx) dty = SOME dtv`
             (ACCEPT_TAC o MATCH_MP
               vyperTypeValuesTheory.evaluate_type_well_formed_type_value)) >>
         `runtime_place_typed cx ee (StoragePlace tr slot dtv) dtv` by
           simp[runtime_place_typed_storage] >>
         mp_tac (Q.INST [`H` |-> `HH`,
           `observations` |-> `[StorageRoot tr (w2n (rootHH : bytes32)) tvHH]`,
           `p` |-> `StoragePlace tr slot dtv`, `st` |-> `ee`, `st'` |-> `ff`,
           `leaf_tv` |-> `dtv`] write_place_preserves_storage_well_formed_on) >>
         impl_tac
         >- (simp[] >>
             qexistsl_tac [`pathHH`, `deltaHH`] >> simp[]) >>
         simp[])
     >- (drule write_memory_place_frame >> strip_tac >>
         `ff.accounts = ee.accounts /\ ff.tStorage = ee.tStorage` by simp[] >>
         metis_tac[storage_well_formed_on_backends]) >>
     fs[target_post_def, place_ptr_rel_def]) >>
  irule relayout_store_gas_outcome >> simp[] >>
  goal_assum (drule_at (Pat `gas_marked_path _ _ _ _ _ _`)) >> simp[] >>
  metis_tac[]
QED
