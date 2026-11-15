Theory assignPlaceStorageSuffix
Ancestors
  placeStoreSlots placeStoreStorage stmtSimDefs exprSimHyps
  loweringPosts compileEnv stmtLowering valueEncodingProps vyperScopePreservation
  vyperTyping vyperValue words vyperStorageFootprint vyperStoragePlaceObserved
Libs monadsyntax horizonTypeLib

Theorem assign_place_typed_storage_suffix_run:
  compile_store_slots cenv src dst dty (loc = LocTransient) sa = ((),sb) /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  0 < type_slot_size dtv /\ well_formed_type_value dtv /\
  value_has_type dtv v /\ val_in_memory dtv v (w2n sw) s.vs_memory /\
  w2n sw + type_memory_size dtv < dimword (:256) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME w /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  (loc = LocStorage \/ loc = LocTransient) /\
  acyclic_struct_metadata cenv.ce_struct_fields /\ expr_sim_inv cenv cx env ee /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee s /\ storage_place_observed H p /\
    regions_consistent (FST H) /\ storage_locks_separated (FST H) (SND H)) /\
  place_ptr_rel cenv cx s (PlaceR p) w (SOME loc) (Type dty) /\
  write_place cx p v ee = (INL (),ff) /\
  local_ptrs_reserved cenv sa /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func cenv cx ff t) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_frame cenv ee sa s cenv ff t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `?H. valid_horizon _ _ H _`
    (qx_choose_then `H0` assume_tac) >>
  `stmt_state_rel H0 ctx func cenv cx ee s /\ storage_place_observed H0 p /\
   regions_consistent (FST H0) /\ storage_locks_separated (FST H0) (SND H0)` by
    metis_tac[] >> pop_assum strip_assume_tac >>
  drule_all place_store_storage_destination >> strip_tac >>
  qpat_x_assum `loc = LocStorage \/ loc = LocTransient` kall_tac >> gvs[] >>
  `stmt_state_rel H0 ctx func cenv cx ee s` by metis_tac[] >>
  drule_all place_store_storage_write_inv >> strip_tac >> gvs[] >>
  `regions_consistent (FST H0)` by fs[valid_horizon_def] >>
  drule_all place_store_storage_leaf_bounds >> strip_tac >>
  `n2w (w2n root + delta) = root + n2w delta` by
    simp[GSYM wordsTheory.word_add_n2w] >>
  `(slot_loc tr = LocTransient) <=> tr` by (Cases_on `tr` >> simp[slot_loc_def]) >>
  pop_assum (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  qspecl_then [`cenv`, `src`, `dst`, `dty`, `tr`, `sa`, `sb`, `dtv`, `func`,
    `s`, `sw`, `w2n root+delta`, `ctx`, `cx`, `env`, `ee`, `writes`, `v`]
    mp_tac (at_horizon_named "H" place_store_slots_suffix_run_horizons) >>
  impl_tac >- (simp[] >> metis_tac[]) >> strip_tac >>
  `!HH. valid_horizon cx st0 HH ee.storage_trace ==>
    stmt_state_rel HH ctx func cenv cx
      (set_storage cx ee tr (apply_writes (root+n2w delta) writes
        (get_storage cx ee tr))) t` by suspend "horizons" >>
  qexists_tac `t` >> simp[] >>
  irule (at_horizon_named "H" alloca_frame_of_mem_frame) >>
  simp[vyperStorageBackendTheory.set_storage_scopes] >>
  qexistsl_tac [`H0`, `ctx`, `cx`, `func`] >> simp[] >> metis_tac[]
QED

Resume assign_place_typed_storage_suffix_run[horizons]:
  markerLib.RESUME_TAC >> rpt strip_tac >>
  `stmt_state_rel HH ctx func cenv cx ee s /\
   storage_place_observed HH (StoragePlace tr (root+n2w delta) dtv) /\
   regions_consistent (FST HH) /\ storage_locks_separated (FST HH) (SND HH)` by
    metis_tac[] >> pop_assum strip_assume_tac >>
  `?rk rt pth dl. MEM (tr,rk,rt) (FST HH) /\
    storage_subregion rt pth dl dtv /\
    root+n2w delta = rk+n2w dl` by fs[storage_place_observed_def] >>
  `w2n (root+n2w delta) = w2n rk+dl` by
    (mp_tac (Q.INST [`H` |-> `HH`, `rootk` |-> `rk`, `root` |-> `rt`,
       `path` |-> `pth`, `delta` |-> `dl`, `tv` |-> `dtv`]
       (SPEC_ALL (at_horizon_named "H" place_store_storage_leaf_bounds))) >>
     impl_tac >- simp[] >> strip_tac >> metis_tac[]) >>
  qpat_x_assum `!H rootk root path delta. _`
    (qspecl_then [`HH`, `rk`, `rt`, `pth`, `dl`] mp_tac) >>
  simp[]
QED
Finalise assign_place_typed_storage_suffix_run
